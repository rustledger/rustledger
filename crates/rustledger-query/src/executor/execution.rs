//! Query execution functions for different query types.

use rayon::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};

use rustledger_core::{Amount, Directive, Inventory, NaiveDate, Position};

/// Threshold for parallel row evaluation. Below this, sequential is faster.
const PARALLEL_THRESHOLD: usize = 1000;

use crate::ast::{
    CreateTableStmt, Expr, FunctionCall, InsertSource, InsertStmt, SelectQuery, Target,
    UnaryOperator,
};
use crate::error::QueryError;

use super::Executor;
use super::types::{PostingSource, QueryResult, Row, RowOrigin, Table, TableRow, Value, hash_row};

/// Normalized form of a `JOURNAL ... AT <mode>` clause.
///
/// Computed once per query rather than calling `to_uppercase()` per row —
/// avoids per-row allocations and lets the inner loop branch on a copy
/// type. `Other` covers any unrecognized AT mode (treated like the
/// default branch in row construction).
#[derive(Copy, Clone, PartialEq, Eq)]
enum AtMode {
    None,
    Cost,
    Units,
    Other,
}

impl AtMode {
    const fn from_query(at_function: Option<&str>) -> Self {
        match at_function {
            None => Self::None,
            Some(s) if s.eq_ignore_ascii_case("COST") => Self::Cost,
            Some(s) if s.eq_ignore_ascii_case("UNITS") => Self::Units,
            Some(_) => Self::Other,
        }
    }
}

/// Widths `JOURNAL` applies to its payee and narration columns, matching
/// beancount's `transform_journal` (`MAXWIDTH(payee, 48)` /
/// `MAXWIDTH(narration, 80)`).
const JOURNAL_PAYEE_MAXWIDTH: i64 = 48;
/// See [`JOURNAL_PAYEE_MAXWIDTH`].
const JOURNAL_NARRATION_MAXWIDTH: i64 = 80;

impl Executor<'_> {
    /// Execute a SELECT query.
    pub(super) fn execute_select(&self, query: &SelectQuery) -> Result<QueryResult, QueryError> {
        self.execute_select_with_origins(query, false)
    }

    /// [`Self::execute_select`], with each row's [`RowOrigin`] kept in the
    /// result when `keep_origins` is set and the row has one (#2442): a
    /// subquery's rows for its outer query, and the rows a table stores.
    ///
    /// A row has one when it was read from one posting and at least one of
    /// its columns passes that posting's `position` through unchanged. A
    /// grouped, aggregated or DISTINCT result keeps none: its rows have no
    /// one posting behind them (a DISTINCT row stands for every posting with
    /// those values), so they answer from the values.
    pub(super) fn execute_select_with_origins(
        &self,
        query: &SelectQuery,
        keep_origins: bool,
    ) -> Result<QueryResult, QueryError> {
        // Check if we have a subquery
        if let Some(from) = &query.from {
            if let Some(subquery) = &from.subquery {
                return self.execute_select_from_subquery(query, subquery, keep_origins);
            }
            // Check if we're selecting from a user-created table
            if let Some(table_name) = &from.table_name {
                return self.execute_select_from_table(query, table_name, keep_origins);
            }
        }

        // A double-quoted string naming a posting column is that column, as
        // in bean-query (#2596).
        if let Some(resolved) =
            self.resolve_double_quoted_columns(query, super::quoted_columns::is_posting_column)
        {
            return self.execute_select_with_origins(&resolved, keep_origins);
        }

        // Find ORDER BY expressions not in SELECT and add as hidden columns.
        let hidden_targets = self.find_hidden_order_by_targets(query);
        let num_hidden = hidden_targets.len();

        // Create extended targets including hidden columns
        let mut extended_targets = query.targets.clone();
        extended_targets.extend(hidden_targets);

        // Determine column names (including hidden columns)
        let column_names = self.resolve_column_names(&extended_targets)?;
        let mut result = QueryResult::new(column_names.clone());

        // Collect matching postings
        let postings = self.collect_postings(query)?;

        // Check if this is an aggregate query.
        // A query is aggregate if any SELECT target contains an aggregate function,
        // or if it has an explicit GROUP BY or HAVING clause.
        let is_aggregate = Self::is_aggregate_query(query);

        // The columns holding each row's posting `position`, when the rows
        // keep their origin.
        let position_columns = (keep_origins && !is_aggregate && !query.distinct)
            .then(|| Self::position_columns(&query.targets))
            .filter(|columns| !columns.is_empty());
        let origin_of = |ctx: &super::PostingContext<'_>| {
            position_columns.as_ref().map(|columns| RowOrigin {
                posting: Self::context_source(ctx),
                columns: std::sync::Arc::clone(columns),
            })
        };

        if is_aggregate {
            // Determine GROUP BY expressions:
            // - If explicit GROUP BY is provided, use it
            // - Otherwise, implicitly group by non-aggregate columns in SELECT
            //   (matches Python beancount behavior)
            let group_by_exprs: Option<Vec<Expr>> = if let Some(ref group_exprs) = query.group_by {
                Some(Self::resolve_group_by_aliases(group_exprs, &query.targets)?)
            } else {
                let implicit = Self::extract_implicit_group_by_exprs(&query.targets);
                if implicit.is_empty() {
                    None // Pure aggregate like SELECT count(*)
                } else {
                    Some(implicit)
                }
            };

            // Group and aggregate
            let grouped = self.group_postings(&postings, group_by_exprs.as_ref())?;
            for (group_key, group) in grouped {
                // Use extended_targets to include hidden columns for ORDER BY
                let row = self.evaluate_aggregate_row(&extended_targets, &group)?;

                // Apply HAVING filter on aggregated row
                // Note: HAVING only references visible columns, which are at indices 0..N
                if let Some(having_expr) = &query.having
                    && !self.evaluate_having_filter(
                        having_expr,
                        &row,
                        &column_names,
                        &query.targets,
                        &group,
                    )?
                {
                    continue;
                }

                // Carry the GROUP BY key alongside the aggregated row so the
                // text renderer can recover per-row currency context for
                // numeric aggregates (issue #988).
                result.add_aggregate_row(row, group_key);
            }
        } else {
            // Check if query has window functions
            let window_contexts = if Self::has_window_functions(&extended_targets) {
                Some(self.compute_window_contexts(&postings, &extended_targets)?)
            } else {
                None
            };

            // Simple query - one row per posting
            // Use parallel evaluation for large datasets
            let use_parallel = postings.len() >= PARALLEL_THRESHOLD && window_contexts.is_none();

            if use_parallel {
                // Parallel row evaluation
                let rows: Result<Vec<Row>, QueryError> = postings
                    .par_iter()
                    .map(|ctx| self.evaluate_row(&extended_targets, ctx))
                    .collect();
                let rows = rows?;

                if query.distinct {
                    // Sequential deduplication after parallel evaluation
                    let mut seen_hashes: FxHashSet<u64> =
                        FxHashSet::with_capacity_and_hasher(rows.len(), Default::default());
                    for row in rows {
                        let row_hash = hash_row(&row);
                        if seen_hashes.insert(row_hash) {
                            result.add_row(row);
                        }
                    }
                } else {
                    // Bulk-assign for performance, but keep the
                    // `row_group_keys` sidecar in lockstep with `rows`
                    // (issue #1175). The sidecar is a load-bearing
                    // invariant — `QueryResult::sort_by` `assert_eq!`s
                    // the lengths because a desynced sidecar would
                    // silently apply the wrong currency hint to a row.
                    // Non-aggregate rows get `None` per row, matching
                    // what `add_row` would set.
                    let n = rows.len();
                    result.rows = rows;
                    result.row_group_keys.resize(n, None);
                    if position_columns.is_some() {
                        result.row_origins = postings.iter().map(origin_of).collect();
                    }
                }
            } else {
                // Sequential evaluation for small datasets or window queries
                let mut seen_hashes: FxHashSet<u64> = if query.distinct {
                    FxHashSet::with_capacity_and_hasher(postings.len(), Default::default())
                } else {
                    FxHashSet::default()
                };

                for (i, ctx) in postings.iter().enumerate() {
                    // Use extended_targets to include hidden columns for ORDER BY
                    let row = if let Some(ref wctxs) = window_contexts {
                        self.evaluate_row_with_window(&extended_targets, ctx, Some(&wctxs[i]))?
                    } else {
                        self.evaluate_row(&extended_targets, ctx)?
                    };
                    if query.distinct {
                        // O(1) hash-based deduplication
                        let row_hash = hash_row(&row);
                        if seen_hashes.insert(row_hash) {
                            result.add_row(row);
                        }
                    } else {
                        result.add_row_with_origin(row, origin_of(ctx));
                    }
                }
            }
        }

        // Apply ORDER BY (BEFORE PIVOT — matches bean-query order, and
        // means the strip-hidden step below operates on the
        // pre-pivot shape where hidden cols are still trailing).
        if let Some(order_by) = &query.order_by {
            let visible_cols = result.columns.len() - num_hidden;
            self.sort_results(&mut result, order_by, visible_cols)?;
        }
        // NO fallback sort. Grouped output keeps the order the groups were
        // first seen in, which is what `group_postings` preserves and what
        // bean-query does.
        //
        // This branch used to sort by the first column when a query grouped
        // without an ORDER BY, claiming to match Python beancount. It does
        // not -- verified against beanquery 0.2.0, which returns groups in
        // first-appearance order for both explicit and implicit GROUP BY:
        //
        //   SELECT account, year, sum(number) GROUP BY account, year
        //     bean-query  Assets:A/2024, Equity:O/2024, Assets:B/2025, ...
        //     sorted      Assets:A/2024, Assets:B/2025, Equity:O/2024, ...
        //
        // The sort also applied HERE and not in the aggregate `FROM` path,
        // so the same query returned differently-ordered rows depending on
        // whether the user wrote `FROM #postings` -- and with a LIMIT, that
        // meant different ROWS (#2235). Insertion order is deterministic on
        // its own, so nothing is lost by dropping it.

        // Remove hidden columns after sorting (BEFORE PIVOT). With this
        // order, PIVOT operates on the visible-only shape and doesn't
        // need to know anything about hidden columns. Pre-#1034 the
        // strip ran AFTER pivot, but `apply_pivot` reshapes the
        // column layout so the trailing positions become pivot values
        // (not hidden cols), and the strip silently dropped pivot
        // values instead.
        if num_hidden > 0 {
            let visible_count = result.columns.len() - num_hidden;
            result.columns.truncate(visible_count);
            for row in &mut result.rows {
                row.truncate(visible_count);
            }
        }

        // Apply PIVOT BY transformation (AFTER sort + strip — see above
        // comment). At this point `result` is in its final pre-pivot
        // shape: only visible select targets, sorted as the user
        // requested.
        if let Some(pivot_exprs) = &query.pivot_by {
            result = self.apply_pivot(
                &result,
                pivot_exprs,
                &query.group_by,
                query.order_by.is_some(),
            )?;
        }

        // Apply LIMIT
        if let Some(limit) = query.limit {
            result.truncate(limit as usize);
        }

        Ok(result)
    }

    /// Find ORDER BY expressions not already in SELECT.
    ///
    /// These are added as hidden columns for sorting, then stripped from the final output.
    /// For aggregate queries with explicit GROUP BY, only expressions in GROUP BY or
    /// aggregate expressions are allowed. Returns targets with aliases set to the full
    /// expression string for column-name matching in `sort_results`.
    fn find_hidden_order_by_targets(&self, query: &SelectQuery) -> Vec<Target> {
        let Some(order_by) = &query.order_by else {
            return Vec::new();
        };

        let mut hidden = Vec::new();
        for spec in order_by {
            // Positional ordinals (`ORDER BY 1`) reference an existing SELECT
            // column by position; they are resolved in `sort_results` and must
            // not be materialized as a hidden constant column (which would make
            // the sort key the literal integer for every row).
            if matches!(spec.expr, Expr::Literal(crate::ast::Literal::Integer(_))) {
                continue;
            }
            // For aggregate queries, only allow ORDER BY on expressions that are
            // in GROUP BY or are themselves aggregates.
            if let Some(group_by) = &query.group_by {
                // A GROUP BY entry names the expression directly, or a target
                // holding it by position (`GROUP BY 1`) or by alias. Only the
                // first was recognized, so `SELECT account AS a, count(*)
                // GROUP BY 1 ORDER BY account` sorted by a column named
                // `account` that the output did not have, and failed (#2596,
                // where `SELECT "account"` heads its column `"account"`).
                let target_holds = |t: Option<&Target>| t.is_some_and(|t| t.expr == spec.expr);
                let in_group_by = group_by.iter().any(|g| match g {
                    _ if *g == spec.expr => true,
                    Expr::Literal(crate::ast::Literal::Integer(n)) => target_holds(
                        usize::try_from(*n)
                            .ok()
                            .and_then(|n| n.checked_sub(1))
                            .and_then(|i| query.targets.get(i)),
                    ),
                    Expr::Column(name) => target_holds(
                        query
                            .targets
                            .iter()
                            .find(|t| t.alias.as_deref() == Some(name.as_str())),
                    ),
                    _ => false,
                });
                let is_aggregate = Self::is_aggregate_expr(&spec.expr);
                if !in_group_by && !is_aggregate {
                    continue;
                }
            }

            // Check if this ORDER BY is already reachable by name in the
            // projected output. A target only covers it when the sorted output
            // column carries the ORDER BY's name: either the target is
            // unaliased (its output name is the expression itself) or its alias
            // equals the ORDER BY reference. A target whose expression matches
            // but is aliased to a *different* name does NOT cover it — the
            // output column is named by the alias, so `sort_results` would fail
            // a literal name lookup for the raw column (#1627). In that case we
            // still append a hidden column carrying the raw name.
            // Same spelling the header uses, and the same one `sort_results`
            // now looks up. These two have to agree: a hidden column named by
            // `Display` would be invisible to a lookup by `header_name`, so
            // changing one alone trades one miss for another (#2177).
            let expr_str = crate::ast::header_name(&spec.expr);
            let in_select = query.targets.iter().any(|t| {
                (t.expr == spec.expr && t.alias.is_none())
                    || t.alias.as_deref() == Some(expr_str.as_str())
            });

            if !in_select {
                hidden.push(Target {
                    expr: spec.expr.clone(),
                    alias: Some(expr_str),
                });
            }
        }

        hidden
    }

    /// The output columns of default-FROM `targets` that hold the posting's
    /// `position` as it is: a bare `position` column, renamed or not, and the
    /// `position` a `SELECT *` expands to. Any other expression, such as
    /// `units(position)`, is a value the posting does not answer for.
    fn position_columns(targets: &[Target]) -> std::sync::Arc<[usize]> {
        let wildcard_position = super::WILDCARD_COLUMNS
            .iter()
            .position(|c| *c == "position");
        let mut columns = Vec::new();
        let mut index = 0;
        for target in targets {
            match &target.expr {
                Expr::Wildcard => {
                    if let Some(offset) = wildcard_position {
                        columns.push(index + offset);
                    }
                    index += super::WILDCARD_COLUMNS.len();
                }
                Expr::Column(name) => {
                    if name.eq_ignore_ascii_case("position") {
                        columns.push(index);
                    }
                    index += 1;
                }
                _ => index += 1,
            }
        }
        columns.into()
    }

    /// Where the posting a default-FROM row reads lives: in the ledger, by
    /// index, or in the transaction a FROM clause synthesized.
    pub(super) fn context_source(ctx: &super::PostingContext<'_>) -> PostingSource {
        let posting = ctx.posting_index;
        match (&ctx.transaction, ctx.directive_index) {
            (super::TransactionRef::Ledger(_), Some(directive)) => {
                PostingSource::Ledger { directive, posting }
            }
            (super::TransactionRef::Ledger(txn), None) => PostingSource::Shared {
                transaction: std::sync::Arc::new((*txn).clone()),
                posting,
            },
            (super::TransactionRef::Synthesized(txn), _) => PostingSource::Shared {
                transaction: std::sync::Arc::clone(txn),
                posting,
            },
        }
    }

    /// Whether `query` calls `weight`, `cost` or `sum` on a bare column
    /// anywhere: the calls a row's origin answers (#2442). Its source keeps
    /// origins only then, so a query that reads none pays nothing for them.
    fn reads_posting_functions(query: &SelectQuery) -> bool {
        let mut reads = false;
        let mut note = |expr: &Expr| {
            if let Expr::Function(call) = expr
                && let [Expr::Column(_)] = call.args.as_slice()
                && ["WEIGHT", "COST", "SUM"]
                    .iter()
                    .any(|f| call.name.eq_ignore_ascii_case(f))
            {
                reads = true;
            }
        };
        for target in &query.targets {
            super::visit_expr(&target.expr, &mut note);
        }
        for expr in query
            .where_clause
            .iter()
            .chain(query.having.iter())
            .chain(query.group_by.iter().flatten())
            .chain(query.order_by.iter().flatten().map(|o| &o.expr))
        {
            super::visit_expr(expr, &mut note);
        }
        reads
    }

    /// Execute a SELECT query that sources from a subquery.
    pub(super) fn execute_select_from_subquery(
        &self,
        outer_query: &SelectQuery,
        inner_query: &SelectQuery,
        keep_origins: bool,
    ) -> Result<QueryResult, QueryError> {
        // Execute the inner query first, keeping each row's posting when the
        // outer query can read `weight`, `cost` or `sum` of a column passing
        // it through, or must keep it itself (#2442).
        let inner_keeps = keep_origins || Self::reads_posting_functions(outer_query);
        let inner_result = self.execute_select_with_origins(inner_query, inner_keeps)?;

        // A double-quoted string naming one of the subquery's columns is that
        // column, as in bean-query (#2596). Known only now that the inner
        // query has run; the rewritten query starts over, since whether the
        // inner rows need their postings may differ.
        if let Some(resolved) = self.resolve_double_quoted_columns(outer_query, |name| {
            inner_result.columns.iter().any(|c| c == name)
        }) {
            return self.execute_select_from_subquery(&resolved, inner_query, keep_origins);
        }

        // Build a column name -> index mapping for the inner result
        let inner_column_map: FxHashMap<String, usize> = inner_result
            .columns
            .iter()
            .enumerate()
            .map(|(i, name)| (name.to_lowercase(), i))
            .collect();

        // Aggregate queries over a subquery must group/aggregate, exactly like
        // the table-source path (`execute_select_from_table`). Without this,
        // `SELECT count(*) FROM (SELECT ...)` was evaluated per inner row,
        // yielding one (empty) row per row instead of a single aggregated value.
        let is_aggregate = Self::is_aggregate_query(outer_query);
        if is_aggregate {
            let table = Table {
                columns: inner_result.columns,
                rows: inner_result.rows,
                // An inner result's columns are already wildcard-expanded.
                hidden: Vec::new(),
                origins: inner_result.row_origins,
            };
            return self.execute_aggregate_from_table(outer_query, &table, &inner_column_map);
        }

        // ORDER BY expressions the outer query does not select, such as a
        // subquery column it leaves out (`SELECT account FROM (SELECT date,
        // account) ORDER BY date`), are evaluated as hidden trailing columns
        // and stripped after sorting, as `execute_select` and the table path
        // do (#2436).
        let hidden_targets = self.find_hidden_order_by_targets(outer_query);
        let num_hidden = hidden_targets.len();
        let mut extended_targets = outer_query.targets.clone();
        extended_targets.extend(hidden_targets);

        // Determine outer column names (including hidden columns)
        let outer_column_names =
            self.resolve_subquery_column_names(&extended_targets, &inner_result.columns, &[])?;
        let mut result = QueryResult::new(outer_column_names);

        // Use FxHashSet for O(1) DISTINCT deduplication
        let mut seen_hashes: FxHashSet<u64> = if outer_query.distinct {
            FxHashSet::with_capacity_and_hasher(inner_result.rows.len(), Default::default())
        } else {
            FxHashSet::default()
        };

        // The postings this query's own rows keep, for a query over it.
        let mut carrier = (keep_origins && !outer_query.distinct).then(|| {
            OriginCarrier::new(
                &outer_query.targets,
                &inner_column_map,
                &inner_result.columns,
                &[],
            )
        });

        // Process each row from the inner result
        for i in 0..inner_result.rows.len() {
            let inner_row = TableRow::at(&inner_result.rows, &inner_result.row_origins, i);
            // Apply outer WHERE clause if present
            if let Some(where_expr) = &outer_query.where_clause
                && !self.evaluate_subquery_filter(where_expr, inner_row, &inner_column_map)?
            {
                continue;
            }

            // Evaluate outer targets (including hidden columns)
            let outer_row = self.evaluate_subquery_row(
                &extended_targets,
                inner_row,
                &inner_column_map,
                &inner_result.columns,
                &[],
            )?;

            if outer_query.distinct {
                // O(1) hash-based deduplication, over the visible columns
                // only: a hidden sort column must not split duplicates.
                let row_hash = hash_row(&outer_row[..outer_row.len() - num_hidden]);
                if seen_hashes.insert(row_hash) {
                    result.add_row(outer_row);
                }
            } else {
                let origin = carrier
                    .as_mut()
                    .and_then(|carrier| carrier.carry(inner_row.origin));
                result.add_row_with_origin(outer_row, origin);
            }
        }

        // Apply ORDER BY, then remove the hidden columns
        let visible_cols = result.columns.len() - num_hidden;
        if let Some(order_by) = &outer_query.order_by {
            self.sort_results(&mut result, order_by, visible_cols)?;
        }
        result.columns.truncate(visible_cols);
        for row in &mut result.rows {
            row.truncate(visible_cols);
        }

        // Apply LIMIT
        if let Some(limit) = outer_query.limit {
            result.truncate(limit as usize);
        }

        Ok(result)
    }

    /// Whether `name` is a column a FROM filter can read: evaluated on a
    /// one-posting sample transaction by the FROM filter itself, so the
    /// answer cannot drift from what the filter resolves (#2435).
    fn is_from_filter_column(&self, name: &str) -> bool {
        let Some(date) = rustledger_core::naive_date(2000, 1, 1) else {
            return true;
        };
        let sample = rustledger_core::Transaction::new(date, "").with_synthesized_posting(
            rustledger_core::Posting::new(
                "Assets:Sample",
                rustledger_core::Amount::new(rust_decimal::Decimal::ONE, "SAMPLE"),
            ),
        );
        !matches!(
            self.evaluate_from_filter(&Expr::Column(name.to_string()), &sample, 0, None, None),
            Err(QueryError::UnknownColumn(_))
        )
    }

    /// Execute a SELECT query that sources from a user-created or built-in table.
    ///
    /// Built-in tables (system tables) start with `#`:
    /// - `#prices`: Price directives from the ledger
    pub(super) fn execute_select_from_table(
        &self,
        query: &SelectQuery,
        table_name: &str,
        keep_origins: bool,
    ) -> Result<QueryResult, QueryError> {
        // Check for user-created tables first (exact match takes precedence),
        // then fall back to built-in system tables (which support aliases like
        // "transactions" for "#transactions" for beancount compatibility).
        let builtin_table;
        let table = if let Some(user_table) = self.tables.get(table_name) {
            user_table
        } else if let Some(builtin) = self.get_builtin_table(table_name, query)? {
            builtin_table = builtin;
            &builtin_table
        } else {
            let hint = if table_name.starts_with('#') {
                ". Available system tables: #accounts, #balances, #commodities, #documents, #entries, #events, #notes, #postings, #prices, #transactions"
            } else {
                ""
            };
            let missing =
                || QueryError::Evaluation(format!("table '{table_name}' does not exist{hint}"));
            // A bare name that is no table is an expression, the FROM filter,
            // as beanquery reads it: `FROM flag` filters on `flag`. The parser
            // cannot tell the two apart, so it hands every such name here.
            // (It read `FROM flag;` and a subquery's `FROM flag)` as filters
            // only because it could not parse a table there, #2435, and
            // `FROM flag` alone as a missing table.) A name that is no column
            // either is the table it was written as, and missing, decided
            // before running anything, so a ledger with no transaction to
            // evaluate it on reports it too, as beanquery's compiler does.
            if !table_name.starts_with('#')
                && self.is_from_filter_column(table_name)
                && let Some(from) = &query.from
            {
                let as_filter = SelectQuery {
                    from: Some(crate::ast::FromClause {
                        table_name: None,
                        filter: Some(Expr::Column(table_name.to_string())),
                        ..from.clone()
                    }),
                    ..query.clone()
                };
                return self.execute_select_with_origins(&as_filter, keep_origins);
            }
            return Err(missing());
        };

        // A double-quoted string naming one of the table's columns is that
        // column, as in bean-query (#2596). The rewritten query starts over:
        // a built-in table is built for the columns the query reads.
        if let Some(resolved) = self
            .resolve_double_quoted_columns(query, |name| table.columns.iter().any(|c| c == name))
        {
            return self.execute_select_from_table(&resolved, table_name, keep_origins);
        }

        // Build a column name -> index mapping for the table
        let column_map: FxHashMap<String, usize> = table
            .columns
            .iter()
            .enumerate()
            .map(|(i, name)| (name.to_lowercase(), i))
            .collect();

        // Check if this is an aggregate query; if so, use the grouping path.
        // A query is aggregate if any SELECT target contains an aggregate function,
        // or if it has an explicit GROUP BY or HAVING clause.
        let is_aggregate = Self::is_aggregate_query(query);

        if is_aggregate {
            return self.execute_aggregate_from_table(query, table, &column_map);
        }

        // Find ORDER BY expressions not in SELECT and add as hidden columns.
        let hidden_targets = self.find_hidden_order_by_targets(query);
        let num_hidden = hidden_targets.len();
        let mut extended_targets = query.targets.clone();
        extended_targets.extend(hidden_targets);

        // Determine column names for the result (including hidden columns)
        let column_names =
            self.resolve_subquery_column_names(&extended_targets, &table.columns, &table.hidden)?;
        let mut result = QueryResult::new(column_names);

        // Use FxHashSet for O(1) DISTINCT deduplication
        let mut seen_hashes: FxHashSet<u64> = if query.distinct {
            FxHashSet::with_capacity_and_hasher(table.rows.len(), Default::default())
        } else {
            FxHashSet::default()
        };

        // `balance` is a running total over the post-WHERE output stream, in
        // table (entry) order — a streaming window column, not a property of a
        // posting. The materialized table carries an UNFILTERED snapshot, which
        // is wrong the moment WHERE drops rows that carry other commodities
        // (e.g. `... WHERE account = "Assets:Bank"` must not see the AAPL leg of
        // a stock purchase). Recompute it here over the surviving rows, in entry
        // order, before ORDER BY — mirroring the default path's `collect_postings`.
        // Gated so non-balance queries pay nothing (the per-row Inventory clone
        // was the #1080 hot path). `account_balance` is intentionally NOT
        // recomputed: it is the account's true ledger balance across all postings.
        let balance_idx = column_map.get("balance").copied();
        let position_idx = column_map.get("position").copied();
        // `SELECT *` expands to every table column (including `balance`), but
        // `query_references_column` doesn't see through the wildcard — so treat a
        // wildcard target as referencing `balance`, else `SELECT * FROM #postings
        // WHERE ...` would still emit the pre-WHERE snapshot.
        let selects_all = query
            .targets
            .iter()
            .any(|t| matches!(t.expr, Expr::Wildcard));
        let track_balance = balance_idx.is_some()
            && position_idx.is_some()
            && (selects_all || super::query_references_column(query, "balance"));
        // SHARED backing: this is cloned once per output row below, and the
        // clone is what #1086 is about — a contiguous copy per row holds
        // O(rows x lots) positions at once. Structural sharing makes each
        // snapshot O(1) and the chain O(base + deltas).
        let mut running_balance = Inventory::new_shared();

        // The postings this query's own rows keep, for a query over it.
        let mut carrier = (keep_origins && !query.distinct).then(|| {
            OriginCarrier::new(&query.targets, &column_map, &table.columns, &table.hidden)
        });

        // Process each row from the table
        for i in 0..table.rows.len() {
            let row = table.row(i);
            // Apply WHERE clause if present
            if let Some(where_expr) = &query.where_clause
                && !self.evaluate_subquery_filter(where_expr, row, &column_map)?
            {
                continue;
            }

            // Recompute the running `balance` cell over WHERE-surviving rows.
            let overridden_row;
            let row = if track_balance {
                if let Some(Value::Position(pos)) = position_idx.map(|i| &row[i]) {
                    running_balance
                        .add((**pos).clone())
                        .map_err(|e| QueryError::Evaluation(e.to_string()))?;
                }
                let mut r = row.to_vec();
                if let Some(i) = balance_idx {
                    r[i] = Value::Inventory(std::sync::Arc::new(running_balance.clone()));
                }
                overridden_row = r;
                TableRow {
                    values: &overridden_row,
                    origin: row.origin,
                }
            } else {
                row
            };

            // Evaluate targets (including hidden columns)
            let result_row = self.evaluate_subquery_row(
                &extended_targets,
                row,
                &column_map,
                &table.columns,
                &table.hidden,
            )?;

            if query.distinct {
                // DISTINCT should only consider visible columns, not hidden sort columns.
                let visible: Vec<Value>;
                let hash_target = if num_hidden > 0 {
                    visible = result_row[..result_row.len() - num_hidden].to_vec();
                    &visible
                } else {
                    &result_row
                };
                let row_hash = hash_row(hash_target);
                if seen_hashes.insert(row_hash) {
                    result.add_row(result_row);
                }
            } else {
                let origin = carrier
                    .as_mut()
                    .and_then(|carrier| carrier.carry(row.origin));
                result.add_row_with_origin(result_row, origin);
            }
        }

        // Apply ORDER BY
        if let Some(order_by) = &query.order_by {
            let visible_cols = result.columns.len() - num_hidden;
            self.sort_results(&mut result, order_by, visible_cols)?;
        }

        // Remove hidden columns after sorting
        if num_hidden > 0 {
            let visible_count = result.columns.len() - num_hidden;
            result.columns.truncate(visible_count);
            for row in &mut result.rows {
                row.truncate(visible_count);
            }
        }

        // Apply PIVOT BY, in the same pipeline slot `execute_select` uses:
        // after ORDER BY and the hidden-column strip, before LIMIT. Omitting
        // it here meant a query with a FROM clause parsed its PIVOT BY, built
        // the transformation's validated inputs, and then returned the
        // un-pivoted result with no error (#2216).
        //
        // PIVOT BY requires GROUP BY, and a query with GROUP BY is routed to
        // `execute_aggregate_from_table`, so reaching `apply_pivot` from here
        // always ends in `PivotWithoutGroupBy`. That is the point: the clause
        // is refused out loud rather than dropped.
        if let Some(pivot_exprs) = &query.pivot_by {
            result = self.apply_pivot(
                &result,
                pivot_exprs,
                &query.group_by,
                query.order_by.is_some(),
            )?;
        }

        // Apply LIMIT
        if let Some(limit) = query.limit {
            result.truncate(limit as usize);
        }

        Ok(result)
    }

    /// Execute an aggregate SELECT query (with GROUP BY / aggregate functions) against a table.
    ///
    /// Groups the table rows by the GROUP BY expressions, evaluates aggregate functions
    /// per group, applies HAVING filtering, then ORDER BY and LIMIT.
    fn execute_aggregate_from_table(
        &self,
        query: &SelectQuery,
        table: &Table,
        column_map: &FxHashMap<String, usize>,
    ) -> Result<QueryResult, QueryError> {
        use rustc_hash::FxHashMap as HashMap;

        // ORDER BY expressions the query does not select, such as an
        // aggregate (`GROUP BY account ORDER BY count(*)`), are evaluated per
        // group as hidden trailing columns and stripped after sorting, as
        // `execute_select` does. Without them the sort could not find the
        // expression (#2436).
        let hidden_targets = self.find_hidden_order_by_targets(query);
        let num_hidden = hidden_targets.len();
        let mut extended_targets = query.targets.clone();
        extended_targets.extend(hidden_targets);

        // Determine column names for the result (including hidden columns)
        let column_names =
            self.resolve_subquery_column_names(&extended_targets, &table.columns, &table.hidden)?;
        let mut result = QueryResult::new(column_names.clone());

        // Determine GROUP BY expressions.
        // If no explicit GROUP BY, implicitly group by non-aggregate columns (beancount compat).
        let group_by_exprs: Option<Vec<Expr>> = if let Some(ref exprs) = query.group_by {
            Some(Self::resolve_group_by_aliases(exprs, &query.targets)?)
        } else {
            let implicit = Self::extract_implicit_group_by_exprs(&query.targets);
            if implicit.is_empty() {
                None // Pure aggregate like SELECT count(*)
            } else {
                Some(implicit)
            }
        };

        // Group table rows by GROUP BY key.
        // Maintain a Vec of keys in insertion order for deterministic results.
        let mut group_map: HashMap<String, (Vec<Value>, Vec<TableRow<'_>>)> = HashMap::default();
        let mut key_order: Vec<String> = Vec::new();

        for i in 0..table.rows.len() {
            let row = table.row(i);
            // Apply WHERE clause if present
            if let Some(where_expr) = &query.where_clause
                && !self.evaluate_subquery_filter(where_expr, row, column_map)?
            {
                continue;
            }

            let key_values: Vec<Value> = if let Some(ref exprs) = group_by_exprs {
                exprs
                    .iter()
                    .map(|expr| self.evaluate_subquery_expr(expr, row, column_map))
                    .collect::<Result<Vec<_>, _>>()?
            } else {
                vec![]
            };

            let key = Self::make_group_key(&key_values);
            let entry = group_map.entry(key.clone()).or_insert_with(|| {
                key_order.push(key);
                (key_values, Vec::new())
            });
            entry.1.push(row);
        }

        // For pure aggregates (no GROUP BY), always produce one row even if no
        // rows matched: COUNT(*) should return 0, SUM/AVG return NULL.
        if group_map.is_empty() && group_by_exprs.is_none() {
            let empty_key = String::new();
            group_map.insert(empty_key.clone(), (vec![], vec![]));
            key_order.push(empty_key);
        } else if group_map.is_empty() {
            // No groups, so no rows -- but do NOT return here. ORDER BY and
            // LIMIT are no-ops on an empty result, PIVOT is not: it reshapes
            // the COLUMNS, and skipping it left `WHERE <no match> ... PIVOT BY`
            // reporting the un-pivoted header while the same query emptied by
            // HAVING reported the pivoted one. bean-query gives the pivoted
            // shape for both (#2216).
            return self.finish_aggregate_result(result, query, num_hidden);
        }

        // Build alias map once (used by HAVING evaluation).
        let alias_map: HashMap<String, usize> = query
            .targets
            .iter()
            .enumerate()
            .filter_map(|(i, t)| t.alias.as_ref().map(|a| (a.to_uppercase(), i)))
            .collect();
        let col_map: HashMap<String, usize> = column_names
            .iter()
            .enumerate()
            .map(|(i, name)| (name.to_uppercase(), i))
            .collect();

        // Evaluate aggregate expressions per group and apply HAVING.
        // Iterate in insertion order for deterministic results.
        for key in key_order {
            let (_, group_rows) = group_map.remove(&key).expect("key must exist in group_map");
            let mut row = Vec::new();
            for target in &extended_targets {
                let val =
                    self.evaluate_aggregate_table_expr(&target.expr, &group_rows, column_map)?;
                row.push(val);
            }

            // Apply HAVING filter if present
            if let Some(having_expr) = &query.having {
                let having_val = self.evaluate_having_table_expr(
                    having_expr,
                    &row,
                    &col_map,
                    &alias_map,
                    &group_rows,
                    column_map,
                )?;
                match having_val {
                    Value::Boolean(true) => {}
                    Value::Boolean(false) | Value::Null => continue,
                    _ => {
                        return Err(QueryError::Type(
                            "HAVING clause must evaluate to boolean".to_string(),
                        ));
                    }
                }
            }

            result.add_row(row);
        }

        self.finish_aggregate_result(result, query, num_hidden)
    }

    /// ORDER BY, then PIVOT BY, then LIMIT -- the tail every aggregate result
    /// goes through, including an empty one.
    ///
    /// Shared so the no-groups case cannot skip it. It used to `return` early,
    /// which was harmless for ORDER BY and LIMIT (no-ops on zero rows) and not
    /// for PIVOT, which reshapes the COLUMNS: `WHERE <no match> ... PIVOT BY`
    /// reported the un-pivoted header while the same query emptied by HAVING
    /// reported the pivoted one. bean-query gives the pivoted shape for both.
    ///
    /// The last `num_hidden` columns are ORDER BY expressions the query does
    /// not select: they are sorted on, then stripped before PIVOT, the slot
    /// `execute_select` strips them in.
    fn finish_aggregate_result(
        &self,
        mut result: QueryResult,
        query: &SelectQuery,
        num_hidden: usize,
    ) -> Result<QueryResult, QueryError> {
        let visible_cols = result.columns.len() - num_hidden;
        if let Some(order_by) = &query.order_by {
            self.sort_results(&mut result, order_by, visible_cols)?;
        }
        result.columns.truncate(visible_cols);
        for row in &mut result.rows {
            row.truncate(visible_cols);
        }

        if let Some(pivot_exprs) = &query.pivot_by {
            result = self.apply_pivot(
                &result,
                pivot_exprs,
                &query.group_by,
                query.order_by.is_some(),
            )?;
        }

        if let Some(limit) = query.limit {
            result.truncate(limit as usize);
        }

        Ok(result)
    }

    /// Resolve column names for a query from a subquery.
    pub(super) fn resolve_subquery_column_names(
        &self,
        targets: &[Target],
        inner_columns: &[String],
        hidden: &[String],
    ) -> Result<Vec<String>, QueryError> {
        let mut names = Vec::new();
        for target in targets {
            if let Some(alias) = &target.alias {
                // As the parser left it: an unquoted alias is already folded
                // to lower case (#2164), a quoted one keeps its case (#2577).
                names.push(alias.clone());
            } else if matches!(target.expr, Expr::Wildcard) {
                // Expand wildcard to all VISIBLE inner columns.
                names.extend(
                    inner_columns
                        .iter()
                        .filter(|c| !Self::wildcard_hidden(c, hidden))
                        .cloned(),
                );
            } else {
                names.push(self.expr_to_name(&target.expr));
            }
        }
        Ok(names)
    }

    /// Whether a table column is hidden from `SELECT *` expansion.
    ///
    /// Upstream beanquery's wildcard omits the structured `entry` column,
    /// and our underscore-prefixed helper columns (`_entry_meta`,
    /// `_posting_meta`) were ALSO leaking into `SELECT *` before #1800 —
    /// one rule now covers both. The `table_hidden` list is per-table,
    /// because bean-query's treatment of `meta` is not uniform — see
    /// [`Table::hidden`]. Every hidden column stays addressable by explicit
    /// name. Pinned by `select_star_hides_structured_and_helper_columns`
    /// and `select_star_matches_bean_query_per_table`.
    fn wildcard_hidden(name: &str, table_hidden: &[String]) -> bool {
        name.starts_with('_')
            || name == "entry"
            || table_hidden.iter().any(|h| h.eq_ignore_ascii_case(name))
    }

    /// [`Self::evaluate_subquery_expr`] of a call to `func`, whose name is
    /// `name_upper` in upper case.
    fn evaluate_subquery_function(
        &self,
        name_upper: &str,
        func: &FunctionCall,
        row: TableRow<'_>,
        column_map: &FxHashMap<String, usize>,
    ) -> Result<Value, QueryError> {
        // Metadata functions need row context — intercept before
        // generic evaluate_function_on_values which loses row access.
        if matches!(
            name_upper,
            "META" | "ENTRY_META" | "ANY_META" | "POSTING_META"
        ) {
            return self.eval_meta_on_table_row(name_upper, func, row, column_map);
        }

        // `has_account(regex)` on a table with an `accounts` column, such as
        // `#entries` and the entries `PRINT` filters: beanquery compiles it
        // to `regex ~? any(accounts)`, so an `open` or a `note` has the
        // accounts it names. Its argument is a pattern, and a bare word there
        // is the pattern, as in the FROM filter (`evaluate_from_filter`).
        if name_upper == "HAS_ACCOUNT"
            && let Some(&accounts) = column_map.get("accounts")
        {
            let [arg] = func.args.as_slice() else {
                return Err(QueryError::InvalidArguments(
                    "has_account".to_string(),
                    "expected 1 argument".to_string(),
                ));
            };
            let pattern = match arg {
                Expr::Column(name) if !column_map.contains_key(&name.to_lowercase()) => {
                    name.clone()
                }
                _ => match self.evaluate_subquery_expr(arg, row, column_map)? {
                    Value::String(s) => s,
                    _ => {
                        return Err(QueryError::Type(
                            "has_account expects a string pattern".to_string(),
                        ));
                    }
                },
            };
            let regex = self.python_regex(&pattern, super::RegexMode::SearchIgnoreCase)?;
            return Ok(Value::Boolean(match row.get(accounts) {
                Some(Value::StringSet(set)) => {
                    regex
                        .is_match_any(set.iter().map(String::as_str))
                        .map_err(|e| super::word_boundary_error(&pattern, &e))?
                }
                _ => false,
            }));
        }

        // `weight` and `cost` of a posting column need the POSTING, as on
        // the default FROM (#1966, #2428), and a table row has only values.
        // A row read from a posting keeps it (`RowOrigin`, #2442): when the
        // column holds that posting's `position`, answer from the posting
        // through the default FROM's own route, computed here, once, for a
        // row a query reads. Any other column, an alias of some other value
        // included, keeps the value path.
        if let [Expr::Column(column)] = func.args.as_slice()
            && let Some(posting) = self.row_posting(row, column_map, column)
            && let Some(value) = super::posting_function(name_upper, posting)
        {
            return value;
        }

        // Evaluate function arguments.
        let args: Vec<Value> = func
            .args
            .iter()
            .map(|a| {
                if matches!(a, Expr::Wildcard) {
                    Ok(Value::Null)
                } else {
                    self.evaluate_subquery_expr(a, row, column_map)
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
        self.evaluate_function_on_values(name_upper, &args)
    }

    /// Evaluate a filter expression against a subquery row.
    pub(super) fn evaluate_subquery_filter(
        &self,
        expr: &Expr,
        row: TableRow<'_>,
        column_map: &FxHashMap<String, usize>,
    ) -> Result<bool, QueryError> {
        let val = self.evaluate_subquery_expr(expr, row, column_map)?;
        self.to_bool(&val)
    }

    /// Evaluate an expression against a subquery row.
    pub(super) fn evaluate_subquery_expr(
        &self,
        expr: &Expr,
        row: TableRow<'_>,
        column_map: &FxHashMap<String, usize>,
    ) -> Result<Value, QueryError> {
        match expr {
            Expr::Attribute { operand, name } => {
                Self::eval_attribute(self.evaluate_subquery_expr(operand, row, column_map)?, name)
            }
            Expr::Subscript { operand, key } => {
                Self::eval_subscript(&self.evaluate_subquery_expr(operand, row, column_map)?, key)
            }
            Expr::Wildcard => Err(QueryError::Evaluation(
                "Wildcard not allowed in expression context".to_string(),
            )),
            Expr::Column(name) => {
                let lower = name.to_lowercase();
                if let Some(&idx) = column_map.get(&lower) {
                    Ok(row.get(idx).cloned().unwrap_or(Value::Null))
                } else {
                    Err(QueryError::Evaluation(format!(
                        "column '{name}' not found in subquery result"
                    )))
                }
            }
            Expr::Literal(lit) => self.evaluate_literal(lit),
            Expr::Function(func) => {
                // Wildcard (*) in a function argument is only valid for COUNT.
                let has_wildcard = func.args.iter().any(|a| matches!(a, Expr::Wildcard));
                if has_wildcard && func.name.to_uppercase() != "COUNT" {
                    return Err(QueryError::InvalidArguments(
                        func.name.clone(),
                        "wildcard (*) is only allowed with COUNT".to_string(),
                    ));
                }

                self.evaluate_subquery_function(&func.name.to_uppercase(), func, row, column_map)
            }
            Expr::BinaryOp(op) => {
                let left = self.evaluate_subquery_expr(&op.left, row, column_map)?;
                if let Some(value) = self.short_circuit(op.op, &left)? {
                    return Ok(value);
                }
                let right = self.evaluate_subquery_expr(&op.right, row, column_map)?;
                self.binary_op_on_values(op.op, &left, &right)
            }
            Expr::UnaryOp(op) => {
                let val = self.evaluate_subquery_expr(&op.operand, row, column_map)?;
                self.unary_op_on_value(op.op, &val)
            }
            Expr::Paren(inner) => self.evaluate_subquery_expr(inner, row, column_map),
            Expr::Window(_) => Err(QueryError::Evaluation(
                "Window functions not supported in subquery expressions".to_string(),
            )),
            Expr::Between { value, low, high } => {
                let val = self.evaluate_subquery_expr(value, row, column_map)?;
                let low_val = self.evaluate_subquery_expr(low, row, column_map)?;
                let high_val = self.evaluate_subquery_expr(high, row, column_map)?;

                let ge = self.compare_values(&val, &low_val, std::cmp::Ordering::is_ge)?;
                let le = self.compare_values(&val, &high_val, std::cmp::Ordering::is_le)?;

                match (ge, le) {
                    (Value::Boolean(g), Value::Boolean(l)) => Ok(Value::Boolean(g && l)),
                    _ => Err(QueryError::Type(
                        "BETWEEN requires comparable values".to_string(),
                    )),
                }
            }
            Expr::Set(elements) => {
                // Evaluate all elements and collect as Set (supports any value types)
                let mut values = Vec::with_capacity(elements.len());
                for elem in elements {
                    let val = self.evaluate_subquery_expr(elem, row, column_map)?;
                    if !matches!(val, Value::Null) {
                        values.push(val);
                    }
                }
                Ok(Value::Set(values))
            }
        }
    }

    /// Evaluate a row of targets against a subquery row.
    pub(super) fn evaluate_subquery_row(
        &self,
        targets: &[Target],
        inner_row: TableRow<'_>,
        column_map: &FxHashMap<String, usize>,
        inner_columns: &[String],
        hidden: &[String],
    ) -> Result<Row, QueryError> {
        let mut row = Vec::new();
        for target in targets {
            if matches!(target.expr, Expr::Wildcard) {
                // Expand wildcard to the VISIBLE inner values, matching the
                // name expansion above.
                row.extend(
                    inner_row
                        .iter()
                        .zip(inner_columns)
                        .filter(|(_, c)| !Self::wildcard_hidden(c, hidden))
                        .map(|(v, _)| v.clone()),
                );
            } else {
                row.push(self.evaluate_subquery_expr(&target.expr, inner_row, column_map)?);
            }
        }
        Ok(row)
    }

    /// Execute a JOURNAL query.
    pub(super) fn execute_journal(
        &self,
        query: &crate::ast::JournalQuery,
    ) -> Result<QueryResult, QueryError> {
        // A double-quoted string naming a posting column in the FROM filter
        // is that column, as in bean-query (#2596).
        if let Some(from) = &query.from
            && let Some(filter) = from.filter.as_ref().and_then(|f| {
                super::quoted_columns::resolve_double_quoted_expr(
                    f,
                    super::quoted_columns::is_posting_column,
                )
            })
        {
            let mut resolved = query.clone();
            if let Some(from) = &mut resolved.from {
                from.filter = Some(filter);
            }
            return self.execute_journal(&resolved);
        }

        // JOURNAL is a shorthand for SELECT with specific columns
        //
        // The account pattern is a pattern even when double-quoted and named
        // like a column. Deliberately unlike bean-query, whose
        // `transform_journal` turns it into `account ~ "<pattern>"` and so
        // hands it to the double-quote rule (#2596, `quoted_columns.rs`):
        // `JOURNAL "account"` there reads `account ~ account` and lists every
        // posting, an artifact of the rewrite rather than a meaning anyone
        // writes. Here it matches accounts containing `account`.
        let account_pattern = &query.account_pattern;

        // bean-query's `transform_journal` makes it `account ~ "<pattern>"`,
        // so it is a Python regex searched case-insensitively (#2656). A
        // pattern rledger cannot use is an error, as it is for `~`: it used to
        // fall back to a substring match, which answered a refused lookahead
        // or a typo'd `(` with rows matching something else.
        let account_regex =
            self.python_regex(account_pattern, super::RegexMode::SearchIgnoreCase)?;

        let columns = vec![
            "date".to_string(),
            "flag".to_string(),
            "payee".to_string(),
            "narration".to_string(),
            "account".to_string(),
            "position".to_string(),
            "balance".to_string(),
        ];
        let mut result = QueryResult::new(columns);

        // Cumulative balance across every matched posting in this JOURNAL run.
        // Matches Python `bean-query`'s JOURNAL → SELECT translation, where the
        // `balance` column is `summary_func(balance)` over the running
        // cumulative inventory of WHERE-filtered postings — not per-account.
        // Aligns with the cumulative `balance` semantics introduced for SELECT
        // in PR #940; the JOURNAL command was missed in that change. Issue #955.
        // Same row-per-snapshot shape as `running_balance` above.
        // An AVERAGE account presented as its pools, as SELECT's running
        // `balance` and `BALANCES` present it (#2543).
        let mut cumulative_balance = super::running_balance::RunningBalance::new();
        // `AT COST`'s running balance: the sum of each row's cost, which is
        // what `at_cost` of the cumulative balance is, but exact. A lot bought
        // as `{{500 USD}}` of 3 costs 500 on its row (`compute_posting_cost`),
        // while `at_cost` of a balance holding it multiplies the rounded
        // per-unit cost back out to 500.00…01 (#2425). Shared for the same
        // reason `cumulative_balance` is (#1086).
        let mut cost_balance = rustledger_core::Inventory::new_shared();

        // Normalize the AT mode once per query rather than calling
        // to_uppercase() per row (which would allocate twice — once for
        // position_value, once for balance_for_row). Issue #957 self-review.
        let at_mode = AtMode::from_query(query.at_function.as_deref());

        // Filter transactions that touch the account. Resolve the directive
        // source via `resolved_directives()` — under `new_with_sources` (CLI /
        // LSP) `self.directives` is empty and the data is in
        // `spanned_directives`. Iterating `self.directives` directly here is
        // what made `JOURNAL` return zero rows in the CLI.
        //
        // The FROM clause's date window comes from `window_transactions`, the
        // one definition `SELECT` iterates too. JOURNAL used to walk the
        // ledger itself and applied only the filter expression, so `OPEN ON`
        // and `CLOSE ON` were silently ignored here (#2401).
        //
        // A FROM filter that reads a posting column is a row filter, joined
        // with AND to the account match, as beanquery's `transform_journal` makes
        // it (#2414); an entry-level one keeps or drops the transaction.
        let from_filter = query.from.as_ref().and_then(|f| f.filter.as_ref());
        let row_filter = from_filter.is_some_and(super::evaluation::from_filter_reads_postings);
        // A row filter reading `accounts` shares one set per transaction
        // across its postings (#2580), as SELECT's scan does.
        let filter_reads_accounts =
            row_filter && from_filter.is_some_and(super::filter_reads_txn_accounts);
        for (directive_index, txn) in
            self.window_transactions(query.from.as_ref(), self.resolved_directives().enumerate())?
        {
            if let Some(filter) = from_filter
                && !row_filter
                && (txn.postings.is_empty()
                    || !self.evaluate_from_filter(filter, &txn, 0, directive_index, None)?)
            {
                continue;
            }
            let txn_accounts = filter_reads_accounts.then(|| {
                std::sync::Arc::new(super::system_tables::TxnAccounts::of(&txn).into_owned())
            });

            for (i, posting) in txn.postings.iter().enumerate() {
                // The FROM filter first, then the account pattern, as
                // beanquery's `EvalAnd([from, where])` evaluates them: a row
                // the filter drops never has its account matched, so a word
                // boundary cannot fail on it (#2656).
                let mut matches = if row_filter && let Some(filter) = from_filter {
                    self.evaluate_from_filter(
                        filter,
                        &txn,
                        i,
                        directive_index,
                        txn_accounts.as_ref(),
                    )?
                } else {
                    true
                };
                if matches {
                    matches = account_regex
                        .is_match(&posting.account)
                        .map_err(|e| super::word_boundary_error(account_pattern, &e))?;
                }

                if matches {
                    // Resolve the posting into a Position once. Used for
                    // both the running balance accumulator and the
                    // default-case position column. With cost when the
                    // posting carries a cost annotation; bare units
                    // otherwise.
                    let pos = posting.amount().map(|units| {
                        Position::from_posting(units, posting.cost.as_deref(), txn.date)
                    });

                    // `AT COST` shows `cost_balance` instead (see below), so
                    // this running balance is only kept for the other modes.
                    if let Some(ref p) = pos
                        && !matches!(at_mode, AtMode::Cost)
                    {
                        cumulative_balance.add(
                            posting,
                            txn.date,
                            p.clone(),
                            self.account_is_average(&posting.account),
                        )?;
                    }

                    // Apply AT function if specified, using the at_mode
                    // precomputed once per query above.
                    //
                    // - default (no AT): show the full Position (units +
                    //   cost when present), matching bean-query's
                    //   JOURNAL column. Issue #955.
                    // - AT COST: when a cost annotation is present and
                    //   resolves, show the cost-currency total
                    //   (units × per-unit cost). Otherwise fall back to
                    //   the original units — so the output currency is
                    //   not guaranteed to be the cost currency.
                    // - AT UNITS: show just the units, dropping cost.
                    let position_value = match at_mode {
                        AtMode::None => pos
                            .as_ref()
                            .map_or(Value::Null, |p| Value::Position(Box::new(p.clone()))),
                        AtMode::Cost => {
                            // The posting's booked cost, as `cost(position)`
                            // gives it: exact for a `{{T}}` lot (#2425).
                            let value = if let Some(cost) = super::compute_posting_cost(posting) {
                                cost?
                            } else if let Some(units) = posting.amount() {
                                // A cost not booked to a number and currency:
                                // resolve it, checked (this was a bare `*`).
                                if let Some(cost_spec) = &posting.cost
                                    && let Some(cost) = cost_spec.resolve(units.number, txn.date)
                                {
                                    let total = units
                                        .number
                                        .checked_mul(cost.number)
                                        .ok_or_else(|| super::overflow_err(&cost.currency))?;
                                    Value::Amount(Amount::new(total, &cost.currency))
                                } else {
                                    Value::Amount(units.clone())
                                }
                            } else {
                                Value::Null
                            };
                            if let Value::Amount(amount) = &value {
                                cost_balance
                                    .add(Position::simple(amount.clone()))
                                    .map_err(|e| QueryError::Evaluation(e.to_string()))?;
                            }
                            value
                        }
                        AtMode::Units | AtMode::Other => posting
                            .amount()
                            .map_or(Value::Null, |u| Value::Amount(u.clone())),
                    };

                    // Apply the same AT-mode transformation to the balance
                    // column that bean-query's `summary_func(balance)`
                    // applies. Issue #957: previously the balance always
                    // showed the full cumulative inventory regardless of
                    // AT mode; that diverged from bean-query, where AT
                    // cost collapses the balance to cost-currency totals
                    // and AT units strips lots from the balance.
                    // An out-of-range cost basis is reported, not
                    // clamped: a query cell showing a saturated total is
                    // indistinguishable from a real one (#1863).
                    let balance_for_row = match at_mode {
                        AtMode::Cost => cost_balance.clone(),
                        AtMode::Units => cumulative_balance
                            .snapshot()?
                            .at_units()
                            .map_err(|e| QueryError::Evaluation(e.to_string()))?,
                        AtMode::None | AtMode::Other => cumulative_balance.snapshot()?,
                    };

                    // `JOURNAL` is defined by beancount as a SELECT whose
                    // payee and narration go through `MAXWIDTH`
                    // (`beanquery/compiler.py::transform_journal`:
                    // `MAXWIDTH(payee, 48)`, `MAXWIDTH(narration, 80)`).
                    // Skipping it let a single long narration widen the
                    // column without bound — the command exists to give a
                    // readable ledger view, and an 800-character memo
                    // defeats that.
                    // Propagate rather than substituting a fallback. The
                    // arguments are fully controlled here — a string and a
                    // width comfortably above the placeholder's own length
                    // — so this cannot fail in practice; if it ever does,
                    // that is a bug worth surfacing, not worth hiding
                    // behind a silently emptied payee.
                    let payee = Self::maxwidth_on_values(&[
                        Value::String(
                            txn.payee
                                .as_ref()
                                .map_or_else(String::new, ToString::to_string),
                        ),
                        Value::Integer(JOURNAL_PAYEE_MAXWIDTH),
                    ])?;
                    let narration = Self::maxwidth_on_values(&[
                        Value::String(txn.narration.to_string()),
                        Value::Integer(JOURNAL_NARRATION_MAXWIDTH),
                    ])?;
                    let row = vec![
                        Value::Date(txn.date),
                        Value::String(txn.flag.to_string()),
                        payee,
                        narration,
                        Value::String(posting.account.to_string()),
                        position_value,
                        Value::Inventory(std::sync::Arc::new(balance_for_row)),
                    ];
                    result.add_row(row);
                }
            }
            cumulative_balance.end_transaction();
        }

        Ok(result)
    }

    /// Execute a BALANCES query.
    pub(super) fn execute_balances(
        &self,
        query: &crate::ast::BalancesQuery,
    ) -> Result<QueryResult, QueryError> {
        // A double-quoted string naming a posting column, in the FROM filter
        // or the WHERE, is that column, as in bean-query, whose BALANCES is a
        // SELECT over the postings (#2596).
        let resolve = |e: &Expr| {
            super::quoted_columns::resolve_double_quoted_expr(
                e,
                super::quoted_columns::is_posting_column,
            )
        };
        let filter = query
            .from
            .as_ref()
            .and_then(|f| f.filter.as_ref())
            .and_then(resolve);
        let where_clause = query.where_clause.as_ref().and_then(resolve);
        if filter.is_some() || where_clause.is_some() {
            let mut resolved = query.clone();
            if let (Some(from), Some(filter)) = (&mut resolved.from, filter) {
                from.filter = Some(filter);
            }
            if where_clause.is_some() {
                resolved.where_clause = where_clause;
            }
            return self.execute_balances(&resolved);
        }

        // The WHERE filters POSTINGS before they are summed, as in bean-query,
        // whose BALANCES is `SELECT account, SUM(position) ... GROUP BY
        // account` with the WHERE on the postings (`transform_balances`), and
        // whose compiler joins the FROM expression to it with AND
        // (`c_where = EvalAnd([c_from_expr, c_where])`). So the WHERE is
        // folded into the FROM filter, which the scan already evaluates per
        // posting when it reads a posting column (#2414): `BALANCES WHERE x`
        // and `BALANCES FROM x` are one query, as they are in bean-query. It
        // used to filter the result rows, so it could only see `account` and
        // the total: `WHERE year = 2024` or `WHERE narration ~ 'x'` matched
        // nothing or everything (#2630).
        if let Some(where_clause) = &query.where_clause {
            return self.execute_balances(&fold_balances_where(query, where_clause)?);
        }

        // Build up balances by processing all transactions (with FROM filtering).
        // Local map rather than struct state — see issue #958.
        let balances = self.build_balances_with_filter(query.from.as_ref())?;

        let columns = vec!["account".to_string(), "balance".to_string()];
        let mut result = QueryResult::new(columns);

        // Order rows by `account_sortkey`: account type first (Assets,
        // Liabilities, Equity, Income, Expenses, honoring `name_*` renames),
        // then name. beanquery's BALANCES is sugar for `... GROUP BY account
        // ORDER BY account_sortkey(account)`; plain name order put Expenses
        // before Liabilities (#2409).
        let mut accounts: Vec<_> = balances.keys().collect();
        accounts.sort_by_cached_key(|account| (self.account_type_index(account), *account));

        for account in accounts {
            // Safety: account comes from balances.keys(), so it's guaranteed to exist
            let Some(balance) = balances.get(account) else {
                continue; // Defensive: skip if somehow the key disappeared
            };

            // Apply AT function if specified
            let balance_value = if let Some(at_func) = &query.at_function {
                match at_func.to_uppercase().as_str() {
                    "COST" => {
                        // Sum up cost basis
                        let cost_inventory = balance
                            .at_cost()
                            .map_err(|e| QueryError::Evaluation(e.to_string()))?;
                        Value::Inventory(std::sync::Arc::new(cost_inventory))
                    }
                    "UNITS" => {
                        // Just the units (remove cost info)
                        let units_inventory = balance
                            .at_units()
                            .map_err(|e| QueryError::Evaluation(e.to_string()))?;
                        Value::Inventory(std::sync::Arc::new(units_inventory))
                    }
                    _ => Value::Inventory(std::sync::Arc::new(balance.clone())),
                }
            } else {
                Value::Inventory(std::sync::Arc::new(balance.clone()))
            };

            result.add_row(vec![Value::String(account.to_string()), balance_value]);
        }

        Ok(result)
    }

    /// Execute a PRINT query.
    ///
    /// PRINT prints the entry stream the `FROM` clause gives, the one the
    /// posting sources iterate the transactions of: `OPEN ON` / `CLOSE` /
    /// `CLEAR` applied ([`Self::window_entries`], #2411), then the filter
    /// expression, evaluated on each entry as beanquery evaluates it on its
    /// `entries` table. Each entry is rendered by the canonical formatter,
    /// `rustledger_core::format`, so a cost, price, metadata, booking method
    /// or escaped string prints as `rledger format` writes it and the output
    /// loads back (#2426). This used to print every directive of the ledger
    /// through a formatter of its own, which dropped all of those.
    ///
    /// One row per entry, in a `directive` column. A row's text ends with a
    /// newline and starts with one where beancount's `print_entries` puts a
    /// blank line (before a transaction or a commodity, and between runs of
    /// different directive types), so the rows concatenated are bean-query's
    /// `PRINT` output; the CLI writes them that way.
    pub(super) fn execute_print(
        &self,
        query: &crate::ast::PrintQuery,
    ) -> Result<QueryResult, QueryError> {
        // A double-quoted string naming an entry column in the FROM filter is
        // that column, as in bean-query, which compiles it against its
        // `entries` table (#2596): the posting columns but the posting-only
        // ones.
        if let Some(from) = &query.from
            && let Some(filter) = from.filter.as_ref().and_then(|f| {
                super::quoted_columns::resolve_double_quoted_expr(f, |name| {
                    super::quoted_columns::is_posting_column(name)
                        && !super::evaluation::POSTING_ONLY_COLUMNS.contains(&name)
                })
            })
        {
            let mut resolved = query.clone();
            if let Some(from) = &mut resolved.from {
                from.filter = Some(filter);
            }
            return self.execute_print(&resolved);
        }

        let mut result = QueryResult::new(vec!["directive".to_string()]);

        // PRINT prints entries, so its FROM filter is entry-level, and a
        // posting column in it is an error, as in both bean-query versions:
        // which entries would `account ~ 'Bank'` print? `has_account()` says
        // it (#2414).
        let from = query.from.as_ref();
        let filter = from.and_then(|f| f.filter.as_ref());
        if let Some(column) = filter.and_then(super::evaluation::print_filter_posting_column) {
            return Err(QueryError::Evaluation(format!(
                "column \"{column}\" is a posting column, and PRINT prints entries: \
                 to print the entries with a posting to an account, \
                 use FROM has_account('<regex>')"
            )));
        }
        // The filter reads an entry as a row of `#entries`, whatever its
        // type: `narration` is NULL on an `open`, and `has_account()` asks
        // about the entry's `accounts`, as beanquery's `entries` table does.
        let entry_columns: FxHashMap<String, usize> = super::system_tables::ENTRY_TABLE_COLUMNS
            .iter()
            .enumerate()
            .map(|(i, name)| ((*name).to_string(), i))
            .collect();

        let config = rustledger_core::format::FormatConfig::default();
        let mut previous: Option<std::mem::Discriminant<Directive>> = None;
        for (index, entry) in self.window_entries(from, self.resolved_directives().enumerate())? {
            let synthesized;
            let directive = match &entry {
                super::types::EntryRef::Ledger(directive) => *directive,
                super::types::EntryRef::Synthesized(txn) => {
                    synthesized = Directive::Transaction((**txn).clone());
                    &synthesized
                }
            };
            if let Some(filter) = filter {
                let row = self.directive_to_entry_row(
                    index,
                    directive,
                    index.and_then(|i| self.get_source_location(i)),
                );
                if !self.evaluate_subquery_filter(filter, TableRow::plain(&row), &entry_columns)? {
                    continue;
                }
            }

            // beancount's `print_entries`: a blank line before every
            // transaction and commodity, and where the directive type
            // changes; the first entry is compared with its own type.
            let kind = std::mem::discriminant(directive);
            let blank = matches!(
                directive,
                Directive::Transaction(_) | Directive::Commodity(_)
            ) || previous.is_some_and(|p| p != kind);
            previous = Some(kind);
            let mut text = String::new();
            if blank {
                text.push('\n');
            }
            // `rledger format`'s canonical form, through the one function
            // that turns a typed directive into it (`rledger add`, `extract`
            // and the FFI `format.entry` use it too). Calling
            // `rustledger_core::format` directly printed that emitter's
            // intermediate text, which `rledger format` then rewrote:
            // `price X  110 USD` for `price X 110 USD`.
            let formatted = rustledger_parser::format::canonicalize_directives(
                std::iter::once(directive),
                &config,
            )
            .map_err(|e| {
                QueryError::Evaluation(format!(
                    "cannot print the {} of {}: {e}",
                    directive.type_name(),
                    directive.date()
                ))
            })?;
            text.push_str(&formatted);
            result.add_row(vec![Value::String(text)]);
        }

        Ok(result)
    }

    /// Execute a CREATE TABLE statement.
    pub(super) fn execute_create_table(
        &mut self,
        create: &CreateTableStmt,
    ) -> Result<QueryResult, QueryError> {
        let table_name = create.table_name.to_uppercase();

        // Check if table already exists
        if self.tables.contains(&table_name) {
            return Err(QueryError::Evaluation(format!(
                "table '{}' already exists",
                create.table_name
            )));
        }

        let table = if let Some(select) = &create.as_select {
            // CREATE TABLE ... AS SELECT ..., keeping the posting each row was
            // read from, so `weight`, `cost` and `sum` of a column passing its
            // `position` through answer from the posting (#2441, #2442).
            let result = self.execute_select_with_origins(select, true)?;
            let origins = self.detach_origins(result.row_origins);
            Table {
                columns: result.columns,
                rows: result.rows,
                hidden: Vec::new(),
                origins,
            }
        } else {
            // CREATE TABLE ... (col1, col2, ...)
            let columns = create.columns.iter().map(|c| c.name.clone()).collect();
            Table::new(columns)
        };
        // The types `.describe` shows for the columns declared with one.
        let declared = create
            .columns
            .iter()
            .filter_map(|c| Some((c.name.clone(), c.type_hint.as_ref()?.to_lowercase())))
            .collect();

        self.tables.insert(&create.table_name, table, declared);

        // Return empty result with a message
        let mut result = QueryResult::new(vec!["result".to_string()]);
        result.add_row(vec![Value::String(format!(
            "Created table '{}'",
            create.table_name
        ))]);
        Ok(result)
    }

    /// `origins` as a table that outlives this executor keeps them, each
    /// posting a copy rather than an index into this executor's ledger (see
    /// [`Self::detach_source`] and `CreatedTables`).
    fn detach_origins(&self, origins: Vec<Option<RowOrigin>>) -> Vec<Option<RowOrigin>> {
        if origins.iter().all(Option::is_none) {
            return Vec::new();
        }
        origins
            .into_iter()
            .map(|origin| {
                let origin = origin?;
                Some(RowOrigin {
                    posting: self.detach_source(origin.posting)?,
                    columns: origin.columns,
                })
            })
            .collect()
    }

    /// Execute an INSERT statement.
    pub(super) fn execute_insert(
        &mut self,
        insert: &InsertStmt,
    ) -> Result<QueryResult, QueryError> {
        let table_name = insert.table_name.to_uppercase();
        let Some(table) = self.tables.get(&table_name) else {
            return Err(QueryError::Evaluation(format!(
                "table '{}' does not exist",
                insert.table_name
            )));
        };

        // The table column each inserted value goes to.
        let targets: Vec<usize> = match &insert.columns {
            Some(cols) => cols
                .iter()
                .map(|c| {
                    table
                        .columns
                        .iter()
                        .position(|column| column.eq_ignore_ascii_case(c))
                        .ok_or_else(|| {
                            QueryError::Evaluation(format!(
                                "column '{}' does not exist in table '{}'",
                                c, insert.table_name
                            ))
                        })
                })
                .collect::<Result<_, _>>()?,
            None => (0..table.columns.len()).collect(),
        };
        let width_mismatch = |found: String| {
            QueryError::Evaluation(match &insert.columns {
                Some(cols) => format!("INSERT has {} columns but {found}", cols.len()),
                None => format!("table has {} columns but {found}", table.columns.len()),
            })
        };
        // Each inserted row's values, and for a SELECT the posting each row
        // was read from.
        let (rows_to_insert, origins): (Vec<Vec<Value>>, Vec<Option<RowOrigin>>) =
            match &insert.source {
                InsertSource::Values(value_rows) => {
                    let mut rows = Vec::with_capacity(value_rows.len());
                    for value_row in value_rows {
                        if value_row.len() != targets.len() {
                            return Err(width_mismatch(format!(
                                "VALUES has {} values",
                                value_row.len()
                            )));
                        }
                        let row = value_row
                            .iter()
                            .map(|expr| self.evaluate_literal_expr(expr))
                            .collect::<Result<Vec<_>, _>>()?;
                        rows.push(row);
                    }
                    (rows, Vec::new())
                }
                InsertSource::Select(select) => {
                    // The rows inserted keep their postings, as a table created
                    // from the same SELECT would, or they would answer from the
                    // value (#2441, #2442).
                    let result = self.execute_select_with_origins(select, true)?;
                    if result.columns.len() != targets.len() {
                        return Err(width_mismatch(format!(
                            "SELECT returns {} columns",
                            result.columns.len()
                        )));
                    }
                    // Source column `k` lands in table column `targets[k]`, so
                    // the table column holds the posting's `position` where
                    // the source column did. A column named twice keeps the
                    // last value written to it, so only that source counts.
                    let mut carrier = OriginCarrier::from_pass_through(
                        targets
                            .iter()
                            .copied()
                            .enumerate()
                            .filter(|&(k, t)| !targets[k + 1..].contains(&t))
                            .map(|(k, t)| (t, k))
                            .collect(),
                    );
                    let origins = result
                        .row_origins
                        .iter()
                        .map(|origin| carrier.carry(origin.as_ref()))
                        .collect();
                    (result.rows, self.detach_origins(origins))
                }
            };

        let rows_inserted = rows_to_insert.len();
        let table = self
            .tables
            .get_mut(&table_name)
            .expect("table existence verified above");
        let width = table.columns.len();
        let mut origins = origins.into_iter();
        for mut source_row in rows_to_insert {
            let mut row = vec![Value::Null; width];
            for (k, &to) in targets.iter().enumerate() {
                row[to] = std::mem::replace(&mut source_row[k], Value::Null);
            }
            table.add_row_with_origin(row, origins.next().flatten());
        }

        // Return result with row count
        let mut result = QueryResult::new(vec!["result".to_string()]);
        result.add_row(vec![Value::String(format!(
            "Inserted {} row(s) into '{}'",
            rows_inserted, insert.table_name
        ))]);
        Ok(result)
    }

    /// Evaluate a literal expression (for INSERT VALUES).
    pub(super) fn evaluate_literal_expr(&self, expr: &Expr) -> Result<Value, QueryError> {
        match expr {
            Expr::Literal(lit) => self.evaluate_literal(lit),
            Expr::UnaryOp(unary) => {
                let value = self.evaluate_literal_expr(&unary.operand)?;
                match unary.op {
                    UnaryOperator::Neg => match value {
                        Value::Number(n) => Ok(Value::Number(-n)),
                        Value::Integer(i) => Ok(Value::Integer(-i)),
                        _ => Err(QueryError::Type(
                            "cannot negate non-numeric value".to_string(),
                        )),
                    },
                    UnaryOperator::Not => match value {
                        Value::Boolean(b) => Ok(Value::Boolean(!b)),
                        _ => Err(QueryError::Type(
                            "cannot negate non-boolean value".to_string(),
                        )),
                    },
                    _ => Err(QueryError::Evaluation(
                        "unsupported operator in INSERT VALUES".to_string(),
                    )),
                }
            }
            Expr::Paren(inner) => self.evaluate_literal_expr(inner),
            Expr::Function(func) => {
                // Allow some simple functions in VALUES
                let name = func.name.to_uppercase();
                match name.as_str() {
                    "DATE" => {
                        // DATE(year, month, day) or DATE('YYYY-MM-DD')
                        if func.args.len() == 1 {
                            let arg = self.evaluate_literal_expr(&func.args[0])?;
                            if let Value::String(s) = arg
                                && let Ok(date) = s.parse::<NaiveDate>()
                            {
                                return Ok(Value::Date(date));
                            }
                            Err(QueryError::Type("invalid date string".to_string()))
                        } else if func.args.len() == 3 {
                            let year = self.evaluate_literal_expr(&func.args[0])?;
                            let month = self.evaluate_literal_expr(&func.args[1])?;
                            let day = self.evaluate_literal_expr(&func.args[2])?;
                            match (year, month, day) {
                                (Value::Integer(y), Value::Integer(m), Value::Integer(d)) => {
                                    if let Some(date) =
                                        rustledger_core::naive_date(y as i32, m as u32, d as u32)
                                    {
                                        Ok(Value::Date(date))
                                    } else {
                                        Err(QueryError::Type("invalid date components".to_string()))
                                    }
                                }
                                _ => Err(QueryError::Type(
                                    "DATE() requires integer arguments".to_string(),
                                )),
                            }
                        } else {
                            Err(QueryError::Evaluation(
                                "DATE() requires 1 or 3 arguments".to_string(),
                            ))
                        }
                    }
                    _ => Err(QueryError::Evaluation(format!(
                        "function '{}' not supported in INSERT VALUES",
                        func.name
                    ))),
                }
            }
            _ => Err(QueryError::Evaluation(
                "only literals, unary operators, and DATE() function supported in INSERT VALUES"
                    .to_string(),
            )),
        }
    }

    /// Evaluate metadata functions (`META`, `ENTRY_META`, etc.) in table context.
    ///
    /// Uses hidden `_entry_meta` and `_posting_meta` columns from the table row
    /// to look up metadata by key.
    pub(super) fn eval_meta_on_table_row(
        &self,
        name: &str,
        func: &crate::ast::FunctionCall,
        row: TableRow<'_>,
        column_map: &FxHashMap<String, usize>,
    ) -> Result<Value, QueryError> {
        if func.args.len() != 1 {
            return Err(QueryError::InvalidArguments(
                name.to_string(),
                "expected 1 argument (key)".to_string(),
            ));
        }

        let key = match self.evaluate_subquery_expr(&func.args[0], row, column_map)? {
            Value::String(s) => s,
            Value::Null => return Ok(Value::Null),
            _ => {
                return Err(QueryError::Type(format!(
                    "{name}: argument must be a string key"
                )));
            }
        };

        // Determine which metadata column to use
        let meta_col = match name {
            "POSTING_META" | "META" => "_posting_meta",
            "ENTRY_META" => "_entry_meta",
            "ANY_META" => {
                // Check posting meta first, fall back to entry meta
                if let Some(&idx) = column_map.get("_posting_meta")
                    && let Some(Value::Object(meta)) = row.get(idx)
                    && let Some(val) = meta.get(&key)
                {
                    return Ok(val.clone());
                }
                "_entry_meta"
            }
            _ => "_entry_meta",
        };

        // A table that carries only the visible `meta` (as `#entries` does,
        // where the entry's metadata IS the row's metadata) resolves through
        // it. This cannot misfire on `#postings`, which carries `meta`,
        // `_entry_meta` and `_posting_meta` as three DISTINCT values: the
        // fallback is reached only when the requested helper column is absent.
        let meta_col = if column_map.contains_key(meta_col) {
            meta_col
        } else {
            "meta"
        };

        if let Some(&idx) = column_map.get(meta_col)
            && let Some(Value::Object(meta)) = row.get(idx)
            && let Some(val) = meta.get(&key)
        {
            return Ok(val.clone());
        }

        Ok(Value::Null)
    }
}

/// `query` with its `WHERE` folded into its `FROM` filter, joined with AND,
/// as bean-query's compiler joins the two (#2630). The scan then evaluates it
/// on each posting when it reads a posting column and on each entry when it
/// reads only entry columns, which answer the same for every posting.
///
/// # Errors
///
/// A `WHERE` that reads `balance` or `account_balance`. Before #2630 a
/// `BALANCES WHERE` filtered the result rows, so `balance` there was the
/// account's total (`WHERE NOT empty(balance)` hid empty accounts); filtering
/// postings, it would be the running balance of the postings being filtered,
/// which bean-query computes over every posting it has tested so far,
/// rejected ones included. Neither is a total, and silently changing what an
/// existing query means is worse than refusing it. bean-query has no
/// `account_balance` column at all. Deliberately unlike bean-query, which
/// accepts `balance` here.
fn fold_balances_where(
    query: &crate::ast::BalancesQuery,
    where_clause: &Expr,
) -> Result<crate::ast::BalancesQuery, QueryError> {
    for column in ["balance", "account_balance"] {
        if super::expr_references_column(where_clause, column) {
            return Err(QueryError::Evaluation(format!(
                "BALANCES' WHERE filters the postings before they are summed, \
                 as bean-query's does, so column \"{column}\" there is not an \
                 account's total: to filter accounts by their total, use \
                 SELECT account, sum(position) ... GROUP BY account HAVING ..."
            )));
        }
    }
    let mut folded = query.clone();
    folded.where_clause = None;
    let from = folded.from.get_or_insert(crate::ast::FromClause {
        open_on: None,
        close_on: None,
        close: false,
        clear: false,
        filter: None,
        subquery: None,
        table_name: None,
    });
    from.filter = Some(match from.filter.take() {
        None => where_clause.clone(),
        Some(filter) => Expr::BinaryOp(Box::new(crate::ast::BinaryOp {
            left: Expr::Paren(Box::new(bare_has_account_as_string(filter))),
            op: crate::ast::BinaryOperator::And,
            right: Expr::Paren(Box::new(where_clause.clone())),
        })),
    });
    Ok(folded)
}

/// A `FROM has_account(Bank)` filter with its bare-word pattern made a
/// string. `evaluate_from_filter` reads a bare word there as the pattern only
/// when the call is the whole filter; joined to a WHERE it would be read as a
/// column.
fn bare_has_account_as_string(filter: Expr) -> Expr {
    match filter {
        Expr::Function(mut func)
            if func.name.eq_ignore_ascii_case("HAS_ACCOUNT")
                && matches!(func.args.as_slice(), [Expr::Column(_)]) =>
        {
            if let Some(Expr::Column(name)) = func.args.pop() {
                func.args.push(Expr::string(name));
            }
            Expr::Function(func)
        }
        other => other,
    }
}

/// Carries each source row's [`RowOrigin`] to the row a query computes from
/// it (#2442): an output column that passes a source column through unchanged
/// holds the posting's `position` when that source column does. So a
/// posting's origin survives a subquery over a subquery, a table built from a
/// table, and any renaming on the way.
pub(super) struct OriginCarrier {
    /// (output column, source column) for each output column that is a bare
    /// source column, in output order.
    pass_through: Vec<(usize, usize)>,
    /// The last source layout seen and the output layout it gives, so the
    /// rows sharing a layout share one.
    last: Option<(std::sync::Arc<[usize]>, Option<std::sync::Arc<[usize]>>)>,
}

impl OriginCarrier {
    /// For a query whose output columns are `targets`, over source rows
    /// named by `column_map` and `source_columns` (`hidden` being the
    /// source's columns `SELECT *` leaves out).
    pub(super) fn new(
        targets: &[Target],
        column_map: &FxHashMap<String, usize>,
        source_columns: &[String],
        hidden: &[String],
    ) -> Self {
        let mut pass_through = Vec::new();
        let mut index = 0;
        for target in targets {
            match &target.expr {
                Expr::Wildcard => {
                    for (source, name) in source_columns.iter().enumerate() {
                        if !Executor::wildcard_hidden(name, hidden) {
                            pass_through.push((index, source));
                            index += 1;
                        }
                    }
                }
                Expr::Column(name) => {
                    if let Some(&source) = column_map.get(&name.to_lowercase()) {
                        pass_through.push((index, source));
                    }
                    index += 1;
                }
                _ => index += 1,
            }
        }
        Self::from_pass_through(pass_through)
    }

    /// For output columns that are the source columns `pass_through` pairs
    /// them with.
    pub(super) const fn from_pass_through(pass_through: Vec<(usize, usize)>) -> Self {
        Self {
            pass_through,
            last: None,
        }
    }

    /// The origin of a row computed from a source row with `origin`: the
    /// same posting, held by the output columns passing one of its position
    /// columns through, or `None` when no output column does.
    pub(super) fn carry(&mut self, origin: Option<&RowOrigin>) -> Option<RowOrigin> {
        let origin = origin?;
        let columns = match &self.last {
            Some((source, carried)) if std::sync::Arc::ptr_eq(source, &origin.columns) => {
                carried.clone()
            }
            _ => {
                let carried: Vec<usize> = self
                    .pass_through
                    .iter()
                    .filter(|(_, source)| origin.holds_position(*source))
                    .map(|(output, _)| *output)
                    .collect();
                let carried = (!carried.is_empty()).then(|| std::sync::Arc::from(carried));
                self.last = Some((std::sync::Arc::clone(&origin.columns), carried.clone()));
                carried
            }
        }?;
        Some(RowOrigin {
            posting: origin.posting.clone(),
            columns,
        })
    }
}
