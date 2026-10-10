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
use super::types::{QueryResult, Row, Table, Value, hash_row};

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
        // Check if we have a subquery
        if let Some(from) = &query.from {
            if let Some(subquery) = &from.subquery {
                return self.execute_select_from_subquery(query, subquery);
            }
            // Check if we're selecting from a user-created table
            if let Some(table_name) = &from.table_name {
                return self.execute_select_from_table(query, table_name);
            }
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
            let has_windows = Self::has_window_functions(&query.targets);
            let window_contexts = if has_windows {
                if let Some(wf) = Self::find_window_function(&query.targets) {
                    Some(self.compute_window_contexts(&postings, wf)?)
                } else {
                    None
                }
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
                        result.add_row(row);
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
                let in_group_by = group_by.contains(&spec.expr);
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

    /// `inner` with a hidden target for each posting-derived value `outer`
    /// reads from one of its columns, or `None` when it needs none (#2432).
    ///
    /// `weight(c)`, `cost(c)` and `sum(c)` of a posting column need the
    /// posting, and the outer query sees only the inner query's row values:
    /// a `Position` without the price `weight` ranks second or the total a
    /// `{{T}}` cost carries. So when `c` is one of the inner query's columns
    /// passed straight through (a bare column target, or `position` from its
    /// `SELECT *`), the inner query computes the value itself,
    /// where its own routing reaches the posting: from the posting on the
    /// default FROM, from the hidden columns of `#postings`, or from its own
    /// subquery by this same rewrite. The result lands in a hidden column
    /// named for `c` (see `hidden_weight_column`), which the outer row
    /// evaluator reads in place of the value path. A column the inner query
    /// computes, such as `units(position) AS position`, gets none.
    ///
    /// An inner query that groups, aggregates, pivots or is DISTINCT is left
    /// alone: an extra column would change which rows it returns.
    fn with_hidden_posting_columns(
        &self,
        outer: &SelectQuery,
        inner: &SelectQuery,
    ) -> Option<SelectQuery> {
        // `PIVOT BY` requires a `GROUP BY`, so it is covered too.
        if inner.distinct || Self::is_aggregate_query(inner) {
            return None;
        }

        // Which values the outer query reads, per column it reads them from.
        let mut needed: Vec<(String, &str)> = Vec::new();
        let mut note = |expr: &Expr| {
            if let Expr::Function(call) = expr
                && let [Expr::Column(column)] = call.args.as_slice()
            {
                let kind = match call.name.to_uppercase().as_str() {
                    "WEIGHT" | super::WEIGHT_OR_NULL | super::WEIGHT_FAILED => "weight",
                    "COST" | super::COST_OR_NULL | super::COST_FAILED => "cost",
                    "SUM" | super::LOT_TOTAL => "lot total",
                    _ => return,
                };
                let key = (column.to_lowercase(), kind);
                if !needed.contains(&key) {
                    needed.push(key);
                }
            }
        };
        for target in &outer.targets {
            super::visit_expr(&target.expr, &mut note);
        }
        for expr in outer
            .where_clause
            .iter()
            .chain(outer.having.iter())
            .chain(outer.group_by.iter().flatten())
            .chain(outer.order_by.iter().flatten().map(|o| &o.expr))
        {
            super::visit_expr(expr, &mut note);
        }
        if needed.is_empty() {
            return None;
        }

        // `position` from the inner query's `SELECT *`, which never hides it.
        // If the inner source has no such column, computing a value from it
        // fails with the same unknown column the outer query would report.
        let wildcard = inner
            .targets
            .iter()
            .any(|t| matches!(t.expr, Expr::Wildcard));

        let mut targets = inner.targets.clone();
        for (column, kind) in needed {
            // The inner column the outer one names, passed straight through.
            let mut named = inner.targets.iter().filter(|t| {
                !matches!(t.expr, Expr::Wildcard)
                    && t.alias
                        .as_ref()
                        .map_or_else(|| self.expr_to_name(&t.expr), |alias| alias.to_lowercase())
                        == column
            });
            let source = match (named.next(), named.next()) {
                (
                    Some(Target {
                        expr: Expr::Column(source),
                        ..
                    }),
                    None,
                ) => source.clone(),
                (None, _) if wildcard && column == "position" => column.clone(),
                _ => continue,
            };
            let hidden = |name: &str, alias: String| Target {
                expr: Expr::Function(FunctionCall {
                    name: name.to_string(),
                    args: vec![Expr::Column(source.clone())],
                }),
                alias: Some(alias),
            };
            let (value, failed, value_column, error_column) = match kind {
                "weight" => (
                    super::WEIGHT_OR_NULL,
                    super::WEIGHT_FAILED,
                    super::hidden_weight_column(&column),
                    super::hidden_weight_error_column(&column),
                ),
                "cost" => (
                    super::COST_OR_NULL,
                    super::COST_FAILED,
                    super::hidden_cost_column(&column),
                    super::hidden_cost_error_column(&column),
                ),
                _ => {
                    targets.push(hidden(
                        super::LOT_TOTAL,
                        super::hidden_lot_total_column(&column),
                    ));
                    continue;
                }
            };
            targets.push(hidden(value, value_column));
            targets.push(hidden(failed, error_column));
        }
        (targets.len() > inner.targets.len()).then(|| SelectQuery {
            targets,
            ..inner.clone()
        })
    }

    /// `select` with hidden targets carrying `weight`, `cost` and the lot
    /// total of each of its columns that can pass a posting's `position`
    /// through, for a table that stores its rows (`CREATE TABLE ... AS
    /// SELECT`, `INSERT ... SELECT`), or `None` when there is none (#2441).
    ///
    /// A subquery computes these for the columns its outer query reads
    /// ([`Self::with_hidden_posting_columns`]). A stored table has no outer
    /// query yet, so it keeps them for every column that can need them: a
    /// bare `position`, renamed or not; a column of a stored table that
    /// keeps them itself; and any bare column of a subquery, which computes
    /// them only for the columns that pass a posting through. Without them a
    /// table answered `weight(position)` from the `Position` value, which
    /// has no price, and `cost` / `sum` from the per-unit cost a `{{T}}` lot
    /// rounds to: `10 EUR` for `10 EUR @ 1.10 USD`, and
    /// `500.00000000000000000000000001 USD` for `3 X {{500 USD}}`.
    ///
    /// The values are stored in the same NUL-named columns `#postings` and
    /// subqueries use (see `hidden_weight_column`), which the row evaluator
    /// reads for any table and `SELECT *` never shows.
    pub(super) fn with_stored_posting_columns(&self, select: &SelectQuery) -> Option<SelectQuery> {
        let from = select.from.as_ref();
        let from_subquery = from.is_some_and(|f| f.subquery.is_some());
        let from_table = from
            .and_then(|f| f.table_name.as_ref())
            .and_then(|name| self.tables.get(&name.to_uppercase()));
        let mut reads: Vec<Target> = Vec::new();
        let mut read = |column: String| {
            for function in ["WEIGHT", "COST", "SUM"] {
                reads.push(Target {
                    expr: Expr::Function(FunctionCall {
                        name: function.to_string(),
                        args: vec![Expr::Column(column.clone())],
                    }),
                    alias: None,
                });
            }
        };
        for target in &select.targets {
            match &target.expr {
                Expr::Wildcard => read("position".to_string()),
                Expr::Column(source) => {
                    let carries = source.eq_ignore_ascii_case("position")
                        || from_subquery
                        || from_table.is_some_and(|t| {
                            let hidden = super::hidden_weight_column(source);
                            t.columns.contains(&hidden)
                        });
                    if carries {
                        read(target.alias.as_ref().map_or_else(
                            || self.expr_to_name(&target.expr),
                            |alias| alias.to_lowercase(),
                        ));
                    }
                }
                _ => {}
            }
        }
        if reads.is_empty() {
            return None;
        }
        self.with_hidden_posting_columns(&SelectQuery::new(reads), select)
    }

    /// Execute a SELECT query that sources from a subquery.
    pub(super) fn execute_select_from_subquery(
        &self,
        outer_query: &SelectQuery,
        inner_query: &SelectQuery,
    ) -> Result<QueryResult, QueryError> {
        // Execute the inner query first, with the posting-derived values the
        // outer query needs carried beside its posting columns (#2432).
        let with_hidden = self.with_hidden_posting_columns(outer_query, inner_query);
        let inner_result = self.execute_select(with_hidden.as_ref().unwrap_or(inner_query))?;

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

        // Process each row from the inner result
        for inner_row in &inner_result.rows {
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
                result.add_row(outer_row);
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
            self.evaluate_from_filter(&Expr::Column(name.to_string()), &sample, 0, None),
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
    ) -> Result<QueryResult, QueryError> {
        let table_name_upper = table_name.to_uppercase();

        // Check for user-created tables first (exact match takes precedence),
        // then fall back to built-in system tables (which support aliases like
        // "transactions" for "#transactions" for beancount compatibility).
        let builtin_table;
        let table = if let Some(user_table) = self.tables.get(&table_name_upper) {
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
                return self.execute_select(&as_filter);
            }
            return Err(missing());
        };

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

        // Process each row from the table
        for row in &table.rows {
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
                let mut r = row.clone();
                if let Some(i) = balance_idx {
                    r[i] = Value::Inventory(std::sync::Arc::new(running_balance.clone()));
                }
                overridden_row = r;
                &overridden_row
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
                result.add_row(result_row);
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
        let mut group_map: HashMap<String, (Vec<Value>, Vec<&Row>)> = HashMap::default();
        let mut key_order: Vec<String> = Vec::new();

        for row in &table.rows {
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
    ///
    /// A NUL-prefixed column holds a posting-derived value beside a posting
    /// column (see `hidden_weight_column`) and is never shown.
    fn wildcard_hidden(name: &str, table_hidden: &[String]) -> bool {
        name.starts_with('_')
            || name.starts_with('\u{0}')
            || name == "entry"
            || table_hidden.iter().any(|h| h.eq_ignore_ascii_case(name))
    }

    /// [`Self::evaluate_subquery_expr`] of a call to `func`'s arguments under
    /// the upper-case `name_upper`, which an attempt (#2432) sets to the
    /// function it attempts.
    fn evaluate_subquery_function(
        &self,
        name_upper: &str,
        func: &FunctionCall,
        row: &[Value],
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
            let regex = self.require_regex(&pattern)?;
            return Ok(Value::Boolean(match row.get(accounts) {
                Some(Value::StringSet(set)) => set.iter().any(|a| regex.is_match(a)),
                _ => false,
            }));
        }

        // `weight`, `cost` and `sum` of a posting column need the
        // POSTING, as on the default FROM (#1966, #2428, #2430), and a
        // table row has only values. A table built from postings
        // carries them in hidden columns beside that column: read them
        // there (see `hidden_weight_column`). A column with none, an
        // alias of some other value included, keeps the value path.
        if let [Expr::Column(column)] = func.args.as_slice() {
            let cell = |kind: &str, suffix: &str| {
                super::hidden_index(column_map, kind, column, suffix).and_then(|i| row.get(i))
            };
            // The hidden value, unless computing it failed: an error
            // message is raised (`#postings`), and TRUE takes the
            // value path, which raises the error itself.
            let hidden = |kind: &str| {
                let value = cell(kind, "")?;
                match cell(kind, " error") {
                    Some(Value::Boolean(true)) => None,
                    Some(Value::String(message)) => {
                        Some(Err(QueryError::Evaluation(message.clone())))
                    }
                    _ => Some(Ok(value.clone())),
                }
            };
            match name_upper {
                "WEIGHT" => {
                    if let Some(weight) = hidden("weight") {
                        return weight;
                    }
                }
                "COST" => {
                    if let Some(cost) = hidden("cost") {
                        return cost;
                    }
                }
                super::LOT_TOTAL => {
                    return Ok(cell("lot total", "").cloned().unwrap_or(Value::Null));
                }
                _ => {}
            }
        }
        if name_upper == super::LOT_TOTAL {
            return Ok(Value::Null);
        }
        if let Some((function, failed_half)) = Self::attempt_of(name_upper) {
            let result = self.evaluate_subquery_function(function, func, row, column_map);
            return Ok(Self::attempt_value(failed_half, result));
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
        row: &[Value],
        column_map: &FxHashMap<String, usize>,
    ) -> Result<bool, QueryError> {
        let val = self.evaluate_subquery_expr(expr, row, column_map)?;
        self.to_bool(&val)
    }

    /// Evaluate an expression against a subquery row.
    pub(super) fn evaluate_subquery_expr(
        &self,
        expr: &Expr,
        row: &[Value],
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
        inner_row: &[Value],
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
        // JOURNAL is a shorthand for SELECT with specific columns
        let account_pattern = &query.account_pattern;

        // Try to compile as regex (using cache)
        let account_regex = self.get_or_compile_regex(account_pattern);

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
        let mut cumulative_balance = rustledger_core::Inventory::new_shared();
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
        for (directive_index, txn) in
            self.window_transactions(query.from.as_ref(), self.resolved_directives().enumerate())?
        {
            if let Some(filter) = from_filter
                && !row_filter
                && (txn.postings.is_empty()
                    || !self.evaluate_from_filter(filter, &txn, 0, directive_index)?)
            {
                continue;
            }

            for (i, posting) in txn.postings.iter().enumerate() {
                // Match account using regex or substring
                let mut matches = if let Some(ref regex) = account_regex {
                    regex.is_match(&posting.account)
                } else {
                    posting.account.contains(account_pattern)
                };
                if matches
                    && row_filter
                    && let Some(filter) = from_filter
                {
                    matches = self.evaluate_from_filter(filter, &txn, i, directive_index)?;
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
                        cumulative_balance
                            .add(p.clone())
                            .map_err(|e| QueryError::Evaluation(e.to_string()))?;
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
                            .at_units()
                            .map_err(|e| QueryError::Evaluation(e.to_string()))?,
                        AtMode::None | AtMode::Other => cumulative_balance.clone(),
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
        }

        Ok(result)
    }

    /// Execute a BALANCES query.
    pub(super) fn execute_balances(
        &self,
        query: &crate::ast::BalancesQuery,
    ) -> Result<QueryResult, QueryError> {
        // Build up balances by processing all transactions (with FROM filtering).
        // Local map rather than struct state — see issue #958.
        let balances = self.build_balances_with_filter(query.from.as_ref())?;

        let columns = vec!["account".to_string(), "balance".to_string()];
        let mut result = QueryResult::new(columns.clone());

        // Build column map for WHERE clause evaluation (lowercase keys for
        // consistent lookup with evaluate_subquery_filter)
        let column_map: FxHashMap<String, usize> = columns
            .iter()
            .enumerate()
            .map(|(i, c)| (c.to_lowercase(), i))
            .collect();

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

            let row = vec![Value::String(account.to_string()), balance_value];

            // Apply WHERE clause filter if present
            if let Some(where_expr) = &query.where_clause
                && !self.evaluate_subquery_filter(where_expr, &row, &column_map)?
            {
                continue;
            }

            result.add_row(row);
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
                if !self.evaluate_subquery_filter(filter, &row, &entry_columns)? {
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
        if self.tables.contains_key(&table_name) {
            return Err(QueryError::Evaluation(format!(
                "table '{}' already exists",
                create.table_name
            )));
        }

        let table = if let Some(select) = &create.as_select {
            // CREATE TABLE ... AS SELECT ..., keeping the posting-derived
            // values of its posting columns beside them (#2441).
            let stored = self.with_stored_posting_columns(select);
            let result = self.execute_select(stored.as_ref().unwrap_or(select))?;
            Table {
                columns: result.columns,
                rows: result.rows,
                // Nothing beyond the NUL-named columns, which every table
                // hides (`wildcard_hidden`).
                hidden: Vec::new(),
            }
        } else {
            // CREATE TABLE ... (col1, col2, ...)
            let columns = create.columns.iter().map(|c| c.name.clone()).collect();
            Table::new(columns)
        };

        self.tables.insert(table_name, table);

        // Return empty result with a message
        let mut result = QueryResult::new(vec!["result".to_string()]);
        result.add_row(vec![Value::String(format!(
            "Created table '{}'",
            create.table_name
        ))]);
        Ok(result)
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

        // The columns an INSERT writes: all but the NUL-named ones holding
        // each row's posting-derived values (#2441), which no query names.
        let visible: Vec<usize> = (0..table.columns.len())
            .filter(|&i| !table.columns[i].starts_with('\u{0}'))
            .collect();
        // The table column each inserted value goes to.
        let targets: Vec<usize> = match &insert.columns {
            Some(cols) => cols
                .iter()
                .map(|c| {
                    visible
                        .iter()
                        .copied()
                        .find(|&i| table.columns[i].eq_ignore_ascii_case(c))
                        .ok_or_else(|| {
                            QueryError::Evaluation(format!(
                                "column '{}' does not exist in table '{}'",
                                c, insert.table_name
                            ))
                        })
                })
                .collect::<Result<_, _>>()?,
            None => visible.clone(),
        };
        let width_mismatch = |found: String| {
            QueryError::Evaluation(match &insert.columns {
                Some(cols) => format!("INSERT has {} columns but {found}", cols.len()),
                None => format!("table has {} columns but {found}", visible.len()),
            })
        };
        // Each inserted row's values, and for a SELECT the result's columns,
        // whose hidden ones carry the posting-derived values of the posting
        // columns it passes through.
        let (rows_to_insert, source): (Vec<Vec<Value>>, Option<Vec<String>>) = match &insert.source
        {
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
                (rows, None)
            }
            InsertSource::Select(select) => {
                // The rows inserted keep their posting-derived values, as a
                // table created from the same SELECT would, or they would
                // answer from the value (#2441).
                let stored = self.with_stored_posting_columns(select);
                let result = self.execute_select(stored.as_ref().unwrap_or(select))?;
                let shown = result
                    .columns
                    .iter()
                    .filter(|c| !c.starts_with('\u{0}'))
                    .count();
                if shown != targets.len() {
                    return Err(width_mismatch(format!("SELECT returns {shown} columns")));
                }
                (result.rows, Some(result.columns))
            }
        };

        // A hidden cell with no posting behind it: NULL, with each failure
        // flag TRUE, so `weight`, `cost` and `sum` take the value path, which
        // is all a row without a posting has.
        let no_posting = |column: &str| {
            if column.starts_with('\u{0}') && column.ends_with(") error") {
                Value::Boolean(true)
            } else {
                Value::Null
            }
        };
        // The table's columns after this insert: a hidden value the source
        // carries for a column the table keeps none for adds that hidden
        // column (a table made by `CREATE TABLE t (account, position)` has
        // none until a posting arrives), with the rows already there marked
        // as having no posting.
        let mut columns_after = table.columns.clone();
        // For each inserted value, the (table, source) cells of its hidden
        // values.
        let index = |columns: &[String], name: &str| columns.iter().position(|c| c == name);
        let mut copies: Vec<(usize, usize)> = Vec::new();
        let mut value_at: Vec<usize> = Vec::with_capacity(targets.len());
        match &source {
            Some(columns) => {
                for (k, (i, name)) in columns
                    .iter()
                    .enumerate()
                    .filter(|(_, c)| !c.starts_with('\u{0}'))
                    .enumerate()
                {
                    value_at.push(i);
                    let table_column = table.columns[targets[k]].clone();
                    for (kind, suffix) in [
                        ("weight", ""),
                        ("weight", " error"),
                        ("cost", ""),
                        ("cost", " error"),
                        ("lot total", ""),
                    ] {
                        let Some(from) = index(columns, &super::hidden_name(kind, name, suffix))
                        else {
                            continue;
                        };
                        let hidden = super::hidden_name(kind, &table_column, suffix);
                        let to = index(&columns_after, &hidden).unwrap_or_else(|| {
                            columns_after.push(hidden);
                            columns_after.len() - 1
                        });
                        copies.push((to, from));
                    }
                }
            }
            None => value_at.extend(0..targets.len()),
        }

        let rows_inserted = rows_to_insert.len();
        let table = self
            .tables
            .get_mut(&table_name)
            .expect("table existence verified above");
        let added = table.columns.len()..columns_after.len();
        if !added.is_empty() {
            for row in &mut table.rows {
                row.extend(columns_after[added.clone()].iter().map(|c| no_posting(c)));
            }
            table.columns = columns_after;
        }
        let template: Vec<Value> = table.columns.iter().map(|c| no_posting(c)).collect();
        for mut source_row in rows_to_insert {
            let mut row = template.clone();
            for (&to, &from) in targets.iter().zip(&value_at) {
                row[to] = std::mem::replace(&mut source_row[from], Value::Null);
            }
            for &(to, from) in &copies {
                row[to] = std::mem::replace(&mut source_row[from], Value::Null);
            }
            table.add_row(row);
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
        row: &[Value],
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
