//! Query execution functions for different query types.

use rayon::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};

use rustledger_core::{Amount, Directive, NaiveDate, Position};

/// Threshold for parallel row evaluation. Below this, sequential is faster.
const PARALLEL_THRESHOLD: usize = 1000;

use crate::ast::{
    CreateTableStmt, Expr, InsertSource, InsertStmt, OrderSpec, SelectQuery, SortDirection, Target,
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
        let postings = self.collect_postings(query.from.as_ref(), query.where_clause.as_ref())?;

        // Check if this is an aggregate query.
        // A query is aggregate if any SELECT target contains an aggregate function,
        // or if it has an explicit GROUP BY or HAVING clause.
        let is_aggregate = query
            .targets
            .iter()
            .any(|t| Self::is_aggregate_expr(&t.expr))
            || query.group_by.is_some()
            || query.having.is_some();

        // Track whether grouping is applied (explicit or implicit) for fallback sort
        let mut has_grouping = false;

        if is_aggregate {
            // Determine GROUP BY expressions:
            // - If explicit GROUP BY is provided, use it
            // - Otherwise, implicitly group by non-aggregate columns in SELECT
            //   (matches Python beancount behavior)
            let group_by_exprs: Option<Vec<Expr>> = if let Some(ref group_exprs) = query.group_by {
                Some(Self::resolve_group_by_aliases(group_exprs, &query.targets))
            } else {
                let implicit = Self::extract_implicit_group_by_exprs(&query.targets);
                if implicit.is_empty() {
                    None // Pure aggregate like SELECT count(*)
                } else {
                    Some(implicit)
                }
            };

            // Track if grouping is applied for deterministic fallback sort
            has_grouping = group_by_exprs.is_some();

            // Group and aggregate
            let grouped = self.group_postings(&postings, group_by_exprs.as_ref())?;
            for (_, group) in grouped {
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

                result.add_row(row);
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
                    result.rows = rows;
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

        // Apply PIVOT BY transformation
        if let Some(pivot_exprs) = &query.pivot_by {
            result = self.apply_pivot(&result, pivot_exprs, &query.targets)?;
        }

        // Apply ORDER BY
        if let Some(order_by) = &query.order_by {
            self.sort_results(&mut result, order_by)?;
        } else if has_grouping && !result.rows.is_empty() && !result.columns.is_empty() {
            // When there's GROUP BY (explicit or implicit) but no ORDER BY, sort by
            // the first column for deterministic output (matches Python beancount behavior)
            let first_col = result.columns[0].clone();
            let default_order = vec![OrderSpec {
                expr: Expr::Column(first_col),
                direction: SortDirection::Asc,
            }];
            self.sort_results(&mut result, &default_order)?;
        }

        // Remove hidden columns after sorting
        if num_hidden > 0 {
            let visible_count = result.columns.len() - num_hidden;
            result.columns.truncate(visible_count);
            for row in &mut result.rows {
                row.truncate(visible_count);
            }
        }

        // Apply LIMIT
        if let Some(limit) = query.limit {
            result.rows.truncate(limit as usize);
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
            // For aggregate queries, only allow ORDER BY on expressions that are
            // in GROUP BY or are themselves aggregates.
            if let Some(group_by) = &query.group_by {
                let in_group_by = group_by.contains(&spec.expr);
                let is_aggregate = Self::is_aggregate_expr(&spec.expr);
                if !in_group_by && !is_aggregate {
                    continue;
                }
            }

            // Check if it's already in SELECT (by expression or by alias)
            let expr_str = spec.expr.to_string();
            let in_select = query.targets.iter().any(|t| {
                if t.expr == spec.expr {
                    return true;
                }
                if let Some(alias) = &t.alias
                    && alias == &expr_str
                {
                    return true;
                }
                false
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

    /// Execute a SELECT query that sources from a subquery.
    pub(super) fn execute_select_from_subquery(
        &self,
        outer_query: &SelectQuery,
        inner_query: &SelectQuery,
    ) -> Result<QueryResult, QueryError> {
        // Execute the inner query first
        let inner_result = self.execute_select(inner_query)?;

        // Build a column name -> index mapping for the inner result
        let inner_column_map: FxHashMap<String, usize> = inner_result
            .columns
            .iter()
            .enumerate()
            .map(|(i, name)| (name.to_lowercase(), i))
            .collect();

        // Determine outer column names
        let outer_column_names =
            self.resolve_subquery_column_names(&outer_query.targets, &inner_result.columns)?;
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

            // Evaluate outer targets
            let outer_row =
                self.evaluate_subquery_row(&outer_query.targets, inner_row, &inner_column_map)?;

            if outer_query.distinct {
                // O(1) hash-based deduplication
                let row_hash = hash_row(&outer_row);
                if seen_hashes.insert(row_hash) {
                    result.add_row(outer_row);
                }
            } else {
                result.add_row(outer_row);
            }
        }

        // Apply ORDER BY
        if let Some(order_by) = &outer_query.order_by {
            self.sort_results(&mut result, order_by)?;
        }

        // Apply LIMIT
        if let Some(limit) = outer_query.limit {
            result.rows.truncate(limit as usize);
        }

        Ok(result)
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
        } else if let Some(builtin) = self.get_builtin_table(table_name) {
            builtin_table = builtin;
            &builtin_table
        } else {
            let hint = if table_name.starts_with('#') {
                ". Available system tables: #accounts, #balances, #commodities, #documents, #entries, #events, #notes, #postings, #prices, #transactions"
            } else {
                ""
            };
            return Err(QueryError::Evaluation(format!(
                "table '{table_name}' does not exist{hint}"
            )));
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
        let is_aggregate = query
            .targets
            .iter()
            .any(|t| Self::is_aggregate_expr(&t.expr))
            || query.group_by.is_some()
            || query.having.is_some();

        if is_aggregate {
            return self.execute_aggregate_from_table(query, table, &column_map);
        }

        // Find ORDER BY expressions not in SELECT and add as hidden columns.
        let hidden_targets = self.find_hidden_order_by_targets(query);
        let num_hidden = hidden_targets.len();
        let mut extended_targets = query.targets.clone();
        extended_targets.extend(hidden_targets);

        // Determine column names for the result (including hidden columns)
        let column_names = self.resolve_subquery_column_names(&extended_targets, &table.columns)?;
        let mut result = QueryResult::new(column_names);

        // Use FxHashSet for O(1) DISTINCT deduplication
        let mut seen_hashes: FxHashSet<u64> = if query.distinct {
            FxHashSet::with_capacity_and_hasher(table.rows.len(), Default::default())
        } else {
            FxHashSet::default()
        };

        // Process each row from the table
        for row in &table.rows {
            // Apply WHERE clause if present
            if let Some(where_expr) = &query.where_clause
                && !self.evaluate_subquery_filter(where_expr, row, &column_map)?
            {
                continue;
            }

            // Evaluate targets (including hidden columns)
            let result_row = self.evaluate_subquery_row(&extended_targets, row, &column_map)?;

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
            self.sort_results(&mut result, order_by)?;
        }

        // Remove hidden columns after sorting
        if num_hidden > 0 {
            let visible_count = result.columns.len() - num_hidden;
            result.columns.truncate(visible_count);
            for row in &mut result.rows {
                row.truncate(visible_count);
            }
        }

        // Apply LIMIT
        if let Some(limit) = query.limit {
            result.rows.truncate(limit as usize);
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
        use std::collections::HashMap;

        // Determine column names for the result
        let column_names = self.resolve_subquery_column_names(&query.targets, &table.columns)?;
        let mut result = QueryResult::new(column_names.clone());

        // Determine GROUP BY expressions.
        // If no explicit GROUP BY, implicitly group by non-aggregate columns (beancount compat).
        let group_by_exprs: Option<Vec<Expr>> = if let Some(ref exprs) = query.group_by {
            Some(Self::resolve_group_by_aliases(exprs, &query.targets))
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
        let mut group_map: HashMap<String, (Vec<Value>, Vec<&Row>)> = HashMap::new();
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
            return Ok(result);
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
            for target in &query.targets {
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

        // Apply ORDER BY
        if let Some(order_by) = &query.order_by {
            self.sort_results(&mut result, order_by)?;
        }

        // Apply LIMIT
        if let Some(limit) = query.limit {
            result.rows.truncate(limit as usize);
        }

        Ok(result)
    }

    /// Resolve column names for a query from a subquery.
    pub(super) fn resolve_subquery_column_names(
        &self,
        targets: &[Target],
        inner_columns: &[String],
    ) -> Result<Vec<String>, QueryError> {
        let mut names = Vec::new();
        for (i, target) in targets.iter().enumerate() {
            if let Some(alias) = &target.alias {
                names.push(alias.clone());
            } else if matches!(target.expr, Expr::Wildcard) {
                // Expand wildcard to all inner columns
                names.extend(inner_columns.iter().cloned());
            } else {
                names.push(self.expr_to_name(&target.expr, i));
            }
        }
        Ok(names)
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

                // Metadata functions need row context — intercept before
                // generic evaluate_function_on_values which loses row access.
                let name_upper = func.name.to_uppercase();
                if matches!(
                    name_upper.as_str(),
                    "META" | "ENTRY_META" | "ANY_META" | "POSTING_META"
                ) {
                    return self.eval_meta_on_table_row(&name_upper, func, row, column_map);
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
                self.evaluate_function_on_values(&func.name, &args)
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
    ) -> Result<Row, QueryError> {
        let mut row = Vec::new();
        for target in targets {
            if matches!(target.expr, Expr::Wildcard) {
                // Expand wildcard to all values from inner row
                row.extend(inner_row.iter().cloned());
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
        let mut cumulative_balance = rustledger_core::Inventory::new();

        // Normalize the AT mode once per query rather than calling
        // to_uppercase() per row (which would allocate twice — once for
        // position_value, once for balance_for_row). Issue #957 self-review.
        let at_mode = AtMode::from_query(query.at_function.as_deref());

        // Filter transactions that touch the account
        for directive in self.directives {
            if let Directive::Transaction(txn) = directive {
                // Apply FROM clause filter if present
                if let Some(from) = &query.from
                    && let Some(filter) = &from.filter
                    && !self.evaluate_from_filter(filter, txn)?
                {
                    continue;
                }

                for posting in &txn.postings {
                    // Match account using regex or substring
                    let matches = if let Some(ref regex) = account_regex {
                        regex.is_match(&posting.account)
                    } else {
                        posting.account.contains(account_pattern)
                    };

                    if matches {
                        // Resolve the posting into a Position once. Used for
                        // both the running balance accumulator and the
                        // default-case position column. With cost when the
                        // posting carries a cost annotation; bare units
                        // otherwise.
                        let pos = posting.amount().map(|units| {
                            if let Some(cost_spec) = &posting.cost
                                && let Some(cost) = cost_spec.resolve(units.number, txn.date)
                            {
                                Position::with_cost(units.clone(), cost)
                            } else {
                                Position::simple(units.clone())
                            }
                        });

                        if let Some(ref p) = pos {
                            cumulative_balance.add(p.clone());
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
                                if let Some(units) = posting.amount() {
                                    if let Some(cost_spec) = &posting.cost
                                        && let Some(cost) =
                                            cost_spec.resolve(units.number, txn.date)
                                    {
                                        let total = units.number * cost.number;
                                        Value::Amount(Amount::new(total, &cost.currency))
                                    } else {
                                        Value::Amount(units.clone())
                                    }
                                } else {
                                    Value::Null
                                }
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
                        let balance_for_row = match at_mode {
                            AtMode::Cost => cumulative_balance.at_cost(),
                            AtMode::Units => cumulative_balance.at_units(),
                            AtMode::None | AtMode::Other => cumulative_balance.clone(),
                        };

                        let row = vec![
                            Value::Date(txn.date),
                            Value::String(txn.flag.to_string()),
                            Value::String(
                                txn.payee
                                    .as_ref()
                                    .map_or_else(String::new, ToString::to_string),
                            ),
                            Value::String(txn.narration.to_string()),
                            Value::String(posting.account.to_string()),
                            position_value,
                            Value::Inventory(Box::new(balance_for_row)),
                        ];
                        result.add_row(row);
                    }
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

        // Sort accounts for consistent output
        let mut accounts: Vec<_> = balances.keys().collect();
        accounts.sort();

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
                        let cost_inventory = balance.at_cost();
                        Value::Inventory(Box::new(cost_inventory))
                    }
                    "UNITS" => {
                        // Just the units (remove cost info)
                        let units_inventory = balance.at_units();
                        Value::Inventory(Box::new(units_inventory))
                    }
                    _ => Value::Inventory(Box::new(balance.clone())),
                }
            } else {
                Value::Inventory(Box::new(balance.clone()))
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
    pub(super) fn execute_print(
        &self,
        query: &crate::ast::PrintQuery,
    ) -> Result<QueryResult, QueryError> {
        // PRINT outputs directives in Beancount format
        let columns = vec!["directive".to_string()];
        let mut result = QueryResult::new(columns);

        for directive in self.directives {
            // Apply FROM clause filter if present
            if let Some(from) = &query.from
                && let Some(filter) = &from.filter
            {
                // PRINT filters at transaction level
                if let Directive::Transaction(txn) = directive
                    && !self.evaluate_from_filter(filter, txn)?
                {
                    continue;
                }
            }

            // Format the directive as a string
            let formatted = self.format_directive(directive);
            result.add_row(vec![Value::String(formatted)]);
        }

        Ok(result)
    }

    /// Format a directive for PRINT output.
    pub(super) fn format_directive(&self, directive: &Directive) -> String {
        match directive {
            Directive::Transaction(txn) => {
                let mut out = format!("{} {} ", txn.date, txn.flag);
                if let Some(payee) = &txn.payee {
                    out.push_str(&format!("\"{payee}\" "));
                }
                out.push_str(&format!("\"{}\"", txn.narration));

                for tag in &txn.tags {
                    out.push_str(&format!(" #{tag}"));
                }
                for link in &txn.links {
                    out.push_str(&format!(" ^{link}"));
                }
                out.push('\n');

                for posting in &txn.postings {
                    out.push_str(&format!("  {}", posting.account));
                    if let Some(units) = posting.amount() {
                        out.push_str(&format!("  {} {}", units.number, units.currency));
                    }
                    out.push('\n');
                }
                out
            }
            Directive::Balance(bal) => {
                format!(
                    "{} balance {} {} {}\n",
                    bal.date, bal.account, bal.amount.number, bal.amount.currency
                )
            }
            Directive::Open(open) => {
                let mut out = format!("{} open {}", open.date, open.account);
                if !open.currencies.is_empty() {
                    out.push_str(&format!(" {}", open.currencies.join(",")));
                }
                out.push('\n');
                out
            }
            Directive::Close(close) => {
                format!("{} close {}\n", close.date, close.account)
            }
            Directive::Commodity(comm) => {
                format!("{} commodity {}\n", comm.date, comm.currency)
            }
            Directive::Pad(pad) => {
                format!("{} pad {} {}\n", pad.date, pad.account, pad.source_account)
            }
            Directive::Event(event) => {
                format!(
                    "{} event \"{}\" \"{}\"\n",
                    event.date, event.event_type, event.value
                )
            }
            Directive::Query(query) => {
                format!(
                    "{} query \"{}\" \"{}\"\n",
                    query.date, query.name, query.query
                )
            }
            Directive::Note(note) => {
                format!("{} note {} \"{}\"\n", note.date, note.account, note.comment)
            }
            Directive::Document(doc) => {
                format!("{} document {} \"{}\"\n", doc.date, doc.account, doc.path)
            }
            Directive::Price(price) => {
                format!(
                    "{} price {} {} {}\n",
                    price.date, price.currency, price.amount.number, price.amount.currency
                )
            }
            Directive::Custom(custom) => {
                format!("{} custom \"{}\"\n", custom.date, custom.custom_type)
            }
        }
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
            // CREATE TABLE ... AS SELECT ...
            let result = self.execute_select(select)?;
            Table {
                columns: result.columns,
                rows: result.rows,
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

        // Check if table exists
        if !self.tables.contains_key(&table_name) {
            return Err(QueryError::Evaluation(format!(
                "table '{}' does not exist",
                insert.table_name
            )));
        }

        // Get the table's column count for validation
        let table_column_count = self
            .tables
            .get(&table_name)
            .expect("table existence verified above")
            .columns
            .len();

        let rows_to_insert: Vec<Vec<Value>> = match &insert.source {
            InsertSource::Values(value_rows) => {
                // Evaluate each row of expressions
                let mut rows = Vec::with_capacity(value_rows.len());
                for value_row in value_rows {
                    // Validate column count
                    if let Some(ref cols) = insert.columns {
                        if value_row.len() != cols.len() {
                            return Err(QueryError::Evaluation(format!(
                                "INSERT has {} columns but VALUES has {} values",
                                cols.len(),
                                value_row.len()
                            )));
                        }
                    } else if value_row.len() != table_column_count {
                        return Err(QueryError::Evaluation(format!(
                            "table has {} columns but VALUES has {} values",
                            table_column_count,
                            value_row.len()
                        )));
                    }

                    // Evaluate each expression in the row
                    let mut row = Vec::with_capacity(value_row.len());
                    for expr in value_row {
                        let value = self.evaluate_literal_expr(expr)?;
                        row.push(value);
                    }
                    rows.push(row);
                }
                rows
            }
            InsertSource::Select(select) => {
                // Execute the SELECT and use its results
                let result = self.execute_select(select)?;

                // Validate column count
                if let Some(ref cols) = insert.columns {
                    if result.columns.len() != cols.len() {
                        return Err(QueryError::Evaluation(format!(
                            "INSERT has {} columns but SELECT returns {} columns",
                            cols.len(),
                            result.columns.len()
                        )));
                    }
                } else if result.columns.len() != table_column_count {
                    return Err(QueryError::Evaluation(format!(
                        "table has {} columns but SELECT returns {} columns",
                        table_column_count,
                        result.columns.len()
                    )));
                }

                result.rows
            }
        };

        let rows_inserted = rows_to_insert.len();

        // Insert rows into the table
        if let Some(ref cols) = insert.columns {
            // Insert with specific columns - need to map to table column positions
            let table = self
                .tables
                .get(&table_name)
                .expect("table existence verified above");
            let col_indices: Vec<Option<usize>> = cols
                .iter()
                .map(|c| {
                    table
                        .columns
                        .iter()
                        .position(|tc| tc.eq_ignore_ascii_case(c))
                })
                .collect();

            // Validate all column names exist
            for (i, idx) in col_indices.iter().enumerate() {
                if idx.is_none() {
                    return Err(QueryError::Evaluation(format!(
                        "column '{}' does not exist in table '{}'",
                        cols[i], insert.table_name
                    )));
                }
            }

            // Build full rows with NULLs for missing columns
            let table = self
                .tables
                .get_mut(&table_name)
                .expect("table existence verified above");
            for value_row in rows_to_insert {
                let mut full_row = vec![Value::Null; table_column_count];
                for (i, value) in value_row.into_iter().enumerate() {
                    // Use .get() for defensive bounds checking even though validation
                    // should guarantee lengths match
                    if let Some(idx) = col_indices.get(i).copied().flatten() {
                        full_row[idx] = value;
                    }
                }
                table.add_row(full_row);
            }
        } else {
            // Insert all columns in order
            let table = self
                .tables
                .get_mut(&table_name)
                .expect("table existence verified above");
            for row in rows_to_insert {
                table.add_row(row);
            }
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

        if let Some(&idx) = column_map.get(meta_col)
            && let Some(Value::Object(meta)) = row.get(idx)
            && let Some(val) = meta.get(&key)
        {
            return Ok(val.clone());
        }

        Ok(Value::Null)
    }
}
