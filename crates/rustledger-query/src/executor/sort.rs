//! Sorting and pivoting functions.

use std::collections::HashMap;

use crate::ast::{Expr, Literal, OrderSpec, SortDirection};
use crate::error::QueryError;

use super::Executor;
use super::types::{QueryResult, Row, Value, hash_single_value};

impl Executor<'_> {
    pub(super) fn sort_results(
        &self,
        result: &mut QueryResult,
        order_by: &[OrderSpec],
        // Number of user-visible SELECT columns. `result.columns` may have
        // trailing hidden ORDER BY columns appended (stripped after sorting),
        // so positional ordinals must be range-checked against this, not
        // `result.columns.len()`, or `ORDER BY <n>` could address a hidden
        // column instead of erroring.
        visible_cols: usize,
    ) -> Result<(), QueryError> {
        if order_by.is_empty() {
            return Ok(());
        }

        // Build a map from column names to indices
        let column_indices: std::collections::HashMap<&str, usize> = result
            .columns
            .iter()
            .enumerate()
            .map(|(i, name)| (name.as_str(), i))
            .collect();

        // Resolve ORDER BY expressions to column indices
        let mut sort_specs: Vec<(usize, bool)> = Vec::new();
        for spec in order_by {
            // Try to resolve the expression to a column index
            let idx = match &spec.expr {
                // Positional ORDER BY: `ORDER BY 1` sorts by the first SELECT
                // column (1-based), matching beanquery / SQL. Without this the
                // integer is treated as a constant expression and silently
                // no-ops the sort.
                Expr::Literal(Literal::Integer(n)) => {
                    let n = *n;
                    if n < 1 || (n as usize) > visible_cols {
                        return Err(QueryError::Evaluation(format!(
                            "ORDER BY position {n} is out of range (1..={visible_cols})"
                        )));
                    }
                    (n as usize) - 1
                }
                Expr::Column(name) => column_indices
                    .get(name.as_str())
                    .copied()
                    .ok_or_else(|| QueryError::UnknownColumn(name.clone()))?,
                Expr::Function(func) => {
                    // First try to find a column with the function name (e.g., "sum" for sum(amount))
                    // Then try the full expression string (e.g., "account_sortkey(account)")
                    let expr_str = spec.expr.to_string();
                    column_indices
                        .get(func.name.as_str())
                        .or_else(|| column_indices.get(expr_str.as_str()))
                        .copied()
                        .ok_or_else(|| {
                            QueryError::Evaluation(format!(
                                "ORDER BY expression not found in SELECT: {expr_str}"
                            ))
                        })?
                }
                _ => {
                    // For other expression kinds (binary ops, literals, etc.),
                    // look up by string representation (matches hidden column aliases).
                    let expr_str = spec.expr.to_string();
                    column_indices
                        .get(expr_str.as_str())
                        .copied()
                        .ok_or_else(|| {
                            QueryError::Evaluation(format!(
                                "ORDER BY expression not found in SELECT: {expr_str}"
                            ))
                        })?
                }
            };
            let ascending = spec.direction != SortDirection::Desc;
            sort_specs.push((idx, ascending));
        }

        // Sort the rows. Use `QueryResult::sort_by` (not `result.rows.sort_by`)
        // so the per-row `row_group_keys` sidecar stays in lockstep — without
        // this, the renderer would apply a row's currency hint to a different
        // row's content after sort.
        result.sort_by(|a, b| {
            for (idx, ascending) in &sort_specs {
                if *idx >= a.len() || *idx >= b.len() {
                    continue;
                }
                let ord = self.compare_values_for_sort(&a[*idx], &b[*idx]);
                if ord != std::cmp::Ordering::Equal {
                    return if *ascending { ord } else { ord.reverse() };
                }
            }
            std::cmp::Ordering::Equal
        });

        Ok(())
    }
    /// Apply the PIVOT BY transformation, matching bean-query semantics
    /// (issue #1034).
    ///
    /// **Syntax**: `PIVOT BY <row_key_col>, <spread_col>` — exactly two
    /// columns. The FIRST column is kept as the row key; the SECOND column's
    /// distinct values become the new column headers (matching bean-query's
    /// `test_pivot_one_column`). All other columns become "value" cells,
    /// populated at the intersection of (`row_key_col` value, `spread_col`
    /// value).
    ///
    /// **Validation** (rules 1–3 match `_compile_pivot_by` in
    /// `beanquery/compiler.py`; rule 4 is rledger-specific):
    /// - exactly two pivot columns (`PivotWrongArity` otherwise)
    /// - the two columns must differ (`PivotSameColumn` otherwise)
    /// - the second column must be a GROUP BY target
    ///   (`PivotSecondNotInGroupBy` otherwise)
    /// - PIVOT BY requires an explicit `GROUP BY` clause
    ///   (`PivotWithoutGroupBy` otherwise). Bean-query reaches the
    ///   same outcome through grammar — the second-must-be-in-GROUP-BY
    ///   rule is only checked when GROUP BY exists, but their parser
    ///   typically rejects PIVOT-without-GROUP-BY queries earlier.
    ///   rledger's parser is more permissive, so we surface the case
    ///   with a specific error rather than the misleading "second
    ///   column not in GROUP BY".
    ///
    /// **Input contract**: callers should provide `result` with at most
    /// one row per `(key_col, pivot_value_col)` pair — the typical
    /// guarantee from `GROUP BY <key>, <pivot_value>`. If the input has
    /// duplicate `(key, pivot_value)` rows, only the first one in row
    /// order contributes its value cells; later duplicates are silently
    /// ignored. Validator-rejected aggregate queries always satisfy
    /// this; non-aggregate queries with PIVOT would need the caller to
    /// enforce uniqueness.
    ///
    /// **Pipeline ordering**: this runs AFTER `sort_results` and the
    /// hidden-column strip (`execute_select`), so `result.columns`
    /// holds only the visible select targets in the user-requested
    /// sort order. That contract is what makes the strip+pivot
    /// interaction (item #4 of #1034) cleanly disappear.
    pub(super) fn apply_pivot(
        &self,
        result: &QueryResult,
        pivot_exprs: &[Expr],
        group_by: &Option<Vec<Expr>>,
    ) -> Result<QueryResult, QueryError> {
        // The parser uses `at_least(1)` for the PIVOT BY clause and
        // execute_select only calls this fn inside `if let Some(pivot_exprs)`,
        // so an empty slice is unreachable. Belt-and-suspenders.
        debug_assert!(
            !pivot_exprs.is_empty(),
            "apply_pivot called with empty pivot_exprs (parser invariant violated)"
        );

        // Validation #1: arity. Bean-query requires exactly two columns.
        if pivot_exprs.len() != 2 {
            return Err(QueryError::PivotWrongArity(pivot_exprs.len()));
        }

        // Validation #2: PIVOT BY requires an explicit GROUP BY clause.
        // Implicit grouping (aggregates without GROUP BY) produces a
        // single-row result whose key dimension is undefined — PIVOT
        // can't identify a row key from such a result. Reject early
        // so the user gets a specific error, not the misleading
        // "second column not in GROUP BY".
        let Some(gb) = group_by.as_ref() else {
            return Err(QueryError::PivotWithoutGroupBy);
        };

        // `PIVOT BY <row_key>, <spread>`: the FIRST column stays as the row key;
        // the SECOND column's distinct values become the new columns (matching
        // beanquery — previously these two roles were reversed, which inverted
        // the output axes).
        let key_col_idx = self.find_pivot_column(result, &pivot_exprs[0])?;
        let pivot_value_col_idx = self.find_pivot_column(result, &pivot_exprs[1])?;

        // Validation #3: the two columns must differ.
        if pivot_value_col_idx == key_col_idx {
            return Err(QueryError::PivotSameColumn);
        }

        // Validation #4: the second column (the one spread into new columns)
        // must be a GROUP BY target. Resolve each GROUP BY expression to its
        // result column index and check membership.
        let pivot_in_group_by = gb
            .iter()
            .filter_map(|expr| self.find_pivot_column(result, expr).ok())
            .any(|idx| idx == pivot_value_col_idx);
        if !pivot_in_group_by {
            return Err(QueryError::PivotSecondNotInGroupBy);
        }

        // Collect unique pivot values, preserving the row-order they
        // appear in (which post-sort means the user's ORDER BY drives
        // the new column order). Linear-scan dedup via structural
        // PartialEq — pivot values are typically small (handful of
        // currencies), and `Value` doesn't implement `Hash` because
        // some inner types (Decimal, Inventory) don't, so a pure
        // hash-based dedup either risks 2⁻⁶⁴ collisions (false-merging
        // distinct values) or requires a wrapper type. Structural eq
        // sidesteps both.
        let mut pivot_values: Vec<Value> = Vec::new();
        for row in &result.rows {
            let v = row.get(pivot_value_col_idx).cloned().unwrap_or(Value::Null);
            if !pivot_values.contains(&v) {
                pivot_values.push(v);
            }
        }

        // The "value" cells to place at each (key, pivot_value)
        // intersection are EVERY OTHER column that's not the pivot and
        // not the key. Today the typical query has exactly one such
        // column (the aggregate), but the design generalizes.
        let value_col_idxs: Vec<usize> = (0..result.columns.len())
            .filter(|i| *i != pivot_value_col_idx && *i != key_col_idx)
            .collect();

        // Build new column names. Layout: [key_col, <value_col × pivot_value>...].
        //
        // Single-value-column case (the typical SUM(number) shape) gets
        // just the pivot value as the header — matches bean-query
        // exactly. Multi-value-column case qualifies with the value
        // column name (`<value_col> / <pivot_value>`) so the headers
        // stay unambiguous when there's more than one aggregate. The
        // asymmetry is deliberate: a single-aggregate header like
        // `USD` is what users expect from the typical pivot.
        let mut new_columns: Vec<String> =
            Vec::with_capacity(1 + value_col_idxs.len() * pivot_values.len());
        new_columns.push(result.columns[key_col_idx].clone());
        for pv in &pivot_values {
            let pv_str = Self::value_to_string(pv);
            if value_col_idxs.len() == 1 {
                new_columns.push(pv_str);
            } else {
                for &vci in &value_col_idxs {
                    new_columns.push(format!("{} / {pv_str}", result.columns[vci]));
                }
            }
        }

        let mut new_result = QueryResult::new(new_columns);

        // Group rows by their key-column value, preserving first-seen
        // order so the post-sort row order survives into the pivot.
        //
        // The hash bucket is a fast first-pass; structural `==` inside
        // the bucket guarantees we don't false-merge distinct keys
        // that share a u64 hash (probability ~2⁻⁶⁴, but pinned out
        // for correctness). Same pattern as `pivot_lookup` below.
        let mut groups: Vec<(Value, Vec<&Row>)> = Vec::new();
        let mut group_index: HashMap<u64, Vec<usize>> = HashMap::new();
        for row in &result.rows {
            let key = row.get(key_col_idx).cloned().unwrap_or(Value::Null);
            let h = hash_single_value(&key);
            let bucket = group_index.entry(h).or_default();
            let existing = bucket.iter().find(|&&idx| groups[idx].0 == key).copied();
            if let Some(idx) = existing {
                groups[idx].1.push(row);
            } else {
                bucket.push(groups.len());
                groups.push((key, vec![row]));
            }
        }

        // Build pivoted rows.
        for (key, group_rows) in groups {
            let mut new_row: Vec<Value> =
                Vec::with_capacity(1 + value_col_idxs.len() * pivot_values.len());
            new_row.push(key);

            // For each pivot value, find the input row in this group
            // whose pivot column equals it; pull the value-column cell.
            // Hash bucket + structural `==` for collision-safety, same
            // pattern as the group_index above.
            //
            // If multiple input rows share the same `(key, pivot_value)`
            // pair, only the first one wins — see "Input contract" in
            // the function docstring.
            let mut pivot_lookup: HashMap<u64, Vec<&Row>> = HashMap::new();
            for &row in &group_rows {
                let pv = row.get(pivot_value_col_idx).cloned().unwrap_or(Value::Null);
                pivot_lookup
                    .entry(hash_single_value(&pv))
                    .or_default()
                    .push(row);
            }

            for pv in &pivot_values {
                let pv_hash = hash_single_value(pv);
                // Find the row in this bucket whose pivot value equals
                // `pv` structurally — guards against the hash-only
                // collision case.
                let matched = pivot_lookup.get(&pv_hash).and_then(|bucket| {
                    bucket
                        .iter()
                        .find(|row| row.get(pivot_value_col_idx).is_some_and(|cell| cell == pv))
                });
                for &vci in &value_col_idxs {
                    let cell = matched
                        .and_then(|row| row.get(vci))
                        .cloned()
                        .unwrap_or(Value::Null);
                    new_row.push(cell);
                }
            }

            new_result.add_row(new_row);
        }

        Ok(new_result)
    }
    pub(super) fn find_pivot_column(
        &self,
        result: &QueryResult,
        pivot_expr: &Expr,
    ) -> Result<usize, QueryError> {
        match pivot_expr {
            Expr::Column(name) => {
                let upper_name = name.to_uppercase();
                result
                    .columns
                    .iter()
                    .position(|c| c.to_uppercase() == upper_name)
                    .ok_or_else(|| {
                        QueryError::Evaluation(format!(
                            "PIVOT BY column '{name}' not found in SELECT"
                        ))
                    })
            }
            Expr::Literal(Literal::Integer(n)) => {
                let idx = (*n as usize).saturating_sub(1);
                if idx < result.columns.len() {
                    Ok(idx)
                } else {
                    Err(QueryError::Evaluation(format!(
                        "PIVOT BY column index {n} out of range"
                    )))
                }
            }
            Expr::Literal(Literal::Number(n)) => {
                // Defensive: literal whole numbers parse as Integer (issue #938),
                // so this arm is only reachable for fractional literals like `1.0`.
                use rust_decimal::prelude::ToPrimitive;
                let idx = n.to_usize().unwrap_or(0).saturating_sub(1);
                if idx < result.columns.len() {
                    Ok(idx)
                } else {
                    Err(QueryError::Evaluation(format!(
                        "PIVOT BY column index {n} out of range"
                    )))
                }
            }
            Expr::Function(func) => {
                // Two-tier resolution matching `sort_results`'s ORDER BY
                // logic: try the bare function name first (e.g.
                // `YEAR(date)` → column `year`), then fall back to the
                // full expression string (e.g. column literally named
                // `YEAR(date)`). Same convention as bean-query's column
                // naming.
                //
                // Without this, `PIVOT BY YEAR(date), account` would
                // fail at find_pivot_column AND `GROUP BY YEAR(date)`
                // would silently be skipped from the membership check
                // — misreporting `PivotSecondNotInGroupBy` for valid
                // queries (Copilot review on PR #1037).
                let expr_str = pivot_expr.to_string();
                let upper_func = func.name.to_uppercase();
                result
                    .columns
                    .iter()
                    .position(|c| c.to_uppercase() == upper_func)
                    .or_else(|| result.columns.iter().position(|c| c == &expr_str))
                    .ok_or_else(|| {
                        QueryError::Evaluation(format!(
                            "PIVOT BY expression '{expr_str}' not found in SELECT"
                        ))
                    })
            }
            _ => {
                // For other expression kinds (binary ops, literals,
                // etc.) try the full expression string against column
                // names — matches the hidden-column alias convention
                // used by `find_hidden_order_by_targets`.
                let expr_str = pivot_expr.to_string();
                result
                    .columns
                    .iter()
                    .position(|c| c == &expr_str)
                    .ok_or_else(|| {
                        QueryError::Evaluation(format!(
                            "PIVOT BY expression '{expr_str}' not found in SELECT"
                        ))
                    })
            }
        }
    }

    /// Convert a value to string for display/grouping.
    pub(super) fn value_to_string(val: &Value) -> String {
        match val {
            Value::String(s) => s.clone(),
            Value::Number(n) => n.to_string(),
            Value::Integer(i) => i.to_string(),
            Value::Date(d) => d.to_string(),
            Value::Boolean(b) => b.to_string(),
            Value::Amount(a) => format!("{} {}", a.number, a.currency),
            Value::Position(p) => p.to_string(),
            Value::Inventory(inv) => inv.to_string(),
            Value::StringSet(ss) => ss.join(", "),
            Value::Set(values) => {
                // Format set elements as comma-separated values
                let strs: Vec<String> = values.iter().map(Self::value_to_string).collect();
                format!("({})", strs.join(", "))
            }
            Value::Metadata(meta) => {
                // Render each metadata value through the same Value path as
                // every other cell, so a string shows as `good` rather than
                // the Debug form `String("good")`.
                let pairs: Vec<String> = meta
                    .iter()
                    .map(|(k, v)| {
                        format!(
                            "{k}: {}",
                            Self::value_to_string(&Self::meta_value_to_value(Some(v)))
                        )
                    })
                    .collect();
                format!("{{{}}}", pairs.join(", "))
            }
            Value::Interval(i) => format!("{} {:?}", i.count, i.unit),
            Value::Object(obj) => {
                // Format object as {key: value, ...}
                let pairs: Vec<String> = obj
                    .iter()
                    .map(|(k, v)| format!("{k}: {}", Self::value_to_string(v)))
                    .collect();
                format!("{{{}}}", pairs.join(", "))
            }
            Value::Null => "NULL".to_string(),
        }
    }
}
