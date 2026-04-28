//! Sorting and pivoting functions.

use std::collections::HashMap;

use crate::ast::{Expr, Literal, OrderSpec, SortDirection, Target};
use crate::error::QueryError;

use super::Executor;
use super::types::{QueryResult, Row, Value, hash_single_value};

impl Executor<'_> {
    pub(super) fn sort_results(
        &self,
        result: &mut QueryResult,
        order_by: &[OrderSpec],
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

        // Sort the rows
        result.rows.sort_by(|a, b| {
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
    pub(super) fn apply_pivot(
        &self,
        result: &QueryResult,
        pivot_exprs: &[Expr],
        _targets: &[Target],
    ) -> Result<QueryResult, QueryError> {
        if pivot_exprs.is_empty() {
            return Ok(result.clone());
        }

        // For simplicity, we'll pivot on the first expression only
        // A full implementation would support multiple pivot columns
        let pivot_expr = &pivot_exprs[0];

        // Find which column in the result matches the pivot expression
        let pivot_col_idx = self.find_pivot_column(result, pivot_expr)?;

        // Collect unique pivot values
        let mut pivot_values: Vec<Value> = result
            .rows
            .iter()
            .map(|row| row.get(pivot_col_idx).cloned().unwrap_or(Value::Null))
            .collect();
        pivot_values.sort_by(|a, b| self.compare_values_for_sort(a, b));
        pivot_values.dedup();

        // Build new column names: original columns (except pivot) + pivot values
        let mut new_columns: Vec<String> = result
            .columns
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != pivot_col_idx)
            .map(|(_, c)| c.clone())
            .collect();

        // Identify the "value" column (usually the last one, or the one with aggregate)
        let value_col_idx = result.columns.len() - 1;

        // Add pivot value columns
        for pv in &pivot_values {
            new_columns.push(Self::value_to_string(pv));
        }

        let mut new_result = QueryResult::new(new_columns);

        // Group rows by non-pivot, non-value columns
        let group_cols: Vec<usize> = (0..result.columns.len())
            .filter(|i| *i != pivot_col_idx && *i != value_col_idx)
            .collect();

        let mut groups: HashMap<String, Vec<&Row>> = HashMap::new();
        for row in &result.rows {
            let key: String = group_cols
                .iter()
                .map(|&i| Self::value_to_string(&row[i]))
                .collect::<Vec<_>>()
                .join("|");
            groups.entry(key).or_default().push(row);
        }

        // Build pivoted rows
        for (_key, group_rows) in groups {
            let mut new_row: Vec<Value> = group_cols
                .iter()
                .map(|&i| group_rows[0][i].clone())
                .collect();

            // Build O(1) pivot value -> row index for this group
            let pivot_index: HashMap<u64, usize> = group_rows
                .iter()
                .enumerate()
                .filter_map(|(idx, row)| {
                    row.get(pivot_col_idx).map(|v| (hash_single_value(v), idx))
                })
                .collect();

            // Add pivot values with O(1) lookup
            for pv in &pivot_values {
                let pv_hash = hash_single_value(pv);
                if let Some(&row_idx) = pivot_index.get(&pv_hash) {
                    new_row.push(
                        group_rows[row_idx]
                            .get(value_col_idx)
                            .cloned()
                            .unwrap_or(Value::Null),
                    );
                } else {
                    new_row.push(Value::Null);
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
            _ => {
                // For complex expressions, try to find a matching column by string representation
                // This is a simplified approach
                Err(QueryError::Evaluation(
                    "PIVOT BY must reference a column name or index".to_string(),
                ))
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
                // Format metadata as key=value pairs
                let pairs: Vec<String> = meta.iter().map(|(k, v)| format!("{k}: {v:?}")).collect();
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
