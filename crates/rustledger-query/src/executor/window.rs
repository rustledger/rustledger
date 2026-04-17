//! Window function support.

use std::collections::HashMap;

use crate::ast::{Expr, SortDirection, Target, WindowFunction};
use crate::error::QueryError;

use super::Executor;
use super::types::{PostingContext, Value, WindowContext};

impl Executor<'_> {
    pub(super) fn has_window_functions(targets: &[Target]) -> bool {
        targets.iter().any(|t| Self::is_window_expr(&t.expr))
    }
    pub(super) fn evaluate_window_function(
        &self,
        wf: &WindowFunction,
        window_ctx: Option<&WindowContext>,
    ) -> Result<Value, QueryError> {
        let ctx = window_ctx.ok_or_else(|| {
            QueryError::Evaluation("Window function requires window context".to_string())
        })?;

        match wf.name.to_uppercase().as_str() {
            "ROW_NUMBER" => Ok(Value::Integer(ctx.row_number as i64)),
            "RANK" => Ok(Value::Integer(ctx.rank as i64)),
            "DENSE_RANK" => Ok(Value::Integer(ctx.dense_rank as i64)),
            _ => Err(QueryError::Evaluation(format!(
                "Window function '{}' not yet implemented",
                wf.name
            ))),
        }
    }
    pub(super) fn compute_window_contexts(
        &self,
        postings: &[PostingContext],
        wf: &WindowFunction,
    ) -> Result<Vec<WindowContext>, QueryError> {
        let spec = &wf.over;

        // Compute partition keys for each posting
        let mut partition_keys: Vec<String> = Vec::with_capacity(postings.len());
        for ctx in postings {
            if let Some(partition_exprs) = &spec.partition_by {
                let mut key_values = Vec::new();
                for expr in partition_exprs {
                    key_values.push(self.evaluate_expr(expr, ctx)?);
                }
                partition_keys.push(Self::make_group_key(&key_values));
            } else {
                // No partition - all rows in one partition
                partition_keys.push(String::new());
            }
        }

        // Group posting indices by partition key
        let mut partitions: HashMap<String, Vec<usize>> = HashMap::new();
        for (idx, key) in partition_keys.iter().enumerate() {
            partitions.entry(key.clone()).or_default().push(idx);
        }

        // Compute order values for sorting within partitions
        let mut order_values: Vec<Vec<Value>> = Vec::with_capacity(postings.len());
        for ctx in postings {
            if let Some(order_specs) = &spec.order_by {
                let mut values = Vec::new();
                for order_spec in order_specs {
                    values.push(self.evaluate_expr(&order_spec.expr, ctx)?);
                }
                order_values.push(values);
            } else {
                order_values.push(Vec::new());
            }
        }

        // Initialize window contexts
        let mut window_contexts: Vec<WindowContext> = vec![
            WindowContext {
                row_number: 0,
                rank: 0,
                dense_rank: 0,
            };
            postings.len()
        ];

        // Process each partition
        for indices in partitions.values() {
            // Sort indices within partition by order values
            let mut sorted_indices: Vec<usize> = indices.clone();
            if let Some(order_specs) = &spec.order_by {
                sorted_indices.sort_by(|&a, &b| {
                    let vals_a = &order_values[a];
                    let vals_b = &order_values[b];
                    for (i, (va, vb)) in vals_a.iter().zip(vals_b.iter()).enumerate() {
                        let cmp = self.compare_values_for_sort(va, vb);
                        if cmp != std::cmp::Ordering::Equal {
                            return if order_specs
                                .get(i)
                                .is_some_and(|s| s.direction == SortDirection::Desc)
                            {
                                cmp.reverse()
                            } else {
                                cmp
                            };
                        }
                    }
                    std::cmp::Ordering::Equal
                });
            }

            // Assign ranks within the partition
            let mut rank = 1;
            let mut dense_rank = 1;
            let mut prev_values: Option<&Vec<Value>> = None;

            for (position, &original_idx) in sorted_indices.iter().enumerate() {
                let current_values = &order_values[original_idx];

                let is_tie = if let Some(prev) = prev_values {
                    current_values == prev
                } else {
                    false
                };

                if !is_tie && position > 0 {
                    rank = position + 1;
                    dense_rank += 1;
                }
                window_contexts[original_idx] = WindowContext {
                    row_number: position + 1,
                    rank,
                    dense_rank,
                };

                prev_values = Some(current_values);
            }
        }

        Ok(window_contexts)
    }
    pub(super) fn find_window_function(targets: &[Target]) -> Option<&WindowFunction> {
        for target in targets {
            if let Expr::Window(wf) = &target.expr {
                return Some(wf);
            }
        }
        None
    }
}
