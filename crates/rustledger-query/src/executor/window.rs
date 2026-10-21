//! Window function support.
//!
//! `OVER (...)` is a rustledger extension: bean-query has no window functions
//! (beanquery 0.2.0 rejects `OVER` as a syntax error), so nothing here has a
//! compatibility target.

use rustc_hash::FxHashMap as HashMap;

use crate::ast::{Expr, SortDirection, Target, WindowFunction};
use crate::error::QueryError;

use super::Executor;
use super::types::{PostingContext, Value, WindowContext};

/// A window function rustledger implements.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum WindowKind {
    RowNumber,
    Rank,
    DenseRank,
    Min,
    Max,
}

impl WindowKind {
    fn of(wf: &WindowFunction) -> Result<Self, QueryError> {
        let name = wf.name.to_uppercase();
        let kind = match name.as_str() {
            "ROW_NUMBER" => Self::RowNumber,
            "RANK" => Self::Rank,
            "DENSE_RANK" => Self::DenseRank,
            "MIN" => Self::Min,
            "MAX" => Self::Max,
            _ => {
                return Err(QueryError::Evaluation(format!(
                    "Window function '{}' not yet implemented",
                    wf.name
                )));
            }
        };
        if matches!(kind, Self::Min | Self::Max)
            && (wf.args.len() != 1 || matches!(wf.args[0], Expr::Wildcard))
        {
            return Err(QueryError::InvalidArguments(
                name,
                "expected 1 argument".to_string(),
            ));
        }
        Ok(kind)
    }
}

impl Executor<'_> {
    pub(super) fn has_window_functions(targets: &[Target]) -> bool {
        targets.iter().any(|t| Self::is_window_expr(&t.expr))
    }

    /// The value of the `index`-th window function of the row's targets.
    pub(super) fn evaluate_window_function(
        window_ctx: Option<&WindowContext>,
        index: usize,
    ) -> Result<Value, QueryError> {
        window_ctx
            .and_then(|ctx| ctx.values.get(index))
            .cloned()
            .ok_or_else(|| {
                QueryError::Evaluation("Window function requires window context".to_string())
            })
    }

    /// Every window function's value on every posting: `postings[i]`'s
    /// context holds the value of each window target of `targets`, in target
    /// order.
    ///
    /// Each window function is computed over its OWN `OVER` clause. They were
    /// all computed over the first one's, so in
    /// `ROW_NUMBER() OVER (PARTITION BY account), ROW_NUMBER() OVER ()` the
    /// second numbered rows within accounts too.
    pub(super) fn compute_window_contexts(
        &self,
        postings: &[PostingContext],
        targets: &[Target],
    ) -> Result<Vec<WindowContext>, QueryError> {
        let mut contexts = vec![WindowContext::default(); postings.len()];
        for target in targets {
            if let Expr::Window(wf) = &target.expr {
                let column = self.compute_window_column(postings, wf)?;
                for (ctx, value) in contexts.iter_mut().zip(column) {
                    ctx.values.push(value);
                }
            }
        }
        Ok(contexts)
    }

    /// Whether two `ORDER BY` key lists tie in the sort's own ordering — the
    /// relation `RANK` gives and the running frame's peers are defined by.
    /// `Value` equality is a different relation: `Number(1)` ties `Integer(1)`,
    /// and positions that differ only in a cost date tie in the position
    /// order. Grouping peers with `!=` split one tied run into several ranks
    /// and shrank the running `MIN` / `MAX` frame at each split.
    fn order_values_tie(&self, a: &[Value], b: &[Value]) -> bool {
        a.len() == b.len()
            && a.iter()
                .zip(b)
                .all(|(va, vb)| self.compare_values_for_sort(va, vb) == std::cmp::Ordering::Equal)
    }

    /// One window function's value on every posting, in posting order.
    ///
    /// `MIN` and `MAX` follow SQL's default frame. With no `ORDER BY` in the
    /// `OVER` clause the frame is the whole partition. With one, it runs from
    /// the partition's first row through the current row AND its peers (the
    /// rows whose `ORDER BY` values tie with it, the same ties `RANK` gives),
    /// so the result is a running minimum or maximum. Values compare as the
    /// aggregate `MIN`/`MAX` compare them (#2447): NULLs are skipped, a frame
    /// with no other value is NULL, amounts, positions and inventories order
    /// as `ORDER BY` orders them (an amount by currency, then number), and of
    /// values that compare equal the first in the frame is kept.
    fn compute_window_column(
        &self,
        postings: &[PostingContext],
        wf: &WindowFunction,
    ) -> Result<Vec<Value>, QueryError> {
        let kind = WindowKind::of(wf)?;
        let spec = &wf.over;

        // Group posting indices by partition key, each partition in posting
        // order.
        let mut partitions: HashMap<String, Vec<usize>> = HashMap::default();
        for (idx, ctx) in postings.iter().enumerate() {
            let key = if let Some(partition_exprs) = &spec.partition_by {
                let mut key_values = Vec::with_capacity(partition_exprs.len());
                for expr in partition_exprs {
                    key_values.push(self.evaluate_expr(expr, ctx)?);
                }
                Self::make_group_key(&key_values)
            } else {
                String::new()
            };
            partitions.entry(key).or_default().push(idx);
        }

        // Compute order values for sorting within partitions
        let mut order_values: Vec<Vec<Value>> = Vec::with_capacity(postings.len());
        for ctx in postings {
            let mut values = Vec::new();
            for order_spec in spec.order_by.iter().flatten() {
                values.push(self.evaluate_expr(&order_spec.expr, ctx)?);
            }
            order_values.push(values);
        }

        // The argument of MIN / MAX on every posting.
        let args: Vec<Value> = if matches!(kind, WindowKind::Min | WindowKind::Max) {
            postings
                .iter()
                .map(|ctx| self.evaluate_expr(&wf.args[0], ctx))
                .collect::<Result<_, _>>()?
        } else {
            Vec::new()
        };

        let mut column = vec![Value::Null; postings.len()];

        for indices in partitions.values() {
            // Sort indices within partition by order values (stable, so
            // ties keep posting order).
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

            // Peer groups: runs of consecutive rows whose order values tie.
            // With no ORDER BY every row ties, and the partition is one group.
            let mut groups: Vec<&[usize]> = Vec::new();
            let mut start = 0;
            for end in 1..=sorted_indices.len() {
                if end == sorted_indices.len()
                    || !self.order_values_tie(
                        &order_values[sorted_indices[end]],
                        &order_values[sorted_indices[start]],
                    )
                {
                    groups.push(&sorted_indices[start..end]);
                    start = end;
                }
            }

            let mut position: usize = 0;
            let mut dense_rank: usize = 0;
            let mut running: Option<Value> = None;
            for group in groups {
                dense_rank += 1;
                let rank = position + 1;
                if matches!(kind, WindowKind::Min | WindowKind::Max) {
                    for &idx in group {
                        running =
                            self.min_max_step(running, args[idx].clone(), kind == WindowKind::Max)?;
                    }
                }
                for &idx in group {
                    position += 1;
                    column[idx] = match kind {
                        WindowKind::RowNumber => Value::Integer(position as i64),
                        WindowKind::Rank => Value::Integer(rank as i64),
                        WindowKind::DenseRank => Value::Integer(dense_rank as i64),
                        WindowKind::Min | WindowKind::Max => running.clone().unwrap_or(Value::Null),
                    };
                }
            }
        }

        Ok(column)
    }

    /// Fold `value` into a running `MIN` (or `MAX`, when `max`), exactly as
    /// the aggregate `MIN` / `MAX` arms do: a NULL is skipped, and the
    /// current value is replaced only by a STRICTLY smaller (larger) one, so
    /// of values that compare equal the first is kept.
    fn min_max_step(
        &self,
        current: Option<Value>,
        value: Value,
        max: bool,
    ) -> Result<Option<Value>, QueryError> {
        if matches!(value, Value::Null) {
            return Ok(current);
        }
        Ok(Some(match current {
            None => value,
            Some(current) => {
                let replace = if max {
                    self.value_less_than(&current, &value)?
                } else {
                    self.value_less_than(&value, &current)?
                };
                if replace { value } else { current }
            }
        }))
    }
}
