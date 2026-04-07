//! Aggregation and grouping functions.

use std::collections::HashMap;

use rust_decimal::Decimal;
use rustledger_core::{Amount, Inventory, Position};

use crate::ast::{Expr, Target, UnaryOperator};
use crate::error::QueryError;

use super::Executor;
use super::types::{PostingContext, Row, Value};

impl<'a> Executor<'a> {
    pub(super) fn is_aggregate_expr(expr: &Expr) -> bool {
        match expr {
            Expr::Function(func) => {
                // Check if this function itself is an aggregate
                if matches!(
                    func.name.to_uppercase().as_str(),
                    "SUM" | "COUNT" | "MIN" | "MAX" | "FIRST" | "LAST" | "AVG"
                ) {
                    return true;
                }
                // Also check if any argument contains an aggregate (e.g., units(sum(position)))
                func.args.iter().any(Self::is_aggregate_expr)
            }
            Expr::BinaryOp(op) => {
                Self::is_aggregate_expr(&op.left) || Self::is_aggregate_expr(&op.right)
            }
            Expr::UnaryOp(op) => Self::is_aggregate_expr(&op.operand),
            Expr::Paren(inner) => Self::is_aggregate_expr(inner),
            _ => false,
        }
    }

    /// Extract non-aggregate expressions from SELECT targets for implicit GROUP BY.
    ///
    /// When aggregate functions are mixed with non-aggregated columns and no explicit
    /// GROUP BY is provided, Python beancount implicitly groups by the non-aggregated
    /// columns. This function extracts those columns.
    ///
    /// For example, in `SELECT sum(number), currency, account`:
    /// - `sum(number)` is an aggregate
    /// - `currency` and `account` are non-aggregates that should be grouped by
    ///
    /// Duplicate expressions are filtered out to avoid redundant evaluation during
    /// grouping and unnecessarily larger group keys.
    pub(super) fn extract_implicit_group_by_exprs(targets: &[Target]) -> Vec<Expr> {
        let mut non_aggregate_exprs = Vec::new();
        for target in targets {
            // Skip wildcard - it expands to all columns, not useful for grouping
            if matches!(target.expr, Expr::Wildcard) {
                continue;
            }
            // Only include non-aggregate expressions, and deduplicate
            if !Self::is_aggregate_expr(&target.expr) && !non_aggregate_exprs.contains(&target.expr)
            {
                non_aggregate_exprs.push(target.expr.clone());
            }
        }
        non_aggregate_exprs
    }
    pub(super) fn make_group_key(values: &[Value]) -> String {
        use std::fmt::Write;
        let mut key = String::new();
        for (i, v) in values.iter().enumerate() {
            if i > 0 {
                key.push('\x00'); // Null separator between values
            }
            match v {
                Value::String(s) => {
                    key.push('S');
                    key.push_str(s);
                }
                Value::Number(n) => {
                    key.push('N');
                    let _ = write!(key, "{n}");
                }
                Value::Integer(n) => {
                    key.push('I');
                    let _ = write!(key, "{n}");
                }
                Value::Date(d) => {
                    key.push('D');
                    let _ = write!(key, "{d}");
                }
                Value::Boolean(b) => {
                    key.push(if *b { 'T' } else { 'F' });
                }
                Value::Amount(a) => {
                    key.push('A');
                    let _ = write!(key, "{} {}", a.number, a.currency);
                }
                Value::Position(p) => {
                    key.push('P');
                    let _ = write!(key, "{} {}", p.units.number, p.units.currency);
                }
                Value::Inventory(_) => {
                    // Inventories are complex; use a placeholder
                    // (unlikely to be used as GROUP BY key)
                    key.push('V');
                }
                Value::StringSet(ss) => {
                    key.push('Z');
                    for s in ss {
                        key.push_str(s);
                        key.push(',');
                    }
                }
                Value::Set(values) => {
                    // Generic set - use debug representation
                    key.push('E');
                    let _ = write!(key, "{values:?}");
                }
                Value::Metadata(meta) => {
                    // Metadata as GROUP BY key - use debug representation
                    key.push('M');
                    let _ = write!(key, "{meta:?}");
                }
                Value::Interval(i) => {
                    key.push('R');
                    let _ = write!(key, "{} {:?}", i.count, i.unit);
                }
                Value::Object(obj) => {
                    // Objects are complex; serialize keys/values
                    key.push('O');
                    for (k, v) in obj.as_ref() {
                        key.push_str(k);
                        key.push(':');
                        let _ = write!(key, "{v:?}");
                        key.push(';');
                    }
                }
                Value::Null => {
                    key.push('0');
                }
            }
        }
        key
    }
    pub(super) fn group_postings<'b>(
        &self,
        postings: &'b [PostingContext<'a>],
        group_by: Option<&Vec<Expr>>,
    ) -> Result<Vec<(Vec<Value>, Vec<&'b PostingContext<'a>>)>, QueryError> {
        if let Some(group_exprs) = group_by {
            // Use HashMap for O(1) grouping
            let mut group_map: HashMap<String, (Vec<Value>, Vec<&PostingContext<'a>>)> =
                HashMap::new();

            for ctx in postings {
                let mut key_values = Vec::with_capacity(group_exprs.len());
                for expr in group_exprs {
                    key_values.push(self.evaluate_expr(expr, ctx)?);
                }
                let hash_key = Self::make_group_key(&key_values);

                group_map
                    .entry(hash_key)
                    .or_insert_with(|| (key_values, Vec::new()))
                    .1
                    .push(ctx);
            }

            Ok(group_map.into_values().collect())
        } else {
            // No GROUP BY - all postings in one group
            // But if there are no postings, return no groups (matching Python beancount)
            if postings.is_empty() {
                Ok(vec![])
            } else {
                Ok(vec![(Vec::new(), postings.iter().collect())])
            }
        }
    }
    pub(super) fn evaluate_aggregate_row(
        &self,
        targets: &[Target],
        group: &[&PostingContext],
    ) -> Result<Row, QueryError> {
        let mut row = Vec::new();
        for target in targets {
            row.push(self.evaluate_aggregate_expr(&target.expr, group)?);
        }
        Ok(row)
    }
    pub(super) fn evaluate_aggregate_expr(
        &self,
        expr: &Expr,
        group: &[&PostingContext],
    ) -> Result<Value, QueryError> {
        match expr {
            Expr::Function(func) => {
                match func.name.to_uppercase().as_str() {
                    "COUNT" => {
                        // COUNT(*) counts all rows
                        Ok(Value::Integer(group.len() as i64))
                    }
                    "SUM" => {
                        if func.args.len() != 1 {
                            return Err(QueryError::InvalidArguments(
                                "SUM".to_string(),
                                "expected 1 argument".to_string(),
                            ));
                        }
                        // Track whether we're summing plain numbers or amounts/positions
                        let mut total_inventory = Inventory::new();
                        let mut total_number = Decimal::ZERO;
                        let mut has_positions = false;
                        let mut has_numbers = false;

                        for ctx in group {
                            let val = self.evaluate_expr(&func.args[0], ctx)?;
                            match val {
                                Value::Amount(amt) => {
                                    let pos = Position::simple(amt);
                                    total_inventory.add(pos);
                                    has_positions = true;
                                }
                                Value::Position(pos) => {
                                    total_inventory.add(*pos);
                                    has_positions = true;
                                }
                                Value::Number(n) => {
                                    total_number += n;
                                    has_numbers = true;
                                }
                                Value::Integer(i) => {
                                    total_number += Decimal::from(i);
                                    has_numbers = true;
                                }
                                Value::Null => {}
                                _ => {
                                    return Err(QueryError::Type(
                                        "SUM requires numeric or position value".to_string(),
                                    ));
                                }
                            }
                        }

                        // Return appropriate type based on what was summed
                        if has_positions {
                            // If we have any amounts/positions, return as inventory
                            // (also add any plain numbers as __NUMBER__ currency)
                            if has_numbers && !total_number.is_zero() {
                                total_inventory.add(Position::simple(Amount::new(
                                    total_number,
                                    "__NUMBER__".to_string(),
                                )));
                            }
                            Ok(Value::Inventory(Box::new(total_inventory)))
                        } else if has_numbers {
                            // Pure number sum - return as Number
                            Ok(Value::Number(total_number))
                        } else {
                            // No values summed (all nulls)
                            Ok(Value::Null)
                        }
                    }
                    "FIRST" => {
                        if func.args.len() != 1 {
                            return Err(QueryError::InvalidArguments(
                                "FIRST".to_string(),
                                "expected 1 argument".to_string(),
                            ));
                        }
                        // Find chronologically first posting (by transaction date)
                        if let Some(ctx) = group.iter().min_by_key(|c| c.transaction.date) {
                            self.evaluate_expr(&func.args[0], ctx)
                        } else {
                            Ok(Value::Null)
                        }
                    }
                    "LAST" => {
                        if func.args.len() != 1 {
                            return Err(QueryError::InvalidArguments(
                                "LAST".to_string(),
                                "expected 1 argument".to_string(),
                            ));
                        }
                        // Find chronologically last posting (by transaction date)
                        if let Some(ctx) = group.iter().max_by_key(|c| c.transaction.date) {
                            self.evaluate_expr(&func.args[0], ctx)
                        } else {
                            Ok(Value::Null)
                        }
                    }
                    "MIN" => {
                        if func.args.len() != 1 {
                            return Err(QueryError::InvalidArguments(
                                "MIN".to_string(),
                                "expected 1 argument".to_string(),
                            ));
                        }
                        let mut min_val: Option<Value> = None;
                        for ctx in group {
                            let val = self.evaluate_expr(&func.args[0], ctx)?;
                            if matches!(val, Value::Null) {
                                continue;
                            }
                            min_val = Some(match min_val {
                                None => val,
                                Some(current) => {
                                    if self.value_less_than(&val, &current)? {
                                        val
                                    } else {
                                        current
                                    }
                                }
                            });
                        }
                        Ok(min_val.unwrap_or(Value::Null))
                    }
                    "MAX" => {
                        if func.args.len() != 1 {
                            return Err(QueryError::InvalidArguments(
                                "MAX".to_string(),
                                "expected 1 argument".to_string(),
                            ));
                        }
                        let mut max_val: Option<Value> = None;
                        for ctx in group {
                            let val = self.evaluate_expr(&func.args[0], ctx)?;
                            if matches!(val, Value::Null) {
                                continue;
                            }
                            max_val = Some(match max_val {
                                None => val,
                                Some(current) => {
                                    if self.value_less_than(&current, &val)? {
                                        val
                                    } else {
                                        current
                                    }
                                }
                            });
                        }
                        Ok(max_val.unwrap_or(Value::Null))
                    }
                    "AVG" => {
                        if func.args.len() != 1 {
                            return Err(QueryError::InvalidArguments(
                                "AVG".to_string(),
                                "expected 1 argument".to_string(),
                            ));
                        }
                        let mut sum = Decimal::ZERO;
                        let mut count = 0i64;
                        for ctx in group {
                            let val = self.evaluate_expr(&func.args[0], ctx)?;
                            match val {
                                Value::Number(n) => {
                                    sum += n;
                                    count += 1;
                                }
                                Value::Integer(i) => {
                                    sum += Decimal::from(i);
                                    count += 1;
                                }
                                Value::Null => {}
                                _ => {
                                    return Err(QueryError::Type(
                                        "AVG expects numeric values".to_string(),
                                    ));
                                }
                            }
                        }
                        if count == 0 {
                            Ok(Value::Null)
                        } else {
                            Ok(Value::Number(sum / Decimal::from(count)))
                        }
                    }
                    _ => {
                        // Non-aggregate function — check if any argument contains
                        // an aggregate (SUM, COUNT, etc.). If not, evaluate the whole
                        // expression with the first posting context, which preserves
                        // access to metadata, account info, etc.
                        let has_aggregate_arg = func.args.iter().any(Self::is_aggregate_expr);
                        if !has_aggregate_arg {
                            if let Some(ctx) = group.first() {
                                return self.evaluate_expr(expr, ctx);
                            }
                            return Ok(Value::Null);
                        }
                        // At least one arg contains an aggregate — evaluate all args
                        // in aggregate mode, then apply function to pre-evaluated values.
                        let mut evaluated_args = Vec::with_capacity(func.args.len());
                        for arg in &func.args {
                            evaluated_args.push(self.evaluate_aggregate_expr(arg, group)?);
                        }
                        self.evaluate_function_on_values(&func.name, &evaluated_args)
                    }
                }
            }
            Expr::Column(_) => {
                // For non-aggregate columns in aggregate query, take first value
                if let Some(ctx) = group.first() {
                    self.evaluate_expr(expr, ctx)
                } else {
                    Ok(Value::Null)
                }
            }
            Expr::BinaryOp(op) => {
                let left = self.evaluate_aggregate_expr(&op.left, group)?;
                let right = self.evaluate_aggregate_expr(&op.right, group)?;
                // Re-evaluate with computed values
                self.binary_op_on_values(op.op, &left, &right)
            }
            Expr::UnaryOp(op) => {
                let val = self.evaluate_aggregate_expr(&op.operand, group)?;
                self.unary_op_on_value(op.op, &val)
            }
            Expr::Paren(inner) => self.evaluate_aggregate_expr(inner, group),
            Expr::Between { value, low, high } => {
                let val = self.evaluate_aggregate_expr(value, group)?;
                let low_val = self.evaluate_aggregate_expr(low, group)?;
                let high_val = self.evaluate_aggregate_expr(high, group)?;
                let ge = self.compare_values(&val, &low_val, std::cmp::Ordering::is_ge)?;
                let le = self.compare_values(&val, &high_val, std::cmp::Ordering::is_le)?;
                match (ge, le) {
                    (Value::Boolean(g), Value::Boolean(l)) => Ok(Value::Boolean(g && l)),
                    _ => Err(QueryError::Type(
                        "BETWEEN requires comparable values".to_string(),
                    )),
                }
            }
            _ => {
                // For other expressions (Column, Literal, Wildcard, Window), evaluate on first row
                if let Some(ctx) = group.first() {
                    self.evaluate_expr(expr, ctx)
                } else {
                    Ok(Value::Null)
                }
            }
        }
    }
    pub(super) fn evaluate_having_filter(
        &self,
        having_expr: &Expr,
        row: &[Value],
        column_names: &[String],
        targets: &[Target],
        group: &[&PostingContext],
    ) -> Result<bool, QueryError> {
        // Build a map of column name -> index for quick lookup
        let col_map: HashMap<String, usize> = column_names
            .iter()
            .enumerate()
            .map(|(i, name)| (name.to_uppercase(), i))
            .collect();

        // Also map aliases
        let alias_map: HashMap<String, usize> = targets
            .iter()
            .enumerate()
            .filter_map(|(i, t)| t.alias.as_ref().map(|a| (a.to_uppercase(), i)))
            .collect();

        let val = self.evaluate_having_expr(having_expr, row, &col_map, &alias_map, group)?;

        match val {
            Value::Boolean(b) => Ok(b),
            Value::Null => Ok(false), // NULL is treated as false in HAVING
            _ => Err(QueryError::Type(
                "HAVING clause must evaluate to boolean".to_string(),
            )),
        }
    }
    pub(super) fn evaluate_having_expr(
        &self,
        expr: &Expr,
        row: &[Value],
        col_map: &HashMap<String, usize>,
        alias_map: &HashMap<String, usize>,
        group: &[&PostingContext],
    ) -> Result<Value, QueryError> {
        match expr {
            Expr::Column(name) => {
                let upper_name = name.to_uppercase();
                // Try alias first, then column name
                if let Some(&idx) = alias_map.get(&upper_name) {
                    Ok(row.get(idx).cloned().unwrap_or(Value::Null))
                } else if let Some(&idx) = col_map.get(&upper_name) {
                    Ok(row.get(idx).cloned().unwrap_or(Value::Null))
                } else {
                    Err(QueryError::Evaluation(format!(
                        "Column '{name}' not found in SELECT clause for HAVING"
                    )))
                }
            }
            Expr::Literal(lit) => self.evaluate_literal(lit),
            Expr::Function(_) => {
                // Re-evaluate aggregate function on group
                self.evaluate_aggregate_expr(expr, group)
            }
            Expr::BinaryOp(op) => {
                let left = self.evaluate_having_expr(&op.left, row, col_map, alias_map, group)?;
                let right = self.evaluate_having_expr(&op.right, row, col_map, alias_map, group)?;
                self.binary_op_on_values(op.op, &left, &right)
            }
            Expr::UnaryOp(op) => {
                let val = self.evaluate_having_expr(&op.operand, row, col_map, alias_map, group)?;
                match op.op {
                    UnaryOperator::Not => {
                        let b = self.to_bool(&val)?;
                        Ok(Value::Boolean(!b))
                    }
                    UnaryOperator::Neg => match val {
                        Value::Number(n) => Ok(Value::Number(-n)),
                        Value::Integer(i) => Ok(Value::Integer(-i)),
                        _ => Err(QueryError::Type(
                            "Cannot negate non-numeric value".to_string(),
                        )),
                    },
                    UnaryOperator::IsNull => Ok(Value::Boolean(matches!(val, Value::Null))),
                    UnaryOperator::IsNotNull => Ok(Value::Boolean(!matches!(val, Value::Null))),
                }
            }
            Expr::Paren(inner) => self.evaluate_having_expr(inner, row, col_map, alias_map, group),
            Expr::Wildcard => Err(QueryError::Evaluation(
                "Wildcard not allowed in HAVING clause".to_string(),
            )),
            Expr::Window(_) => Err(QueryError::Evaluation(
                "Window functions not allowed in HAVING clause".to_string(),
            )),
            Expr::Between { value, low, high } => {
                let val = self.evaluate_having_expr(value, row, col_map, alias_map, group)?;
                let low_val = self.evaluate_having_expr(low, row, col_map, alias_map, group)?;
                let high_val = self.evaluate_having_expr(high, row, col_map, alias_map, group)?;

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
                    let val = self.evaluate_having_expr(elem, row, col_map, alias_map, group)?;
                    if !matches!(val, Value::Null) {
                        values.push(val);
                    }
                }
                Ok(Value::Set(values))
            }
        }
    }
}
