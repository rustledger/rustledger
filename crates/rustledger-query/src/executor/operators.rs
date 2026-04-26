//! Binary and unary operators, comparisons, and arithmetic operations.

use rust_decimal::Decimal;

use crate::ast::{BinaryOp, BinaryOperator, UnaryOp, UnaryOperator};
use crate::error::QueryError;

use super::Executor;
use super::types::{Interval, PostingContext, Value};

impl Executor<'_> {
    /// Evaluate a binary operation.
    pub(super) fn evaluate_binary_op(
        &self,
        op: &BinaryOp,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        let left = self.evaluate_expr(&op.left, ctx)?;
        let right = self.evaluate_expr(&op.right, ctx)?;

        match op.op {
            BinaryOperator::Eq => Ok(Value::Boolean(self.values_equal(&left, &right))),
            BinaryOperator::Ne => Ok(Value::Boolean(!self.values_equal(&left, &right))),
            BinaryOperator::Lt => self.compare_values(&left, &right, std::cmp::Ordering::is_lt),
            BinaryOperator::Le => self.compare_values(&left, &right, std::cmp::Ordering::is_le),
            BinaryOperator::Gt => self.compare_values(&left, &right, std::cmp::Ordering::is_gt),
            BinaryOperator::Ge => self.compare_values(&left, &right, std::cmp::Ordering::is_ge),
            BinaryOperator::And => {
                let l = self.to_bool(&left)?;
                let r = self.to_bool(&right)?;
                Ok(Value::Boolean(l && r))
            }
            BinaryOperator::Or => {
                let l = self.to_bool(&left)?;
                let r = self.to_bool(&right)?;
                Ok(Value::Boolean(l || r))
            }
            BinaryOperator::Regex => {
                // ~ operator: string matches regex pattern
                // NULL ~ pattern returns false (matches Python beancount behavior)
                let s = match left {
                    Value::String(s) => s,
                    Value::Null => return Ok(Value::Boolean(false)),
                    _ => {
                        return Err(QueryError::Type(
                            "regex requires string left operand".to_string(),
                        ));
                    }
                };
                let pattern = match right {
                    Value::String(p) => p,
                    _ => {
                        return Err(QueryError::Type(
                            "regex requires string pattern".to_string(),
                        ));
                    }
                };
                // Use cached regex matching
                let re = self.require_regex(&pattern)?;
                Ok(Value::Boolean(re.is_match(&s)))
            }
            BinaryOperator::In => {
                // Check if left value is in right set
                match right {
                    Value::StringSet(set) => {
                        // StringSet from columns like tags, links
                        let needle = match left {
                            Value::String(s) => s,
                            _ => {
                                return Err(QueryError::Type(
                                    "IN requires string left operand for StringSet".to_string(),
                                ));
                            }
                        };
                        Ok(Value::Boolean(set.contains(&needle)))
                    }
                    Value::Set(values) => {
                        // Generic set from set literal - check if left equals any element
                        let found = values.iter().any(|v| self.values_equal(&left, v));
                        Ok(Value::Boolean(found))
                    }
                    // Fall back to scalar equality so `x IN ('a')` ≡ `x = 'a'`,
                    // matching SQL/bean-query semantics (issue #916).
                    other => Ok(Value::Boolean(self.values_equal(&left, &other))),
                }
            }
            BinaryOperator::NotRegex => {
                // !~ operator: string does not match regex pattern
                // NULL !~ pattern returns true (matches Python beancount behavior)
                let s = match left {
                    Value::String(s) => s,
                    Value::Null => return Ok(Value::Boolean(true)),
                    _ => {
                        return Err(QueryError::Type(
                            "!~ requires string left operand".to_string(),
                        ));
                    }
                };
                let pattern = match right {
                    Value::String(p) => p,
                    _ => {
                        return Err(QueryError::Type("!~ requires string pattern".to_string()));
                    }
                };
                let re = self.require_regex(&pattern)?;
                Ok(Value::Boolean(!re.is_match(&s)))
            }
            BinaryOperator::NotIn => {
                // NOT IN: check if left value is not in right set
                match right {
                    Value::StringSet(set) => {
                        // StringSet from columns like tags, links
                        let needle = match left {
                            Value::String(s) => s,
                            _ => {
                                return Err(QueryError::Type(
                                    "NOT IN requires string left operand for StringSet".to_string(),
                                ));
                            }
                        };
                        Ok(Value::Boolean(!set.contains(&needle)))
                    }
                    Value::Set(values) => {
                        // Generic set from set literal - check if left equals any element
                        let found = values.iter().any(|v| self.values_equal(&left, v));
                        Ok(Value::Boolean(!found))
                    }
                    // Fall back to scalar inequality so `x NOT IN ('a')` ≡ `x != 'a'`,
                    // matching SQL/bean-query semantics (issue #916).
                    other => Ok(Value::Boolean(!self.values_equal(&left, &other))),
                }
            }
            BinaryOperator::Add => {
                // Handle date + interval
                match (&left, &right) {
                    (Value::Date(d), Value::Interval(i)) | (Value::Interval(i), Value::Date(d)) => {
                        i.add_to_date(*d)
                            .map(Value::Date)
                            .ok_or_else(|| QueryError::Evaluation("date overflow".to_string()))
                    }
                    _ => self.arithmetic_op(&left, &right, |a, b| a + b),
                }
            }
            BinaryOperator::Sub => {
                // Handle date - interval
                match (&left, &right) {
                    (Value::Date(d), Value::Interval(i)) => {
                        let neg_count = i.count.checked_neg().ok_or_else(|| {
                            QueryError::Evaluation("interval count overflow".to_string())
                        })?;
                        let neg_interval = Interval::new(neg_count, i.unit);
                        neg_interval
                            .add_to_date(*d)
                            .map(Value::Date)
                            .ok_or_else(|| QueryError::Evaluation("date overflow".to_string()))
                    }
                    _ => self.arithmetic_op(&left, &right, |a, b| a - b),
                }
            }
            BinaryOperator::Mul => self.arithmetic_op(&left, &right, |a, b| a * b),
            BinaryOperator::Div => self.arithmetic_op(&left, &right, |a, b| a / b),
            BinaryOperator::Mod => self.arithmetic_op(&left, &right, |a, b| a % b),
        }
    }

    /// Evaluate a unary operation.
    pub(super) fn evaluate_unary_op(
        &self,
        op: &UnaryOp,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        let val = self.evaluate_expr(&op.operand, ctx)?;
        self.unary_op_on_value(op.op, &val)
    }

    /// Apply a unary operator to a value.
    pub(super) fn unary_op_on_value(
        &self,
        op: UnaryOperator,
        val: &Value,
    ) -> Result<Value, QueryError> {
        match op {
            UnaryOperator::Not => {
                let b = self.to_bool(val)?;
                Ok(Value::Boolean(!b))
            }
            UnaryOperator::Neg => match val {
                Value::Number(n) => Ok(Value::Number(-*n)),
                Value::Integer(i) => Ok(Value::Integer(-*i)),
                _ => Err(QueryError::Type(
                    "negation requires numeric value".to_string(),
                )),
            },
            UnaryOperator::IsNull => Ok(Value::Boolean(matches!(val, Value::Null))),
            UnaryOperator::IsNotNull => Ok(Value::Boolean(!matches!(val, Value::Null))),
        }
    }

    /// Check if two values are equal.
    pub(super) fn values_equal(&self, left: &Value, right: &Value) -> bool {
        // BQL treats NULL = NULL as TRUE
        match (left, right) {
            (Value::Null, Value::Null) => true,
            (Value::String(a), Value::String(b)) => a == b,
            (Value::Number(a), Value::Number(b)) => a == b,
            (Value::Integer(a), Value::Integer(b)) => a == b,
            (Value::Number(a), Value::Integer(b)) => *a == Decimal::from(*b),
            (Value::Integer(a), Value::Number(b)) => Decimal::from(*a) == *b,
            (Value::Date(a), Value::Date(b)) => a == b,
            (Value::Boolean(a), Value::Boolean(b)) => a == b,
            _ => false,
        }
    }

    /// Compare two values.
    pub(super) fn compare_values<F>(
        &self,
        left: &Value,
        right: &Value,
        pred: F,
    ) -> Result<Value, QueryError>
    where
        F: FnOnce(std::cmp::Ordering) -> bool,
    {
        let ord = match (left, right) {
            (Value::Number(a), Value::Number(b)) => a.cmp(b),
            (Value::Integer(a), Value::Integer(b)) => a.cmp(b),
            (Value::Number(a), Value::Integer(b)) => a.cmp(&Decimal::from(*b)),
            (Value::Integer(a), Value::Number(b)) => Decimal::from(*a).cmp(b),
            (Value::String(a), Value::String(b)) => a.cmp(b),
            (Value::Date(a), Value::Date(b)) => a.cmp(b),
            _ => return Err(QueryError::Type("cannot compare values".to_string())),
        };
        Ok(Value::Boolean(pred(ord)))
    }

    /// Check if left value is less than right value.
    pub(super) fn value_less_than(&self, left: &Value, right: &Value) -> Result<bool, QueryError> {
        let ord = match (left, right) {
            (Value::Number(a), Value::Number(b)) => a.cmp(b),
            (Value::Integer(a), Value::Integer(b)) => a.cmp(b),
            (Value::Number(a), Value::Integer(b)) => a.cmp(&Decimal::from(*b)),
            (Value::Integer(a), Value::Number(b)) => Decimal::from(*a).cmp(b),
            (Value::String(a), Value::String(b)) => a.cmp(b),
            (Value::Date(a), Value::Date(b)) => a.cmp(b),
            _ => return Err(QueryError::Type("cannot compare values".to_string())),
        };
        Ok(ord.is_lt())
    }

    /// Perform arithmetic operation.
    pub(super) fn arithmetic_op<F>(
        &self,
        left: &Value,
        right: &Value,
        op: F,
    ) -> Result<Value, QueryError>
    where
        F: FnOnce(Decimal, Decimal) -> Decimal,
    {
        let (a, b) = match (left, right) {
            (Value::Number(a), Value::Number(b)) => (*a, *b),
            (Value::Integer(a), Value::Integer(b)) => (Decimal::from(*a), Decimal::from(*b)),
            (Value::Number(a), Value::Integer(b)) => (*a, Decimal::from(*b)),
            (Value::Integer(a), Value::Number(b)) => (Decimal::from(*a), *b),
            _ => {
                return Err(QueryError::Type(
                    "arithmetic requires numeric values".to_string(),
                ));
            }
        };
        Ok(Value::Number(op(a, b)))
    }

    /// Convert a value to boolean using SQL/beanquery truthiness rules.
    ///
    /// Booleans pass through directly. NULL is false. Other types follow
    /// Python beanquery's implicit truthiness so that functions like
    /// `grep(pattern, text)` — which return the matched substring on success
    /// and NULL on failure — work in `WHERE` and as operands of `AND`/`OR`/
    /// `NOT` without an explicit comparison.
    ///
    /// - Strings: non-empty is true.
    /// - Integers / numbers: non-zero is true.
    /// - Sets / metadata / objects: non-empty is true.
    /// - Other structured types (Date, Amount, Position, …): always true.
    pub(super) fn to_bool(&self, val: &Value) -> Result<bool, QueryError> {
        Ok(match val {
            Value::Boolean(b) => *b,
            Value::Null => false,
            Value::String(s) => !s.is_empty(),
            Value::Integer(i) => *i != 0,
            Value::Number(n) => !n.is_zero(),
            Value::StringSet(s) => !s.is_empty(),
            Value::Set(s) => !s.is_empty(),
            Value::Metadata(m) => !m.is_empty(),
            Value::Object(o) => !o.is_empty(),
            // Date, Amount, Position, Inventory, Interval — present implies truthy.
            Value::Date(_)
            | Value::Amount(_)
            | Value::Position(_)
            | Value::Inventory(_)
            | Value::Interval(_) => true,
        })
    }

    /// Apply a binary operator to pre-evaluated values (for subquery context).
    pub(super) fn binary_op_on_values(
        &self,
        op: BinaryOperator,
        left: &Value,
        right: &Value,
    ) -> Result<Value, QueryError> {
        match op {
            BinaryOperator::Eq => Ok(Value::Boolean(self.values_equal(left, right))),
            BinaryOperator::Ne => Ok(Value::Boolean(!self.values_equal(left, right))),
            BinaryOperator::Lt => self.compare_values(left, right, std::cmp::Ordering::is_lt),
            BinaryOperator::Le => self.compare_values(left, right, std::cmp::Ordering::is_le),
            BinaryOperator::Gt => self.compare_values(left, right, std::cmp::Ordering::is_gt),
            BinaryOperator::Ge => self.compare_values(left, right, std::cmp::Ordering::is_ge),
            BinaryOperator::And => {
                let l = self.to_bool(left)?;
                let r = self.to_bool(right)?;
                Ok(Value::Boolean(l && r))
            }
            BinaryOperator::Or => {
                let l = self.to_bool(left)?;
                let r = self.to_bool(right)?;
                Ok(Value::Boolean(l || r))
            }
            BinaryOperator::Regex => {
                // ~ operator: string matches regex pattern
                // NULL ~ pattern returns false (matches Python beancount behavior)
                let s = match left {
                    Value::String(s) => s,
                    Value::Null => return Ok(Value::Boolean(false)),
                    _ => {
                        return Err(QueryError::Type(
                            "regex requires string left operand".to_string(),
                        ));
                    }
                };
                let pattern = match right {
                    Value::String(p) => p,
                    _ => {
                        return Err(QueryError::Type(
                            "regex requires string pattern".to_string(),
                        ));
                    }
                };
                // Use cached regex matching
                let re = self.require_regex(pattern)?;
                Ok(Value::Boolean(re.is_match(s)))
            }
            BinaryOperator::In => {
                // Check if left value is in right set
                match right {
                    Value::StringSet(set) => {
                        // StringSet from columns like tags, links
                        let needle = match left {
                            Value::String(s) => s,
                            _ => {
                                return Err(QueryError::Type(
                                    "IN requires string left operand for StringSet".to_string(),
                                ));
                            }
                        };
                        Ok(Value::Boolean(set.contains(needle)))
                    }
                    Value::Set(values) => {
                        // Generic set from set literal - check if left equals any element
                        let found = values.iter().any(|v| self.values_equal(left, v));
                        Ok(Value::Boolean(found))
                    }
                    // Fall back to scalar equality so `x IN ('a')` ≡ `x = 'a'`,
                    // matching SQL/bean-query semantics (issue #916).
                    _ => Ok(Value::Boolean(self.values_equal(left, right))),
                }
            }
            BinaryOperator::NotRegex => {
                // !~ operator: string does not match regex pattern
                // NULL !~ pattern returns true (matches Python beancount behavior)
                let s = match left {
                    Value::String(s) => s,
                    Value::Null => return Ok(Value::Boolean(true)),
                    _ => {
                        return Err(QueryError::Type(
                            "!~ requires string left operand".to_string(),
                        ));
                    }
                };
                let pattern = match right {
                    Value::String(p) => p,
                    _ => {
                        return Err(QueryError::Type("!~ requires string pattern".to_string()));
                    }
                };
                let re = self.require_regex(pattern)?;
                Ok(Value::Boolean(!re.is_match(s)))
            }
            BinaryOperator::NotIn => {
                // NOT IN: check if left value is not in right set
                match right {
                    Value::StringSet(set) => {
                        // StringSet from columns like tags, links
                        let needle = match left {
                            Value::String(s) => s,
                            _ => {
                                return Err(QueryError::Type(
                                    "NOT IN requires string left operand for StringSet".to_string(),
                                ));
                            }
                        };
                        Ok(Value::Boolean(!set.contains(needle)))
                    }
                    Value::Set(values) => {
                        // Generic set from set literal - check if left does not equal any element
                        let found = values.iter().any(|v| self.values_equal(left, v));
                        Ok(Value::Boolean(!found))
                    }
                    // Fall back to scalar inequality so `x NOT IN ('a')` ≡ `x != 'a'`,
                    // matching SQL/bean-query semantics (issue #916).
                    _ => Ok(Value::Boolean(!self.values_equal(left, right))),
                }
            }
            BinaryOperator::Add => {
                // Handle date + interval
                match (left, right) {
                    (Value::Date(d), Value::Interval(i)) | (Value::Interval(i), Value::Date(d)) => {
                        i.add_to_date(*d)
                            .map(Value::Date)
                            .ok_or_else(|| QueryError::Evaluation("date overflow".to_string()))
                    }
                    _ => self.arithmetic_op(left, right, |a, b| a + b),
                }
            }
            BinaryOperator::Sub => {
                // Handle date - interval
                match (left, right) {
                    (Value::Date(d), Value::Interval(i)) => {
                        let neg_count = i.count.checked_neg().ok_or_else(|| {
                            QueryError::Evaluation("interval count overflow".to_string())
                        })?;
                        let neg_interval = Interval::new(neg_count, i.unit);
                        neg_interval
                            .add_to_date(*d)
                            .map(Value::Date)
                            .ok_or_else(|| QueryError::Evaluation("date overflow".to_string()))
                    }
                    _ => self.arithmetic_op(left, right, |a, b| a - b),
                }
            }
            BinaryOperator::Mul => self.arithmetic_op(left, right, |a, b| a * b),
            BinaryOperator::Div => self.arithmetic_op(left, right, |a, b| a / b),
            BinaryOperator::Mod => self.arithmetic_op(left, right, |a, b| a % b),
        }
    }

    /// Compare two values for sorting purposes.
    pub(super) fn compare_values_for_sort(
        &self,
        left: &Value,
        right: &Value,
    ) -> std::cmp::Ordering {
        match (left, right) {
            (Value::Null, Value::Null) => std::cmp::Ordering::Equal,
            (Value::Null, _) => std::cmp::Ordering::Greater, // Nulls sort last
            (_, Value::Null) => std::cmp::Ordering::Less,
            (Value::Number(a), Value::Number(b)) => a.cmp(b),
            (Value::Integer(a), Value::Integer(b)) => a.cmp(b),
            (Value::Number(a), Value::Integer(b)) => a.cmp(&Decimal::from(*b)),
            (Value::Integer(a), Value::Number(b)) => Decimal::from(*a).cmp(b),
            (Value::String(a), Value::String(b)) => a.cmp(b),
            (Value::Date(a), Value::Date(b)) => a.cmp(b),
            (Value::Boolean(a), Value::Boolean(b)) => a.cmp(b),
            // Compare amounts by their numeric value (same currency assumed)
            (Value::Amount(a), Value::Amount(b)) => a.number.cmp(&b.number),
            // Compare positions by their units' numeric value
            (Value::Position(a), Value::Position(b)) => a.units.number.cmp(&b.units.number),
            // Compare inventories by first position's value (for single-currency)
            (Value::Inventory(a), Value::Inventory(b)) => {
                let a_val = a.positions().first().map(|p| &p.units.number);
                let b_val = b.positions().first().map(|p| &p.units.number);
                match (a_val, b_val) {
                    (Some(av), Some(bv)) => av.cmp(bv),
                    (Some(_), None) => std::cmp::Ordering::Less,
                    (None, Some(_)) => std::cmp::Ordering::Greater,
                    (None, None) => std::cmp::Ordering::Equal,
                }
            }
            // Compare intervals by approximate days
            (Value::Interval(a), Value::Interval(b)) => a.to_approx_days().cmp(&b.to_approx_days()),
            _ => std::cmp::Ordering::Equal, // Can't compare other types
        }
    }
}
