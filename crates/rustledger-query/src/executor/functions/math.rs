//! Math function implementations for the BQL executor.

use rust_decimal::Decimal;

use crate::ast::FunctionCall;
use crate::error::QueryError;

use super::super::Executor;
use super::super::types::{PostingContext, Value};

impl Executor<'_> {
    /// Evaluate math functions: `ABS`, `NEG`, `ROUND`, `SAFEDIV`.
    pub(crate) fn eval_math_function(
        &self,
        name: &str,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        match name {
            "ABS" => {
                Self::require_args(name, func, 1)?;
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::Number(n) => Ok(Value::Number(n.abs())),
                    Value::Integer(i) => Ok(Value::Integer(i.abs())),
                    _ => Err(QueryError::Type("ABS expects a number".to_string())),
                }
            }
            "NEG" => {
                Self::require_args(name, func, 1)?;
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::Number(n) => Ok(Value::Number(-n)),
                    Value::Integer(i) => Ok(Value::Integer(-i)),
                    _ => Err(QueryError::Type("NEG expects a number".to_string())),
                }
            }
            "ROUND" => self.eval_round(func, ctx),
            "SAFEDIV" => self.eval_safediv(func, ctx),
            _ => unreachable!(),
        }
    }

    /// Evaluate ROUND function (takes 1-2 arguments).
    pub(crate) fn eval_round(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        if func.args.is_empty() || func.args.len() > 2 {
            return Err(QueryError::InvalidArguments(
                "ROUND".to_string(),
                "expected 1 or 2 arguments".to_string(),
            ));
        }

        let val = self.evaluate_expr(&func.args[0], ctx)?;
        let decimals = if func.args.len() == 2 {
            match self.evaluate_expr(&func.args[1], ctx)? {
                Value::Integer(i) => i as u32,
                _ => {
                    return Err(QueryError::Type(
                        "ROUND second arg must be integer".to_string(),
                    ));
                }
            }
        } else {
            0
        };

        match val {
            Value::Number(n) => Ok(Value::Number(n.round_dp(decimals))),
            Value::Integer(i) => Ok(Value::Integer(i)),
            _ => Err(QueryError::Type("ROUND expects a number".to_string())),
        }
    }

    /// Evaluate SAFEDIV function.
    pub(crate) fn eval_safediv(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        Self::require_args("SAFEDIV", func, 2)?;
        let num = self.evaluate_expr(&func.args[0], ctx)?;
        let den = self.evaluate_expr(&func.args[1], ctx)?;

        match (num, den) {
            (Value::Number(n), Value::Number(d)) => {
                if d.is_zero() {
                    Ok(Value::Number(Decimal::ZERO))
                } else {
                    Ok(Value::Number(n / d))
                }
            }
            (Value::Integer(n), Value::Integer(d)) => {
                if d == 0 {
                    Ok(Value::Integer(0))
                } else {
                    Ok(Value::Integer(n / d))
                }
            }
            // Mixed numeric operands: coerce the integer to Decimal and divide
            // (matches beanquery, which accepts int↔decimal). A zero divisor
            // yields 0 — the "safe" in SAFEDIV — consistent with the
            // Number/Number arm above.
            (Value::Number(n), Value::Integer(d)) => {
                let d = Decimal::from(d);
                Ok(Value::Number(if d.is_zero() {
                    Decimal::ZERO
                } else {
                    n / d
                }))
            }
            (Value::Integer(n), Value::Number(d)) => {
                let n = Decimal::from(n);
                Ok(Value::Number(if d.is_zero() {
                    Decimal::ZERO
                } else {
                    n / d
                }))
            }
            _ => Err(QueryError::Type("SAFEDIV expects two numbers".to_string())),
        }
    }
}
