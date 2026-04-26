//! Utility function implementations for the BQL executor.
//!
//! This module includes metadata, conversion, casting, and helper functions.

use rust_decimal::Decimal;
use rustledger_core::{Amount, Inventory, MetaValue, Position};

use crate::ast::FunctionCall;
use crate::error::QueryError;

use super::super::Executor;
use super::super::types::{PostingContext, Value};

impl Executor<'_> {
    /// Evaluate metadata functions: `META`, `ENTRY_META`, `ANY_META`.
    ///
    /// - `META(key)` - Get metadata value from the posting
    /// - `ENTRY_META(key)` - Get metadata value from the transaction
    /// - `ANY_META(key)` - Get metadata value from posting, falling back to transaction
    pub(crate) fn eval_meta_function(
        &self,
        name: &str,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        Self::require_args(name, func, 1)?;

        let key = match self.evaluate_expr(&func.args[0], ctx)? {
            Value::String(s) => s,
            _ => {
                return Err(QueryError::Type(format!(
                    "{name}: argument must be a string key"
                )));
            }
        };

        let posting = &ctx.transaction.postings[ctx.posting_index];

        let meta_value = match name {
            "META" | "POSTING_META" => posting.meta.get(&key),
            "ENTRY_META" => ctx.transaction.meta.get(&key),
            "ANY_META" => posting
                .meta
                .get(&key)
                .or_else(|| ctx.transaction.meta.get(&key)),
            _ => unreachable!(),
        };

        Ok(Self::meta_value_to_value(meta_value))
    }

    /// Convert a `MetaValue` to a `Value`.
    pub(crate) fn meta_value_to_value(mv: Option<&MetaValue>) -> Value {
        match mv {
            None => Value::Null,
            Some(MetaValue::String(s)) => Value::String(s.clone()),
            Some(MetaValue::Number(n)) => Value::Number(*n),
            Some(MetaValue::Date(d)) => Value::Date(*d),
            Some(MetaValue::Bool(b)) => Value::Boolean(*b),
            Some(MetaValue::Amount(a)) => Value::Amount(a.clone()),
            Some(MetaValue::Account(s)) => Value::String(s.clone()),
            Some(MetaValue::Currency(s)) => Value::String(s.clone()),
            Some(MetaValue::Tag(s)) => Value::String(s.clone()),
            Some(MetaValue::Link(s)) => Value::String(s.clone()),
            Some(MetaValue::None) => Value::Null,
        }
    }

    /// Evaluate CONVERT function (currency conversion).
    ///
    /// `CONVERT(position, currency)` - Convert position/amount to target currency.
    /// `CONVERT(position, currency, date)` - Convert using price at specific date.
    pub(crate) fn eval_convert(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        if func.args.len() < 2 || func.args.len() > 3 {
            return Err(QueryError::InvalidArguments(
                "CONVERT".to_string(),
                "expected 2 or 3 arguments: (value, currency[, date])".to_string(),
            ));
        }

        let val = self.evaluate_expr(&func.args[0], ctx)?;

        let target_currency = match self.evaluate_expr(&func.args[1], ctx)? {
            Value::String(s) => s,
            Value::Null => {
                return Err(QueryError::Type(
                    concat!(
                        "CONVERT: second argument evaluated to NULL; ",
                        "expected a currency string ",
                        "(this often means an aggregate expression couldn't ",
                        "evaluate against an empty group — see issue #902)",
                    )
                    .to_string(),
                ));
            }
            _ => {
                return Err(QueryError::Type(
                    "CONVERT: second argument must be a currency string".to_string(),
                ));
            }
        };

        // When no date is specified, use the latest price (matches Python beancount behavior)
        let date: Option<rustledger_core::NaiveDate> = if func.args.len() == 3 {
            match self.evaluate_expr(&func.args[2], ctx)? {
                Value::Date(d) => Some(d),
                _ => {
                    return Err(QueryError::Type(
                        "CONVERT: third argument must be a date".to_string(),
                    ));
                }
            }
        } else {
            None // Use latest price when no date specified
        };

        // Helper to convert an amount, using latest price if no date specified
        let convert_amount = |amt: &Amount| -> Option<Amount> {
            if let Some(d) = date {
                self.price_db.convert(amt, &target_currency, d)
            } else {
                self.price_db.convert_latest(amt, &target_currency)
            }
        };

        match val {
            Value::Position(p) => {
                if p.units.currency == target_currency {
                    Ok(Value::Amount(p.units))
                } else if let Some(converted) = convert_amount(&p.units) {
                    Ok(Value::Amount(converted))
                } else {
                    // Return original units if no conversion available
                    Ok(Value::Amount(p.units))
                }
            }
            Value::Amount(a) => {
                if a.currency == target_currency {
                    Ok(Value::Amount(a))
                } else if let Some(converted) = convert_amount(&a) {
                    Ok(Value::Amount(converted))
                } else {
                    Ok(Value::Amount(a))
                }
            }
            Value::Inventory(inv) => {
                // Convert each position, keeping originals when no conversion available
                // (matches Python beancount behavior)
                let mut result = Inventory::default();
                for pos in inv.positions() {
                    if pos.units.currency == target_currency {
                        result.add(Position::simple(pos.units.clone()));
                    } else if let Some(converted) = convert_amount(&pos.units) {
                        result.add(Position::simple(converted));
                    } else {
                        // No conversion available - keep original (Python beancount behavior)
                        result.add(Position::simple(pos.units.clone()));
                    }
                }
                // If result has single currency matching target, return as Amount
                // If result is empty, return zero in target currency (issue #586)
                let positions = result.positions();
                if positions.is_empty() {
                    Ok(Value::Amount(Amount::new(Decimal::ZERO, &target_currency)))
                } else if positions.len() == 1 && positions[0].units.currency == target_currency {
                    Ok(Value::Amount(positions[0].units.clone()))
                } else {
                    Ok(Value::Inventory(Box::new(result)))
                }
            }
            Value::Number(n) => {
                // Just wrap the number as an amount with the target currency
                Ok(Value::Amount(Amount::new(n, &target_currency)))
            }
            Value::Null => {
                // For null values (e.g., empty sum), return zero in target currency
                // This matches Python beancount behavior for empty balances
                Ok(Value::Amount(Amount::new(Decimal::ZERO, &target_currency)))
            }
            _ => Err(QueryError::Type(
                "CONVERT expects a position, amount, inventory, or number".to_string(),
            )),
        }
    }

    /// Evaluate INT function (convert to integer).
    pub(crate) fn eval_int(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        Self::require_args("INT", func, 1)?;
        let val = self.evaluate_expr(&func.args[0], ctx)?;
        Self::value_to_int(&val)
    }

    /// Evaluate DECIMAL function (convert to decimal).
    pub(crate) fn eval_decimal(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        Self::require_args("DECIMAL", func, 1)?;
        let val = self.evaluate_expr(&func.args[0], ctx)?;
        Self::value_to_decimal(&val)
    }

    /// Evaluate STR function (convert to string).
    pub(crate) fn eval_str(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        Self::require_args("STR", func, 1)?;
        let val = self.evaluate_expr(&func.args[0], ctx)?;
        Self::value_to_str(&val)
    }

    /// Evaluate BOOL function (convert to boolean).
    pub(crate) fn eval_bool(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        Self::require_args("BOOL", func, 1)?;
        let val = self.evaluate_expr(&func.args[0], ctx)?;
        Self::value_to_bool(&val)
    }

    // =========================================================================
    // Value conversion helpers (shared between eval_* and evaluate_function_on_values)
    // =========================================================================

    /// Convert a Value to string.
    pub(crate) fn value_to_str(val: &Value) -> Result<Value, QueryError> {
        match val {
            Value::String(s) => Ok(Value::String(s.clone())),
            Value::Integer(i) => Ok(Value::String(i.to_string())),
            Value::Number(n) => Ok(Value::String(n.to_string())),
            Value::Boolean(b) => Ok(Value::String(if *b { "TRUE" } else { "FALSE" }.to_string())),
            Value::Date(d) => Ok(Value::String(d.to_string())),
            Value::Amount(a) => Ok(Value::String(format!("{} {}", a.number, a.currency))),
            Value::Null => Ok(Value::Null),
            _ => Err(QueryError::Type(
                "STR expects a string, integer, number, boolean, date, or amount".to_string(),
            )),
        }
    }

    /// Convert a Value to integer.
    pub(crate) fn value_to_int(val: &Value) -> Result<Value, QueryError> {
        use rust_decimal::prelude::ToPrimitive;
        match val {
            Value::Integer(i) => Ok(Value::Integer(*i)),
            Value::Number(n) => {
                let truncated = n.trunc();
                truncated.to_i64().map(Value::Integer).ok_or_else(|| {
                    QueryError::Type(format!("INT: cannot convert '{n}' to integer"))
                })
            }
            Value::Boolean(b) => Ok(Value::Integer(i64::from(*b))),
            Value::String(s) => s
                .parse::<i64>()
                .map(Value::Integer)
                .map_err(|_| QueryError::Type(format!("INT: cannot parse '{s}' as integer"))),
            Value::Null => Ok(Value::Null),
            _ => Err(QueryError::Type(
                "INT expects a number, integer, boolean, or string".to_string(),
            )),
        }
    }

    /// Convert a Value to decimal.
    pub(crate) fn value_to_decimal(val: &Value) -> Result<Value, QueryError> {
        match val {
            Value::Number(n) => Ok(Value::Number(*n)),
            Value::Integer(i) => Ok(Value::Number(Decimal::from(*i))),
            Value::Boolean(b) => Ok(Value::Number(if *b { Decimal::ONE } else { Decimal::ZERO })),
            Value::String(s) => s
                .parse::<Decimal>()
                .map(Value::Number)
                .map_err(|_| QueryError::Type(format!("DECIMAL: cannot parse '{s}' as decimal"))),
            Value::Null => Ok(Value::Null),
            _ => Err(QueryError::Type(
                "DECIMAL expects a number, integer, boolean, or string".to_string(),
            )),
        }
    }

    /// Convert a Value to boolean.
    pub(crate) fn value_to_bool(val: &Value) -> Result<Value, QueryError> {
        match val {
            Value::Boolean(b) => Ok(Value::Boolean(*b)),
            Value::Integer(i) => Ok(Value::Boolean(*i != 0)),
            Value::Number(n) => Ok(Value::Boolean(!n.is_zero())),
            Value::String(s) => {
                let s_upper = s.to_uppercase();
                match s_upper.as_str() {
                    "TRUE" | "YES" | "1" | "T" | "Y" => Ok(Value::Boolean(true)),
                    "FALSE" | "NO" | "0" | "F" | "N" | "" => Ok(Value::Boolean(false)),
                    _ => Err(QueryError::Type(format!(
                        "BOOL: cannot parse '{s}' as boolean"
                    ))),
                }
            }
            Value::Null => Ok(Value::Null),
            _ => Err(QueryError::Type(
                "BOOL expects a boolean, number, integer, or string".to_string(),
            )),
        }
    }

    /// Evaluate COALESCE function.
    pub(crate) fn eval_coalesce(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        for arg in &func.args {
            let val = self.evaluate_expr(arg, ctx)?;
            if !matches!(val, Value::Null) {
                return Ok(val);
            }
        }
        Ok(Value::Null)
    }

    /// Evaluate ONLY function.
    ///
    /// `ONLY(key, inventory)` - Extract amount with given currency from inventory.
    /// Returns the amount if exactly one position matches, NULL otherwise.
    pub(crate) fn eval_only(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        Self::require_args("ONLY", func, 2)?;

        // Get the currency key
        let key = match self.evaluate_expr(&func.args[0], ctx)? {
            Value::String(s) => s,
            _ => {
                return Err(QueryError::Type(
                    "ONLY: first argument must be a currency string".to_string(),
                ));
            }
        };

        // Get the inventory
        let inv = match self.evaluate_expr(&func.args[1], ctx)? {
            Value::Inventory(inv) => inv,
            Value::Position(pos) => {
                // If it's a single position, check if it matches
                if pos.units.currency == key {
                    return Ok(Value::Amount(pos.units));
                }
                return Ok(Value::Null);
            }
            Value::Amount(amt) => {
                // If it's a single amount, check if it matches
                if amt.currency == key {
                    return Ok(Value::Amount(amt));
                }
                return Ok(Value::Null);
            }
            Value::Null => return Ok(Value::Null),
            _ => {
                return Err(QueryError::Type(
                    "ONLY: second argument must be an inventory, position, or amount".to_string(),
                ));
            }
        };

        // Find positions matching the currency
        let matching: Vec<_> = inv
            .positions()
            .iter()
            .filter(|p| p.units.currency == key)
            .collect();

        match matching.len() {
            0 => Ok(Value::Null),
            1 => Ok(Value::Amount(matching[0].units.clone())),
            _ => Ok(Value::Null), // Multiple matches, return NULL
        }
    }
}
