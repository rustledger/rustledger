//! Position and inventory function implementations for the BQL executor.

use rust_decimal::Decimal;
use rustledger_core::{Amount, InternedStr, Inventory, Position};

use crate::ast::FunctionCall;
use crate::error::QueryError;

use super::super::Executor;
use super::super::types::{PostingContext, Value};

impl Executor<'_> {
    /// Evaluate position/amount functions: `NUMBER`, `CURRENCY`, `GETITEM`, `UNITS`, `COST`, `WEIGHT`, `VALUE`.
    pub(crate) fn eval_position_function(
        &self,
        name: &str,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        match name {
            "NUMBER" => {
                Self::require_args(name, func, 1)?;
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::Amount(a) => Ok(Value::Number(a.number)),
                    Value::Position(p) => Ok(Value::Number(p.units.number)),
                    Value::Number(n) => Ok(Value::Number(n)),
                    Value::Integer(i) => Ok(Value::Number(Decimal::from(i))),
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "NUMBER expects an amount or position".to_string(),
                    )),
                }
            }
            "CURRENCY" => {
                Self::require_args(name, func, 1)?;
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::Amount(a) => Ok(Value::String(a.currency.to_string())),
                    Value::Position(p) => Ok(Value::String(p.units.currency.to_string())),
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "CURRENCY expects an amount or position".to_string(),
                    )),
                }
            }
            "GETITEM" | "GET" => self.eval_getitem(func, ctx),
            "UNITS" => self.eval_units(func, ctx),
            "COST" => self.eval_cost(func, ctx),
            "WEIGHT" => self.eval_weight(func, ctx),
            "VALUE" => self.eval_value(func, ctx),
            _ => unreachable!(),
        }
    }

    /// Evaluate inventory functions: `EMPTY`, `FILTER_CURRENCY`, `POSSIGN`.
    pub(crate) fn eval_inventory_function(
        &self,
        name: &str,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        match name {
            "EMPTY" => {
                Self::require_args(name, func, 1)?;
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::Inventory(inv) => Ok(Value::Boolean(inv.is_empty())),
                    Value::Null => Ok(Value::Boolean(true)),
                    _ => Err(QueryError::Type("EMPTY expects an inventory".to_string())),
                }
            }
            "FILTER_CURRENCY" => {
                Self::require_args(name, func, 2)?;
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                let currency = self.evaluate_expr(&func.args[1], ctx)?;

                match (val, currency) {
                    (Value::Inventory(inv), Value::String(curr)) => {
                        let filtered: Vec<Position> = inv
                            .positions()
                            .iter()
                            .filter(|p| p.units.currency.as_str() == curr)
                            .cloned()
                            .collect();
                        let mut new_inv = Inventory::new();
                        for pos in filtered {
                            new_inv.add(pos);
                        }
                        Ok(Value::Inventory(Box::new(new_inv)))
                    }
                    (Value::Null, _) => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "FILTER_CURRENCY expects (inventory, string)".to_string(),
                    )),
                }
            }
            "POSSIGN" => {
                Self::require_args(name, func, 2)?;
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                let account = self.evaluate_expr(&func.args[1], ctx)?;

                let account_str = match account {
                    Value::String(s) => s,
                    _ => {
                        return Err(QueryError::Type(
                            "POSSIGN expects (amount, account_string)".to_string(),
                        ));
                    }
                };

                // Determine if account is credit-normal (Liabilities, Equity, Income)
                // These need their signs inverted; Assets/Expenses are debit-normal
                let first_component = account_str.split(':').next().unwrap_or("");
                let is_credit_normal =
                    matches!(first_component, "Liabilities" | "Equity" | "Income");

                match val {
                    Value::Amount(mut a) => {
                        if is_credit_normal {
                            a.number = -a.number;
                        }
                        Ok(Value::Amount(a))
                    }
                    Value::Number(n) => {
                        let adjusted = if is_credit_normal { -n } else { n };
                        Ok(Value::Number(adjusted))
                    }
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "POSSIGN expects (amount, account_string)".to_string(),
                    )),
                }
            }
            _ => unreachable!(),
        }
    }

    /// Evaluate GETITEM/GET function.
    pub(crate) fn eval_getitem(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        Self::require_args("GETITEM", func, 2)?;
        let val = self.evaluate_expr(&func.args[0], ctx)?;
        let key = self.evaluate_expr(&func.args[1], ctx)?;

        match (val, key) {
            (Value::Inventory(inv), Value::String(currency)) => {
                let total = inv.units(&currency);
                if total.is_zero() {
                    Ok(Value::Null)
                } else {
                    Ok(Value::Amount(Amount::new(total, currency)))
                }
            }
            _ => Err(QueryError::Type(
                "GETITEM expects (inventory, string)".to_string(),
            )),
        }
    }

    /// Evaluate UNITS function.
    pub(crate) fn eval_units(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        Self::require_args("UNITS", func, 1)?;
        let val = self.evaluate_expr(&func.args[0], ctx)?;

        match val {
            Value::Position(p) => Ok(Value::Amount(p.units)),
            Value::Amount(a) => Ok(Value::Amount(a)),
            Value::Inventory(inv) => {
                let positions: Vec<String> = inv
                    .positions()
                    .iter()
                    .map(|p| format!("{} {}", p.units.number, p.units.currency))
                    .collect();
                Ok(Value::String(positions.join(", ")))
            }
            _ => Err(QueryError::Type(
                "UNITS expects a position or inventory".to_string(),
            )),
        }
    }

    /// Evaluate COST function.
    pub(crate) fn eval_cost(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        Self::require_args("COST", func, 1)?;
        let val = self.evaluate_expr(&func.args[0], ctx)?;

        match val {
            Value::Position(p) => {
                if let Some(cost) = &p.cost {
                    let total = p.units.number * cost.number;
                    Ok(Value::Amount(Amount::new(total, cost.currency.clone())))
                } else {
                    Ok(Value::Amount(p.units))
                }
            }
            Value::Amount(a) => Ok(Value::Amount(a)),
            Value::Inventory(inv) => {
                let mut total = Decimal::ZERO;
                let mut currency: Option<InternedStr> = None;
                for pos in inv.positions() {
                    if let Some(cost) = &pos.cost {
                        total += pos.units.number * cost.number;
                        if currency.is_none() {
                            currency = Some(cost.currency.clone());
                        }
                    } else {
                        total += pos.units.number;
                        if currency.is_none() {
                            currency = Some(pos.units.currency.clone());
                        }
                    }
                }
                if let Some(curr) = currency {
                    Ok(Value::Amount(Amount::new(total, curr)))
                } else {
                    Ok(Value::Null)
                }
            }
            _ => Err(QueryError::Type(
                "COST expects a position or inventory".to_string(),
            )),
        }
    }

    /// Evaluate WEIGHT function.
    pub(crate) fn eval_weight(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        Self::require_args("WEIGHT", func, 1)?;
        let val = self.evaluate_expr(&func.args[0], ctx)?;

        match val {
            Value::Position(p) => {
                if let Some(cost) = &p.cost {
                    let total = p.units.number * cost.number;
                    Ok(Value::Amount(Amount::new(total, cost.currency.clone())))
                } else {
                    Ok(Value::Amount(p.units))
                }
            }
            Value::Amount(a) => Ok(Value::Amount(a)),
            _ => Err(QueryError::Type(
                "WEIGHT expects a position or amount".to_string(),
            )),
        }
    }

    /// Evaluate VALUE function (market value conversion).
    ///
    /// Converts positions/amounts/inventories to their market value using the latest
    /// available price. This matches Python beancount's behavior where `value(position)`
    /// uses the most recent price, not the transaction date.
    ///
    /// If no target currency is specified, it is inferred from the position's cost
    /// currency (for positions with cost basis) or falls back to the executor's
    /// target currency setting.
    pub(crate) fn eval_value(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        if func.args.is_empty() || func.args.len() > 2 {
            return Err(QueryError::InvalidArguments(
                "VALUE".to_string(),
                "expected 1-2 arguments".to_string(),
            ));
        }

        // Evaluate the first argument (position/amount/inventory)
        let val = self.evaluate_expr(&func.args[0], ctx)?;

        // Get explicit target currency if provided
        let explicit_currency = if func.args.len() == 2 {
            match self.evaluate_expr(&func.args[1], ctx)? {
                Value::String(s) => Some(s),
                _ => {
                    return Err(QueryError::Type(
                        "VALUE second argument must be a currency string".to_string(),
                    ));
                }
            }
        } else {
            None
        };

        // Use shared implementation for consistent behavior
        self.convert_to_market_value(&val, explicit_currency.as_deref())
    }

    /// Evaluate GETPRICE function.
    ///
    /// `GETPRICE(base_currency, quote_currency)` - Get price using context date
    /// `GETPRICE(base_currency, quote_currency, date)` - Get price at specific date
    pub(crate) fn eval_getprice(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        if func.args.len() < 2 || func.args.len() > 3 {
            return Err(QueryError::InvalidArguments(
                "GETPRICE".to_string(),
                "expected 2 or 3 arguments: (base_currency, quote_currency[, date])".to_string(),
            ));
        }

        // Get base currency - handle NULL gracefully
        let base = match self.evaluate_expr(&func.args[0], ctx)? {
            Value::String(s) => s,
            Value::Null => return Ok(Value::Null),
            _ => {
                return Err(QueryError::Type(
                    "GETPRICE: first argument must be a currency string".to_string(),
                ));
            }
        };

        // Get quote currency - handle NULL gracefully
        let quote = match self.evaluate_expr(&func.args[1], ctx)? {
            Value::String(s) => s,
            Value::Null => return Ok(Value::Null),
            _ => {
                return Err(QueryError::Type(
                    "GETPRICE: second argument must be a currency string".to_string(),
                ));
            }
        };

        // Get date (optional, defaults to context date)
        let date = if func.args.len() == 3 {
            match self.evaluate_expr(&func.args[2], ctx)? {
                Value::Date(d) => d,
                _ => {
                    return Err(QueryError::Type(
                        "GETPRICE: third argument must be a date".to_string(),
                    ));
                }
            }
        } else {
            ctx.transaction.date
        };

        // Look up the price
        match self.price_db.get_price(&base, &quote, date) {
            Some(price) => Ok(Value::Number(price)),
            None => Ok(Value::Null),
        }
    }
}
