//! Account function implementations for the BQL executor.

use crate::ast::FunctionCall;
use crate::error::QueryError;

use super::super::Executor;
use super::super::types::{PostingContext, Value};

impl Executor<'_> {
    /// Evaluate account functions: `PARENT`, `LEAF`, `ROOT`, `ACCOUNT_DEPTH`, `ACCOUNT_SORTKEY`.
    pub(crate) fn eval_account_function(
        &self,
        name: &str,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        match name {
            "PARENT" => {
                Self::require_args(name, func, 1)?;
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::String(s) => {
                        if let Some(idx) = s.rfind(':') {
                            Ok(Value::String(s[..idx].to_string()))
                        } else {
                            Ok(Value::Null)
                        }
                    }
                    _ => Err(QueryError::Type(
                        "PARENT expects an account string".to_string(),
                    )),
                }
            }
            "LEAF" => {
                Self::require_args(name, func, 1)?;
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::String(s) => {
                        if let Some(idx) = s.rfind(':') {
                            Ok(Value::String(s[idx + 1..].to_string()))
                        } else {
                            Ok(Value::String(s))
                        }
                    }
                    _ => Err(QueryError::Type(
                        "LEAF expects an account string".to_string(),
                    )),
                }
            }
            "ROOT" => self.eval_root(func, ctx),
            "ACCOUNT_DEPTH" => {
                Self::require_args(name, func, 1)?;
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::String(s) => {
                        let depth = s.chars().filter(|c| *c == ':').count() + 1;
                        Ok(Value::Integer(depth as i64))
                    }
                    _ => Err(QueryError::Type(
                        "ACCOUNT_DEPTH expects an account string".to_string(),
                    )),
                }
            }
            "ACCOUNT_SORTKEY" => {
                Self::require_args(name, func, 1)?;
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::String(s) => {
                        // Return "{type_index}-{account}" for sorting
                        // Type indices match Python beancount:
                        // Assets=0, Liabilities=1, Equity=2, Income=3, Expenses=4, Other=5
                        let type_index = Self::account_type_index(&s);
                        Ok(Value::String(format!("{type_index}-{s}")))
                    }
                    _ => Err(QueryError::Type(
                        "ACCOUNT_SORTKEY expects an account string".to_string(),
                    )),
                }
            }
            _ => unreachable!(),
        }
    }

    /// Evaluate account metadata functions: `OPEN_DATE`, `CLOSE_DATE`, `OPEN_META`.
    pub(crate) fn eval_account_meta_function(
        &self,
        name: &str,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        match name {
            "OPEN_DATE" => {
                Self::require_args(name, func, 1)?;
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::String(account) => {
                        if let Some(info) = self.account_info.get(&account) {
                            Ok(info.open_date.map_or(Value::Null, Value::Date))
                        } else {
                            Ok(Value::Null)
                        }
                    }
                    _ => Err(QueryError::Type(
                        "OPEN_DATE expects an account string".to_string(),
                    )),
                }
            }
            "CLOSE_DATE" => {
                Self::require_args(name, func, 1)?;
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::String(account) => {
                        if let Some(info) = self.account_info.get(&account) {
                            Ok(info.close_date.map_or(Value::Null, Value::Date))
                        } else {
                            Ok(Value::Null)
                        }
                    }
                    _ => Err(QueryError::Type(
                        "CLOSE_DATE expects an account string".to_string(),
                    )),
                }
            }
            "OPEN_META" => {
                Self::require_args(name, func, 2)?;
                let account_val = self.evaluate_expr(&func.args[0], ctx)?;
                let key_val = self.evaluate_expr(&func.args[1], ctx)?;

                let (account, key) = match (account_val, key_val) {
                    (Value::String(a), Value::String(k)) => (a, k),
                    _ => {
                        return Err(QueryError::Type(
                            "OPEN_META expects (account_string, key_string)".to_string(),
                        ));
                    }
                };

                if let Some(info) = self.account_info.get(&account) {
                    let meta_value = info.open_meta.get(&key);
                    Ok(Self::meta_value_to_value(meta_value))
                } else {
                    Ok(Value::Null)
                }
            }
            _ => unreachable!(),
        }
    }

    /// Evaluate ROOT function (takes 1-2 arguments).
    pub(crate) fn eval_root(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        if func.args.is_empty() || func.args.len() > 2 {
            return Err(QueryError::InvalidArguments(
                "ROOT".to_string(),
                "expected 1 or 2 arguments".to_string(),
            ));
        }

        let val = self.evaluate_expr(&func.args[0], ctx)?;
        let n = if func.args.len() == 2 {
            let raw = match self.evaluate_expr(&func.args[1], ctx)? {
                Value::Integer(i) => i,
                _ => {
                    return Err(QueryError::Type(
                        "ROOT second arg must be integer".to_string(),
                    ));
                }
            };
            // Reject negatives explicitly — without this guard, `i as usize`
            // would silently turn -1 into `usize::MAX` and the slice below
            // would always return the whole account string.
            usize::try_from(raw).map_err(|_| {
                QueryError::Type(format!(
                    "ROOT second arg must be a non-negative integer, got {raw}"
                ))
            })?
        } else {
            1
        };

        match val {
            Value::String(s) => {
                let parts: Vec<&str> = s.split(':').collect();
                if n >= parts.len() {
                    Ok(Value::String(s))
                } else {
                    Ok(Value::String(parts[..n].join(":")))
                }
            }
            _ => Err(QueryError::Type(
                "ROOT expects an account string".to_string(),
            )),
        }
    }

    /// Get the account type index for sorting.
    ///
    /// Returns the type index matching Python beancount:
    /// - Assets = 0
    /// - Liabilities = 1
    /// - Equity = 2
    /// - Income = 3
    /// - Expenses = 4
    /// - Other = 5 (for custom account types)
    pub(crate) fn account_type_index(account: &str) -> u8 {
        // Extract the first component (root account type)
        let root = account.split(':').next().unwrap_or(account);
        match root {
            "Assets" => 0,
            "Liabilities" => 1,
            "Equity" => 2,
            "Income" => 3,
            "Expenses" => 4,
            _ => 5, // Custom account types sort last
        }
    }
}
