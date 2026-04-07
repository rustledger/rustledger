//! String function implementations for the BQL executor.

use regex::Regex;

use crate::ast::FunctionCall;
use crate::error::QueryError;

use super::super::Executor;
use super::super::types::{PostingContext, Value};

impl Executor<'_> {
    /// Evaluate string functions: `LENGTH`, `UPPER`, `LOWER`, `SUBSTR`, `TRIM`, `STARTSWITH`, `ENDSWITH`.
    pub(crate) fn eval_string_function(
        &self,
        name: &str,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        match name {
            "LENGTH" => {
                Self::require_args(name, func, 1)?;
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::String(s) => Ok(Value::Integer(s.len() as i64)),
                    Value::StringSet(s) => Ok(Value::Integer(s.len() as i64)),
                    _ => Err(QueryError::Type(
                        "LENGTH expects a string or set".to_string(),
                    )),
                }
            }
            "UPPER" => {
                Self::require_args(name, func, 1)?;
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::String(s) => Ok(Value::String(s.to_uppercase())),
                    _ => Err(QueryError::Type("UPPER expects a string".to_string())),
                }
            }
            "LOWER" => {
                Self::require_args(name, func, 1)?;
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::String(s) => Ok(Value::String(s.to_lowercase())),
                    _ => Err(QueryError::Type("LOWER expects a string".to_string())),
                }
            }
            "TRIM" => {
                Self::require_args(name, func, 1)?;
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::String(s) => Ok(Value::String(s.trim().to_string())),
                    _ => Err(QueryError::Type("TRIM expects a string".to_string())),
                }
            }
            "SUBSTR" | "SUBSTRING" => self.eval_substr(func, ctx),
            "STARTSWITH" => {
                Self::require_args(name, func, 2)?;
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                let prefix = self.evaluate_expr(&func.args[1], ctx)?;
                match (val, prefix) {
                    (Value::String(s), Value::String(p)) => Ok(Value::Boolean(s.starts_with(&p))),
                    _ => Err(QueryError::Type(
                        "STARTSWITH expects two strings".to_string(),
                    )),
                }
            }
            "ENDSWITH" => {
                Self::require_args(name, func, 2)?;
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                let suffix = self.evaluate_expr(&func.args[1], ctx)?;
                match (val, suffix) {
                    (Value::String(s), Value::String(p)) => Ok(Value::Boolean(s.ends_with(&p))),
                    _ => Err(QueryError::Type("ENDSWITH expects two strings".to_string())),
                }
            }
            "GREP" => self.eval_grep(func, ctx),
            "GREPN" => self.eval_grepn(func, ctx),
            "SUBST" => self.eval_subst(func, ctx),
            "SPLITCOMP" => self.eval_splitcomp(func, ctx),
            "JOINSTR" => self.eval_joinstr(func, ctx),
            "MAXWIDTH" => self.eval_maxwidth(func, ctx),
            _ => unreachable!(),
        }
    }

    /// Evaluate GREP function (regex match).
    ///
    /// `GREP(pattern, string)` - Return matched portion or null
    pub(crate) fn eval_grep(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        Self::require_args("GREP", func, 2)?;

        let pattern = match self.evaluate_expr(&func.args[0], ctx)? {
            Value::String(s) => s,
            _ => {
                return Err(QueryError::Type(
                    "GREP: first argument must be a pattern string".to_string(),
                ));
            }
        };
        let string = match self.evaluate_expr(&func.args[1], ctx)? {
            Value::String(s) => s,
            _ => {
                return Err(QueryError::Type(
                    "GREP: second argument must be a string".to_string(),
                ));
            }
        };

        let re = Regex::new(&pattern)
            .map_err(|e| QueryError::Type(format!("GREP: invalid regex '{pattern}': {e}")))?;

        match re.find(&string) {
            Some(m) => Ok(Value::String(m.as_str().to_string())),
            None => Ok(Value::Null),
        }
    }

    /// Evaluate GREPN function (regex capture group).
    ///
    /// `GREPN(pattern, string, n)` - Return nth capture group
    pub(crate) fn eval_grepn(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        Self::require_args("GREPN", func, 3)?;

        let pattern = match self.evaluate_expr(&func.args[0], ctx)? {
            Value::String(s) => s,
            _ => {
                return Err(QueryError::Type(
                    "GREPN: first argument must be a pattern string".to_string(),
                ));
            }
        };
        let string = match self.evaluate_expr(&func.args[1], ctx)? {
            Value::String(s) => s,
            _ => {
                return Err(QueryError::Type(
                    "GREPN: second argument must be a string".to_string(),
                ));
            }
        };
        let n = match self.evaluate_expr(&func.args[2], ctx)? {
            Value::Integer(i) => i as usize,
            Value::Number(n) => {
                use rust_decimal::prelude::ToPrimitive;
                n.to_usize().ok_or_else(|| {
                    QueryError::Type("GREPN: third argument must be a non-negative integer".into())
                })?
            }
            _ => {
                return Err(QueryError::Type(
                    "GREPN: third argument must be an integer".to_string(),
                ));
            }
        };

        let re = Regex::new(&pattern)
            .map_err(|e| QueryError::Type(format!("GREPN: invalid regex '{pattern}': {e}")))?;

        match re.captures(&string) {
            Some(caps) => match caps.get(n) {
                Some(m) => Ok(Value::String(m.as_str().to_string())),
                None => Ok(Value::Null),
            },
            None => Ok(Value::Null),
        }
    }

    /// Evaluate SUBST function (regex substitution).
    ///
    /// `SUBST(pattern, replacement, string)` - Replace matches with replacement
    pub(crate) fn eval_subst(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        Self::require_args("SUBST", func, 3)?;

        let pattern = match self.evaluate_expr(&func.args[0], ctx)? {
            Value::String(s) => s,
            _ => {
                return Err(QueryError::Type(
                    "SUBST: first argument must be a pattern string".to_string(),
                ));
            }
        };
        let replacement = match self.evaluate_expr(&func.args[1], ctx)? {
            Value::String(s) => s,
            _ => {
                return Err(QueryError::Type(
                    "SUBST: second argument must be a replacement string".to_string(),
                ));
            }
        };
        let string = match self.evaluate_expr(&func.args[2], ctx)? {
            Value::String(s) => s,
            _ => {
                return Err(QueryError::Type(
                    "SUBST: third argument must be a string".to_string(),
                ));
            }
        };

        let re = Regex::new(&pattern)
            .map_err(|e| QueryError::Type(format!("SUBST: invalid regex '{pattern}': {e}")))?;

        Ok(Value::String(
            re.replace_all(&string, &replacement).to_string(),
        ))
    }

    /// Evaluate SPLITCOMP function (split and get component).
    ///
    /// `SPLITCOMP(string, delimiter, n)` - Split and return nth component (0-based)
    pub(crate) fn eval_splitcomp(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        Self::require_args("SPLITCOMP", func, 3)?;

        let string = match self.evaluate_expr(&func.args[0], ctx)? {
            Value::String(s) => s,
            _ => {
                return Err(QueryError::Type(
                    "SPLITCOMP: first argument must be a string".to_string(),
                ));
            }
        };
        let delimiter = match self.evaluate_expr(&func.args[1], ctx)? {
            Value::String(s) => s,
            _ => {
                return Err(QueryError::Type(
                    "SPLITCOMP: second argument must be a delimiter string".to_string(),
                ));
            }
        };
        let n = match self.evaluate_expr(&func.args[2], ctx)? {
            Value::Integer(i) => i as usize,
            Value::Number(n) => {
                use rust_decimal::prelude::ToPrimitive;
                n.to_usize().ok_or_else(|| {
                    QueryError::Type(
                        "SPLITCOMP: third argument must be a non-negative integer".into(),
                    )
                })?
            }
            _ => {
                return Err(QueryError::Type(
                    "SPLITCOMP: third argument must be an integer".to_string(),
                ));
            }
        };

        let parts: Vec<&str> = string.split(&delimiter).collect();
        match parts.get(n) {
            Some(part) => Ok(Value::String((*part).to_string())),
            None => Ok(Value::Null),
        }
    }

    /// Evaluate JOINSTR function (join values with separator).
    ///
    /// `JOINSTR(value, ...)` - Join multiple values with comma separator
    pub(crate) fn eval_joinstr(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        if func.args.is_empty() {
            return Err(QueryError::InvalidArguments(
                "JOINSTR".to_string(),
                "expected at least 1 argument".to_string(),
            ));
        }

        let mut parts = Vec::new();
        for arg in &func.args {
            let val = self.evaluate_expr(arg, ctx)?;
            match val {
                Value::String(s) => parts.push(s),
                Value::StringSet(ss) => parts.extend(ss),
                Value::Null => {} // Skip nulls
                other => parts.push(Self::value_to_string(&other)),
            }
        }

        Ok(Value::String(parts.join(", ")))
    }

    /// Evaluate MAXWIDTH function (truncate with ellipsis).
    ///
    /// `MAXWIDTH(string, n)` - Truncate string to n characters with ellipsis
    pub(crate) fn eval_maxwidth(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        Self::require_args("MAXWIDTH", func, 2)?;

        let string = match self.evaluate_expr(&func.args[0], ctx)? {
            Value::String(s) => s,
            _ => {
                return Err(QueryError::Type(
                    "MAXWIDTH: first argument must be a string".to_string(),
                ));
            }
        };
        let n = match self.evaluate_expr(&func.args[1], ctx)? {
            Value::Integer(i) => i as usize,
            Value::Number(n) => {
                use rust_decimal::prelude::ToPrimitive;
                n.to_usize().ok_or_else(|| {
                    QueryError::Type("MAXWIDTH: second argument must be a positive integer".into())
                })?
            }
            _ => {
                return Err(QueryError::Type(
                    "MAXWIDTH: second argument must be an integer".to_string(),
                ));
            }
        };

        if string.chars().count() <= n {
            Ok(Value::String(string))
        } else if n <= 3 {
            Ok(Value::String(string.chars().take(n).collect()))
        } else {
            let truncated: String = string.chars().take(n - 3).collect();
            Ok(Value::String(format!("{truncated}...")))
        }
    }

    /// Evaluate SUBSTR/SUBSTRING function.
    pub(crate) fn eval_substr(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        if func.args.len() < 2 || func.args.len() > 3 {
            return Err(QueryError::InvalidArguments(
                "SUBSTR".to_string(),
                "expected 2 or 3 arguments".to_string(),
            ));
        }

        let val = self.evaluate_expr(&func.args[0], ctx)?;
        let start = self.evaluate_expr(&func.args[1], ctx)?;
        let len = if func.args.len() == 3 {
            Some(self.evaluate_expr(&func.args[2], ctx)?)
        } else {
            None
        };

        match (val, start, len) {
            (Value::String(s), Value::Integer(start), None) => {
                let start = start.max(0) as usize;
                let result: String = s.chars().skip(start).collect();
                Ok(Value::String(result))
            }
            (Value::String(s), Value::Integer(start), Some(Value::Integer(len))) => {
                let start = start.max(0) as usize;
                let len = len.max(0) as usize;
                let result: String = s.chars().skip(start).take(len).collect();
                Ok(Value::String(result))
            }
            _ => Err(QueryError::Type(
                "SUBSTR expects (string, int, [int])".to_string(),
            )),
        }
    }
}
