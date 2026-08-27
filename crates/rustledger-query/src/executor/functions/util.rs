//! Utility function implementations for the BQL executor.
//!
//! This module includes metadata, conversion, casting, and helper functions.

use rust_decimal::Decimal;
use rustledger_core::{MetaValue, Metadata};

use crate::ast::FunctionCall;
use crate::error::QueryError;

use super::super::Executor;
use super::super::types::{PostingContext, SourceLocation, Value};

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

        // beanquery exposes `filename`/`lineno` as members of a posting's /
        // entry's metadata. Resolve them per scope: posting metadata carries
        // the POSTING's location, entry metadata the enclosing directive's.
        let posting_loc = self.resolved_source_location(ctx);
        let entry_loc = ctx
            .directive_index
            .and_then(|i| self.get_source_location(i).cloned());

        let meta_value = match name {
            "META" | "POSTING_META" => Self::meta_lookup(&posting.meta, posting_loc.as_ref(), &key),
            "ENTRY_META" => Self::meta_lookup(&ctx.transaction.meta, entry_loc.as_ref(), &key),
            "ANY_META" => Self::meta_lookup(&posting.meta, posting_loc.as_ref(), &key)
                .or_else(|| Self::meta_lookup(&ctx.transaction.meta, entry_loc.as_ref(), &key)),
            _ => unreachable!(),
        };

        Ok(Self::meta_value_to_value(meta_value.as_ref()))
    }

    /// beanquery's parser injects `filename` and `lineno` into every posting's
    /// and entry's metadata dict. rledger keeps source location in spans, not in
    /// the meta map, so synthesize those two keys at the BQL boundary from the
    /// resolved location. A user-defined key of the same name wins (callers
    /// consult the raw map first).
    fn source_location_meta_key(loc: Option<&SourceLocation>, key: &str) -> Option<MetaValue> {
        let loc = loc?;
        match key {
            "filename" => Some(MetaValue::String(loc.filename.clone())),
            // beanquery's lineno is an integer; emit a true `Int` (the `lineno`
            // column is also `Integer`). Falls back to `Number` only on the
            // practically-impossible case of a line number exceeding i64.
            "lineno" => Some(i64::try_from(loc.lineno).map_or_else(
                |_| MetaValue::Number(Decimal::from(loc.lineno as u64)),
                MetaValue::Int,
            )),
            _ => None,
        }
    }

    /// The synthetic `filename` source-location column value.
    pub(crate) fn source_filename_value(loc: Option<&SourceLocation>) -> Value {
        loc.map_or(Value::Null, |l| Value::String(l.filename.clone()))
    }

    /// The line number as an `i64`, saturating to `i64::MAX` only on the
    /// practically-impossible case of a line number exceeding `i64` — the single,
    /// overflow-checked replacement for the unchecked `loc.lineno as i64` casts
    /// (bug #4). Shared by the `lineno` and `location` columns so they can never
    /// disagree on the same posting.
    fn lineno_i64(loc: &SourceLocation) -> i64 {
        i64::try_from(loc.lineno).unwrap_or(i64::MAX)
    }

    /// The synthetic `lineno` source-location column value, as an `Integer`.
    /// Reads the `SourceLocation`, never the directive's metadata.
    ///
    /// bean-query stores the location in the same dict users write to, so a
    /// directive carrying `lineno: 999` makes its `lineno` COLUMN report 999
    /// instead of the real line. We do not match that: a column named
    /// `lineno` should say where the directive is, not what someone typed.
    /// Immune by construction rather than by a guard (#2168).
    ///
    /// The `meta` map itself does let the user's value win, which DOES match
    /// bean-query -- `augmented_meta` only fills keys that are absent.
    pub(crate) fn source_lineno_value(loc: Option<&SourceLocation>) -> Value {
        loc.map_or(Value::Null, |l| Value::Integer(Self::lineno_i64(l)))
    }

    /// The synthetic `location` source-location column value (`filename:lineno`),
    /// using the same saturated line number as [`Self::source_lineno_value`].
    pub(crate) fn source_location_value(loc: Option<&SourceLocation>) -> Value {
        loc.map_or(Value::Null, |l| {
            Value::String(format!("{}:{}", l.filename, Self::lineno_i64(l)))
        })
    }

    /// Look up a single metadata key, falling back to the synthetic
    /// source-location keys (`filename`/`lineno`) when absent from `raw`.
    fn meta_lookup(raw: &Metadata, loc: Option<&SourceLocation>, key: &str) -> Option<MetaValue> {
        raw.get(key)
            .cloned()
            .or_else(|| Self::source_location_meta_key(loc, key))
    }

    /// Return `raw` extended with beanquery's synthetic `filename`/`lineno`
    /// metadata keys resolved from `loc` (existing user keys win). Used to
    /// materialize the full `meta` column value.
    pub(crate) fn augmented_meta(raw: &Metadata, loc: Option<&SourceLocation>) -> Metadata {
        if loc.is_none() {
            return raw.clone();
        }
        let mut meta = raw.clone();
        for key in ["filename", "lineno"] {
            if !meta.contains_key(key)
                && let Some(value) = Self::source_location_meta_key(loc, key)
            {
                meta.insert(key.to_string(), value);
            }
        }
        meta
    }

    /// Convert a `MetaValue` to a `Value`.
    pub(crate) fn meta_value_to_value(mv: Option<&MetaValue>) -> Value {
        match mv {
            None => Value::Null,
            Some(MetaValue::String(s)) => Value::String(s.clone()),
            Some(MetaValue::Number(n)) => Value::Number(*n),
            Some(MetaValue::Int(i)) => Value::Integer(*i),
            Some(MetaValue::Date(d)) => Value::Date(*d),
            Some(MetaValue::Bool(b)) => Value::Boolean(*b),
            Some(MetaValue::Amount(a)) => Value::Amount(a.clone()),
            // Lower typed meta values to BQL String at the query boundary
            // (matches bean-query semantics — no first-class Account/Currency
            // type in the SQL surface).
            Some(MetaValue::Account(a)) => Value::String(a.to_string()),
            Some(MetaValue::Currency(c)) => Value::String(c.to_string()),
            Some(MetaValue::Tag(t)) => Value::String(t.to_string()),
            Some(MetaValue::Link(l)) => Value::String(l.to_string()),
            Some(MetaValue::None) => Value::Null,
        }
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
}

#[cfg(test)]
mod tests {
    use super::super::super::Executor;
    use super::super::super::types::{SourceLocation, Value};

    fn loc(lineno: usize) -> SourceLocation {
        SourceLocation {
            filename: "f.bean".to_string(),
            lineno,
        }
    }

    #[test]
    fn source_lineno_value_basics() {
        assert_eq!(
            Executor::source_lineno_value(Some(&loc(42))),
            Value::Integer(42)
        );
        assert_eq!(Executor::source_lineno_value(None), Value::Null);
    }

    // bug #4: a line number exceeding `i64` must saturate to `i64::MAX`, not wrap
    // negative as the old unchecked `loc.lineno as i64` cast did. Only reachable
    // where `usize` is wider than `i64`.
    #[cfg(target_pointer_width = "64")]
    #[test]
    fn source_lineno_value_saturates_on_overflow() {
        assert_eq!(
            Executor::source_lineno_value(Some(&loc(usize::MAX))),
            Value::Integer(i64::MAX)
        );
        // `location` must use the same saturated value so the two columns agree.
        assert_eq!(
            Executor::source_location_value(Some(&loc(usize::MAX))),
            Value::String(format!("f.bean:{}", i64::MAX))
        );
    }

    #[test]
    fn source_filename_and_location_values() {
        assert_eq!(
            Executor::source_filename_value(Some(&loc(7))),
            Value::String("f.bean".to_string())
        );
        assert_eq!(
            Executor::source_location_value(Some(&loc(7))),
            Value::String("f.bean:7".to_string())
        );
        assert_eq!(Executor::source_filename_value(None), Value::Null);
        assert_eq!(Executor::source_location_value(None), Value::Null);
    }
}
