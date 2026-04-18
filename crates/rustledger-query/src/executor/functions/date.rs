//! Date function implementations for the BQL executor.

use rustledger_core::NaiveDate;

use crate::ast::FunctionCall;
use crate::error::QueryError;

use super::super::Executor;
use super::super::types::{Interval, IntervalUnit, PostingContext, Value};

impl Executor<'_> {
    /// Evaluate date functions: `YEAR`, `MONTH`, `DAY`, `WEEKDAY`, `QUARTER`, `YMONTH`, `TODAY`.
    pub(crate) fn eval_date_function(
        &self,
        name: &str,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        if name == "TODAY" {
            if !func.args.is_empty() {
                return Err(QueryError::InvalidArguments(
                    "TODAY".to_string(),
                    "expected 0 arguments".to_string(),
                ));
            }
            return Ok(Value::Date(rustledger_core::NaiveDate::today()));
        }

        // All other date functions expect exactly 1 argument
        if func.args.len() != 1 {
            return Err(QueryError::InvalidArguments(
                name.to_string(),
                "expected 1 argument".to_string(),
            ));
        }

        let val = self.evaluate_expr(&func.args[0], ctx)?;
        let date = match val {
            Value::Date(d) => d,
            _ => return Err(QueryError::Type(format!("{name} expects a date"))),
        };

        match name {
            "YEAR" => Ok(Value::Integer(date.year().into())),
            "MONTH" => Ok(Value::Integer(date.month().into())),
            "DAY" => Ok(Value::Integer(date.day().into())),
            "WEEKDAY" => Ok(Value::Integer(date.weekday().num_days_from_monday().into())),
            "QUARTER" => {
                let quarter = (date.month() - 1) / 3 + 1;
                Ok(Value::Integer(quarter.into()))
            }
            "YMONTH" => Ok(Value::String(format!(
                "{:04}-{:02}",
                date.year(),
                date.month()
            ))),
            _ => unreachable!(),
        }
    }

    /// Evaluate extended date functions.
    pub(crate) fn eval_extended_date_function(
        &self,
        name: &str,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        match name {
            "DATE" => self.eval_date_construct(func, ctx),
            "DATE_DIFF" => self.eval_date_diff(func, ctx),
            "DATE_ADD" => self.eval_date_add(func, ctx),
            "DATE_TRUNC" => self.eval_date_trunc(func, ctx),
            "DATE_PART" => self.eval_date_part(func, ctx),
            "PARSE_DATE" => self.eval_parse_date(func, ctx),
            "DATE_BIN" => self.eval_date_bin(func, ctx),
            "INTERVAL" => self.eval_interval(func, ctx),
            _ => unreachable!(),
        }
    }

    /// Evaluate INTERVAL function (construct an interval).
    pub(crate) fn eval_interval(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        // interval(unit) - creates an interval of 1 unit
        // interval(count, unit) - creates an interval of count units
        match func.args.len() {
            1 => {
                let unit_str = match self.evaluate_expr(&func.args[0], ctx)? {
                    Value::String(s) => s,
                    _ => {
                        return Err(QueryError::Type(
                            "interval() unit must be a string".to_string(),
                        ));
                    }
                };
                let unit = IntervalUnit::parse_unit(&unit_str).ok_or_else(|| {
                    QueryError::InvalidArguments(
                        "INTERVAL".to_string(),
                        format!("invalid interval unit: {unit_str}"),
                    )
                })?;
                Ok(Value::Interval(Interval::new(1, unit)))
            }
            2 => {
                let count = match self.evaluate_expr(&func.args[0], ctx)? {
                    Value::Integer(n) => n,
                    Value::Number(d) => {
                        use rust_decimal::prelude::ToPrimitive;
                        // Reject decimals with fractional parts
                        if !d.fract().is_zero() {
                            return Err(QueryError::Type(
                                "interval() count must be an integer".to_string(),
                            ));
                        }
                        d.to_i64().ok_or_else(|| {
                            QueryError::Type("interval() count must be an integer".to_string())
                        })?
                    }
                    _ => {
                        return Err(QueryError::Type(
                            "interval() count must be a number".to_string(),
                        ));
                    }
                };
                let unit_str = match self.evaluate_expr(&func.args[1], ctx)? {
                    Value::String(s) => s,
                    _ => {
                        return Err(QueryError::Type(
                            "interval() unit must be a string".to_string(),
                        ));
                    }
                };
                let unit = IntervalUnit::parse_unit(&unit_str).ok_or_else(|| {
                    QueryError::InvalidArguments(
                        "INTERVAL".to_string(),
                        format!("invalid interval unit: {unit_str}"),
                    )
                })?;
                Ok(Value::Interval(Interval::new(count, unit)))
            }
            _ => Err(QueryError::InvalidArguments(
                "INTERVAL".to_string(),
                "expected 1 or 2 arguments".to_string(),
            )),
        }
    }

    /// Evaluate DATE function (construct a date).
    ///
    /// `DATE(year, month, day)` - construct from components
    /// `DATE(string)` - parse ISO date string
    pub(crate) fn eval_date_construct(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        match func.args.len() {
            1 => {
                // DATE(string) - parse ISO date
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::String(s) => NaiveDate::parse_from_str(&s, "%Y-%m-%d")
                        .map(Value::Date)
                        .map_err(|_| QueryError::Type(format!("DATE: cannot parse '{s}' as date"))),
                    Value::Date(d) => Ok(Value::Date(d)),
                    _ => Err(QueryError::Type(
                        "DATE: argument must be a string or date".to_string(),
                    )),
                }
            }
            3 => {
                // DATE(year, month, day)
                let year = match self.evaluate_expr(&func.args[0], ctx)? {
                    Value::Integer(i) => i as i32,
                    Value::Number(n) => {
                        use rust_decimal::prelude::ToPrimitive;
                        n.to_i32().ok_or_else(|| {
                            QueryError::Type("DATE: year must be an integer".to_string())
                        })?
                    }
                    _ => {
                        return Err(QueryError::Type(
                            "DATE: year must be an integer".to_string(),
                        ));
                    }
                };
                let month = match self.evaluate_expr(&func.args[1], ctx)? {
                    Value::Integer(i) => i as u32,
                    Value::Number(n) => {
                        use rust_decimal::prelude::ToPrimitive;
                        n.to_u32().ok_or_else(|| {
                            QueryError::Type("DATE: month must be an integer".to_string())
                        })?
                    }
                    _ => {
                        return Err(QueryError::Type(
                            "DATE: month must be an integer".to_string(),
                        ));
                    }
                };
                let day = match self.evaluate_expr(&func.args[2], ctx)? {
                    Value::Integer(i) => i as u32,
                    Value::Number(n) => {
                        use rust_decimal::prelude::ToPrimitive;
                        n.to_u32().ok_or_else(|| {
                            QueryError::Type("DATE: day must be an integer".to_string())
                        })?
                    }
                    _ => return Err(QueryError::Type("DATE: day must be an integer".to_string())),
                };
                NaiveDate::from_ymd_opt(year, month, day)
                    .map(Value::Date)
                    .ok_or_else(|| {
                        QueryError::Type(format!("DATE: invalid date {year}-{month}-{day}"))
                    })
            }
            _ => Err(QueryError::InvalidArguments(
                "DATE".to_string(),
                "expected 1 or 3 arguments".to_string(),
            )),
        }
    }

    /// Evaluate `DATE_DIFF` function (difference in days).
    ///
    /// `DATE_DIFF(date1, date2)` - returns date1 - date2 in days
    pub(crate) fn eval_date_diff(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        Self::require_args("DATE_DIFF", func, 2)?;

        let date1 = match self.evaluate_expr(&func.args[0], ctx)? {
            Value::Date(d) => d,
            _ => {
                return Err(QueryError::Type(
                    "DATE_DIFF: first argument must be a date".to_string(),
                ));
            }
        };
        let date2 = match self.evaluate_expr(&func.args[1], ctx)? {
            Value::Date(d) => d,
            _ => {
                return Err(QueryError::Type(
                    "DATE_DIFF: second argument must be a date".to_string(),
                ));
            }
        };

        let diff = date1.signed_duration_since(date2).num_days();
        Ok(Value::Integer(diff))
    }

    /// Evaluate `DATE_ADD` function (add days or interval to a date).
    ///
    /// `DATE_ADD(date, days)` - returns date + days
    /// `DATE_ADD(date, interval)` - returns date + interval
    pub(crate) fn eval_date_add(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        Self::require_args("DATE_ADD", func, 2)?;

        let date = match self.evaluate_expr(&func.args[0], ctx)? {
            Value::Date(d) => d,
            _ => {
                return Err(QueryError::Type(
                    "DATE_ADD: first argument must be a date".to_string(),
                ));
            }
        };

        let second_arg = self.evaluate_expr(&func.args[1], ctx)?;
        let result = match second_arg {
            Value::Integer(days) => date + rustledger_core::Duration::days(days),
            Value::Number(n) => {
                use rust_decimal::prelude::ToPrimitive;
                let days = n.to_i64().ok_or_else(|| {
                    QueryError::Type("DATE_ADD: days must be an integer".to_string())
                })?;
                date + rustledger_core::Duration::days(days)
            }
            Value::Interval(interval) => interval
                .add_to_date(date)
                .ok_or_else(|| QueryError::Evaluation("DATE_ADD: interval overflow".to_string()))?,
            _ => {
                return Err(QueryError::Type(
                    "DATE_ADD: second argument must be an integer or interval".to_string(),
                ));
            }
        };

        Ok(Value::Date(result))
    }

    /// Evaluate `DATE_TRUNC` function (truncate date to field).
    ///
    /// `DATE_TRUNC(field, date)` - truncate to year/month
    pub(crate) fn eval_date_trunc(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        Self::require_args("DATE_TRUNC", func, 2)?;

        let field = match self.evaluate_expr(&func.args[0], ctx)? {
            Value::String(s) => s.to_uppercase(),
            _ => {
                return Err(QueryError::Type(
                    "DATE_TRUNC: first argument must be a string".to_string(),
                ));
            }
        };
        let date = match self.evaluate_expr(&func.args[1], ctx)? {
            Value::Date(d) => d,
            _ => {
                return Err(QueryError::Type(
                    "DATE_TRUNC: second argument must be a date".to_string(),
                ));
            }
        };

        let result = match field.as_str() {
            "YEAR" => NaiveDate::from_ymd_opt(date.year(), 1, 1),
            "QUARTER" => {
                let quarter = (date.month() - 1) / 3;
                NaiveDate::from_ymd_opt(date.year(), quarter * 3 + 1, 1)
            }
            "MONTH" => NaiveDate::from_ymd_opt(date.year(), date.month(), 1),
            "WEEK" => {
                // Start of week (Monday)
                let days_from_monday = i64::from(date.weekday().num_days_from_monday());
                Some(date - rustledger_core::Duration::days(days_from_monday))
            }
            "DAY" => Some(date),
            _ => {
                return Err(QueryError::Type(format!(
                    "DATE_TRUNC: unknown field '{field}', expected YEAR, QUARTER, MONTH, WEEK, or DAY"
                )));
            }
        };

        result
            .map(Value::Date)
            .ok_or_else(|| QueryError::Type("DATE_TRUNC: invalid date result".to_string()))
    }

    /// Evaluate `DATE_PART` function (extract date component).
    ///
    /// `DATE_PART(field, date)` - extract component
    pub(crate) fn eval_date_part(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        Self::require_args("DATE_PART", func, 2)?;

        let field = match self.evaluate_expr(&func.args[0], ctx)? {
            Value::String(s) => s.to_uppercase(),
            _ => {
                return Err(QueryError::Type(
                    "DATE_PART: first argument must be a string".to_string(),
                ));
            }
        };
        let date = match self.evaluate_expr(&func.args[1], ctx)? {
            Value::Date(d) => d,
            _ => {
                return Err(QueryError::Type(
                    "DATE_PART: second argument must be a date".to_string(),
                ));
            }
        };

        let result = match field.as_str() {
            "YEAR" => i64::from(date.year()),
            "MONTH" => i64::from(date.month()),
            "DAY" => i64::from(date.day()),
            "QUARTER" => i64::from((date.month() - 1) / 3 + 1),
            "WEEK" => i64::from(date.iso_week().week()),
            "WEEKDAY" | "DOW" => i64::from(date.weekday().num_days_from_monday()),
            "DOY" => i64::from(date.ordinal()),
            _ => {
                return Err(QueryError::Type(format!(
                    "DATE_PART: unknown field '{field}', expected YEAR, MONTH, DAY, QUARTER, WEEK, WEEKDAY, DOW, or DOY"
                )));
            }
        };

        Ok(Value::Integer(result))
    }

    /// Evaluate `PARSE_DATE` function (parse date with format).
    ///
    /// `PARSE_DATE(string, format)` - parse with chrono format
    pub(crate) fn eval_parse_date(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        Self::require_args("PARSE_DATE", func, 2)?;

        let string = match self.evaluate_expr(&func.args[0], ctx)? {
            Value::String(s) => s,
            _ => {
                return Err(QueryError::Type(
                    "PARSE_DATE: first argument must be a string".to_string(),
                ));
            }
        };
        let format = match self.evaluate_expr(&func.args[1], ctx)? {
            Value::String(s) => s,
            _ => {
                return Err(QueryError::Type(
                    "PARSE_DATE: second argument must be a format string".to_string(),
                ));
            }
        };

        NaiveDate::parse_from_str(&string, &format)
            .map(Value::Date)
            .map_err(|e| {
                QueryError::Type(format!(
                    "PARSE_DATE: cannot parse '{string}' with format '{format}': {e}"
                ))
            })
    }

    /// Evaluate `DATE_BIN` function (bin dates into buckets).
    ///
    /// `DATE_BIN(stride, source, origin)` - bins source date into buckets of stride size
    /// starting from origin.
    ///
    /// Stride is a string like "1 day", "7 days", "1 week", "1 month", "3 months", "1 year".
    pub(crate) fn eval_date_bin(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        Self::require_args("DATE_BIN", func, 3)?;

        let stride = match self.evaluate_expr(&func.args[0], ctx)? {
            Value::String(s) => s,
            Value::Integer(days) => format!("{days} days"),
            _ => {
                return Err(QueryError::Type(
                    "DATE_BIN: first argument must be a stride string or integer days".to_string(),
                ));
            }
        };

        let source = match self.evaluate_expr(&func.args[1], ctx)? {
            Value::Date(d) => d,
            _ => {
                return Err(QueryError::Type(
                    "DATE_BIN: second argument must be a date".to_string(),
                ));
            }
        };

        let origin = match self.evaluate_expr(&func.args[2], ctx)? {
            Value::Date(d) => d,
            _ => {
                return Err(QueryError::Type(
                    "DATE_BIN: third argument must be a date".to_string(),
                ));
            }
        };

        // Parse stride string
        let stride_lower = stride.to_lowercase();
        let parts: Vec<&str> = stride_lower.split_whitespace().collect();

        let (amount, unit) = match parts.as_slice() {
            [num, unit] => {
                let n: i64 = num.parse().map_err(|_| {
                    QueryError::Type(format!("DATE_BIN: invalid stride number '{num}'"))
                })?;
                (n, *unit)
            }
            [unit] => (1, *unit),
            _ => {
                return Err(QueryError::Type(format!(
                    "DATE_BIN: invalid stride format '{stride}'"
                )));
            }
        };

        // Calculate days from origin to source
        let days_diff = (source - origin).num_days();

        // Calculate binned date based on unit
        let binned = match unit.trim_end_matches('s') {
            "day" => {
                let bucket = days_diff / amount;
                origin + rustledger_core::Duration::days(bucket * amount)
            }
            "week" => {
                let days_per_stride = amount * 7;
                let bucket = days_diff / days_per_stride;
                origin + rustledger_core::Duration::days(bucket * days_per_stride)
            }
            "month" => {
                // For months, we need to work with calendar months
                let months_diff = (source.year() - origin.year()) * 12 + (source.month() as i32)
                    - (origin.month() as i32);
                let bucket = months_diff / (amount as i32);
                let total_months = (origin.month() as i32) - 1 + bucket * (amount as i32);
                let year = origin.year() + total_months / 12;
                let month = (total_months % 12 + 1) as u32;
                NaiveDate::from_ymd_opt(year, month, 1).unwrap_or(origin)
            }
            "quarter" => {
                // 3-month buckets
                let months_diff = (source.year() - origin.year()) * 12 + (source.month() as i32)
                    - (origin.month() as i32);
                let quarters = months_diff / (3 * amount as i32);
                let total_months = (origin.month() as i32) - 1 + quarters * 3 * (amount as i32);
                let year = origin.year() + total_months / 12;
                let month = (total_months % 12 + 1) as u32;
                NaiveDate::from_ymd_opt(year, month, 1).unwrap_or(origin)
            }
            "year" => {
                let years_diff = source.year() - origin.year();
                let bucket = years_diff / (amount as i32);
                let year = origin.year() + bucket * (amount as i32);
                NaiveDate::from_ymd_opt(year, origin.month(), origin.day()).unwrap_or(origin)
            }
            _ => {
                return Err(QueryError::Type(format!(
                    "DATE_BIN: unknown unit '{unit}', expected day(s), week(s), month(s), quarter(s), or year(s)"
                )));
            }
        };

        Ok(Value::Date(binned))
    }
}
