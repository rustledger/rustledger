//! Date function implementations for the BQL executor.

use rustledger_core::NaiveDate;

use crate::ast::FunctionCall;
use crate::error::QueryError;

use super::super::Executor;
use super::super::types::{Interval, IntervalUnit, PostingContext, Value};

/// strftime formats the one-arg `PARSE_DATE` tries (after ISO `FromStr`),
/// covering numeric and month-name shapes — `%m-%d-%Y` first so ambiguous
/// `MM-DD-YYYY` matches dateutil's month-first default.
const PARSE_DATE_FORMATS: &[&str] = &[
    "%Y/%m/%d", "%m-%d-%Y", "%m/%d/%Y", "%B %d %Y", "%b %d %Y", "%d %B %Y", "%d %b %Y",
];

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
            return Ok(Value::Date(jiff::Zoned::now().date()));
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
            "WEEKDAY" => Ok(Value::String(
                super::weekday_abbrev(date.weekday().to_monday_zero_offset() as u32).to_string(),
            )),
            "QUARTER" => {
                // beanquery returns a `YYYY-Qn` string, not an integer.
                let quarter = (date.month() - 1) / 3 + 1;
                Ok(Value::String(format!("{:04}-Q{}", date.year(), quarter)))
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
                    Value::String(s) => s
                        .parse::<NaiveDate>()
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
                rustledger_core::naive_date(year, month, day)
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

        let diff = i64::from(date1.since(date2).unwrap_or_default().get_days());
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
            Value::Integer(days) => add_days(date, days)?,
            Value::Number(n) => {
                use rust_decimal::prelude::ToPrimitive;
                let days = n.to_i64().ok_or_else(|| {
                    QueryError::Type("DATE_ADD: days must be an integer".to_string())
                })?;
                add_days(date, days)?
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
            "YEAR" => rustledger_core::naive_date(i32::from(date.year()), 1, 1),
            "QUARTER" => {
                let quarter = (date.month() as u32 - 1) / 3;
                rustledger_core::naive_date(i32::from(date.year()), quarter * 3 + 1, 1)
            }
            "MONTH" => rustledger_core::naive_date(i32::from(date.year()), date.month() as u32, 1),
            "WEEK" => {
                // Start of week (Monday)
                let days_from_monday = i64::from(date.weekday().to_monday_zero_offset() as u32);
                date.checked_add(jiff::ToSpan::days(-days_from_monday)).ok()
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
            "WEEK" => {
                // ISO week number via strftime %V
                let week_str = jiff::fmt::strtime::format("%V", date).unwrap_or_default();
                week_str.trim().parse::<i64>().unwrap_or(0)
            }
            "WEEKDAY" | "DOW" => i64::from(date.weekday().to_monday_zero_offset()),
            "DOY" => {
                let jan1 = jiff::civil::date(date.year(), 1, 1);
                i64::from(date.since(jan1).unwrap().get_days() + 1)
            }
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
        // beanquery accepts `parse_date(str)` (dateutil) and
        // `parse_date(str, format)`.
        if func.args.is_empty() || func.args.len() > 2 {
            return Err(QueryError::InvalidArguments(
                "PARSE_DATE".to_string(),
                "expected 1 or 2 arguments".to_string(),
            ));
        }

        let string = match self.evaluate_expr(&func.args[0], ctx)? {
            Value::String(s) => s,
            _ => {
                return Err(QueryError::Type(
                    "PARSE_DATE: first argument must be a string".to_string(),
                ));
            }
        };

        // Two-arg form: explicit strftime format.
        if func.args.len() == 2 {
            let format = match self.evaluate_expr(&func.args[1], ctx)? {
                Value::String(s) => s,
                _ => {
                    return Err(QueryError::Type(
                        "PARSE_DATE: second argument must be a format string".to_string(),
                    ));
                }
            };
            return jiff::fmt::strtime::parse(&format, &string)
                .and_then(|tm| tm.to_date())
                .map(Value::Date)
                .map_err(|e| {
                    QueryError::Type(format!(
                        "PARSE_DATE: cannot parse '{string}' with format '{format}': {e}"
                    ))
                });
        }

        // One-arg form: beanquery uses dateutil's flexible parser. We cover the
        // common ISO / numeric / month-name shapes (including dateutil's
        // month-first default for ambiguous `MM-DD-YYYY`); full natural-language
        // parsing is not replicated.
        if let Ok(d) = string.parse::<NaiveDate>() {
            return Ok(Value::Date(d));
        }
        for fmt in PARSE_DATE_FORMATS {
            if let Ok(d) = jiff::fmt::strtime::parse(fmt, &string).and_then(|tm| tm.to_date()) {
                return Ok(Value::Date(d));
            }
        }
        Err(QueryError::Type(format!(
            "PARSE_DATE: cannot parse '{string}' (one-arg parse_date covers ISO/numeric/month-name formats)"
        )))
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
        let days_diff = i64::from(source.since(origin).unwrap_or_default().get_days());

        let sy = i32::from(source.year());
        let sm = i32::from(source.month());
        let oy = i32::from(origin.year());
        let om = i32::from(origin.month());
        let od = origin.day() as u32;
        let amt = amount as i32;

        // Calculate binned date based on unit
        let binned = match unit.trim_end_matches('s') {
            "day" => {
                let bucket = days_diff / amount;
                origin
                    .checked_add(jiff::ToSpan::days(bucket * amount))
                    .unwrap()
            }
            "week" => {
                let days_per_stride = amount * 7;
                let bucket = days_diff / days_per_stride;
                origin
                    .checked_add(jiff::ToSpan::days(bucket * days_per_stride))
                    .unwrap()
            }
            "month" => {
                let months_diff = (sy - oy) * 12 + sm - om;
                let bucket = months_diff / amt;
                let total_months = om - 1 + bucket * amt;
                let year = oy + total_months / 12;
                let month = (total_months % 12 + 1) as u32;
                rustledger_core::naive_date(year, month, 1).unwrap_or(origin)
            }
            "quarter" => {
                let months_diff = (sy - oy) * 12 + sm - om;
                let quarters = months_diff / (3 * amt);
                let total_months = om - 1 + quarters * 3 * amt;
                let year = oy + total_months / 12;
                let month = (total_months % 12 + 1) as u32;
                rustledger_core::naive_date(year, month, 1).unwrap_or(origin)
            }
            "year" => {
                let years_diff = sy - oy;
                let bucket = years_diff / amt;
                let year = oy + bucket * amt;
                rustledger_core::naive_date(year, om as u32, od).unwrap_or(origin)
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

/// Add `days` to `date`, returning a graceful error instead of panicking when
/// `days` is out of range.
///
/// `jiff::ToSpan::days` panics while *constructing* the span if the count is
/// outside jiff's representable range (≈ ±7.3M days), so the previous
/// `date.checked_add(jiff::ToSpan::days(days)).unwrap()` aborted the process on
/// a large offset. Build the span fallibly and propagate overflow as a
/// `QueryError` (beanquery raises a catchable `OverflowError` here).
fn add_days(date: NaiveDate, days: i64) -> Result<NaiveDate, QueryError> {
    let span = jiff::Span::new()
        .try_days(days)
        .map_err(|_| QueryError::Evaluation(format!("DATE_ADD: day offset {days} out of range")))?;
    date.checked_add(span).map_err(|_| {
        QueryError::Evaluation(format!(
            "DATE_ADD: resulting date out of range (adding {days} days)"
        ))
    })
}
