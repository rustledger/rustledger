//! Date function implementations for the BQL executor.

use rustledger_core::NaiveDate;

use crate::error::QueryError;

use super::super::Executor;
use super::super::types::{Interval, IntervalUnit, Value};

/// strftime formats the one-arg `PARSE_DATE` tries (after ISO `FromStr`),
/// covering numeric and month-name shapes — `%m-%d-%Y` first so ambiguous
/// `MM-DD-YYYY` matches dateutil's month-first default.
const PARSE_DATE_FORMATS: &[&str] = &[
    "%Y/%m/%d", "%m-%d-%Y", "%m/%d/%Y", "%B %d %Y", "%b %d %Y", "%d %B %Y", "%d %b %Y",
];

impl Executor<'_> {
    /// Value-core for `INTERVAL` function (construct an interval).
    pub(crate) fn interval_on_values(args: &[Value]) -> Result<Value, QueryError> {
        // interval(unit) - creates an interval of 1 unit
        // interval(count, unit) - creates an interval of count units
        match args.len() {
            1 => {
                let unit_str = match args[0].clone() {
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
                let count = match args[0].clone() {
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
                let unit_str = match args[1].clone() {
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

    /// Value-core for `DATE` function (construct a date).
    pub(crate) fn date_construct_on_values(args: &[Value]) -> Result<Value, QueryError> {
        match args.len() {
            1 => {
                // DATE(string) - parse ISO date
                let val = args[0].clone();
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
                let year = match args[0].clone() {
                    Value::Integer(i) => i32::try_from(i)
                        .map_err(|_| QueryError::Type("DATE: year out of range".to_string()))?,
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
                let month = match args[1].clone() {
                    Value::Integer(i) => u32::try_from(i).map_err(|_| {
                        QueryError::Type("DATE: month must be a non-negative integer".to_string())
                    })?,
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
                let day = match args[2].clone() {
                    Value::Integer(i) => u32::try_from(i).map_err(|_| {
                        QueryError::Type("DATE: day must be a non-negative integer".to_string())
                    })?,
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

    /// Value-core for `DATE_ADD` function (add days or interval to a date).
    pub(crate) fn date_add_on_values(args: &[Value]) -> Result<Value, QueryError> {
        Self::require_args_count("DATE_ADD", args, 2)?;

        let date = match args[0].clone() {
            Value::Date(d) => d,
            _ => {
                return Err(QueryError::Type(
                    "DATE_ADD: first argument must be a date".to_string(),
                ));
            }
        };

        let second_arg = args[1].clone();
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

    /// Value-core for `DATE_TRUNC` function (truncate date to field).
    pub(crate) fn date_trunc_on_values(args: &[Value]) -> Result<Value, QueryError> {
        Self::require_args_count("DATE_TRUNC", args, 2)?;

        let field = match args[0].clone() {
            Value::String(s) => s.to_uppercase(),
            _ => {
                return Err(QueryError::Type(
                    "DATE_TRUNC: first argument must be a string".to_string(),
                ));
            }
        };
        let date = match args[1].clone() {
            Value::Date(d) => d,
            _ => {
                return Err(QueryError::Type(
                    "DATE_TRUNC: second argument must be a date".to_string(),
                ));
            }
        };

        let result = match field.as_str() {
            // Truncation delegates to the shared canonical
            // (`rustledger_core::CalendarPeriod`) so BQL period grouping and the
            // budget report's interval accrual cannot drift apart.
            "YEAR" => Some(rustledger_core::CalendarPeriod::Year.start_of(date)),
            "QUARTER" => Some(rustledger_core::CalendarPeriod::Quarter.start_of(date)),
            "MONTH" => Some(rustledger_core::CalendarPeriod::Month.start_of(date)),
            "WEEK" => Some(rustledger_core::CalendarPeriod::Week.start_of(date)),
            "DAY" => Some(rustledger_core::CalendarPeriod::Day.start_of(date)),
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

    /// Value-core for `DATE_PART` function (extract date component).
    pub(crate) fn date_part_on_values(args: &[Value]) -> Result<Value, QueryError> {
        Self::require_args_count("DATE_PART", args, 2)?;

        let field = match args[0].clone() {
            Value::String(s) => s.to_uppercase(),
            _ => {
                return Err(QueryError::Type(
                    "DATE_PART: first argument must be a string".to_string(),
                ));
            }
        };
        let date = match args[1].clone() {
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
            "QUARTER" => i64::from(rustledger_core::quarter_index0(date.month() as u32) + 1),
            // Typed accessor, not a `%V` format-then-parse round trip: that
            // spelling carried `unwrap_or_default()` + `unwrap_or(0)`, so any
            // failure silently reported week 0 rather than erroring (#1864).
            //
            // NOTE for callers: this is the ISO week NUMBER alone. Pairing it
            // with `DATE_PART(date, 'YEAR')` to build a label is wrong at a year
            // boundary — 2024-12-31 is week 1 of ISO year 2025, not 2024. BQL
            // exposes no ISO-week-year field; use `DATE_TRUNC('WEEK', date)`,
            // which returns the week's Monday and cannot be mismatched.
            "WEEK" => i64::from(date.iso_week_date().week()),
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

    /// Value-core for `PARSE_DATE` function (parse date with format).
    pub(crate) fn parse_date_on_values(args: &[Value]) -> Result<Value, QueryError> {
        // beanquery accepts `parse_date(str)` (dateutil) and
        // `parse_date(str, format)`.
        if args.is_empty() || args.len() > 2 {
            return Err(QueryError::InvalidArguments(
                "PARSE_DATE".to_string(),
                "expected 1 or 2 arguments".to_string(),
            ));
        }

        let string = match args[0].clone() {
            Value::String(s) => s,
            _ => {
                return Err(QueryError::Type(
                    "PARSE_DATE: first argument must be a string".to_string(),
                ));
            }
        };

        // Two-arg form: explicit strftime format.
        if args.len() == 2 {
            let format = match args[1].clone() {
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

    /// Value-core for `DATE_BIN` function (bin dates into buckets).
    pub(crate) fn date_bin_on_values(args: &[Value]) -> Result<Value, QueryError> {
        Self::require_args_count("DATE_BIN", args, 3)?;

        let stride = match args[0].clone() {
            Value::String(s) => s,
            Value::Integer(days) => format!("{days} days"),
            _ => {
                return Err(QueryError::Type(
                    "DATE_BIN: first argument must be a stride string or integer days".to_string(),
                ));
            }
        };

        let source = match args[1].clone() {
            Value::Date(d) => d,
            _ => {
                return Err(QueryError::Type(
                    "DATE_BIN: second argument must be a date".to_string(),
                ));
            }
        };

        let origin = match args[2].clone() {
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

        // A non-positive stride amount would divide-by-zero in the bucket math
        // below; reject it rather than panic (reachable now via eager #postings).
        if amount <= 0 {
            return Err(QueryError::Type(format!(
                "DATE_BIN: stride amount must be positive, got {amount}"
            )));
        }

        // Calculate days from origin to source
        let days_diff = i64::from(source.since(origin).unwrap_or_default().get_days());

        let sy = i32::from(source.year());
        let sm = i32::from(source.month());
        let oy = i32::from(origin.year());
        let om = i32::from(origin.month());
        let od = origin.day() as u32;
        let amt = i32::try_from(amount)
            .map_err(|_| QueryError::Type("DATE_BIN: stride amount too large".to_string()))?;

        // Calculate binned date based on unit
        let binned = match unit.trim_end_matches('s') {
            "day" => {
                let bucket = days_diff / amount;
                add_days(origin, bucket * amount)?
            }
            "week" => {
                let days_per_stride = amount * 7;
                let bucket = days_diff / days_per_stride;
                add_days(origin, bucket * days_per_stride)?
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
