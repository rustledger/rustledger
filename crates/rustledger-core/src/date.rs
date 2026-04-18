//! Date type wrapping `jiff::civil::Date` with chrono-compatible API.
//!
//! This provides a `NaiveDate` type that uses jiff internally but exposes
//! the same interface as `chrono::NaiveDate` for backward compatibility.

use std::fmt;
use std::str::FromStr;

use serde::{Deserialize, Serialize};

/// A calendar date without timezone information.
///
/// This wraps `jiff::civil::Date` and provides the same API surface as
/// `chrono::NaiveDate` so downstream code doesn't need changes.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct NaiveDate(jiff::civil::Date);

impl NaiveDate {
    /// Get today's date in the local timezone.
    #[must_use]
    pub fn today() -> Self {
        Self(jiff::Zoned::now().date())
    }

    /// Create a date from year, month, day. Returns `None` if invalid.
    #[must_use]
    pub fn from_ymd_opt(year: i32, month: u32, day: u32) -> Option<Self> {
        jiff::civil::Date::new(year as i16, month as i8, day as i8)
            .ok()
            .map(Self)
    }

    /// Get the year.
    #[must_use]
    pub fn year(&self) -> i32 {
        self.0.year() as i32
    }

    /// Get the month (1-12).
    #[must_use]
    pub fn month(&self) -> u32 {
        self.0.month() as u32
    }

    /// Get the day of the month (1-31).
    #[must_use]
    pub fn day(&self) -> u32 {
        self.0.day() as u32
    }

    /// Get the month as 0-indexed (0-11). Compatibility with chrono.
    #[must_use]
    pub fn month0(&self) -> u32 {
        self.0.month() as u32 - 1
    }

    /// Get the previous day.
    #[must_use]
    pub fn pred_opt(&self) -> Option<Self> {
        self.0.yesterday().ok().map(Self)
    }

    /// Get the next day.
    #[must_use]
    pub fn succ_opt(&self) -> Option<Self> {
        self.0.tomorrow().ok().map(Self)
    }

    /// Get the day of the week (Monday = 0 .. Sunday = 6).
    #[must_use]
    pub fn weekday(&self) -> Weekday {
        Weekday(self.0.weekday())
    }

    /// Add a signed duration in days.
    #[must_use]
    pub fn checked_add_signed(&self, duration: Duration) -> Option<Self> {
        self.0
            .checked_add(jiff::Span::new().days(duration.days))
            .ok()
            .map(Self)
    }

    /// Subtract a signed duration in days.
    #[must_use]
    pub fn checked_sub_signed(&self, duration: Duration) -> Option<Self> {
        self.0
            .checked_add(jiff::Span::new().days(-duration.days))
            .ok()
            .map(Self)
    }

    /// Add months.
    #[must_use]
    pub fn checked_add_months(&self, months: Months) -> Option<Self> {
        self.0
            .checked_add(jiff::Span::new().months(months.0 as i64))
            .ok()
            .map(Self)
    }

    /// Subtract months.
    #[must_use]
    pub fn checked_sub_months(&self, months: Months) -> Option<Self> {
        self.0
            .checked_add(jiff::Span::new().months(-(months.0 as i64)))
            .ok()
            .map(Self)
    }

    /// Number of years since another date (unsigned).
    #[must_use]
    pub fn years_since(&self, other: Self) -> Option<u32> {
        let days = self.0.since(other.0).ok()?.get_days();
        Some((days.unsigned_abs() / 365) as u32)
    }

    /// Signed duration between two dates in days.
    #[must_use]
    pub fn signed_duration_since(&self, other: Self) -> Duration {
        let days = self.0.since(other.0).unwrap_or_default().get_days();
        Duration {
            days: i64::from(days),
        }
    }

    /// Get the ISO week number.
    #[must_use]
    pub fn iso_week(&self) -> IsoWeek {
        // ISO week: week 1 contains the first Thursday of the year
        let ordinal = self.ordinal();
        let weekday = self.0.weekday().to_monday_one_offset() as u32;
        // ISO 8601 week calculation
        let w = (ordinal + 10 - weekday) / 7;
        IsoWeek(w)
    }

    /// Get the day of the year (1-366).
    #[must_use]
    pub fn ordinal(&self) -> u32 {
        let jan1 = jiff::civil::date(self.0.year(), 1, 1);
        let days = self.0.since(jan1).unwrap_or_default().get_days();
        (days + 1) as u32
    }

    /// Days from Common Era epoch. Used for rkyv serialization.
    #[must_use]
    pub(crate) fn num_days_from_ce(&self) -> i32 {
        // CE epoch is year 1, Jan 1. We use Unix epoch (1970-01-01) as intermediate.
        let unix_epoch = jiff::civil::date(1970, 1, 1);
        let days_from_unix = self.0.since(unix_epoch).unwrap().get_days();
        // Unix epoch is day 719163 from CE
        days_from_unix + 719_163
    }

    /// Create from days since Common Era epoch. Used for rkyv deserialization.
    pub(crate) fn from_num_days_from_ce_opt(days: i32) -> Option<Self> {
        let unix_epoch = jiff::civil::date(1970, 1, 1);
        let days_from_unix = days - 719_163;
        unix_epoch
            .checked_add(jiff::Span::new().days(i64::from(days_from_unix)))
            .ok()
            .map(Self)
    }

    /// Format the date. Supports `%Y-%m-%d` and similar strftime patterns.
    #[must_use]
    pub fn format<'a>(&self, fmt: &'a str) -> FormattedDate<'a> {
        FormattedDate { date: self.0, fmt }
    }

    /// Parse from a string with a strftime format pattern.
    pub fn parse_from_str(s: &str, fmt: &str) -> Result<Self, DateParseError> {
        jiff::fmt::strtime::parse(fmt, s)
            .and_then(|tm| tm.to_date())
            .map(Self)
            .map_err(|e| DateParseError(e.to_string()))
    }

    /// Get the inner jiff Date.
    #[must_use]
    pub fn inner(&self) -> jiff::civil::Date {
        self.0
    }
}

/// Formatted date for display.
pub struct FormattedDate<'a> {
    date: jiff::civil::Date,
    fmt: &'a str,
}

impl fmt::Display for FormattedDate<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Handle common strftime patterns
        let s = jiff::fmt::strtime::format(self.fmt, self.date)
            .unwrap_or_else(|_| self.date.to_string());
        f.write_str(&s)
    }
}

/// Date parse error.
#[derive(Debug)]
pub struct DateParseError(String);

impl fmt::Display for DateParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "date parse error: {}", self.0)
    }
}

impl std::error::Error for DateParseError {}

/// Duration in days (chrono compatibility).
#[derive(Clone, Copy)]
pub struct Duration {
    days: i64,
}

impl Duration {
    /// Create a duration of the given number of days.
    #[must_use]
    pub fn days(days: i64) -> Self {
        Self { days }
    }

    /// Create a duration of the given number of weeks.
    #[must_use]
    pub const fn weeks(weeks: i64) -> Self {
        Self { days: weeks * 7 }
    }

    /// Get the number of days.
    #[must_use]
    pub const fn num_days(&self) -> i64 {
        self.days
    }
}

/// Months duration (chrono compatibility).
#[derive(Clone, Copy)]
pub struct Months(u32);

impl Months {
    /// Create a months duration.
    #[must_use]
    pub const fn new(months: u32) -> Self {
        Self(months)
    }
}

/// Day of the week (chrono compatibility wrapper).
#[derive(Clone, Copy)]
pub struct Weekday(jiff::civil::Weekday);

impl Weekday {
    /// Monday = 0, Tuesday = 1, ..., Sunday = 6.
    #[must_use]
    pub fn num_days_from_monday(&self) -> u32 {
        self.0.to_monday_zero_offset() as u32
    }
}

impl fmt::Display for NaiveDate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Debug for NaiveDate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl FromStr for NaiveDate {
    type Err = DateParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse::<jiff::civil::Date>()
            .map(Self)
            .map_err(|e| DateParseError(e.to_string()))
    }
}

impl std::ops::Sub for NaiveDate {
    type Output = Duration;

    fn sub(self, rhs: Self) -> Duration {
        let days = self.0.since(rhs.0).unwrap_or_default().get_days();
        Duration {
            days: i64::from(days),
        }
    }
}

impl std::ops::Sub for &NaiveDate {
    type Output = Duration;

    fn sub(self, rhs: Self) -> Duration {
        let days = self.0.since(rhs.0).unwrap_or_default().get_days();
        Duration {
            days: i64::from(days),
        }
    }
}

/// ISO week number wrapper.
#[derive(Clone, Copy)]
pub struct IsoWeek(u32);

impl IsoWeek {
    /// Get the week number (1-53).
    #[must_use]
    pub const fn week(&self) -> u32 {
        self.0
    }
}

impl std::ops::Add<Duration> for NaiveDate {
    type Output = Self;

    fn add(self, rhs: Duration) -> Self {
        self.checked_add_signed(rhs).unwrap_or(self)
    }
}

impl std::ops::Sub<Duration> for NaiveDate {
    type Output = Self;

    fn sub(self, rhs: Duration) -> Self {
        self.checked_sub_signed(rhs).unwrap_or(self)
    }
}
