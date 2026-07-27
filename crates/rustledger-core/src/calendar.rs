//! Calendar period truncation — the single definition of "which month/quarter/
//! week/year is this date in, and when does that period start".
//!
//! Two consumers need exactly this arithmetic and had independently derived it:
//! BQL's `DATE_TRUNC` (and the `GROUP BY` period bucketing built on it) and the
//! budget report's per-interval accrual. The formulas are small enough to look
//! harmless — `(month - 1) / 3 * 3 + 1` for a quarter, subtract
//! `weekday().to_monday_zero_offset()` for an ISO week — and a previous
//! duplication sweep inside the query crate alone found the quarter formula
//! written twice and diverging.
//!
//! The failure mode of two copies is quiet: `rledger report budget` on a weekly
//! budget and `SELECT ... GROUP BY DATE_TRUNC('WEEK', date)` over the same
//! ledger would answer with different week boundaries, and no test in either
//! crate would fail. Anything that changes the calendar rules — a configurable
//! first-day-of-week, a fiscal-year quarter offset — must change one place.

use crate::NaiveDate;

/// A calendar period. Periods are anchored to the calendar, never to an
/// arbitrary start date: months begin on the 1st, quarters on Jan/Apr/Jul/Oct 1,
/// years on Jan 1, and weeks on the ISO Monday.
///
/// # Deliberate divergence from Fava (quarters)
///
/// Fava's `_IntervalQuarter.get_prev` tests `date.month > i` where it needs
/// `>=`, so it puts April in Q1, July in Q2 and October in Q3 — every quarter
/// boundary month falls into the preceding quarter. Reported as
/// beancount/fava#2318. rustledger anchors quarters correctly, per the
/// project's Python-compatibility policy: match correct behavior, not bugs.
/// A `custom "budget"` on a `"quarterly"` interval therefore accrues over
/// different boundaries than Fava's budget view for those three months.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum CalendarPeriod {
    /// One calendar day.
    Day,
    /// An ISO week, starting Monday.
    Week,
    /// A calendar month (28, 29, 30 or 31 days).
    Month,
    /// A calendar quarter, anchored at Jan/Apr/Jul/Oct 1.
    Quarter,
    /// A calendar year (365 or 366 days).
    Year,
}

/// Zero-based quarter index for a 1-based month (0 => Q1).
///
/// `month1` must be 1-based (`jiff`'s `Date::month()` guarantees `1..=12`); 0
/// would wrap in release builds, so debug builds assert.
#[must_use]
pub const fn quarter_index0(month1: u32) -> u32 {
    debug_assert!(month1 >= 1);
    (month1 - 1) / 3
}

impl CalendarPeriod {
    /// The first day of the period containing `day`.
    ///
    /// Falls back to `day` itself if the truncated date would be out of range,
    /// which keeps this total rather than panicking on ledger-derived dates.
    ///
    /// For month, quarter and year that fallback is unreachable: the 1st of a
    /// real month always exists. For WEEK it is reachable at the very start of
    /// the representable calendar, where the containing ISO week begins before
    /// `NaiveDate::MIN` and there is no Monday to return; the result then is the
    /// day itself, NOT a week start. No ledger reaches that date, but the
    /// saturation is real and this says so rather than implying stricter
    /// semantics than the code provides.
    #[must_use]
    pub fn start_of(self, day: NaiveDate) -> NaiveDate {
        match self {
            Self::Day => day,
            Self::Week => day
                .checked_sub(
                    jiff::Span::new().days(i64::from(day.weekday().to_monday_zero_offset())),
                )
                .unwrap_or(day),
            Self::Month => NaiveDate::new(day.year(), day.month(), 1).unwrap_or(day),
            Self::Quarter => {
                let month1 = quarter_index0(u32::from(day.month().unsigned_abs())) * 3 + 1;
                i8::try_from(month1)
                    .ok()
                    .and_then(|m| NaiveDate::new(day.year(), m, 1).ok())
                    .unwrap_or(day)
            }
            Self::Year => NaiveDate::new(day.year(), 1, 1).unwrap_or(day),
        }
    }

    /// The first day of the period after the one starting at `start`, or `None`
    /// when that date is outside the representable range.
    ///
    /// `start` is expected to be a period start (the output of [`Self::start_of`]);
    /// the difference between this and `start` is the period's true calendar
    /// length, which is what makes a per-day accrual divide by 28/29/30/31 for a
    /// month and 365/366 for a year.
    ///
    /// Returning `None` rather than saturating to `start` is deliberate: a
    /// caller measuring the period's length would otherwise get zero and, after
    /// the usual `.max(1)` guard, divide by a single day — inflating a yearly
    /// budget by ~365x near the end of the representable range, silently and
    /// with no error anywhere.
    #[must_use]
    pub fn next_start(self, start: NaiveDate) -> Option<NaiveDate> {
        let span = match self {
            Self::Day => jiff::Span::new().days(1),
            Self::Week => jiff::Span::new().days(7),
            Self::Month => jiff::Span::new().months(1),
            Self::Quarter => jiff::Span::new().months(3),
            Self::Year => jiff::Span::new().years(1),
        };
        start.checked_add(span).ok()
    }

    /// The calendar length, in days, of the period starting at `start`.
    ///
    /// Equal to the gap to [`Self::next_start`] wherever that date exists. The
    /// final period of the representable calendar has no representable next
    /// start, but its LENGTH is still well defined, and this returns it: a day
    /// and a week are fixed-length, and month, quarter and year boundaries all
    /// coincide with the end of the calendar, so the span to the last
    /// representable day is the whole period.
    ///
    /// Pro-rata accrual needs the length, not the boundary date. Deriving the
    /// length from `next_start` alone forced callers to give up on the final
    /// period entirely — a budget was reported as `0.00` for a window inside
    /// it, which reads as "nothing budgeted" rather than "cannot say".
    #[must_use]
    pub fn period_days(self, start: NaiveDate) -> i64 {
        let days_between = |a: NaiveDate, b: NaiveDate| {
            i64::from(a.until((jiff::Unit::Day, b)).map_or(0, |s| s.get_days()))
        };
        if let Some(next) = self.next_start(start) {
            return days_between(start, next);
        }
        match self {
            Self::Day => 1,
            Self::Week => 7,
            // `+ 1` because `MAX` is the last day IN the period, not the first
            // day after it.
            Self::Month | Self::Quarter | Self::Year => days_between(start, NaiveDate::MAX) + 1,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::naive_date;

    fn d(y: i32, m: u32, day: u32) -> NaiveDate {
        naive_date(y, m, day).unwrap()
    }

    #[test]
    fn quarters_anchor_to_jan_apr_jul_oct() {
        for (month, want_month) in [
            (1, 1),
            (2, 1),
            (3, 1),
            (4, 4),
            (5, 4),
            (6, 4),
            (7, 7),
            (8, 7),
            (9, 7),
            (10, 10),
            (11, 10),
            (12, 10),
        ] {
            assert_eq!(
                CalendarPeriod::Quarter.start_of(d(2024, month, 15)),
                d(2024, want_month, 1),
                "month {month}"
            );
        }
    }

    #[test]
    fn weeks_anchor_to_iso_monday() {
        // 2024-03-07 is a Thursday; its ISO week began Monday 2024-03-04.
        assert_eq!(CalendarPeriod::Week.start_of(d(2024, 3, 7)), d(2024, 3, 4));
        assert_eq!(CalendarPeriod::Week.start_of(d(2024, 3, 4)), d(2024, 3, 4));
        // A week spanning a year boundary keeps its Monday in the old year.
        assert_eq!(
            CalendarPeriod::Week.start_of(d(2025, 1, 1)),
            d(2024, 12, 30)
        );
    }

    /// Near the end of the representable range the next period start does not
    /// exist. Saturating to `start` would make the period look zero days long,
    /// and a per-day accrual would then divide by one.
    #[test]
    fn next_start_is_none_past_the_representable_range() {
        let last = NaiveDate::MAX;
        assert_eq!(CalendarPeriod::Year.next_start(last), None);
        assert_eq!(CalendarPeriod::Month.next_start(last), None);
    }

    #[test]
    fn month_and_year_truncate_and_advance() {
        assert_eq!(
            CalendarPeriod::Month.start_of(d(2024, 2, 29)),
            d(2024, 2, 1)
        );
        assert_eq!(
            CalendarPeriod::Year.start_of(d(2024, 12, 31)),
            d(2024, 1, 1)
        );
        // Leap February is 29 days long, not 28 or 30.
        let feb = CalendarPeriod::Month.start_of(d(2024, 2, 10));
        assert_eq!(CalendarPeriod::Month.next_start(feb), Some(d(2024, 3, 1)));
        // A leap year is 366 days.
        let y = CalendarPeriod::Year.start_of(d(2024, 6, 1));
        assert_eq!(CalendarPeriod::Year.next_start(y), Some(d(2025, 1, 1)));
    }
}
