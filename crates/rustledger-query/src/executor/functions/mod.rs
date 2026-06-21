//! Function evaluation modules for the BQL executor.
//!
//! This module organizes function implementations by category for better maintainability.

mod account;
mod date;
mod math;
mod position;
pub(in crate::executor) mod string;
mod util;

/// Three-letter English weekday abbreviation (`Mon`..`Sun`) for a Monday-zero
/// offset (0=Mon … 6=Sun). `WEEKDAY(date)` returns this string, matching
/// beanquery (whose `weekday(date)` yields a day name, not an integer).
pub(super) const fn weekday_abbrev(monday_zero_offset: u32) -> &'static str {
    match monday_zero_offset {
        0 => "Mon",
        1 => "Tue",
        2 => "Wed",
        3 => "Thu",
        4 => "Fri",
        5 => "Sat",
        _ => "Sun",
    }
}
