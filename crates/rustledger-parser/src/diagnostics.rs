//! Diagnostic helpers used by the CST-backed converter
//! (`crate::cst::convert`).
//!
//! Originally lived in the legacy `parser.rs` and were hoisted
//! into their own module during the phase 3.2-3.4 architecture
//! review (#1281) so the legacy parser could be deleted in
//! phase 5 (#1262) without first having to relocate them.

use std::borrow::Cow;

/// Hint text attached via `ParseError::with_hint` to every mid-file
/// BOM diagnostic so miette renders it on a dedicated `help:` line
/// rather than burying it inside the primary message body.
pub const BOM_REMOVAL_HINT: &str = concat!(
    "remove the U+FEFF byte at this position; ",
    "if the file is a concatenation of two BOM-prefixed exports, ",
    "strip BOMs from the inner files before concatenating",
);

/// Zero-pad single-digit month/day and normalize '/' separators to '-'.
/// Returns the original string as-is when already in canonical `YYYY-MM-DD` form
/// to avoid unnecessary allocation on the hot path.
#[must_use]
pub fn normalize_date_str(s: &str) -> Cow<'_, str> {
    // Fast path: already canonical (no '/', month+day are 2 digits → length is 10).
    if !s.contains('/') && s.len() == 10 {
        return Cow::Borrowed(s);
    }
    // Separator can be '-' or '/'; the regex guarantees three parts.
    let s = s.replace('/', "-");
    if let Some((year, rest)) = s.split_once('-')
        && let Some((month, day)) = rest.split_once('-')
    {
        return Cow::Owned(format!("{year}-{month:0>2}-{day:0>2}"));
    }
    Cow::Owned(s)
}

/// Build a human-readable reason why a date string is invalid.
#[must_use]
pub fn describe_invalid_date(s: &str) -> String {
    let parts: Vec<&str> = s.split(['-', '/']).collect();
    if parts.len() == 3
        && let (Ok(year), Ok(month), Ok(day)) = (
            parts[0].parse::<i32>(),
            parts[1].parse::<u32>(),
            parts[2].parse::<u32>(),
        )
    {
        if !(1..=12).contains(&month) {
            return format!("month {month} out of range");
        }
        let year_month = format!("{year}-{month:02}");
        return format!("day {day} out of range for {year_month}");
    }
    format!("invalid date '{s}'")
}

/// Return the first whitespace-separated token in `text` that
/// looks like an account name (uppercase start + colon) but
/// contains non-ASCII. Returns the matching token, or `None`.
///
/// Used by the error-recovery classifier to surface
/// `InvalidAccount` for Unicode-character account names — those
/// are the actionable root cause when both they and a BOM byte
/// appear on the same malformed line.
#[must_use]
pub fn find_unicode_account(text: &str) -> Option<&str> {
    for token in text.split_whitespace() {
        if !token.contains(':') {
            continue;
        }
        let first_char = token.chars().next().unwrap_or(' ');
        if !first_char.is_uppercase() {
            continue;
        }
        if !token.is_ascii() {
            return Some(token);
        }
    }
    None
}
