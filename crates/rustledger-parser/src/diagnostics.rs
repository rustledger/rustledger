//! Diagnostic helpers used by the CST-backed converter
//! (`crate::cst::convert`).
//!
//! Originally lived in the legacy `parser.rs` and were hoisted
//! into their own module during the phase 3.2-3.4 architecture
//! review (#1281) so the legacy parser could be deleted in
//! phase 5 (#1262) without first having to relocate them.

/// Hint text attached via `ParseError::with_hint` to every mid-file
/// BOM diagnostic so miette renders it on a dedicated `help:` line
/// rather than burying it inside the primary message body.
pub const BOM_REMOVAL_HINT: &str = concat!(
    "remove the U+FEFF byte at this position; ",
    "if the file is a concatenation of two BOM-prefixed exports, ",
    "strip BOMs from the inner files before concatenating",
);

/// The three fields of a date token, as beancount reads them, each as its
/// digits with the leading zeros removed (`02024-001-01` is `2024`, `1`, `1`;
/// `0000` is `0`). Text rather than integers, so a field too long for any
/// integer type is still echoed as written in a diagnostic.
/// `None` unless `s` is exactly three runs of ASCII digits joined by `-` or
/// `/`, the shape the lexer's `Date` token guarantees (#2808).
#[must_use]
pub fn date_fields(s: &str) -> Option<[&str; 3]> {
    fn field(f: &str) -> Option<&str> {
        if f.is_empty() || !f.bytes().all(|b| b.is_ascii_digit()) {
            return None;
        }
        let digits = f.trim_start_matches('0');
        Some(if digits.is_empty() {
            &f[f.len() - 1..]
        } else {
            digits
        })
    }
    let mut parts = s.split(['-', '/']);
    let (year, month, day) = (parts.next()?, parts.next()?, parts.next()?);
    if parts.next().is_some() {
        return None;
    }
    Some([field(year)?, field(month)?, field(day)?])
}

/// Build a human-readable reason why a date string is invalid.
#[must_use]
pub fn describe_invalid_date(s: &str) -> String {
    if let Some([year, month, day]) = date_fields(s) {
        // Years 1 to 9999, as beancount (Python's `datetime.date`) allows:
        // year 0 (#2811) and a year past 9999 (`20024-01-01`, #2808) are
        // refused, as beancount refuses them (`year 0 is out of range`).
        // A field is echoed as written, however long (#2868 review).
        if !year.parse::<u16>().is_ok_and(|y| (1..=9999).contains(&y)) {
            return format!("year {year} out of range");
        }
        if !month.parse::<u8>().is_ok_and(|m| (1..=12).contains(&m)) {
            return format!("month {month} out of range");
        }
        return format!("day {day} out of range for {year}-{month:0>2}");
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
