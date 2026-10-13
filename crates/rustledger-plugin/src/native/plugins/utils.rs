//! Shared utility functions for native plugins.

/// Whether a metadata value is falsy in Python (`FALSE`, `0`, `""`, and an
/// amount of zero, as beancount's `Amount.__bool__` is `number != 0`); every
/// other value, a date included, is truthy.
#[must_use]
pub fn falsy(value: &crate::types::MetaValueData) -> bool {
    use crate::types::MetaValueData;
    match value {
        MetaValueData::Bool(b) => !b,
        MetaValueData::String(s) => s.is_empty(),
        MetaValueData::Number(n) => n
            .parse::<rust_decimal::Decimal>()
            .is_ok_and(|d| d.is_zero()),
        MetaValueData::Amount(a) => a
            .number
            .parse::<rust_decimal::Decimal>()
            .is_ok_and(|d| d.is_zero()),
        _ => false,
    }
}

#[cfg(test)]
use crate::types::{DirectiveWrapper, PluginOp, PluginOutput};

/// Materialize a plugin's ops back into a flat list of `DirectiveWrapper`s.
///
/// Test-only helper used by the inline plugin tests that previously
/// inspected `output.directives` directly. The mapping is:
/// - `Keep(i)` → `input[i].clone()`
/// - `Modify(i, w)` → `w` (carries `input[i]`'s identity in production,
///   but for test inspection the wrapper's content is what we care about)
/// - `Insert(w)` → `w`
/// - `Delete(_)` → omitted
#[cfg(test)]
#[must_use]
pub fn materialize_ops(input: &[DirectiveWrapper], output: &PluginOutput) -> Vec<DirectiveWrapper> {
    let mut out = Vec::with_capacity(output.ops.len());
    for op in &output.ops {
        match op {
            PluginOp::Keep(i) => out.push(input[*i].clone()),
            PluginOp::Modify(_, w) | PluginOp::Insert(w) => out.push(w.clone()),
            PluginOp::Delete(_) => {}
        }
    }
    out
}

/// Increment a date string by one day.
/// Returns None if the date format is invalid.
pub fn increment_date(date: &str) -> Option<String> {
    let parts: Vec<&str> = date.split('-').collect();
    if parts.len() != 3 {
        return None;
    }

    let year: i32 = parts[0].parse().ok()?;
    let month: u32 = parts[1].parse().ok()?;
    let day: u32 = parts[2].parse().ok()?;

    // Simple date increment (handles month/year rollovers)
    let days_in_month = match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 => {
            if year % 4 == 0 && (year % 100 != 0 || year % 400 == 0) {
                29
            } else {
                28
            }
        }
        _ => return None,
    };

    let (new_year, new_month, new_day) = if day < days_in_month {
        (year, month, day + 1)
    } else if month < 12 {
        (year, month + 1, 1)
    } else {
        (year + 1, 1, 1)
    };

    Some(format!("{new_year:04}-{new_month:02}-{new_day:02}"))
}

/// `error` located at `wrapper`'s source line, as beancount locates a
/// plugin error at an entry's `meta` (left unlocated when the entry has
/// none, such as one a plugin inserted).
#[must_use]
pub fn at_entry(
    error: crate::types::PluginError,
    wrapper: &crate::types::DirectiveWrapper,
) -> crate::types::PluginError {
    match (&wrapper.filename, wrapper.lineno) {
        (Some(file), Some(line)) => error.at(file.clone(), line),
        _ => error,
    }
}

/// Whether `regex` matches at the start of `text`, as Python's
/// `re.match` does (it need not match to the end).
#[must_use]
pub fn python_match(regex: &regex::Regex, text: &str) -> bool {
    regex.find(text).is_some_and(|m| m.start() == 0)
}

/// Compile `pattern`, a Python regular expression, for [`python_match`].
///
/// It is read as Python's `re` reads it (see [`super::py_regex`]) and
/// anchored at the start, so the first match found is the one at the start
/// if there is one.
///
/// # Errors
///
/// The pattern is not a valid Python regular expression, or uses a construct
/// rledger cannot express.
pub fn python_match_regex(pattern: &str) -> Result<regex::Regex, super::py_regex::PyRegexError> {
    super::py_regex::compile_match(pattern)
}

#[cfg(test)]
mod falsy_tests {
    use super::falsy;
    use crate::types::{AmountData, MetaValueData};

    /// Python truthiness of a metadata value, as beancount reads one: an
    /// amount is falsy when its number is zero (`Amount.__bool__`).
    #[test]
    fn falsy_follows_python_truthiness() {
        let amount = |n: &str| {
            MetaValueData::Amount(AmountData {
                number: n.to_string(),
                currency: "USD".to_string(),
            })
        };
        assert!(falsy(&amount("0")));
        assert!(falsy(&amount("0.00")));
        assert!(!falsy(&amount("1")));
        assert!(falsy(&MetaValueData::Bool(false)));
        assert!(falsy(&MetaValueData::String(String::new())));
        assert!(falsy(&MetaValueData::Number("0".to_string())));
        assert!(!falsy(&MetaValueData::String("yes".to_string())));
        assert!(!falsy(&MetaValueData::Date("2024-01-01".to_string())));
    }
}
