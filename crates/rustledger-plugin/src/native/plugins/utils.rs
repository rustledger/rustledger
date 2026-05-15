//! Shared utility functions for native plugins.

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
