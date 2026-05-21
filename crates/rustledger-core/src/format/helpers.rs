//! Shared helper functions for formatting.

use super::format_amount;
use crate::MetaValue;

/// Format a metadata value.
pub fn format_meta_value(value: &MetaValue) -> String {
    match value {
        MetaValue::String(s) => format!("\"{}\"", escape_string(s)),
        MetaValue::Account(a) => a.to_string(),
        MetaValue::Currency(c) => c.to_string(),
        MetaValue::Tag(t) => format!("#{t}"),
        MetaValue::Link(l) => format!("^{l}"),
        MetaValue::Date(d) => d.to_string(),
        MetaValue::Number(n) => n.to_string(),
        MetaValue::Amount(a) => format_amount(a),
        MetaValue::Bool(b) => if *b { "TRUE" } else { "FALSE" }.to_string(),
        MetaValue::None => String::new(),
    }
}

/// Escape a string for output (handle quotes and backslashes).
pub fn escape_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            _ => out.push(c),
        }
    }
    out
}
