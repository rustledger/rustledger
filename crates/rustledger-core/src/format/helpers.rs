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
            // The parser decodes `\t`/`\r` into literal tab/CR, so re-escape
            // them here rather than emitting raw control bytes inside quotes
            // (hostile to terminals/logs, and not round-trippable).
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            _ => out.push(c),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::escape_string;

    #[test]
    fn escapes_quote_backslash_and_controls() {
        assert_eq!(escape_string("a\"b"), "a\\\"b");
        assert_eq!(escape_string("a\\b"), "a\\\\b");
        assert_eq!(escape_string("a\nb"), "a\\nb");
        // The parser decodes `\t`/`\r` to literal tab/CR; Display must re-escape
        // them rather than emit raw control bytes inside the quotes.
        assert_eq!(escape_string("a\tb"), "a\\tb");
        assert_eq!(escape_string("a\rb"), "a\\rb");
    }

    #[test]
    fn leaves_plain_text_untouched() {
        assert_eq!(escape_string("plain text 123"), "plain text 123");
    }
}
