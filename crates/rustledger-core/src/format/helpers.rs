//! Shared helper functions for formatting.

use crate::MetaValue;

/// Format a metadata value.
pub fn format_meta_value(value: &MetaValue, config: &super::FormatConfig) -> String {
    match value {
        MetaValue::String(s) => format!("\"{}\"", escape_string(s)),
        MetaValue::Account(a) => a.to_string(),
        MetaValue::Currency(c) => c.to_string(),
        MetaValue::Tag(t) => format!("#{t}"),
        MetaValue::Link(l) => format!("^{l}"),
        MetaValue::Date(d) => d.to_string(),
        // Bare numbers have no currency to look precision up under —
        // they keep their own scale (same rule as interpolation
        // targets in posting rendering, #1766).
        MetaValue::Number(n) => n.to_string(),
        MetaValue::Amount(a) => super::format_amount_with(a, config),
        MetaValue::Bool(b) => if *b { "TRUE" } else { "FALSE" }.to_string(),
        MetaValue::None => String::new(),
        MetaValue::Int(i) => i.to_string(),
    }
}

/// Escape a string for CSV output (RFC-4180 style).
///
/// Values containing a comma, double quote, or line feed (`\n` — carriage
/// returns do NOT trigger quoting, matching the prior copies
/// byte-for-byte) are wrapped in double quotes with inner quotes doubled;
/// everything else passes through unchanged.
///
/// The single implementation behind every CSV surface (`rledger report
/// --format csv`, BQL CSV output) — these previously carried byte-identical
/// private copies.
#[must_use]
pub fn escape_csv(s: &str) -> String {
    if s.contains(',') || s.contains('"') || s.contains('\n') {
        format!("\"{}\"", s.replace('"', "\"\""))
    } else {
        s.to_string()
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
