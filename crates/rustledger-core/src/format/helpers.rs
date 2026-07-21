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

/// Escape a string as a JSON string body (RFC 8259).
///
/// Handles the required escapes (`"`, `\`, and every C0 control character —
/// `\n`/`\t`/`\r`/`\b`/`\f` by name, the rest as `\uXXXX`), so the result is
/// always valid between JSON double quotes. Unlike [`escape_string`] (which
/// targets beancount source and leaves control bytes other than `\n`/`\t`/`\r`
/// raw), this never emits a bare control character — use it for JSON egress of
/// user-controlled text (e.g. metadata-derived labels), which may carry an
/// arbitrary control byte the parser preserved.
#[must_use]
pub fn escape_json(s: &str) -> String {
    use std::fmt::Write;
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            '\u{08}' => out.push_str("\\b"),
            '\u{0c}' => out.push_str("\\f"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out
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
    use super::{escape_json, escape_string};

    #[test]
    fn escape_json_produces_valid_json_for_control_chars() {
        // The named escapes.
        assert_eq!(escape_json("a\"\\b"), "a\\\"\\\\b");
        assert_eq!(escape_json("x\ny\tz\r"), "x\\ny\\tz\\r");
        assert_eq!(escape_json("\u{08}\u{0c}"), "\\b\\f");
        // Other C0 control chars must become \uXXXX (escape_string leaves these
        // raw, which is invalid JSON) — this is the bug escape_json fixes.
        assert_eq!(escape_json("A\u{1b}B"), "A\\u001bB");
        assert_eq!(escape_json("\u{00}"), "\\u0000");
        // Plain text (incl. non-control unicode) is untouched.
        assert_eq!(escape_json("投資 123"), "投資 123");
    }

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
