//! Command implementations for CLI tools.
//!
//! Each module contains the full implementation for a command,
//! which can be invoked by thin wrapper binaries.

pub mod add_cmd;
pub mod check;
pub mod compat;
pub mod completions;
pub mod config_cmd;
pub mod doctor;
pub mod explain;
pub mod extract_cmd;
pub mod format;
pub mod lint;
pub mod loadcache;
pub mod messages;
pub mod price;
pub mod price_cmd;
pub mod query;
pub mod report_cmd;
pub mod restructure;

/// `value` as pretty-printed JSON, with DEL, the C1 controls, and the other
/// characters [`rustledger_core::format::is_display_unsafe`] names escaped as
/// `\uXXXX` (#2538).
///
/// `serde_json` escapes only what JSON requires (`"`, `\` and C0), so a
/// ledger string carrying a C1 control or a bidi override would otherwise
/// reach the terminal of whoever reads the output raw. Escaped, it decodes
/// to the same string: the output stays faithful data.
pub(crate) fn to_json_pretty<T: serde::Serialize + ?Sized>(
    value: &T,
) -> serde_json::Result<String> {
    // A raw C0 character in `serde_json`'s output is the pretty-printer's
    // own line break (it escapes every C0 inside a string), and outside
    // strings JSON is ASCII, so what is left to escape is inside a string.
    let needs_escape = |c: char| c >= '\u{7f}' && rustledger_core::format::is_display_unsafe(c);
    let json = serde_json::to_string_pretty(value)?;
    if !json.chars().any(needs_escape) {
        return Ok(json);
    }
    let mut out = String::with_capacity(json.len() + 16);
    for c in json.chars() {
        if needs_escape(c) {
            // Every such character is in the Basic Multilingual Plane.
            out.push_str(&format!("\\u{:04x}", u32::from(c)));
        } else {
            out.push(c);
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    #[test]
    fn json_output_escapes_terminal_controls_and_keeps_the_value() {
        let value = serde_json::json!({ "narration": "a\u{1b}[2Jb\u{7f}c\u{9b}d\u{202e}e\n" });
        let json = super::to_json_pretty(&value).unwrap();
        for raw in ['\u{1b}', '\u{7f}', '\u{9b}', '\u{202e}'] {
            assert!(!json.contains(raw), "{raw:?} raw in {json:?}");
        }
        assert!(
            json.contains("\\u007f") && json.contains("\\u009b"),
            "{json}"
        );
        // The same value when read back.
        let back: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(back, value);
    }
}
