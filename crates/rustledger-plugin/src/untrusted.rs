//! Text from a plugin or importer, made safe to show.
//!
//! WASM and Python plugins and WASM importers are the untrusted party:
//! their messages, the source locations they claim, the names they give
//! themselves and what they print reach the user's terminal, a CI log,
//! or a service's web page. Raw, a control character there is an attack
//! on the reader: `ESC [ 2 J` clears the screen, an OSC sequence retitles
//! the terminal or writes the clipboard, a carriage return overwrites a
//! line already shown (#2500's second review). These functions escape
//! every control character (C0, DEL and C1, so a lone `\r` too) as
//! `\u{..}`, so the text reads the same and can do nothing. They also
//! escape the bidirectional embedding, override and isolate characters
//! (U+202A–U+202E, U+2066–U+2069), which reorder how the rest of a line is
//! shown ("Trojan Source"), and the Unicode line and paragraph separators
//! (U+2028, U+2029), which some renderers break lines on. Other text,
//! including right-to-left scripts and zero-width characters, is left as
//! it is: it can mislead only as any text can.
//!
//! Strings from the ledger itself (narrations, payees, metadata, comments)
//! get the same treatment on human-readable output (#2538): a ledger can be
//! shared, included from elsewhere, or imported from a bank's data, where a
//! merchant name is partly the merchant's to choose. Query tables, `report`
//! text and `check` diagnostics escape them with these functions; output
//! that is data (CSV, JSON values, `PRINT`, `rledger format`) keeps them as
//! they are.

use std::borrow::Cow;
use std::fmt::Write;

/// Whether `c` can change how text around it is shown.
///
/// That is a control character (C0, DEL, C1), a bidirectional embedding,
/// override or isolate, or a Unicode line or paragraph separator: the
/// characters these functions escape (each keeps some of them, as its
/// documentation says).
///
/// Defined once, in [`rustledger_core::format::is_display_unsafe`], which
/// JSON output escapes by too.
#[must_use]
pub fn is_unsafe(c: char) -> bool {
    rustledger_core::format::is_display_unsafe(c)
}

fn escape(text: &str, keep: impl Fn(char) -> bool) -> Cow<'_, str> {
    if !text.chars().any(|c| is_unsafe(c) && !keep(c)) {
        return Cow::Borrowed(text);
    }
    let mut out = String::with_capacity(text.len() + 8);
    for c in text.chars() {
        if is_unsafe(c) && !keep(c) {
            let _ = write!(out, "\\u{{{:x}}}", u32::from(c));
        } else {
            out.push(c);
        }
    }
    Cow::Owned(out)
}

/// A plugin's message, or what it printed: every control character
/// escaped except newline and tab, which keep a traceback readable.
#[must_use]
pub fn escape_untrusted_text(text: &str) -> Cow<'_, str> {
    escape(text, |c| c == '\n' || c == '\t')
}

/// A one-line value from a plugin (a file name it claims, its name): every
/// control character escaped, newlines included.
#[must_use]
pub fn escape_untrusted_line(text: &str) -> Cow<'_, str> {
    escape(text, |_| false)
}

/// Source text for a diagnostic snippet, escaped like
/// [`escape_untrusted_text`] but also keeping `\r`, which the snippet
/// renderer reads as a line terminator (`\r\n` files), not as a character
/// to show.
///
/// Escaping lengthens the text, so the result also maps a byte offset into
/// `text` to the offset of the same character in the escaped text, for the
/// spans that point into it.
#[must_use]
pub fn escape_untrusted_source(text: &str) -> EscapedSource<'_> {
    let keep = |c: char| matches!(c, '\n' | '\t' | '\r');
    let mut grown = Vec::new();
    let mut extra = 0;
    for (offset, c) in text.char_indices() {
        if is_unsafe(c) && !keep(c) {
            extra += escaped_len(c) - c.len_utf8();
            grown.push((offset, extra));
        }
    }
    EscapedSource {
        text: escape(text, keep),
        grown,
    }
}

/// The length of `c` escaped as `\u{..}`.
fn escaped_len(c: char) -> usize {
    // `\u{` + the hex digits + `}`.
    let digits = (32 - u32::from(c).leading_zeros()).div_ceil(4).max(1) as usize;
    digits + 4
}

/// Text escaped by [`escape_untrusted_source`], with the offset map.
#[derive(Debug)]
pub struct EscapedSource<'a> {
    /// The escaped text.
    pub text: Cow<'a, str>,
    /// For each escaped character, its byte offset in the input and the
    /// bytes the escaping added up to and including it.
    grown: Vec<(usize, usize)>,
}

impl EscapedSource<'_> {
    /// The same, owning its text.
    #[must_use]
    pub fn into_owned(self) -> EscapedSource<'static> {
        EscapedSource {
            text: Cow::Owned(self.text.into_owned()),
            grown: self.grown,
        }
    }

    /// The offset in [`Self::text`] of what is at `offset` in the input. An
    /// offset at an escaped character maps to the start of its escape, so a
    /// span over the character covers the whole escape.
    #[must_use]
    pub fn offset(&self, offset: usize) -> usize {
        let before = self.grown.partition_point(|&(at, _)| at < offset);
        offset + before.checked_sub(1).map_or(0, |i| self.grown[i].1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_escaping_keeps_line_terminators_and_maps_offsets() {
        let text = "a\u{1b}[2Jb\r\nc\u{9b}d\te";
        let escaped = escape_untrusted_source(text);
        assert_eq!(escaped.text, "a\\u{1b}[2Jb\r\nc\\u{9b}d\te");
        // Every character of the input lands on the same character after
        // escaping; an escaped one on the start of its escape.
        for (offset, c) in text.char_indices() {
            let at = escaped.offset(offset);
            if is_unsafe(c) && !matches!(c, '\r' | '\n' | '\t') {
                assert!(escaped.text[at..].starts_with("\\u{"), "{offset}");
            } else {
                assert!(escaped.text[at..].starts_with(c), "{offset}");
            }
        }
        // The end of the input maps to the end of the escaped text, so a
        // span ending there still ends at the end.
        assert_eq!(escaped.offset(text.len()), escaped.text.len());
        // Nothing to escape: the text is borrowed and offsets are unchanged.
        let plain = escape_untrusted_source("plain\r\ntext");
        assert!(matches!(plain.text, Cow::Borrowed(_)));
        assert_eq!(plain.offset(7), 7);
        // The escape lengths, one to six hex digits.
        for c in ['\u{0}', '\u{1b}', '\u{7f}', '\u{9b}', '\u{202e}'] {
            assert_eq!(
                escaped_len(c),
                escape_untrusted_line(&c.to_string()).len(),
                "{c:?}"
            );
        }
    }

    #[test]
    fn escapes_terminal_controls() {
        assert_eq!(
            escape_untrusted_text("\u{1b}[2J\u{1b}]0;pwned\u{7} ok\r\n\tnext \u{9b}1m"),
            "\\u{1b}[2J\\u{1b}]0;pwned\\u{7} ok\\u{d}\n\tnext \\u{9b}1m"
        );
        assert_eq!(escape_untrusted_line("a\nb\tc"), "a\\u{a}b\\u{9}c");
        assert!(matches!(
            escape_untrusted_text("plain ünïcode"),
            Cow::Borrowed(_)
        ));
        // Bidi overrides and isolates, and line separators, escaped;
        // right-to-left text and zero-width characters kept.
        assert_eq!(
            escape_untrusted_text("a\u{202e}b\u{2066}c\u{2028}d"),
            "a\\u{202e}b\\u{2066}c\\u{2028}d"
        );
        assert!(matches!(
            escape_untrusted_text("שלום \u{200b}x"),
            Cow::Borrowed(_)
        ));
        // Escaping is idempotent: its output has nothing left to escape,
        // so a second pass cannot double-escape.
        let once = escape_untrusted_text("\u{1b}[2J\u{9b}").into_owned();
        assert_eq!(escape_untrusted_text(&once), once);
    }
}
