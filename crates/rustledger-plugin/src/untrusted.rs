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
//! Strings from the ledger itself (narrations, payees) are a separate
//! question: the ledger is the user's own.

use std::borrow::Cow;
use std::fmt::Write;

/// Whether `c` can change how text around it is shown.
fn is_unsafe(c: char) -> bool {
    c.is_control()
        || matches!(c, '\u{202a}'..='\u{202e}' | '\u{2066}'..='\u{2069}' | '\u{2028}' | '\u{2029}')
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

#[cfg(test)]
mod tests {
    use super::*;

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
