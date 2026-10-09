//! Text from a plugin or importer, made safe to show.
//!
//! WASM and Python plugins and WASM importers are the untrusted party:
//! their messages, the source locations they claim, the names they give
//! themselves and what they print reach the user's terminal, a CI log,
//! or a service's web page. Raw, a control character there is an attack
//! on the reader: `ESC [ 2 J` clears the screen, an OSC sequence retitles
//! the terminal or writes the clipboard, a carriage return overwrites a
//! line already shown (#2500's second review). These functions escape
//! every control character as `\u{..}`, so the text reads the same and
//! can do nothing.
//!
//! Strings from the ledger itself (narrations, payees) are a separate
//! question: the ledger is the user's own.

use std::borrow::Cow;
use std::fmt::Write;

fn escape(text: &str, keep: impl Fn(char) -> bool) -> Cow<'_, str> {
    if !text.chars().any(|c| c.is_control() && !keep(c)) {
        return Cow::Borrowed(text);
    }
    let mut out = String::with_capacity(text.len() + 8);
    for c in text.chars() {
        if c.is_control() && !keep(c) {
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
    }
}
