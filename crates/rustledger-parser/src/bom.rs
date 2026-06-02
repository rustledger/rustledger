//! Canonical UTF-8 BOM handling — single source of truth.
//!
//! # Why this module exists
//!
//! Earlier iterations spread BOM-aware logic across three layers:
//!
//! 1. A `bom_filter` callback on the lexer that decided which BOMs were
//!    "leading" (skip) vs. "mid-file" (emit as an error token).
//! 2. An indent-walker arm in `tokenize()` that tried to keep mid-file
//!    BOMs layout-transparent by adjusting `last_newline_end`.
//! 3. A `source.starts_with('\u{FEFF}')` check in `format_source` to
//!    decide whether to re-prepend a BOM on output.
//!
//! Each of those three encoded the same concept ("the source had a
//! leading BOM") with a different predicate. Every round-trip-fidelity
//! bug we hit traced back to two of them disagreeing — most recently a
//! pair of regressions where the lexer accepted a leading-whitespace-
//! then-BOM input but the formatter dropped the BOM on output.
//!
//! # The architecture
//!
//! A UTF-8 BOM is a *serialization* concern, not a *parsing* concern.
//! It carries no semantic meaning to beancount. So:
//!
//! * `strip_leading` runs ONCE at the parser's public entry. The lexer,
//!   parser, indent walker, and every other internal layer operate on a
//!   source that is BOM-free by construction.
//! * The parser records whether a BOM was stripped in
//!   `ParseResult::has_leading_bom`. That flag is the *only* source of
//!   truth downstream. No layer inspects the BOM byte directly.
//! * `restore_leading` runs ONCE at the formatter's public exit, gated
//!   on the flag, restoring byte-stable round-trip identity.
//!
//! # Mid-file BOMs
//!
//! Because the leading BOM is stripped before lexing, any U+FEFF byte
//! the lexer encounters is by construction mid-file and unrecognized.
//! Logos produces a `Token::Error` for it, and the parser's existing
//! error classifier (`error_text.contains('\u{FEFF}')`) surfaces the
//! dedicated diagnostic.
//!
//! # Span coordinates
//!
//! The parser preserves the *original-source* coordinate frame for all
//! spans it returns: if a directive starts at byte 3 of the original
//! source (because the file began with a 3-byte BOM), its span starts
//! at 3. The parser shifts every span up by `BOM_LEN` after running the
//! inner parser on the stripped source. Callers (LSP, FFI, doctor) see
//! coordinates that index into the source they passed in, with no need
//! to be BOM-aware themselves.

/// The UTF-8 byte-order mark (`EF BB BF`).
pub const BOM: &str = "\u{FEFF}";

/// The same BOM as a `char`.
///
/// Use this for `char`-typed predicates like `s.contains(BOM_CHAR)`
/// or `match c { BOM_CHAR => ... }` instead of open-coding
/// `'\u{FEFF}'` — that scatters the BOM concept across every
/// detection site and re-creates the contract drift this module
/// exists to prevent.
pub const BOM_CHAR: char = '\u{FEFF}';

/// Byte length of [`BOM`] in UTF-8 (always 3).
///
/// Used by `parse()` to shift spans back into the original-source
/// coordinate frame after running the inner parser on the
/// BOM-stripped view. Inlined as a const so the compiler can constant-
/// fold the shift arithmetic.
pub const BOM_LEN: usize = BOM.len();

/// Strip a strict-byte-0 leading BOM, returning `(stripped, had_bom)`.
///
/// "Strict byte 0" means the BOM must be the very first bytes of the
/// source. A BOM preceded by ANY content (whitespace, another
/// character, anything) is by definition mid-file and is left in place
/// for the lexer's error path to surface — that's not a "leading BOM"
/// no matter how innocuous the preceding bytes look.
///
/// ```
/// # use rustledger_parser::bom::{strip_leading, BOM};
/// let with_bom = format!("{BOM}2024-01-01 open Assets:Bank\n");
/// let (stripped, had_bom) = strip_leading(&with_bom);
/// assert!(had_bom);
/// assert_eq!(stripped, "2024-01-01 open Assets:Bank\n");
///
/// let (stripped, had_bom) = strip_leading("2024-01-01 open Assets:Bank\n");
/// assert!(!had_bom);
/// assert_eq!(stripped, "2024-01-01 open Assets:Bank\n");
/// ```
#[must_use]
pub fn strip_leading(source: &str) -> (&str, bool) {
    source
        .strip_prefix(BOM)
        .map_or((source, false), |rest| (rest, true))
}

/// Re-prepend a leading BOM if `had_bom`. Idempotent: a call where
/// `formatted` already starts with a BOM returns the input unchanged.
///
/// Takes and returns an owned `String` so the no-BOM path (the
/// overwhelming majority of files) returns the input with zero
/// reallocation and zero byte copies.
///
/// The BOM-prepend path is one allocation (guaranteed by the explicit
/// `reserve(BOM_LEN)` before `insert_str`) plus an O(n) memmove of the
/// existing bytes by 3 positions. Without the explicit reserve,
/// `format_source`'s typically-tight-capacity `String` would force
/// `insert_str` to grow the buffer first AND THEN shift — two passes
/// over the bytes instead of one.
///
/// ```
/// # use rustledger_parser::bom::{restore_leading, BOM};
/// let body = "2024-01-01 open Assets:Bank\n".to_string();
///
/// // No BOM requested → return as-is.
/// let out = restore_leading(body.clone(), false);
/// assert_eq!(out, body);
///
/// // BOM requested and not present → prepend.
/// let out = restore_leading(body.clone(), true);
/// assert!(out.starts_with(BOM));
/// assert_eq!(&out[BOM.len()..], body);
///
/// // BOM requested and already present → idempotent no-op.
/// let with_bom = format!("{BOM}{body}");
/// let out = restore_leading(with_bom.clone(), true);
/// assert_eq!(out, with_bom);
/// ```
#[must_use]
pub fn restore_leading(mut formatted: String, had_bom: bool) -> String {
    if had_bom && !formatted.starts_with(BOM) {
        formatted.reserve(BOM_LEN);
        formatted.insert_str(0, BOM);
    }
    formatted
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bom_len_matches_utf8_encoding() {
        assert_eq!(BOM_LEN, 3);
        assert_eq!(BOM.as_bytes(), &[0xEF, 0xBB, 0xBF]);
    }

    #[test]
    fn strip_leading_strict_byte_0() {
        // BOM at byte 0 → stripped.
        let s = "\u{FEFF}foo";
        let (out, had) = strip_leading(s);
        assert_eq!(out, "foo");
        assert!(had);
    }

    #[test]
    fn strip_leading_no_bom_passthrough() {
        let s = "foo";
        let (out, had) = strip_leading(s);
        assert_eq!(out, "foo");
        assert!(!had);
    }

    #[test]
    fn strip_leading_does_not_match_after_whitespace() {
        // The clipboard-with-padding case we deliberately do NOT treat
        // as a leading BOM — it's mid-file by strict definition. The
        // lexer's error path will surface the U+FEFF byte.
        let s = " \u{FEFF}foo";
        let (out, had) = strip_leading(s);
        assert_eq!(out, s);
        assert!(!had);
    }

    #[test]
    fn strip_leading_only_strips_one_bom() {
        // Double BOM at byte 0: strip the first, leave the second for
        // the lexer to flag as mid-file.
        let s = "\u{FEFF}\u{FEFF}foo";
        let (out, had) = strip_leading(s);
        assert_eq!(out, "\u{FEFF}foo");
        assert!(had);
    }

    #[test]
    fn restore_leading_idempotent_when_already_present() {
        let s = "\u{FEFF}foo".to_string();
        let out = restore_leading(s.clone(), true);
        assert_eq!(out, s);
    }

    #[test]
    fn restore_leading_noop_when_flag_false() {
        let s = "foo".to_string();
        let out = restore_leading(s.clone(), false);
        assert_eq!(out, s);
    }

    #[test]
    fn restore_leading_prepends_when_requested() {
        let s = "foo".to_string();
        let out = restore_leading(s, true);
        assert_eq!(out, "\u{FEFF}foo");
    }

    #[test]
    fn strip_then_restore_round_trip() {
        for input in [
            "\u{FEFF}2024-01-01 open Assets:Bank USD\n",
            "2024-01-01 open Assets:Bank USD\n",
            "\u{FEFF}",
            "",
        ] {
            let (stripped, had) = strip_leading(input);
            let restored = restore_leading(stripped.to_string(), had);
            assert_eq!(restored, input, "round trip broke for {input:?}");
        }
    }
}
