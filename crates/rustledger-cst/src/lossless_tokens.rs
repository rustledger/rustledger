//! Trivia-preserving adapter over the existing Logos lexer.
//!
//! The existing `rustledger_parser::logos_lexer::tokenize` returns
//! `Vec<(Token, Span)>` where:
//!
//! - Content tokens (Date, String, Account, ...) carry real source
//!   bytes via their span.
//! - Some trivia (`Newline`, `Comment`, `PercentComment`, `Shebang`,
//!   `EmacsDirective`, `Indent`, `DeepIndent`) are first-class tokens with
//!   real spans.
//! - **Horizontal whitespace between content tokens is silently
//!   dropped** via the lexer's `#[logos(skip r"[ \t]+")]` attribute.
//! - **The leading UTF-8 BOM is stripped pre-lexer** in
//!   `rustledger_parser::bom::strip_leading` and never seen by the
//!   lexer.
//!
//! This adapter recovers both gaps. The principle: for every byte of
//! `source` in `[0, source.len())`, there is exactly one emitted
//! `(SyntaxKind, Range<usize>)` covering it. Concatenating the
//! covered slices in order reproduces `source` byte-for-byte.
//!
//! See the lexer audit notes in #1262's Phase 1 PR for why this
//! approach was chosen over modifying the existing lexer.

use std::ops::Range;

use rustledger_parser::bom::strip_leading;
use rustledger_parser::logos_lexer::{Token, tokenize};

use crate::syntax_kind::SyntaxKind;

/// UTF-8 byte sequence for the byte-order mark (`U+FEFF`).
const UTF8_BOM_LEN: usize = 3;

/// Tokenize `source` losslessly: every byte of input is covered by
/// exactly one emitted `(SyntaxKind, Range<usize>)`, in source order.
///
/// Reuses `rustledger_parser::logos_lexer::tokenize` for the heavy
/// lifting (literal recognition, post-processing of indent and
/// line-start `#` comments) and adds:
///
/// - A synthetic `BOM` token at `0..3` when the source starts with
///   the UTF-8 byte-order mark. The production parser strips the BOM
///   at the `parse()` boundary BEFORE calling `tokenize`; doing the
///   same here keeps the lexer's mid-file-BOM error path intact while
///   recovering the leading BOM as a first-class token. The
///   lexer-returned spans are shifted by `+UTF8_BOM_LEN` so they
///   reference the ORIGINAL (BOM-included) source bytes.
/// - Synthetic `WHITESPACE` tokens covering every byte gap between
///   consecutive lexer-emitted token spans (the lexer drops mid-line
///   `[ \t]+` via `#[logos(skip ...)]`).
///
/// The returned vector is the token stream that
/// [`crate::parse_flat`] feeds into a `GreenNodeBuilder`.
#[must_use]
pub fn lossless_tokens(source: &str) -> Vec<(SyntaxKind, Range<usize>)> {
    let mut out: Vec<(SyntaxKind, Range<usize>)> = Vec::new();
    let mut cursor = 0usize;

    // Strip the BOM (if any) the same way the production parser
    // does, then emit a synthetic BOM token at offset 0..3 and shift
    // the lexer's spans by the BOM length so they reference the
    // original source's byte offsets.
    let (lexer_source, had_bom) = strip_leading(source);
    let offset = if had_bom {
        out.push((SyntaxKind::BOM, 0..UTF8_BOM_LEN));
        cursor = UTF8_BOM_LEN;
        UTF8_BOM_LEN
    } else {
        0
    };

    for (token, span) in tokenize(lexer_source) {
        let start = span.start + offset;
        let end = span.end + offset;

        // Two reasons `start` could lag `cursor` ≠ 0:
        //
        // - The skipped horizontal whitespace this adapter exists for
        //   (start > cursor). Emit a WHITESPACE filler.
        // - The lexer post-processes line-start `#` comments by
        //   FAST-FORWARDING through other tokens until the next
        //   newline, then emitting the entire line as one Comment.
        //   Subsequent tokens (the `Newline` after the comment) have
        //   `start == cursor`, so no gap. Nothing to do.
        if start > cursor {
            out.push((SyntaxKind::WHITESPACE, cursor..start));
        }

        // Defensive: the lexer should never emit a token whose start
        // precedes the previous token's end. If it ever does (e.g., a
        // future post-processing rewrite of spans), the assertion
        // surfaces the bug instead of silently producing duplicate
        // bytes in the round-trip.
        debug_assert!(
            start >= cursor,
            "tokenize emitted an out-of-order span: cursor={cursor}, token_start={start}",
        );

        out.push((map_token_kind(&token), start..end));
        cursor = end;
    }

    // Trailing bytes (e.g., a file that doesn't end with a newline
    // and finishes mid-whitespace, or any future tokenize quirk). The
    // round-trip contract — "every input byte is covered by exactly
    // one output entry" — requires us to emit something for them.
    if cursor < source.len() {
        out.push((SyntaxKind::WHITESPACE, cursor..source.len()));
    }

    out
}

/// Map a `rustledger_parser::logos_lexer::Token` variant to its
/// `SyntaxKind`. The mapping is 1:1 for content/keyword/punctuation
/// tokens and forwards trivia (`Newline`, `Comment`, ...) to their
/// dedicated `SyntaxKind` variants.
///
/// Token payloads (the `&str` arguments of `Date`, `Number`, ...) are
/// not consulted — phase 1's lossless tokens carry source bytes via
/// spans, not via the variant payload.
#[allow(clippy::too_many_lines)]
const fn map_token_kind(token: &Token<'_>) -> SyntaxKind {
    match token {
        // Literals
        Token::Date(_) => SyntaxKind::DATE,
        Token::Number(_) => SyntaxKind::NUMBER,
        Token::String(_) => SyntaxKind::STRING,
        Token::Account(_) => SyntaxKind::ACCOUNT,
        Token::Currency(_) => SyntaxKind::CURRENCY,
        Token::Tag(_) => SyntaxKind::TAG,
        Token::Link(_) => SyntaxKind::LINK,
        Token::MetaKey(_) => SyntaxKind::META_KEY,
        Token::Flag(_) => SyntaxKind::FLAG,
        Token::True => SyntaxKind::BOOL_TRUE,
        Token::False => SyntaxKind::BOOL_FALSE,
        Token::Null => SyntaxKind::NULL_KW,

        // Keywords
        Token::Txn => SyntaxKind::TXN_KW,
        Token::Balance => SyntaxKind::BALANCE_KW,
        Token::Open => SyntaxKind::OPEN_KW,
        Token::Close => SyntaxKind::CLOSE_KW,
        Token::Commodity => SyntaxKind::COMMODITY_KW,
        Token::Pad => SyntaxKind::PAD_KW,
        Token::Event => SyntaxKind::EVENT_KW,
        Token::Query => SyntaxKind::QUERY_KW,
        Token::Note => SyntaxKind::NOTE_KW,
        Token::Document => SyntaxKind::DOCUMENT_KW,
        Token::Price => SyntaxKind::PRICE_KW,
        Token::Custom => SyntaxKind::CUSTOM_KW,
        Token::Option_ => SyntaxKind::OPTION_KW,
        Token::Include => SyntaxKind::INCLUDE_KW,
        Token::Plugin => SyntaxKind::PLUGIN_KW,
        Token::Pushtag => SyntaxKind::PUSHTAG_KW,
        Token::Poptag => SyntaxKind::POPTAG_KW,
        Token::Pushmeta => SyntaxKind::PUSHMETA_KW,
        Token::Popmeta => SyntaxKind::POPMETA_KW,
        Token::Pending => SyntaxKind::PENDING_KW,

        // Punctuation
        Token::LBrace => SyntaxKind::L_BRACE,
        Token::RBrace => SyntaxKind::R_BRACE,
        Token::LDoubleBrace => SyntaxKind::L_DOUBLE_BRACE,
        Token::RDoubleBrace => SyntaxKind::R_DOUBLE_BRACE,
        Token::LBraceHash => SyntaxKind::L_BRACE_HASH,
        Token::LParen => SyntaxKind::L_PAREN,
        Token::RParen => SyntaxKind::R_PAREN,
        Token::At => SyntaxKind::AT,
        Token::AtAt => SyntaxKind::AT_AT,
        Token::Colon => SyntaxKind::COLON,
        Token::Comma => SyntaxKind::COMMA,
        Token::Tilde => SyntaxKind::TILDE,
        Token::Pipe => SyntaxKind::PIPE,
        Token::Plus => SyntaxKind::PLUS,
        Token::Minus => SyntaxKind::MINUS,
        Token::Star => SyntaxKind::STAR,
        Token::Slash => SyntaxKind::SLASH,
        Token::Hash => SyntaxKind::HASH,

        // Trivia
        Token::Newline => SyntaxKind::NEWLINE,
        Token::Comment(_) => SyntaxKind::COMMENT,
        Token::PercentComment(_) => SyntaxKind::PERCENT_COMMENT,
        Token::Shebang(_) => SyntaxKind::SHEBANG,
        Token::EmacsDirective(_) => SyntaxKind::EMACS_DIRECTIVE,
        Token::Indent(_) => SyntaxKind::INDENT,
        Token::DeepIndent(_) => SyntaxKind::DEEP_INDENT,

        // Errors
        Token::Error(_) => SyntaxKind::ERROR_TOKEN,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Covering-and-disjoint property: for every byte of source, there
    /// is exactly one emitted `(kind, range)` whose range contains it.
    /// The simplest way to assert this is to walk the emitted entries
    /// and verify they tile `[0, source.len())` with no overlap.
    fn assert_tiles_source(source: &str, entries: &[(SyntaxKind, Range<usize>)]) {
        let mut cursor = 0usize;
        for (i, (_kind, range)) in entries.iter().enumerate() {
            assert_eq!(
                range.start, cursor,
                "entry {i} starts at {} but cursor is {cursor} (gap or overlap)",
                range.start,
            );
            assert!(
                range.end >= range.start,
                "entry {i} has end < start: {range:?}",
            );
            cursor = range.end;
        }
        assert_eq!(
            cursor,
            source.len(),
            "entries don't cover the full source (covered {cursor} of {} bytes)",
            source.len(),
        );
    }

    #[test]
    fn empty_source_tiles_trivially() {
        let entries = lossless_tokens("");
        assert!(entries.is_empty());
        assert_tiles_source("", &entries);
    }

    #[test]
    fn whitespace_only_source_is_filled() {
        let source = "    \t  ";
        let entries = lossless_tokens(source);
        // The lexer emits nothing for whitespace-only input; the
        // trailing-bytes case covers everything as one WHITESPACE.
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].0, SyntaxKind::WHITESPACE);
        assert_tiles_source(source, &entries);
    }

    #[test]
    fn bom_is_recovered_as_first_token() {
        let source = "\u{FEFF}2024-01-01 open Assets:Bank\n";
        let entries = lossless_tokens(source);
        assert_eq!(entries[0].0, SyntaxKind::BOM);
        assert_eq!(entries[0].1, 0..UTF8_BOM_LEN);
        assert_tiles_source(source, &entries);
    }

    #[test]
    fn horizontal_whitespace_between_tokens_is_recovered() {
        // The `tokenize` lexer skips the spaces between Date, Open,
        // Account. Lossless adapter must recover them.
        let source = "2024-01-01 open Assets:Bank\n";
        let entries = lossless_tokens(source);
        assert_tiles_source(source, &entries);
        // Sanity: at least one WHITESPACE entry exists.
        assert!(entries.iter().any(|(k, _)| *k == SyntaxKind::WHITESPACE));
    }

    #[test]
    fn full_directive_tiles_source() {
        let source = "\
2024-01-01 open Assets:Bank USD
2024-01-15 * \"Coffee\"
  Assets:Bank  -5.00 USD
  Expenses:Food
";
        let entries = lossless_tokens(source);
        assert_tiles_source(source, &entries);
        // And the concatenation reproduces the source.
        let reconstructed: String = entries
            .iter()
            .map(|(_kind, range)| &source[range.clone()])
            .collect();
        assert_eq!(reconstructed, source);
    }

    #[test]
    fn line_comment_keeps_its_own_span() {
        let source = "; preamble\n2024-01-01 open Assets:Bank\n";
        let entries = lossless_tokens(source);
        assert_eq!(entries[0].0, SyntaxKind::COMMENT);
        assert_tiles_source(source, &entries);
    }
}
