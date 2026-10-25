//! Translate `Token` (with `Span`) into `(SyntaxKind, Range<usize>)`.
//!
//! The Logos lexer now emits `Token::Whitespace` as a first-class
//! token (the `#[logos(skip ...)]` attribute was removed as part of
//! the CST migration). The only piece this layer recovers is the
//! leading UTF-8 BOM — `bom::strip_leading` runs before the lexer and
//! discards it, so we re-inject a `BOM` token at offset `0..3` and
//! shift the lexer's spans by the BOM length.
//!
//! Postcondition: for every byte of `source`, exactly one emitted
//! `(SyntaxKind, Range)` entry covers it. Verified by the inline
//! `assert_tiles` cases in this module's `tests` submodule and, at
//! corpus scale, by the byte-round-trip check in
//! `crates/rustledger-parser/tests/cst_baseline.rs`.

use std::ops::Range;

use crate::bom::strip_leading;
use crate::cst::syntax_kind::SyntaxKind;
use crate::logos_lexer::{Token, TokenIter};

const UTF8_BOM_LEN: usize = 3;

/// Pull-based lossless `(SyntaxKind, Range)` stream: the same entries
/// [`lossless_kind_tokens`] returns, one at a time, without the
/// whole-file `Vec`. The structured parser consumes this directly so
/// neither the intermediate `(Token, Span)` vec nor the projected kind
/// vec is ever materialized (issue #2742: together they peaked at
/// ~4.3 GB on a 173 MB ledger).
pub struct KindTokenIter<'src> {
    inner: TokenIter<'src>,
    bom: Option<Range<usize>>,
    offset: usize,
}

impl<'src> KindTokenIter<'src> {
    /// Stream `(SyntaxKind, Range)` entries for `source`, covering
    /// every byte exactly once (same tiling as
    /// [`lossless_kind_tokens`]).
    pub fn new(source: &'src str) -> Self {
        let (lexer_source, had_bom) = strip_leading(source);
        Self {
            inner: TokenIter::new(lexer_source, /* keep_whitespace = */ true),
            bom: had_bom.then_some(0..UTF8_BOM_LEN),
            offset: if had_bom { UTF8_BOM_LEN } else { 0 },
        }
    }
}

impl Iterator for KindTokenIter<'_> {
    type Item = (SyntaxKind, Range<usize>);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(bom) = self.bom.take() {
            return Some((SyntaxKind::BOM, bom));
        }
        let (token, span) = self.inner.next()?;
        let start = span.start + self.offset;
        let end = span.end + self.offset;
        Some((map_kind(&token), start..end))
    }
}

/// Tokenize `source` losslessly and emit `(SyntaxKind, Range)` entries
/// covering every byte exactly once.
#[must_use]
pub fn lossless_kind_tokens(source: &str) -> Vec<(SyntaxKind, Range<usize>)> {
    // Pre-size (~4 bytes per token) to avoid reallocation churn — profiling
    // flagged this as the 2nd-largest lexer allocation. Capped (like
    // `tokenize_inner`) so a pathological input can't over-reserve. See
    // `crate::logos_lexer::{tokenize_inner, TOKEN_CAPACITY_CAP}`.
    let mut out: Vec<(SyntaxKind, Range<usize>)> =
        Vec::with_capacity((source.len() / 4).min(crate::logos_lexer::TOKEN_CAPACITY_CAP));
    out.extend(KindTokenIter::new(source));
    out
}

/// Map a lexer `Token` variant to its CST `SyntaxKind`. 1:1 mapping;
/// token payloads (`&str` arguments) are not consulted — the CST
/// carries bytes via the range, not via the variant payload.
const fn map_kind(token: &Token<'_>) -> SyntaxKind {
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
        Token::Whitespace(_) => SyntaxKind::WHITESPACE,
        Token::Newline => SyntaxKind::NEWLINE,
        Token::Comment(_) => SyntaxKind::COMMENT,
        Token::PercentComment(_) => SyntaxKind::PERCENT_COMMENT,
        Token::Shebang(_) => SyntaxKind::SHEBANG,
        Token::EmacsDirective(_) => SyntaxKind::EMACS_DIRECTIVE,

        // Indent/DeepIndent are post-processing artifacts from the
        // AST-style `tokenize` — they shouldn't appear in the
        // lossless stream because `tokenize_lossless` keeps the raw
        // Whitespace tokens instead of computing indent levels. If
        // one ever does appear, classify it as Whitespace.
        Token::Indent(_) | Token::DeepIndent(_) => SyntaxKind::WHITESPACE,

        // Errors
        Token::Error(_) => SyntaxKind::ERROR_TOKEN,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Tile-and-cover property: emitted ranges cover `[0, source.len())`
    /// with no gaps and no overlaps.
    fn assert_tiles(source: &str, entries: &[(SyntaxKind, Range<usize>)]) {
        let mut cursor = 0usize;
        for (i, (_kind, range)) in entries.iter().enumerate() {
            assert_eq!(
                range.start, cursor,
                "entry {i} starts at {} but cursor is {cursor}",
                range.start,
            );
            assert!(range.end >= range.start, "entry {i}: end < start");
            cursor = range.end;
        }
        assert_eq!(
            cursor,
            source.len(),
            "entries cover {cursor} of {} bytes",
            source.len(),
        );
    }

    #[test]
    fn empty_source() {
        let entries = lossless_kind_tokens("");
        assert!(entries.is_empty());
        assert_tiles("", &entries);
    }

    #[test]
    fn whitespace_only() {
        let source = "    \t  ";
        let entries = lossless_kind_tokens(source);
        assert_tiles(source, &entries);
        assert!(
            entries.iter().all(|(k, _)| *k == SyntaxKind::WHITESPACE),
            "whitespace-only source should produce only WHITESPACE tokens",
        );
    }

    #[test]
    fn bom_recovered_as_first_token() {
        let source = "\u{FEFF}2024-01-01 open Assets:Bank\n";
        let entries = lossless_kind_tokens(source);
        assert_eq!(entries[0].0, SyntaxKind::BOM);
        assert_eq!(entries[0].1, 0..UTF8_BOM_LEN);
        assert_tiles(source, &entries);
    }

    #[test]
    fn directive_tiles_source() {
        let source = "2024-01-01 open Assets:Bank USD\n2024-01-15 * \"Coffee\"\n  Assets:Bank  -5.00 USD\n  Expenses:Food\n";
        let entries = lossless_kind_tokens(source);
        assert_tiles(source, &entries);
        let reconstructed: String = entries.iter().map(|(_, r)| &source[r.clone()]).collect();
        assert_eq!(reconstructed, source);
    }
}
