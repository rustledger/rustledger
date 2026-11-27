//! Bytes that are not UTF-8, reported where beancount reports them.
//!
//! A file is decoded lossily ([`SourceText::from_utf8_lossy`]), so the parser
//! always has text and never panics, and each invalid sequence is a U+FFFD
//! whose place is remembered. beancount 3.2.3 decides by where the bytes are:
//!
//! - in a comment, nothing: its lexer skips a comment's bytes unread;
//! - in a string literal, `UnicodeDecodeError: 'utf-8' codec can't decode
//!   ...`, one error per string, on the line the string ENDS on (the lexer's
//!   line once it has read the closing quote);
//! - anywhere else, `Invalid token: '\xe9'`, one per run of invalid bytes.
//!
//! rledger reports the same, as parse errors (`P0012`). It used to accept
//! them all silently, so a Latin-1 file loaded here with every `é` turned
//! into U+FFFD, and failed in beancount.

use crate::SourceText;
use rustledger_parser::logos_lexer::{Token, tokenize};
use rustledger_parser::{ParseError, ParseErrorKind, Span};

/// The parse errors for the invalid UTF-8 in `source`, in source order.
/// Empty, at no cost, for a file that was valid UTF-8.
pub fn invalid_utf8_errors(source: &SourceText) -> Vec<ParseError> {
    let invalid = source.invalid_utf8();
    if invalid.is_empty() {
        return Vec::new();
    }
    let text = source.as_str();
    let tokens = tokenize(text);
    let mut errors = Vec::new();
    // The last string reported, so a string with several bad bytes is
    // reported once, as beancount reports it.
    let mut reported_string: Option<usize> = None;
    let mut i = 0;
    while i < invalid.len() {
        let range = invalid[i].clone();
        // The token holding the replacement, if any. Tokens are in source
        // order and do not overlap.
        let at = tokens.partition_point(|(_, span)| span.end <= range.start);
        let token = tokens
            .get(at)
            .filter(|(_, span)| (span.start..span.end).contains(&range.start));
        match token {
            // Skipped unread by beancount's lexer. So is a line it ignores,
            // which no token covers.
            Some((Token::Comment(_) | Token::PercentComment(_), _)) | None => i += 1,
            Some((Token::String(_), span)) => {
                if reported_string != Some(span.start) {
                    reported_string = Some(span.start);
                    // On the closing quote: beancount reports the string on
                    // the line it ends on.
                    let end = span.end.max(span.start + 1);
                    errors.push(
                        ParseError::new(
                            ParseErrorKind::SyntaxError(
                                "a string holds bytes that are not UTF-8, which beancount \
                             cannot decode (UnicodeDecodeError)"
                                    .to_string(),
                            ),
                            Span::new(end - 1, end),
                        )
                        .with_hint("convert the file to UTF-8".to_string()),
                    );
                }
                i += 1;
            }
            Some(_) => {
                // One error for a run of adjacent invalid sequences, as
                // beancount reports `Invalid token: '\xe9\xe9'` once.
                let mut end = range.end;
                i += 1;
                while i < invalid.len() && invalid[i].start == end {
                    end = invalid[i].end;
                    i += 1;
                }
                errors.push(
                    ParseError::new(
                        ParseErrorKind::SyntaxError(
                            "invalid token: bytes that are not UTF-8".to_string(),
                        ),
                        Span::new(range.start, end),
                    )
                    .with_hint("convert the file to UTF-8".to_string()),
                );
            }
        }
    }
    errors
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lines(bytes: &[u8]) -> Vec<(usize, bool)> {
        let source = SourceText::from_utf8_lossy(bytes.to_vec());
        invalid_utf8_errors(&source)
            .iter()
            .map(|e| {
                let line = crate::line_col_in(source.as_str(), e.span.start).0;
                (line, e.message().contains("string"))
            })
            .collect()
    }

    /// Each shape against bean-check 3.2.3: an invalid token in an account,
    /// a currency, or a line of its own (one error for a run); one error per
    /// string, on its last line; nothing in a comment.
    #[test]
    fn test_invalid_utf8_errors_match_beancount_placement() {
        assert_eq!(
            lines(b"2020-01-01 open Assets:Zur\xe9\n2020-01-01 open Assets:B\n"),
            [(1, false)]
        );
        assert_eq!(lines(b"2020-01-01 open Assets:A US\xe9\n"), [(1, false)]);
        assert_eq!(
            lines(b"2020-01-01 open Assets:A\n\xe9\xe9\n2020-01-02 open Assets:B\n"),
            [(2, false)]
        );
        assert_eq!(
            lines(b"2020-01-01 open Assets:A\n2020-01-02 * \"a\xe9\" \"b\xe9\xe9\"\n"),
            [(2, true), (2, true)]
        );
        assert_eq!(
            lines(b"2020-01-01 open Assets:A\n2020-01-02 * \"a\nb\xe9\nc\"\n"),
            [(4, true)]
        );
        assert_eq!(
            lines(b"; zur\xe9\n2020-01-01 open Assets:A ; zur\xe9\n"),
            []
        );
        assert_eq!(
            lines("2020-01-01 open Assets:A ; \u{fffd} is fine\n".as_bytes()),
            []
        );
    }

    /// A U+FFFD written in a valid file is a character like any other.
    #[test]
    fn test_invalid_utf8_errors_ignore_a_written_replacement_character() {
        let source = SourceText::from("2020-01-01 open Assets:A\n  k: \"\u{fffd}\"\n");
        assert!(source.invalid_utf8().is_empty());
        assert!(invalid_utf8_errors(&source).is_empty());
    }
}
