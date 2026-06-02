//! Parse error types.

use crate::Span;
use std::fmt;

/// A parse error with location information.
///
/// Marked `#[non_exhaustive]` so external consumers must go through
/// [`ParseError::new`] and the builder methods rather than constructing
/// via struct literal. Future fields (e.g., a suggested fix-it span,
/// related-information back-references) then land as non-breaking
/// additions. Same `SemVer` hygiene argument as `crate::ParseResult`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ParseError {
    /// The kind of error.
    pub kind: ParseErrorKind,
    /// The span where the error occurred.
    pub span: Span,
    /// Optional context message.
    pub context: Option<String>,
    /// Optional hint for fixing the error.
    pub hint: Option<String>,
}

impl ParseError {
    /// Create a new parse error.
    #[must_use]
    pub const fn new(kind: ParseErrorKind, span: Span) -> Self {
        Self {
            kind,
            span,
            context: None,
            hint: None,
        }
    }

    /// Add context to this error.
    #[must_use]
    pub fn with_context(mut self, context: impl Into<String>) -> Self {
        self.context = Some(context.into());
        self
    }

    /// Add a hint for fixing this error.
    #[must_use]
    pub fn with_hint(mut self, hint: impl Into<String>) -> Self {
        self.hint = Some(hint.into());
        self
    }

    /// Get the span of this error.
    #[must_use]
    pub const fn span(&self) -> (usize, usize) {
        (self.span.start, self.span.end)
    }

    /// Get a numeric code for the error kind.
    #[must_use]
    pub const fn kind_code(&self) -> u32 {
        match &self.kind {
            ParseErrorKind::UnexpectedChar(_) => 1,
            ParseErrorKind::UnexpectedEof => 2,
            ParseErrorKind::Expected(_) => 3,
            ParseErrorKind::InvalidDate(_) => 4,
            ParseErrorKind::InvalidNumber(_) => 5,
            ParseErrorKind::InvalidAccount(_) => 6,
            ParseErrorKind::InvalidCurrency(_) => 7,
            ParseErrorKind::UnclosedString => 8,
            ParseErrorKind::InvalidEscape(_) => 9,
            ParseErrorKind::MissingField(_) => 10,
            ParseErrorKind::IndentationError => 11,
            ParseErrorKind::SyntaxError(_) => 12,
            ParseErrorKind::MissingNewline => 13,
            ParseErrorKind::MissingAccount => 14,
            ParseErrorKind::InvalidDateValue(_) => 15,
            ParseErrorKind::MissingAmount => 16,
            ParseErrorKind::MissingCurrency => 17,
            ParseErrorKind::InvalidAccountFormat(_) => 18,
            ParseErrorKind::MissingDirective => 19,
            ParseErrorKind::InvalidPoptag(_) => 20,
            ParseErrorKind::UnclosedPushtag(_) => 21,
            ParseErrorKind::InvalidPopmeta(_) => 22,
            ParseErrorKind::UnclosedPushmeta(_) => 23,
            ParseErrorKind::DeprecatedPipeSymbol => 24,
            ParseErrorKind::InvalidBookingMethod(_) => 25,
            ParseErrorKind::BomInDirectiveBody => 26,
        }
    }

    /// Get the error message.
    #[must_use]
    pub fn message(&self) -> String {
        format!("{}", self.kind)
    }

    /// One sample `ParseErrorKind` per variant. Used by cross-crate
    /// sync tests that need a complete variant set to verify
    /// schema/test arrays stay in sync with the enum.
    ///
    /// **Single source of truth (round-19).** Pre-round-19 this
    /// function had a `sample()` helper with an exhaustive match
    /// PLUS a hand-maintained `vec![]` that called sample for each
    /// variant. Only the `sample()` match was a compile-time gate —
    /// a contributor adding a variant could update `sample()` and
    /// forget the vec, leaving the returned list silently
    /// incomplete (no compile error, no test failure unless a
    /// downstream sync test specifically required N entries).
    /// Round-19 collapsed both into this single vec literal. The
    /// compile-time enforcement now lives in the
    /// `every_kind_sample_covers_every_variant` test below, whose
    /// exhaustive `variant_index` match catches a missing variant
    /// at compile time and a missing vec entry at test time.
    ///
    /// Marked `#[doc(hidden)]` because this exists for test
    /// infrastructure only — the stable public API is `ParseError`
    /// + `ParseErrorKind` + `kind_code()`; this helper is a
    /// convenience for integration tests.
    #[doc(hidden)]
    #[must_use]
    pub fn every_kind_sample() -> Vec<ParseErrorKind> {
        vec![
            ParseErrorKind::UnexpectedChar('x'),
            ParseErrorKind::UnexpectedEof,
            ParseErrorKind::Expected(String::new()),
            ParseErrorKind::InvalidDate(String::new()),
            ParseErrorKind::InvalidNumber(String::new()),
            ParseErrorKind::InvalidAccount(String::new()),
            ParseErrorKind::InvalidCurrency(String::new()),
            ParseErrorKind::UnclosedString,
            ParseErrorKind::InvalidEscape('x'),
            ParseErrorKind::MissingField(String::new()),
            ParseErrorKind::IndentationError,
            ParseErrorKind::SyntaxError(String::new()),
            ParseErrorKind::MissingNewline,
            ParseErrorKind::MissingAccount,
            ParseErrorKind::InvalidDateValue(String::new()),
            ParseErrorKind::MissingAmount,
            ParseErrorKind::MissingCurrency,
            ParseErrorKind::InvalidAccountFormat(String::new()),
            ParseErrorKind::MissingDirective,
            ParseErrorKind::InvalidPoptag(String::new()),
            ParseErrorKind::UnclosedPushtag(String::new()),
            ParseErrorKind::InvalidPopmeta(String::new()),
            ParseErrorKind::UnclosedPushmeta(String::new()),
            ParseErrorKind::DeprecatedPipeSymbol,
            ParseErrorKind::InvalidBookingMethod(String::new()),
            ParseErrorKind::BomInDirectiveBody,
        ]
    }

    /// Get a short label for the error.
    #[must_use]
    pub const fn label(&self) -> &str {
        match &self.kind {
            ParseErrorKind::UnexpectedChar(_) => "unexpected character",
            ParseErrorKind::UnexpectedEof => "unexpected end of file",
            ParseErrorKind::Expected(_) => "expected different token",
            ParseErrorKind::InvalidDate(_) => "invalid date",
            ParseErrorKind::InvalidNumber(_) => "invalid number",
            ParseErrorKind::InvalidAccount(_) => "invalid account",
            ParseErrorKind::InvalidCurrency(_) => "invalid currency",
            ParseErrorKind::UnclosedString => "unclosed string",
            ParseErrorKind::InvalidEscape(_) => "invalid escape",
            ParseErrorKind::MissingField(_) => "missing field",
            ParseErrorKind::IndentationError => "indentation error",
            ParseErrorKind::SyntaxError(_) => "parse error",
            ParseErrorKind::MissingNewline => "syntax error",
            ParseErrorKind::MissingAccount => "expected account name",
            ParseErrorKind::InvalidDateValue(_) => "invalid date value",
            ParseErrorKind::MissingAmount => "expected amount",
            ParseErrorKind::MissingCurrency => "expected currency",
            ParseErrorKind::InvalidAccountFormat(_) => "invalid account format",
            ParseErrorKind::MissingDirective => "expected directive",
            ParseErrorKind::InvalidPoptag(_) => "invalid poptag",
            ParseErrorKind::UnclosedPushtag(_) => "unclosed pushtag",
            ParseErrorKind::InvalidPopmeta(_) => "invalid popmeta",
            ParseErrorKind::UnclosedPushmeta(_) => "unclosed pushmeta",
            ParseErrorKind::DeprecatedPipeSymbol => "deprecated pipe symbol",
            ParseErrorKind::InvalidBookingMethod(_) => "invalid booking method",
            ParseErrorKind::BomInDirectiveBody => "mid-file BOM",
        }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)?;
        if let Some(ctx) = &self.context {
            write!(f, " ({ctx})")?;
        }
        Ok(())
    }
}

impl std::error::Error for ParseError {}

/// Kinds of parse errors.
///
/// Marked `#[non_exhaustive]` because new variants land routinely
/// (the most recent was `InvalidBookingMethod` — variant 25). Without
/// the attribute, every new variant would be a `SemVer`-breaking change
/// for external consumers that `match err.kind { ... }` exhaustively
/// without a wildcard arm.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ParseErrorKind {
    /// Unexpected character in input.
    UnexpectedChar(char),
    /// Unexpected end of file.
    UnexpectedEof,
    /// Expected a specific token.
    Expected(String),
    /// Invalid date format.
    InvalidDate(String),
    /// Invalid number format.
    InvalidNumber(String),
    /// Invalid account name.
    InvalidAccount(String),
    /// Invalid currency code.
    InvalidCurrency(String),
    /// Unclosed string literal.
    UnclosedString,
    /// Invalid escape sequence in string.
    InvalidEscape(char),
    /// Missing required field.
    MissingField(String),
    /// Indentation error.
    IndentationError,
    /// Generic syntax error.
    SyntaxError(String),
    /// Missing final newline.
    MissingNewline,
    /// Missing account name (e.g., after 'open' keyword).
    MissingAccount,
    /// Invalid date value (e.g., month 13, day 32).
    InvalidDateValue(String),
    /// Missing amount in posting.
    MissingAmount,
    /// Missing currency after number.
    MissingCurrency,
    /// Invalid account format (e.g., missing colon).
    InvalidAccountFormat(String),
    /// Missing directive after date.
    MissingDirective,
    /// Poptag for a tag that was never pushed.
    InvalidPoptag(String),
    /// Pushtag that was never popped (unclosed).
    UnclosedPushtag(String),
    /// Popmeta for a key that was never pushed.
    InvalidPopmeta(String),
    /// Pushmeta that was never popped (unclosed).
    UnclosedPushmeta(String),
    /// Deprecated pipe symbol in transaction.
    DeprecatedPipeSymbol,
    /// Invalid booking method (must be uppercase: FIFO, STRICT, `STRICT_WITH_SIZE`, LIFO, HIFO, NONE, AVERAGE).
    InvalidBookingMethod(String),
    /// UTF-8 byte-order mark detected in a directive body (mid-file
    /// BOM that survived the leading-BOM strip at the parser's
    /// public entry — typically a concatenation accident or an
    /// embedded-BOM payload).
    ///
    /// A dedicated variant rather than `SyntaxError(String)` so that:
    ///
    /// 1. The diagnostic text isn't re-stringified at every emission
    ///    site (Display renders the static message from a `&'static
    ///    str`, so no `to_string()` heap allocation per error).
    /// 2. External consumers get a structural discriminant to match
    ///    on instead of a brittle string-equality compare against a
    ///    message body that might be reworded.
    /// 3. The message text becomes an implementation detail (it
    ///    lives in this enum's Display impl) rather than a public
    ///    `&'static str` constant whose wording would be a `SemVer`
    ///    stability commitment.
    BomInDirectiveBody,
}

impl fmt::Display for ParseErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnexpectedChar(c) => write!(f, "syntax error: unexpected '{c}'"),
            Self::UnexpectedEof => write!(f, "unexpected end of file"),
            Self::Expected(what) => write!(f, "expected {what}"),
            Self::InvalidDate(s) => write!(f, "invalid date '{s}'"),
            Self::InvalidNumber(s) => write!(f, "invalid number '{s}'"),
            Self::InvalidAccount(s) => write!(f, "Invalid account '{s}'"),
            Self::InvalidCurrency(s) => write!(f, "invalid currency '{s}'"),
            Self::UnclosedString => write!(f, "unclosed string literal"),
            Self::InvalidEscape(c) => write!(f, "invalid escape sequence '\\{c}'"),
            Self::MissingField(field) => write!(f, "missing required field: {field}"),
            Self::IndentationError => write!(f, "indentation error"),
            Self::SyntaxError(msg) => write!(f, "parse error: {msg}"),
            Self::MissingNewline => write!(f, "syntax error: missing final newline"),
            Self::MissingAccount => write!(f, "expected account name"),
            Self::InvalidDateValue(msg) => write!(f, "invalid date: {msg}"),
            Self::MissingAmount => write!(f, "expected amount in posting"),
            Self::MissingCurrency => write!(f, "expected currency after number"),
            Self::InvalidAccountFormat(s) => {
                write!(f, "invalid account '{s}': must contain ':'")
            }
            Self::MissingDirective => write!(f, "expected directive after date"),
            Self::InvalidPoptag(tag) => {
                write!(f, "poptag attempted on tag '{tag}' which was never pushed")
            }
            Self::UnclosedPushtag(tag) => {
                write!(f, "pushtag '{tag}' was never popped")
            }
            Self::InvalidPopmeta(key) => {
                write!(f, "popmeta attempted on key '{key}' which was never pushed")
            }
            Self::UnclosedPushmeta(key) => {
                write!(f, "pushmeta '{key}' was never popped")
            }
            Self::DeprecatedPipeSymbol => {
                write!(f, "Pipe symbol is deprecated")
            }
            Self::InvalidBookingMethod(m) => {
                write!(
                    f,
                    "invalid booking method '{m}': must be one of FIFO, STRICT, STRICT_WITH_SIZE, LIFO, HIFO, NONE, AVERAGE"
                )
            }
            Self::BomInDirectiveBody => f.write_str(BOM_MIDFILE_DIAGNOSTIC),
        }
    }
}

/// Mid-file BOM diagnostic message.
///
/// Private — emission sites construct `ParseErrorKind::BomInDirectiveBody`
/// and the Display impl renders this text. External consumers detect
/// the diagnostic structurally via the enum variant, not by string
/// compare against this constant. Reworking the wording is therefore
/// not a `SemVer` break.
///
/// Spelled via `concat!` rather than a `\<newline>` line-continuation
/// literal so editor 'strip trailing whitespace on save' and similar
/// hooks can't collapse word boundaries inside the string.
const BOM_MIDFILE_DIAGNOSTIC: &str = concat!(
    "Invalid token: UTF-8 BOM detected in directive body ",
    "(only a leading BOM is permitted); ",
    "did you concatenate two BOM-prefixed files or paste content with an embedded BOM?",
);

#[cfg(test)]
mod tests {
    use super::*;

    /// Compile-time + test-time gate for `every_kind_sample`'s
    /// completeness. The `variant_index` match is exhaustive over
    /// `ParseErrorKind` — adding a new variant breaks compilation
    /// until an arm is added with a unique index. The runtime
    /// assertion below then catches the case where a contributor
    /// added the variant + the `variant_index` arm but forgot to
    /// add a constructor to `every_kind_sample`'s vec.
    ///
    /// Two compile gates working together:
    ///   1. `variant_index` match exhaustiveness — catches added
    ///      variants at compile time.
    ///   2. The unique-index + max-index assertions — catches a
    ///      missing or duplicate `every_kind_sample` vec entry at
    ///      test time.
    #[test]
    fn every_kind_sample_covers_every_variant() {
        // Assign each variant a unique sequential index. The match
        // is exhaustive — a new variant breaks compile until an
        // arm is added with the next index.
        fn variant_index(k: &ParseErrorKind) -> u32 {
            match k {
                ParseErrorKind::UnexpectedChar(_) => 0,
                ParseErrorKind::UnexpectedEof => 1,
                ParseErrorKind::Expected(_) => 2,
                ParseErrorKind::InvalidDate(_) => 3,
                ParseErrorKind::InvalidNumber(_) => 4,
                ParseErrorKind::InvalidAccount(_) => 5,
                ParseErrorKind::InvalidCurrency(_) => 6,
                ParseErrorKind::UnclosedString => 7,
                ParseErrorKind::InvalidEscape(_) => 8,
                ParseErrorKind::MissingField(_) => 9,
                ParseErrorKind::IndentationError => 10,
                ParseErrorKind::SyntaxError(_) => 11,
                ParseErrorKind::MissingNewline => 12,
                ParseErrorKind::MissingAccount => 13,
                ParseErrorKind::InvalidDateValue(_) => 14,
                ParseErrorKind::MissingAmount => 15,
                ParseErrorKind::MissingCurrency => 16,
                ParseErrorKind::InvalidAccountFormat(_) => 17,
                ParseErrorKind::MissingDirective => 18,
                ParseErrorKind::InvalidPoptag(_) => 19,
                ParseErrorKind::UnclosedPushtag(_) => 20,
                ParseErrorKind::InvalidPopmeta(_) => 21,
                ParseErrorKind::UnclosedPushmeta(_) => 22,
                ParseErrorKind::DeprecatedPipeSymbol => 23,
                ParseErrorKind::InvalidBookingMethod(_) => 24,
                ParseErrorKind::BomInDirectiveBody => 25,
            }
        }
        let samples = ParseError::every_kind_sample();
        let indices: std::collections::BTreeSet<u32> = samples.iter().map(variant_index).collect();
        assert_eq!(
            indices.len(),
            samples.len(),
            "every_kind_sample has duplicate variants (collapsed by variant_index): \
             samples = {samples:?}, unique indices = {indices:?}"
        );
        let max = indices.iter().max().copied().unwrap_or(0);
        assert_eq!(
            samples.len() as u32,
            max + 1,
            "every_kind_sample is missing variants: highest variant_index = {max}, \
             expected {} entries in the vec, got {}. Add the missing constructor \
             to every_kind_sample's vec.",
            max + 1,
            samples.len()
        );
    }

    #[test]
    fn test_parse_error_new() {
        let err = ParseError::new(ParseErrorKind::UnexpectedEof, Span::new(0, 5));
        assert_eq!(err.span(), (0, 5));
        assert!(err.context.is_none());
        assert!(err.hint.is_none());
    }

    #[test]
    fn test_parse_error_with_context() {
        let err = ParseError::new(ParseErrorKind::UnexpectedEof, Span::new(0, 5))
            .with_context("in transaction");
        assert_eq!(err.context, Some("in transaction".to_string()));
    }

    #[test]
    fn test_parse_error_with_hint() {
        let err = ParseError::new(ParseErrorKind::UnexpectedEof, Span::new(0, 5))
            .with_hint("add more input");
        assert_eq!(err.hint, Some("add more input".to_string()));
    }

    #[test]
    fn test_parse_error_display_with_context() {
        let err = ParseError::new(ParseErrorKind::UnexpectedEof, Span::new(0, 5))
            .with_context("parsing header");
        let display = format!("{err}");
        assert!(display.contains("unexpected end of file"));
        assert!(display.contains("parsing header"));
    }

    #[test]
    fn test_kind_codes() {
        // Test all error codes are unique and in expected range
        let kinds = [
            (ParseErrorKind::UnexpectedChar('x'), 1),
            (ParseErrorKind::UnexpectedEof, 2),
            (ParseErrorKind::Expected("foo".to_string()), 3),
            (ParseErrorKind::InvalidDate("bad".to_string()), 4),
            (ParseErrorKind::InvalidNumber("nan".to_string()), 5),
            (ParseErrorKind::InvalidAccount("bad".to_string()), 6),
            (ParseErrorKind::InvalidCurrency("???".to_string()), 7),
            (ParseErrorKind::UnclosedString, 8),
            (ParseErrorKind::InvalidEscape('n'), 9),
            (ParseErrorKind::MissingField("name".to_string()), 10),
            (ParseErrorKind::IndentationError, 11),
            (ParseErrorKind::SyntaxError("oops".to_string()), 12),
            (ParseErrorKind::MissingNewline, 13),
            (ParseErrorKind::MissingAccount, 14),
            (ParseErrorKind::InvalidDateValue("month 13".to_string()), 15),
            (ParseErrorKind::MissingAmount, 16),
            (ParseErrorKind::MissingCurrency, 17),
            (
                ParseErrorKind::InvalidAccountFormat("Assets".to_string()),
                18,
            ),
            (ParseErrorKind::MissingDirective, 19),
            (ParseErrorKind::InvalidPoptag("bad".to_string()), 20),
            (ParseErrorKind::UnclosedPushtag("tag".to_string()), 21),
            (ParseErrorKind::InvalidPopmeta("key".to_string()), 22),
            (ParseErrorKind::UnclosedPushmeta("key".to_string()), 23),
            (ParseErrorKind::DeprecatedPipeSymbol, 24),
            (ParseErrorKind::InvalidBookingMethod("BAD".to_string()), 25),
            (ParseErrorKind::BomInDirectiveBody, 26),
        ];

        for (kind, expected_code) in kinds {
            let err = ParseError::new(kind, Span::new(0, 1));
            assert_eq!(err.kind_code(), expected_code);
        }
    }

    #[test]
    fn test_error_labels() {
        // Test that all error kinds have non-empty labels
        let kinds = [
            ParseErrorKind::UnexpectedChar('x'),
            ParseErrorKind::UnexpectedEof,
            ParseErrorKind::Expected("foo".to_string()),
            ParseErrorKind::InvalidDate("bad".to_string()),
            ParseErrorKind::InvalidNumber("nan".to_string()),
            ParseErrorKind::InvalidAccount("bad".to_string()),
            ParseErrorKind::InvalidCurrency("???".to_string()),
            ParseErrorKind::UnclosedString,
            ParseErrorKind::InvalidEscape('n'),
            ParseErrorKind::MissingField("name".to_string()),
            ParseErrorKind::IndentationError,
            ParseErrorKind::SyntaxError("oops".to_string()),
            ParseErrorKind::MissingNewline,
            ParseErrorKind::MissingAccount,
            ParseErrorKind::InvalidDateValue("month 13".to_string()),
            ParseErrorKind::MissingAmount,
            ParseErrorKind::MissingCurrency,
            ParseErrorKind::InvalidAccountFormat("Assets".to_string()),
            ParseErrorKind::MissingDirective,
            ParseErrorKind::InvalidPoptag("bad".to_string()),
            ParseErrorKind::UnclosedPushtag("tag".to_string()),
            ParseErrorKind::InvalidPopmeta("key".to_string()),
            ParseErrorKind::UnclosedPushmeta("key".to_string()),
            ParseErrorKind::DeprecatedPipeSymbol,
            ParseErrorKind::InvalidBookingMethod("BAD".to_string()),
            ParseErrorKind::BomInDirectiveBody,
        ];

        for kind in kinds {
            let err = ParseError::new(kind, Span::new(0, 1));
            assert!(!err.label().is_empty());
        }
    }

    #[test]
    fn test_error_messages() {
        // Test Display for all error kinds
        let test_cases = [
            (ParseErrorKind::UnexpectedChar('$'), "unexpected '$'"),
            (ParseErrorKind::UnexpectedEof, "unexpected end of file"),
            (
                ParseErrorKind::Expected("number".to_string()),
                "expected number",
            ),
            (
                ParseErrorKind::InvalidDate("2024-13-01".to_string()),
                "invalid date '2024-13-01'",
            ),
            (
                ParseErrorKind::InvalidNumber("abc".to_string()),
                "invalid number 'abc'",
            ),
            (
                ParseErrorKind::InvalidAccount("bad".to_string()),
                "Invalid account 'bad'",
            ),
            (
                ParseErrorKind::InvalidCurrency("???".to_string()),
                "invalid currency '???'",
            ),
            (ParseErrorKind::UnclosedString, "unclosed string literal"),
            (
                ParseErrorKind::InvalidEscape('x'),
                "invalid escape sequence '\\x'",
            ),
            (
                ParseErrorKind::MissingField("date".to_string()),
                "missing required field: date",
            ),
            (ParseErrorKind::IndentationError, "indentation error"),
            (
                ParseErrorKind::SyntaxError("bad token".to_string()),
                "parse error: bad token",
            ),
            (ParseErrorKind::MissingNewline, "missing final newline"),
            (ParseErrorKind::MissingAccount, "expected account name"),
            (
                ParseErrorKind::InvalidDateValue("month 13".to_string()),
                "invalid date: month 13",
            ),
            (ParseErrorKind::MissingAmount, "expected amount in posting"),
            (
                ParseErrorKind::MissingCurrency,
                "expected currency after number",
            ),
            (
                ParseErrorKind::InvalidAccountFormat("Assets".to_string()),
                "must contain ':'",
            ),
            (
                ParseErrorKind::MissingDirective,
                "expected directive after date",
            ),
            (
                ParseErrorKind::InvalidPoptag("bad".to_string()),
                "poptag attempted on tag 'bad'",
            ),
            (
                ParseErrorKind::UnclosedPushtag("tag".to_string()),
                "pushtag 'tag' was never popped",
            ),
            (
                ParseErrorKind::InvalidPopmeta("key".to_string()),
                "popmeta attempted on key 'key'",
            ),
            (
                ParseErrorKind::UnclosedPushmeta("key".to_string()),
                "pushmeta 'key' was never popped",
            ),
            (
                ParseErrorKind::DeprecatedPipeSymbol,
                "Pipe symbol is deprecated",
            ),
            (
                ParseErrorKind::InvalidBookingMethod("BAD".to_string()),
                "invalid booking method 'BAD'",
            ),
            // BOM diagnostic — Display renders BOM_MIDFILE_DIAGNOSTIC.
            // Assert on the salient substrings rather than the full text
            // so a future copyedit of the message body doesn't have to
            // touch this test, but a regression that drops the BOM
            // mention entirely (e.g., Display returning "") would fail.
            (
                ParseErrorKind::BomInDirectiveBody,
                "UTF-8 BOM detected in directive body",
            ),
        ];

        for (kind, expected_substring) in test_cases {
            let msg = format!("{kind}");
            assert!(
                msg.contains(expected_substring),
                "Expected '{expected_substring}' in '{msg}'"
            );
        }
    }

    #[test]
    fn test_parse_error_is_error_trait() {
        let err = ParseError::new(ParseErrorKind::UnexpectedEof, Span::new(0, 1));
        // Verify it implements std::error::Error
        let _: &dyn std::error::Error = &err;
    }
}
