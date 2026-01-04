//! Parse error types.

use crate::Span;
use std::fmt;

/// A parse error with location information.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    /// The kind of error.
    pub kind: ParseErrorKind,
    /// The span where the error occurred.
    pub span: Span,
    /// Optional context message.
    pub context: Option<String>,
}

impl ParseError {
    /// Create a new parse error.
    #[must_use]
    pub const fn new(kind: ParseErrorKind, span: Span) -> Self {
        Self {
            kind,
            span,
            context: None,
        }
    }

    /// Add context to this error.
    #[must_use]
    pub fn with_context(mut self, context: impl Into<String>) -> Self {
        self.context = Some(context.into());
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
        }
    }

    /// Get the error message.
    #[must_use]
    pub fn message(&self) -> String {
        format!("{}", self.kind)
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
#[derive(Debug, Clone, PartialEq, Eq)]
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
}

impl fmt::Display for ParseErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnexpectedChar(c) => write!(f, "syntax error: unexpected '{c}'"),
            Self::UnexpectedEof => write!(f, "unexpected end of file"),
            Self::Expected(what) => write!(f, "expected {what}"),
            Self::InvalidDate(s) => write!(f, "invalid date '{s}'"),
            Self::InvalidNumber(s) => write!(f, "invalid number '{s}'"),
            Self::InvalidAccount(s) => write!(f, "invalid account '{s}'"),
            Self::InvalidCurrency(s) => write!(f, "invalid currency '{s}'"),
            Self::UnclosedString => write!(f, "unclosed string literal"),
            Self::InvalidEscape(c) => write!(f, "invalid escape sequence '\\{c}'"),
            Self::MissingField(field) => write!(f, "missing required field: {field}"),
            Self::IndentationError => write!(f, "indentation error"),
            Self::SyntaxError(msg) => write!(f, "parse error: {msg}"),
            Self::MissingNewline => write!(f, "syntax error: missing final newline"),
        }
    }
}
