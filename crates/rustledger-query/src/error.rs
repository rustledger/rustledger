//! BQL error types.

use thiserror::Error;

/// Error returned when parsing a BQL query fails.
#[derive(Debug, Error)]
#[error("parse error at position {position}: {kind}")]
pub struct ParseError {
    /// The kind of error.
    pub kind: ParseErrorKind,
    /// Position in the input where the error occurred.
    pub position: usize,
}

/// The kind of parse error.
#[derive(Debug, Error)]
pub enum ParseErrorKind {
    /// Unexpected end of input.
    #[error("unexpected end of input")]
    UnexpectedEof,
    /// Syntax error with details.
    #[error("{0}")]
    SyntaxError(String),
}

impl ParseError {
    /// Create a new parse error.
    pub const fn new(kind: ParseErrorKind, position: usize) -> Self {
        Self { kind, position }
    }
}

/// Error returned when executing a query fails.
#[derive(Debug, Error)]
pub enum QueryError {
    /// Parse error.
    #[error("parse error: {0}")]
    Parse(#[from] ParseError),
    /// Type error (incompatible types in operation).
    #[error("type error: {0}")]
    Type(String),
    /// Unknown column name.
    #[error("unknown column: {0}")]
    UnknownColumn(String),
    /// Unknown function name.
    #[error("unknown function: {0}")]
    UnknownFunction(String),
    /// Invalid function arguments.
    #[error("invalid arguments for function {0}: {1}")]
    InvalidArguments(String, String),
    /// Aggregation error.
    #[error("aggregation error: {0}")]
    Aggregation(String),
    /// Evaluation error.
    #[error("evaluation error: {0}")]
    Evaluation(String),
}
