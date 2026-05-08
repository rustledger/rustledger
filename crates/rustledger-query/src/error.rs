//! BQL error types.

use thiserror::Error;

/// Error returned when parsing a BQL query fails.
#[derive(Debug, Error)]
#[error("syntax error at position {position}: {kind}")]
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
///
/// Marked `#[non_exhaustive]` so adding new variants doesn't break
/// downstream consumers that match exhaustively.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum QueryError {
    /// Parse error.
    #[error("parse error: {0}")]
    Parse(#[from] ParseError),
    /// Type error (incompatible types in operation).
    #[error("type error: {0}")]
    Type(String),
    /// Unknown column name.
    #[error("column '{0}' not found")]
    UnknownColumn(String),
    /// Unknown function name.
    #[error("no function matches \"{0}\"")]
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
    /// PIVOT BY clause does not have exactly two columns.
    ///
    /// Matches bean-query's compiler check (`_compile_pivot_by` in
    /// `beanquery/compiler.py`). The first column is the pivot value
    /// (whose values become new column headers); the second is the
    /// GROUP BY column to keep as the row key.
    #[error("PIVOT BY requires exactly two columns, got {0}")]
    PivotWrongArity(usize),
    /// PIVOT BY's two columns refer to the same target.
    ///
    /// Bean-query message: `the two PIVOT BY columns cannot be the
    /// same column`. Same wording reused for upstream parity.
    #[error("the two PIVOT BY columns cannot be the same column")]
    PivotSameColumn,
    /// PIVOT BY's second column isn't in the GROUP BY clause.
    ///
    /// The second pivot column has to be a GROUP BY key — otherwise
    /// the pivot output rows wouldn't have a stable identity. Bean-
    /// query message: `the second PIVOT BY column must be a GROUP BY
    /// column`.
    #[error("the second PIVOT BY column must be a GROUP BY column")]
    PivotSecondNotInGroupBy,
    /// PIVOT BY used on a query with no `GROUP BY` clause.
    ///
    /// Implicit grouping (a SELECT with aggregates but no GROUP BY)
    /// produces a single row whose key is undefined; PIVOT BY's second
    /// column has nothing meaningful to refer to. Distinct from
    /// `PivotSecondNotInGroupBy` (which is for "GROUP BY exists but the
    /// key column isn't in it").
    #[error("PIVOT BY requires an explicit GROUP BY clause")]
    PivotWithoutGroupBy,
}
