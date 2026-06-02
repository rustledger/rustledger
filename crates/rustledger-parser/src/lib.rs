//! Beancount parser using a Logos lexer and a hand-rolled state-machine parser.
//!
//! This crate provides a parser for the Beancount file format. It produces
//! a stream of [`Directive`]s from source text, along with any parse errors.
//!
//! # Features
//!
//! - Full Beancount syntax support (all 12 directive types)
//! - Error recovery (continues parsing after errors)
//! - Precise source locations for error reporting
//! - Support for includes, options, plugins
//!
//! # Example
//!
//! ```ignore
//! use rustledger_parser::parse;
//!
//! let source = r#"
//! 2024-01-15 * "Coffee Shop" "Morning coffee"
//!   Expenses:Food:Coffee  5.00 USD
//!   Assets:Cash
//! "#;
//!
//! let (directives, errors) = parse(source);
//! assert!(errors.is_empty());
//! assert_eq!(directives.len(), 1);
//! ```

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod bom;
mod error;
mod format;
pub mod logos_lexer;
mod parser;

pub use error::{ParseError, ParseErrorKind};
pub use format::format_source;
pub use rustledger_core::{InternedStr, SYNTHESIZED_FILE_ID, Span, Spanned};

use rustledger_core::Directive;

/// Result of parsing a beancount file.
///
/// Marked `#[non_exhaustive]` so external consumers must go through
/// [`parse`] rather than constructing the struct by literal. Future
/// field additions (e.g., diagnostic metadata, source-map back-
/// references) then land as non-breaking changes.
#[derive(Debug)]
#[non_exhaustive]
pub struct ParseResult {
    /// Successfully parsed directives.
    pub directives: Vec<Spanned<Directive>>,
    /// Options found in the file.
    pub options: Vec<(String, String, Span)>,
    /// Include directives found.
    pub includes: Vec<(String, Span)>,
    /// Plugin directives found.
    pub plugins: Vec<(String, Option<String>, Span)>,
    /// Standalone comments found in the file.
    pub comments: Vec<Spanned<String>>,
    /// Parse errors encountered.
    pub errors: Vec<ParseError>,
    /// Deprecation warnings.
    pub warnings: Vec<ParseWarning>,
    /// Every `Currency` token the parser consumed, paired with its
    /// interned value and source-byte range.
    ///
    /// Source-position-aware tooling (LSP rename / references /
    /// document-highlight) walks this list to produce edits, locations,
    /// and highlights without resorting to string search of the source
    /// — which produces false positives in comments, payee strings,
    /// account-name segments, etc. The order matches source order
    /// because the parser fills it as tokens are consumed (and the
    /// parser is strictly forward-advancing, including on error
    /// recovery).
    ///
    /// **Error-recovery contract.** Tokens consumed during a
    /// directive that ultimately fails to parse remain in this list.
    /// Rationale: the lexer's classification of a token as a
    /// `Currency` is independent of whether the surrounding syntax is
    /// valid, and tooling that wants to rename or highlight a
    /// currency the user typed should follow that classification.
    /// Do not "clean up" partially-consumed entries after a parse
    /// failure — that would hide real currency identifiers from
    /// downstream tooling while the user is mid-edit.
    ///
    /// **`file_id` is always 0 in parser output.** The parser
    /// processes one file at a time and doesn't know its own file
    /// id. The loader sets the correct id on each entry via
    /// `.with_file_id(n)` when assembling a multi-file `SourceMap`,
    /// the same way it does for `directives`. Per-file consumers
    /// (today: every LSP handler) can ignore `file_id`; future
    /// multi-file consumers must remember to thread it through.
    pub currency_occurrences: Vec<Spanned<rustledger_core::Currency>>,
    /// `true` iff the parsed source began with a UTF-8 BOM (strict
    /// byte 0).
    ///
    /// This is the **single source of truth** for downstream consumers
    /// that need to know whether to preserve a leading BOM on output
    /// (notably `format_source`). Do NOT inspect the source bytes
    /// directly; the parser already handled the strip/detect logic in
    /// one place ([`crate::bom::strip_leading`]) and stored the result
    /// here. Reproducing the check elsewhere is exactly the contract-
    /// drift class of bug this field was introduced to eliminate.
    ///
    /// Span coordinates in this `ParseResult` are in the **original
    /// source frame** — i.e., if `has_leading_bom` is true, spans
    /// already include the 3-byte BOM offset and index directly into
    /// the caller's source.
    pub has_leading_bom: bool,
}

/// A warning from the parser (non-fatal).
#[derive(Debug, Clone)]
pub struct ParseWarning {
    /// The warning message.
    pub message: String,
    /// Location in source.
    pub span: Span,
}

impl ParseWarning {
    /// Create a new warning.
    pub fn new(message: impl Into<String>, span: Span) -> Self {
        Self {
            message: message.into(),
            span,
        }
    }
}

/// Parse beancount source code.
///
/// Uses a fast token-based parser: a Logos lexer feeds a hand-rolled
/// state-machine parser. An early version targeted winnow's Stream
/// trait but the manual approach turned out simpler and faster, so the
/// winnow dependency was removed.
///
/// # Arguments
///
/// * `source` - The beancount source code to parse
///
/// # Returns
///
/// A `ParseResult` containing directives, options, includes, plugins, and errors.
#[must_use]
pub fn parse(source: &str) -> ParseResult {
    parser::parse(source)
}

/// Parse beancount source code, returning only directives and errors.
///
/// This is a simpler interface when you don't need options/includes/plugins.
#[must_use]
pub fn parse_directives(source: &str) -> (Vec<Spanned<Directive>>, Vec<ParseError>) {
    let result = parse(source);
    (result.directives, result.errors)
}
