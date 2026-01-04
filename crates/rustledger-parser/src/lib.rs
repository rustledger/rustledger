//! Beancount parser using chumsky parser combinators.
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

mod error;
// mod lexer; // Disabled - using direct parser instead
mod parser;
mod span;

pub use error::{ParseError, ParseErrorKind};
pub use span::{Span, Spanned};

use rustledger_core::Directive;

/// Result of parsing a beancount file.
#[derive(Debug)]
pub struct ParseResult {
    /// Successfully parsed directives.
    pub directives: Vec<Spanned<Directive>>,
    /// Options found in the file.
    pub options: Vec<(String, String, Span)>,
    /// Include directives found.
    pub includes: Vec<(String, Span)>,
    /// Plugin directives found.
    pub plugins: Vec<(String, Option<String>, Span)>,
    /// Parse errors encountered.
    pub errors: Vec<ParseError>,
}

/// Parse beancount source code.
///
/// Returns a tuple of (directives, errors). The parser uses error recovery
/// to continue parsing after encountering errors, so both may be non-empty.
///
/// # Arguments
///
/// * `source` - The beancount source code to parse
///
/// # Returns
///
/// A `ParseResult` containing directives, options, includes, plugins, and errors.
pub fn parse(source: &str) -> ParseResult {
    parser::parse(source)
}

/// Parse beancount source code, returning only directives and errors.
///
/// This is a simpler interface when you don't need options/includes/plugins.
pub fn parse_directives(source: &str) -> (Vec<Spanned<Directive>>, Vec<ParseError>) {
    let result = parse(source);
    (result.directives, result.errors)
}
