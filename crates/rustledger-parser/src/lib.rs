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
pub mod cst;
mod diagnostics;
mod error;
mod format;
pub mod logos_lexer;
mod parser;

pub use cst::{
    BeancountLanguage, SyntaxElement, SyntaxKind, SyntaxNode, SyntaxToken, lossless_kind_tokens,
    parse_flat, parse_structured, parse_via_cst,
};
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
/// Routes through the CST-backed implementation
/// ([`parse_via_cst`]): a lossless Logos lexer feeds a structured
/// CST builder, and the converter in `crate::cst::convert` walks
/// the resulting tree to produce the legacy AST-shaped
/// [`ParseResult`]. The previous hand-rolled state-machine parser
/// in `crate::parser` remains in the crate for now — its own
/// internal unit tests still call it directly. Phase 5 of #1262
/// deletes it.
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
    parse_via_cst(source)
}

/// Parse beancount source code, returning only directives and errors.
///
/// This is a simpler interface when you don't need options/includes/plugins.
#[must_use]
pub fn parse_directives(source: &str) -> (Vec<Spanned<Directive>>, Vec<ParseError>) {
    let result = parse(source);
    (result.directives, result.errors)
}

/// Canonical hash-payload serialization for the corpus baseline
/// (#1262 phase 0). **Internal**: this exists only so the baseline
/// integration test can hash a `ParseResult` without listing fields
/// outside the defining crate.
///
/// Returns a byte string that uniquely identifies the `ParseResult`'s
/// observable content. Directives route through `serde_json::to_value`
/// to normalize the `FxHashMap` iteration order in metadata; all
/// other fields use `Debug` formatting, which is deterministic for
/// `Vec`-based types.
///
/// **Why this lives in `rustledger-parser` instead of the test:**
/// `ParseResult` is `#[non_exhaustive]`, which blocks exhaustive
/// destructuring from external crates (including the integration
/// test). Performing the destructure here forces the compiler to
/// flag any field added to `ParseResult` that the canonical
/// serialization does not feed into its output. Without this, a new
/// `ParseResult` field could silently exit the baseline fingerprint —
/// the BOM-flag-omission class of bug the round-3 review caught.
///
/// **Add a new field?** Add a binding (NOT `_`) AND a hasher feed
/// line to the destructure below. The compiler enforces the binding;
/// reviewers must enforce the feed.
///
/// **Determinism precondition:** this routes directives through
/// `serde_json::to_value`, which is only sort-stable when
/// `serde_json`'s `preserve_order` feature is **off**. Cargo feature
/// unification can flip this on workspace-wide; the unit test
/// `serde_json_object_is_sorted` in this crate's tests catches that
/// flip before the canonical hash silently desyncs.
#[doc(hidden)]
#[must_use]
pub fn __baseline_canonical_payload(result: &ParseResult) -> Vec<u8> {
    let ParseResult {
        directives,
        options,
        includes,
        plugins,
        comments,
        errors,
        warnings,
        currency_occurrences,
        has_leading_bom,
    } = result;
    let mut out: Vec<u8> = Vec::new();
    let directives_json = serde_json::to_value(directives)
        .map_or_else(|e| format!("serialize-error:{e}"), |v| v.to_string());
    out.extend_from_slice(b"directives:");
    out.extend_from_slice(directives_json.as_bytes());
    out.extend_from_slice(b"\noptions:");
    out.extend_from_slice(format!("{options:?}").as_bytes());
    out.extend_from_slice(b"\nincludes:");
    out.extend_from_slice(format!("{includes:?}").as_bytes());
    out.extend_from_slice(b"\nplugins:");
    out.extend_from_slice(format!("{plugins:?}").as_bytes());
    out.extend_from_slice(b"\ncomments:");
    out.extend_from_slice(format!("{comments:?}").as_bytes());
    out.extend_from_slice(b"\nerrors:");
    out.extend_from_slice(format!("{errors:?}").as_bytes());
    out.extend_from_slice(b"\nwarnings:");
    out.extend_from_slice(format!("{warnings:?}").as_bytes());
    out.extend_from_slice(b"\ncurrency_occurrences:");
    out.extend_from_slice(format!("{currency_occurrences:?}").as_bytes());
    out.extend_from_slice(b"\nhas_leading_bom:");
    out.extend_from_slice(format!("{has_leading_bom:?}").as_bytes());
    out
}

#[cfg(test)]
mod canonical_payload_determinism {
    //! Guard against cargo feature unification silently enabling
    //! `serde_json/preserve_order` workspace-wide. When `preserve_order`
    //! is OFF, `serde_json::Value::Object` is BTreeMap-backed and sorts
    //! its keys; when ON, it's IndexMap-backed and preserves insertion
    //! order. `__baseline_canonical_payload` relies on the sort-stable
    //! behavior to neutralize `FxHashMap` iteration order in directive
    //! metadata. A workspace crate flipping the feature on would make
    //! canonical hashes vary with hashbrown state across machines —
    //! the very class of bug the canonicalization was added to
    //! prevent. This test fails fast and points at the cargo-feature
    //! cause instead of letting the corpus baseline mysteriously drift.
    use serde_json::json;

    #[test]
    fn serde_json_object_is_sorted() {
        // Insertion order `b, a` would survive under `preserve_order`.
        // Default features sort to `a, b`.
        let v = json!({ "b": 1, "a": 2 });
        let s = v.to_string();
        assert!(
            s.starts_with("{\"a\""),
            "serde_json::Value::Object is not sorting keys (got {s}). \
             This means cargo feature unification turned on \
             serde_json/preserve_order somewhere in the workspace. \
             The corpus baseline's canonical hash assumes sorted \
             Object keys to neutralize FxHashMap iteration order in \
             directive metadata. Find the crate that enabled \
             `serde_json = {{ ..., features = [\"preserve_order\"] }}` \
             and remove it, or thread an alternative canonicalization \
             through __baseline_canonical_payload.",
        );
    }
}
