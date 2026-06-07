//! CST -> `ParseResult` converter (phase 3.2-3.4 of #1262).
//!
//! [`parse_via_cst`] is a parallel implementation of the public
//! [`crate::parse`] entry point that delegates to the CST
//! ([`parse_structured`]) and rebuilds the existing AST-shaped
//! [`ParseResult`] by walking the typed-AST surface from
//! [`crate::cst::ast`]. The current default code path remains the
//! hand-rolled state-machine parser in `crate::parser`; this
//! function is gated behind a feature/env flag for now so the
//! corpus baseline differential test in
//! `tests/cst_vs_legacy_corpus.rs` can compare both paths
//! file-by-file.
//!
//! ## Migration scaffolding
//!
//! Phase 3.2-3.4 builds out converters for each directive type
//! incrementally. Coverage is tracked by the differential test:
//! each converted directive type drops a corresponding file class
//! from the test's allow-list. Once every directive type is
//! covered and the corpus passes byte-identically, a follow-up PR
//! flips [`crate::parse`] to call this function and a later phase
//! deletes `crate::parser`.
//!
//! ## Coverage status
//!
//! Implemented directive converters:
//! - (none yet — scaffolding only)
//!
//! Pending directive converters:
//! - Open, Close, Commodity, Note, Document, Event, Query, Price
//! - Balance, Pad
//! - Pushtag, Poptag, Pushmeta, Popmeta
//! - Option, Include, Plugin, Custom
//! - Transaction (most complex: header + postings + metadata)

use rustledger_core::{Directive, Span, Spanned};

use crate::ParseResult;
use crate::cst::ast::SourceFile;

/// Parse Beancount source via the CST and produce the legacy
/// [`ParseResult`] shape. Parallel implementation of
/// [`crate::parse`]; not yet wired as the default code path.
///
/// See the module-level rustdoc for migration status.
#[must_use]
pub fn parse_via_cst(source: &str) -> ParseResult {
    // BOM detection mirrors the legacy parser's behavior: strip a
    // leading 3-byte BOM from the source before tokenizing and
    // record its presence in the result. Spans index the original
    // source frame INCLUDING the BOM offset.
    let (stripped, has_leading_bom) = crate::bom::strip_leading(source);

    let _source_file = SourceFile::parse(stripped);

    // Scaffolding only: the converter walkers are added in
    // subsequent commits, one directive type at a time. For now,
    // return an empty `ParseResult` so the differential test can
    // wire up and start comparing file-by-file.
    let directives: Vec<Spanned<Directive>> = Vec::new();
    let options: Vec<(String, String, Span)> = Vec::new();
    let includes: Vec<(String, Span)> = Vec::new();
    let plugins: Vec<(String, Option<String>, Span)> = Vec::new();
    let comments: Vec<Spanned<String>> = Vec::new();
    let errors = Vec::new();
    let warnings = Vec::new();
    let currency_occurrences = Vec::new();

    ParseResult {
        directives,
        options,
        includes,
        plugins,
        comments,
        errors,
        warnings,
        currency_occurrences,
        has_leading_bom,
    }
}
