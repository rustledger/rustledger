//! Beancount parser built on a Logos lexer + structured CST.
//!
//! [`parse`] tokenizes via [`logos_lexer`], constructs a lossless
//! CST through [`parse_structured`], and walks it via the
//! converter in `cst::convert` to produce a [`ParseResult`] with
//! the typed AST plus errors, options, includes, plugins,
//! comments, and currency occurrences.
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
//! let result = parse(source);
//! assert!(result.errors.is_empty());
//! assert_eq!(result.directives.len(), 1);
//! ```

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod bom;
pub mod cst;
mod diagnostics;
mod error;
pub mod logos_lexer;

/// Opinionated CST-backed formatter entries.
///
/// **Sole** import path for the formatter surface - `format_source`,
/// `try_format_source`, `format_node`, `canonicalize_directives`,
/// `CanonicalizeError`, `lf_to_crlf_outside_strings`,
/// `crlf_to_lf_outside_strings`, `cr_outside_strings_present`. The
/// flat crate-root re-exports were removed in round-5 and the
/// duplicate `crate::cst::format` path was sealed in round-6 of
/// the PR #1284 reviews, so a future deprecation can be done at
/// exactly one site.
pub mod format {
    pub use crate::cst::format::{
        CanonicalizeError, canonicalize_directives, cr_outside_strings_present,
        crlf_to_lf_outside_strings, format_node, format_source, lf_to_crlf_outside_strings,
        try_format_source,
    };
}

pub use cst::{
    BeancountLanguage, SyntaxElement, SyntaxKind, SyntaxNode, SyntaxToken, lossless_kind_tokens,
    parse_flat, parse_structured, parse_via_cst,
};

// Rowan types CST consumers need. Flat re-exports at the crate
// root match the surrounding `SyntaxNode` / `SyntaxToken` shape -
// downstream `use rustledger_parser::{SyntaxNode, TextRange};`
// resolves both halves uniformly without a sub-module hop.
//
// The set covers what LSP handlers need for tree walking:
// - `TextRange` / `TextSize`: byte-offset ranges on every node
// - `TokenAtOffset`: cursor-position lookup
// - `WalkEvent`: preorder / postorder traversal for folding-range
//   and semantic-tokens implementations
// - `NodeOrToken`: pattern-matching `SyntaxElement` children
// - `Direction`: sibling iteration
//
// `GreenNode` is deliberately NOT re-exported - it's the
// thread-safe storage backing for `SyntaxNode` but downstream
// consumers should walk via the cursor API, not the green tree.
//
// **Stability.** These types are versioned in lockstep with this
// crate, NOT with `rowan` directly. A rowan minor bump that
// changes any of these will require a coordinated bump of this
// crate so the re-export contract holds at THIS crate's semver.
pub use error::{ParseError, ParseErrorKind};
pub use rowan::{Direction, NodeOrToken, TextRange, TextSize, TokenAtOffset, WalkEvent};
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
    /// and highlights without resorting to string search of the source,
    /// which produces false positives in comments, payee strings,
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
    /// failure - that would hide real currency identifiers from
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
    /// Every `Account` token the parser consumed, paired with its
    /// interned value and source-byte range.
    ///
    /// Mirrors [`Self::currency_occurrences`] for the account
    /// shape. The CST conversion (`walk_descendants_once`) tracks
    /// every `ACCOUNT` token whose ancestors do NOT include an
    /// `ERROR_NODE`. The LSP rename handler (phase 5.4) walks
    /// this list to emit exact-span edits without resorting to
    /// per-directive substring search, which used to produce
    /// false positives wherever an account-name fragment appeared
    /// inside a payee string, a STRING-typed metadata value, or a
    /// comment. ACCOUNT-typed metadata values (e.g.
    /// `counterparty: Assets:Bank`) DO produce an `ACCOUNT` token
    /// at the lexer level and ARE included in this list - so a
    /// rename of `Assets:Bank` correctly rewrites that metadata
    /// value too.
    ///
    /// **Migration status (#1262 phase 5.4).** Only the LSP
    /// rename handler currently consumes this index. The sibling
    /// handlers `references`, `document_highlight`, and
    /// `linked_editing` still walk the typed AST with substring
    /// search for accounts (see those modules' rustdoc); migrating
    /// them to consume `account_occurrences` is tracked as a
    /// phase 5.5+ follow-up.
    ///
    /// **Error-recovery contract.** Two notions of "failing
    /// directive" need to be distinguished:
    ///
    /// - A directive that PARSES SYNTACTICALLY but whose
    ///   typed-AST conversion errors (e.g.,
    ///   [`crate::ParseErrorKind::InvalidBookingMethod`] on an
    ///   `open Assets:Bank "GARBAGE"`). The ACCOUNT node is
    ///   intact in the CST and NOT inside an `ERROR_NODE`. The
    ///   token IS tracked - tooling can still rename it during
    ///   the mid-edit state.
    /// - A directive so garbled that the CST wraps the region
    ///   in an `ERROR_NODE`. The ACCOUNT token is inside an
    ///   `ERROR_NODE` and is NOT tracked. This is deliberate -
    ///   the recovery boundary is fuzzy and including such
    ///   tokens would surface as confusing rename hits inside
    ///   garbage source.
    ///
    /// # Limitations
    ///
    /// The list is undifferentiated: declarations (from
    /// open/close/balance/pad/note/document) and references
    /// (from posting accounts and ACCOUNT-typed metadata) are
    /// mixed together. There is no equivalent of the
    /// `commodity_declaration_spans` helper used for currencies
    /// (the account case has six declaration directive shapes vs.
    /// the single `Commodity` shape, so no symmetric helper
    /// exists yet). A future go-to-definition migration will need
    /// either a re-walk over `directives` or an additional
    /// `account_declarations: Vec<Span>` field.
    ///
    /// **`file_id` is always 0 in parser output** - same loader
    /// contract as `currency_occurrences`.
    pub account_occurrences: Vec<Spanned<rustledger_core::Account>>,
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
    /// source frame** - i.e., if `has_leading_bom` is true, spans
    /// already include the 3-byte BOM offset and index directly into
    /// the caller's source.
    pub has_leading_bom: bool,
    /// The lossless CST root the converter walked to produce
    /// everything above. Stored as a [`rowan::GreenNode`], which
    /// is `Send + Sync` and reference-counted internally, so an
    /// `Arc<ParseResult>` (the shape the LSP caches per document)
    /// shares this handle across handler invocations without
    /// re-parsing.
    ///
    /// **Prefer [`Self::syntax_node`]** over reading this field
    /// directly. The method is the supported entry point: it
    /// returns a [`SyntaxNode`] (the cursor-API view), keeps the
    /// `rowan::GreenNode` type name out of consumer code, and
    /// shields callers from minor rowan upgrades that touch the
    /// `GreenNode` shape. The field is public for two reasons —
    /// the exhaustive destructure in
    /// [`__baseline_canonical_payload`] needs to bind it, and
    /// `Arc::clone`-style sharing patterns benefit from direct
    /// access — but downstream code should reach for the method.
    ///
    /// **Byte-offset frame: post-BOM.** The CST is built from
    /// the BOM-stripped source — the parser strips a strict-
    /// byte-0 UTF-8 BOM (see [`crate::bom::strip_leading`]) and
    /// feeds the stripped slice to `parse_structured`. So every
    /// `TextRange` / `TextSize` reachable through this tree is
    /// in the **post-BOM** byte frame: an offset of `0` here
    /// corresponds to byte `BOM_LEN == 3` of the original source
    /// when [`Self::has_leading_bom`] is `true`. This differs
    /// from the typed-AST fields above ([`Self::directives`],
    /// [`Self::currency_occurrences`], [`Self::account_occurrences`],
    /// [`Self::errors`], …), whose spans the converter
    /// pre-shifts back into the *original*-source frame so
    /// downstream consumers can index directly into the caller's
    /// source bytes. CST-walking consumers must apply the
    /// equivalent shift themselves: subtract `BOM_LEN` when
    /// translating an original-source offset down to a CST
    /// offset (e.g., `cst.token_at_offset(orig - BOM_LEN)`), and
    /// add `BOM_LEN` back when emitting an original-source
    /// position from a `TextRange`. The LSP `selection_range`
    /// handler does this — see its rustdoc and the
    /// `bom_prefixed_source_does_not_shift_ranges` regression
    /// test.
    ///
    /// **Canonical-payload exclusion.** This field is deliberately
    /// NOT fed into [`__baseline_canonical_payload`]. The green
    /// node is a redundant cache of the source bytes; the
    /// existing `directives` / `currency_occurrences` /
    /// `account_occurrences` / `errors` fields already capture
    /// everything downstream consumers track for drift detection.
    /// Adding the green node's `Debug` output would multiply
    /// the fingerprint size without surfacing any new drift
    /// signal. The corresponding `assert_field_in_hash` arm is
    /// also intentionally absent in `tests/corpus_baseline.rs`.
    /// A negative-form test (`__canonical_payload_excludes_syntax_root`
    /// in this file) pins the exclusion: it confirms that mutating
    /// `syntax_root` while every other field is equal does NOT
    /// change the canonical payload bytes.
    pub syntax_root: rowan::GreenNode,
}

impl ParseResult {
    /// Cursor-API view of the lossless CST that produced this
    /// `ParseResult`. Equivalent to
    /// `SyntaxNode::new_root(self.syntax_root.clone())`.
    ///
    /// Construction is an `Arc` bump (the green node's internal
    /// refcount); cheap enough to call per request. This is the
    /// supported entry point for CST consumers — prefer it over
    /// reading [`Self::syntax_root`] directly, so the `rowan`
    /// dependency stays an implementation detail.
    #[must_use]
    pub fn syntax_node(&self) -> SyntaxNode {
        SyntaxNode::new_root(self.syntax_root.clone())
    }
}

// Compile-time assertion: `ParseResult` is shared as
// `Arc<ParseResult>` across the LSP's main thread and its
// background worker (see `rustledger-lsp/src/main_loop.rs`).
// A future field whose type is not `Send + Sync` (e.g. an `Rc`,
// a `Cell`, or a non-thread-safe handle) would silently break
// the LSP build at the call site, far from the parser change
// that caused it. This assertion fences the invariant at the
// definition site so the parser crate's own build fails first.
const _: fn() = || {
    const fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<ParseResult>();
};

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
/// the resulting tree to produce the [`ParseResult`].
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
/// `ParseResult` field could silently exit the baseline fingerprint -
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
        account_occurrences,
        has_leading_bom,
        syntax_root,
    } = result;
    // `syntax_root` is a redundant cache of the source bytes; see
    // its rustdoc. Bind it (so the compiler still flags future
    // field additions on this exhaustive destructure) but discard
    // it from the canonical payload.
    let _ = syntax_root;
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
    out.extend_from_slice(b"\naccount_occurrences:");
    out.extend_from_slice(format!("{account_occurrences:?}").as_bytes());
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
    //! canonical hashes vary with hashbrown state across machines -
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

#[cfg(test)]
mod cached_syntax_root_matches_fresh_parse {
    //! The `selection_range` handler (and any future CST-walking
    //! handler) consumes [`ParseResult::syntax_root`] instead of
    //! re-invoking [`crate::parse_structured`]. The safety
    //! argument is "the cached green root is the same tree the
    //! converter walked, which is the same tree a fresh
    //! `parse_structured` would return."
    //!
    //! Today that argument is trivially true because the cache is
    //! populated directly from the converter's `source_file`.
    //! But if a future change introduces post-conversion CST
    //! mutation (span rewrites, error-recovery splicing, trivia
    //! reattachment) the cached root would diverge from a fresh
    //! re-parse — silently, since nothing else compares the two
    //! trees. This test pins the invariant across a small fixture
    //! set covering empty source, every directive kind, error
    //! recovery, mid-file BOM, and metadata-bearing transactions.
    use super::{cst::parse_structured, parse};

    fn assert_round_trip(label: &str, source: &str) {
        let parsed = parse(source);
        let (stripped, _bom) = crate::bom::strip_leading(source);
        let fresh = parse_structured(stripped).green().into_owned();
        assert_eq!(
            parsed.syntax_root, fresh,
            "cached syntax_root diverged from fresh parse_structured for {label}: \n\
             this means something is mutating the green tree between converter \
             capture and consumer access. The two are supposed to be identical."
        );
    }

    #[test]
    fn empty_source() {
        assert_round_trip("empty", "");
    }

    #[test]
    fn simple_directive() {
        assert_round_trip("open", "2024-01-01 open Assets:Bank USD\n");
    }

    #[test]
    fn every_directive_shape() {
        assert_round_trip(
            "directive zoo",
            r#"option "title" "Test"
plugin "myplugin"
include "other.beancount"
2024-01-01 open Assets:Bank USD
2024-01-01 commodity USD
2024-06-15 * "Coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food
2024-12-31 close Assets:Bank
2024-01-31 balance Assets:Bank 100 USD
2024-01-15 pad Assets:Bank Equity:Opening
2024-01-15 note Assets:Bank "deposit pending"
2024-01-15 event "location" "SF"
2024-01-15 price USD 1.00 EUR
"#,
        );
    }

    #[test]
    fn with_parse_errors() {
        // Trigger error recovery (unterminated string, garbled
        // directive) to ensure the post-pass `fixup_directive_spans`
        // and error-node wrapping don't drift between cache and
        // fresh re-parse.
        assert_round_trip(
            "broken",
            "2024-01-01 open Assets:Bank \"unterminated\n2024-01-02 garbage line here\n",
        );
    }

    #[test]
    fn with_metadata_and_comments() {
        assert_round_trip(
            "metadata",
            r#"; standalone comment
2024-01-01 open Assets:Bank USD
  payee_account: Assets:Other
2024-06-15 * "Coffee"  ; eol comment
  memo: "morning"
  Assets:Bank  -5.00 USD
"#,
        );
    }
}

#[cfg(test)]
mod canonical_payload_excludes_syntax_root {
    //! Pins the deliberate exclusion of `ParseResult::syntax_root`
    //! from [`__baseline_canonical_payload`]. The exclusion is
    //! documented in three places (the field's rustdoc, the
    //! destructure comment in `__baseline_canonical_payload`, and
    //! the CHANGELOG entry under `[Unreleased] / Features`) but
    //! none of those are executable. A future contributor
    //! mechanically pattern-matching on "all fields get an arm"
    //! could add a `syntax_root` feed to the canonical payload —
    //! the corpus manifest would silently drift on every source
    //! that touched the green tree.
    //!
    //! This test mutates `syntax_root` while leaving every other
    //! field equal, and asserts the canonical payload bytes are
    //! unchanged.
    use super::{__baseline_canonical_payload, parse};

    #[test]
    fn mutating_syntax_root_does_not_change_canonical_payload() {
        let src_a = "2024-01-01 open Assets:Bank USD\n";
        // A different source produces a different green tree but
        // we want every OTHER field equal; pick a source that
        // produces an identical typed ParseResult on every field
        // EXCEPT `syntax_root`. Empty source is the simplest
        // counterexample for "syntax_root differs"; we go further
        // and synthesize the mutation explicitly to keep the test
        // independent of the converter's behavior.
        let parsed_a = parse(src_a);
        let mut mutated = parse(src_a);
        // Replace the green tree with a freshly-parsed but
        // structurally-different one. `parse("")` gives an empty
        // SOURCE_FILE green root; the original has an OPEN_DIRECTIVE
        // child. Other fields will differ for `parse("")`, so we
        // construct the mutation by swapping ONLY the field.
        mutated.syntax_root = parse("").syntax_root;

        let payload_original = __baseline_canonical_payload(&parsed_a);
        let payload_mutated = __baseline_canonical_payload(&mutated);
        assert_eq!(
            payload_original, payload_mutated,
            "canonical payload changed after mutating only `syntax_root`. \
             Either the destructure in `__baseline_canonical_payload` \
             grew a `syntax_root` feed line (revert that — the field \
             is deliberately excluded; see its rustdoc), or another \
             field now reads from `syntax_root` indirectly. Either \
             way the corpus manifest is about to drift."
        );
    }
}
