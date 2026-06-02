//! Integration test pinning the `ParseErrorEntry.kind_code`
//! enumeration in `openrpc.json` to the actual variant set of
//! `rustledger_parser::ParseErrorKind`.
//!
//! Without this test, the JSON schema's `description` string (which
//! lists every code 1..=N inline as human-readable prose) silently
//! drifts the moment a new `ParseErrorKind` variant lands without a
//! matching openrpc.json edit. The schema is the contract external
//! SDK generators consume; drift here is exactly the
//! contract-distance failure the round-13/14 refactor was eliminating
//! elsewhere.
//!
//! The test extracts every `<N> <description>` token from the
//! description string and asserts the set of codes equals the set
//! produced by exercising `ParseError::kind_code()` over every
//! variant. The reverse direction is intrinsic — `kind_code()` is a
//! `match` over `ParseErrorKind`, so the compiler enforces
//! exhaustive coverage.

use rustledger_parser::{ParseError, ParseErrorKind, Span};
use std::collections::BTreeSet;
use std::path::PathBuf;

/// Build one `ParseError` for every `ParseErrorKind` variant.
///
/// Delegates to `ParseError::every_kind_sample()` whose body is an
/// exhaustive `match` over `&ParseErrorKind` — adding a new variant
/// makes that function fail to compile, forcing the contributor to
/// extend the variant set (which propagates here automatically).
/// Without this delegation, the test would hand-maintain its own
/// list and silently miss new variants that update only `kind_code`.
fn every_kind() -> Vec<ParseErrorKind> {
    ParseError::every_kind_sample()
}

#[test]
fn openrpc_parse_error_entry_lists_every_kind_code() {
    // Load openrpc.json from the crate root (this test file lives in
    // `crates/rustledger-ffi-wasi/tests/`, openrpc.json one dir up).
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let openrpc_path = manifest_dir.join("openrpc.json");
    let raw = std::fs::read_to_string(&openrpc_path)
        .unwrap_or_else(|e| panic!("read {openrpc_path:?}: {e}"));
    let openrpc: serde_json::Value = serde_json::from_str(&raw).expect("parse openrpc.json");

    // Pull out the ParseErrorEntry description string.
    let description = openrpc
        .pointer("/components/schemas/ParseErrorEntry/description")
        .and_then(|v| v.as_str())
        .expect("openrpc.json must define components.schemas.ParseErrorEntry.description");

    // The description contains `Known codes: 1 ..., 2 ..., ..., N ...`.
    // Parse every `<number> <label>` token. The kind labels include
    // spaces and parens, so we split on `, ` and on the leading
    // `Known codes: ` substring rather than tokenizing by char class.
    // Trim leading whitespace so the first digit lands at byte 0 —
    // makes the state machine below simpler (the start-of-string
    // case handles the first code without needing a preceded-by-`:`
    // special case).
    let codes_section = description
        .split_once("Known codes:")
        .map(|(_, rest)| rest.trim_start())
        .expect("description must include the 'Known codes:' enumeration");

    // State-machine parser robust against commas inside labels (e.g.,
    // a future label like "X, Y, and Z" wouldn't be misparsed as
    // three separate codes). A code marker is: a digit-run at
    // start-of-string OR preceded by ", " (the entry separator),
    // followed by SOMETHING that isn't another digit (so a stray
    // 5-digit number embedded in a label isn't misclassified as a
    // code).
    //
    // Round-17 hardening: the previous predicate required `space +
    // letter` after the digit run. That silently dropped codes
    // followed by other terminators (`.`, `)`, `;`, EOF). A
    // description ending with `, 27.` would have not registered
    // code 27 in `documented_codes`, weakening the test's
    // "description mentions every code" guarantee. The new predicate
    // accepts ANY non-digit terminator including end-of-string.
    let mut documented_codes: BTreeSet<u32> = BTreeSet::new();
    let bytes = codes_section.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let at_start_of_string = i == 0;
        let preceded_by_comma_space = i >= 2 && bytes[i - 2] == b',' && bytes[i - 1] == b' ';
        if !bytes[i].is_ascii_digit() || !(at_start_of_string || preceded_by_comma_space) {
            i += 1;
            continue;
        }
        let digit_start = i;
        while i < bytes.len() && bytes[i].is_ascii_digit() {
            i += 1;
        }
        let digit_end = i;
        // The digit-run must be a code marker, not part of a longer
        // alphanumeric token. Acceptable terminators are:
        //   - end-of-string
        //   - any non-digit, non-letter byte (space, punctuation)
        // This rejects e.g. "v2024" (digit run inside word) while
        // accepting "26", "26 BOM", "26.", "26)", "26;".
        let valid_terminator =
            i == bytes.len() || !(bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_');
        if valid_terminator && let Ok(n) = codes_section[digit_start..digit_end].parse::<u32>() {
            documented_codes.insert(n);
        }
    }

    let actual_codes: BTreeSet<u32> = every_kind()
        .into_iter()
        .map(|kind| {
            let err = ParseError::new(kind, Span::new(0, 1));
            err.kind_code()
        })
        .collect();

    // Direction 1: every Rust kind_code is documented.
    let missing_from_docs: Vec<_> = actual_codes.difference(&documented_codes).collect();
    assert!(
        missing_from_docs.is_empty(),
        "openrpc.json's ParseErrorEntry description is missing these kind_codes: {missing_from_docs:?}. \
         Update components.schemas.ParseErrorEntry.description in openrpc.json to mention each new variant."
    );

    // Direction 2: every documented code is a real Rust variant.
    let extra_in_docs: Vec<_> = documented_codes.difference(&actual_codes).collect();
    assert!(
        extra_in_docs.is_empty(),
        "openrpc.json's ParseErrorEntry description mentions these kind_codes that do not exist as ParseErrorKind variants: {extra_in_docs:?}. \
         Remove them from the description."
    );
}
