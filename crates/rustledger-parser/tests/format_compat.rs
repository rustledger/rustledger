//! Format-compat suite - phase 4.2 of the CST migration (#1262).
//!
//! Pins the formatter's promise on the historical destructive-formatting
//! bug classes (#1142, #1156, #1157, #1252, plus the regressions surfaced
//! during PR #1284's seven review rounds). Each subdirectory of
//! `tests/format_compat/cases/` is one fixture:
//!
//! - `input.bean` - what the user typed (or an editor stored).
//! - `expected.bean` - the byte-exact output `format_source` MUST emit.
//!
//! The harness asserts:
//!
//! 1. `format_source(input) == expected` - the formatter renders the
//!    fixture exactly as documented.
//! 2. `format_source(expected) == expected` - idempotence: re-formatting
//!    canonical text is a no-op.
//! 3. The parser produces zero errors on `expected` - the canonical
//!    output is itself parseable.
//!
//! All three stages run for every fixture (the harness does NOT
//! short-circuit on a stage-1 mismatch). Without that, a malformed
//! `expected.bean` paired with an unexpected formatter output would
//! report only the format mismatch and leave the unparsable golden
//! file invisible. Stages 2 and 3 also run inside `catch_unwind` so
//! a panic in `format_source` or `parse` (e.g. on a pathological
//! input a future regression introduces) does not discard the
//! already-recorded stage-1 failures from this OR earlier fixtures
//! in the loop.
//!
//! New fixtures land here whenever a destructive-formatting bug is
//! reported, fixed, or its absence merits a regression pin.
//!
//! **Coverage floor.** Bug-class coverage is asserted by a
//! [`REQUIRED_FIXTURES`] name-set check, not a fixture count. A
//! count floor doesn't notice when a critical fixture is swapped
//! for an inert one, and tempts contributors to delete cases up to
//! the floor "to clean up." The name-set check forces the deletion
//! of a load-bearing fixture (BOM, CRLF, #1252 repro, etc.) to be
//! a deliberate, reviewable change to this constant - not silent
//! disappearance from the cases directory.

use std::fs;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};

use rustledger_parser::format::format_source;
use rustledger_parser::parse;

/// Bug-class fixtures that MUST exist for the suite to be load-bearing.
///
/// Editing this set is the explicit, reviewable signal that a
/// regression class is being intentionally retired (or renamed). A
/// drift PR cannot silently delete one of these fixtures without
/// also editing this constant - which surfaces in review.
///
/// Additional, non-required fixtures are encouraged (browse
/// `tests/format_compat/cases/` to see the full set). The harness
/// runs all of them; only this subset is mandatory.
const REQUIRED_FIXTURES: &[&str] = &[
    // #1252 reproducer + bug classes the formatter rewrite fixed.
    "issue_1252_destructive_repro",
    "trailing_comment_on_directive_header",
    "trailing_comment_eof_no_newline",
    "posting_trailing_comment",
    "pushtag_poptag_pair_preserved",
    "pushmeta_popmeta_pair_preserved",
    // Sign / paren preservation in BALANCE / PRICE / postings
    // (Copilot #2 on PR #1284).
    "balance_leading_unary_minus_preserves_sign",
    "balance_leading_parenthesized_expression",
    "price_leading_unary_minus_preserves_sign",
    "posting_arithmetic_with_parens",
    "metadata_unary_minus_value",
    // Cost-spec shape.
    "cost_spec_per_unit_plus_total_marker",
    "cost_spec_with_negative_amount",
    // Canonical-form choices documented in PR-4 of #1262.
    "commas_stripped_per_canonical_form",
    "unary_plus_stripped_per_canonical_form",
    "bom_dropped",
    "missing_final_newline_added",
    "multiple_trailing_blank_lines_collapsed",
    // Line-ending handling.
    "crlf_outside_strings_folded",
    "crlf_inside_strings_preserved",
    // The bug class #1142 closed: posting-level metadata
    // interleaved between postings.
    "posting_with_interleaved_metadata",
    // String-literal interior preservation: the formatter must
    // not re-quote, re-escape, or collapse internal newlines.
    "multiline_note_string_preserved",
    // Per-directive metadata attachment (sibling of #1142).
    "balance_assertion_with_metadata",
    // Tag/link source-order preservation on transaction headers
    // (sibling of #1252).
    "transaction_tags_and_links_source_order",
    // Unicode column-alignment correctness for non-Latin account
    // names.
    "non_latin_account_names",
];

/// Cross-side coverage pairs between the file-pair fixture set
/// (this suite) and the inline `IDEMPOTENCE_MATRIX` in
/// `crates/rustledger-parser/src/cst/format.rs`.
///
/// Each tuple is `(file_pair_name, matrix_name)`. The two test
/// surfaces overlap deliberately per the README's two-audience
/// design: the inline matrix exercises property-style invariants
/// (idempotence, lexer agreement, round-trip through
/// `canonicalize_directives`); the file-pair surface gives users
/// a reviewable view of the formatter's contract on the same bug
/// classes.
///
/// Without an explicit pairing, the names drift apart and a
/// one-sided deletion silently halves coverage. The integration
/// test below asserts that every `file_pair_name` exists as a
/// directory under `cases/`. The inline unit test
/// `idempotence_matrix_mirrors_format_compat_pairs` (in
/// `cst::format::tests`) asserts that every `matrix_name` exists
/// in `IDEMPOTENCE_MATRIX`. Both sides have to be edited together
/// to add or retire a pair, or one side's check fires.
const MIRROR_PAIRS: &[(&str, &str)] = &[
    (
        "balance_leading_unary_minus_preserves_sign",
        "balance_leading_unary_minus",
    ),
    (
        "balance_leading_parenthesized_expression",
        "balance_leading_parenthesized_expression",
    ),
    (
        "price_leading_unary_minus_preserves_sign",
        "price_leading_unary_minus",
    ),
    ("cost_spec_with_negative_amount", "cost_spec_with_negative"),
    (
        "cost_spec_with_comma_and_date",
        "cost_spec_with_comma_and_date",
    ),
    (
        "cost_spec_per_unit_plus_total_marker",
        "transaction_with_per_unit_plus_total_cost",
    ),
    ("metadata_unary_minus_value", "metadata_unary_minus"),
    ("metadata_arithmetic_value", "metadata_arithmetic"),
    ("non_latin_account_names", "non_latin_account_name"),
    ("posting_trailing_comment", "posting_with_trailing_comment"),
    ("multiline_note_string_preserved", "multiline_note_string"),
    ("comment_with_unbalanced_quote", "comment_containing_quote"),
    (
        "transaction_tags_and_links_source_order",
        "transaction_with_tags_and_links",
    ),
    ("custom_directive_with_date_value", "custom_with_date_value"),
    ("options_includes_plugins_block", "options_and_includes"),
    (
        "balance_assertion_with_metadata",
        "balance_assertion_with_meta",
    ),
    ("crlf_outside_strings_folded", "crlf_input"),
];

#[test]
fn format_compat_fixtures_match_expected_output() {
    let cases_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("format_compat")
        .join("cases");
    assert!(
        cases_dir.is_dir(),
        "format_compat cases directory missing at {}",
        cases_dir.display(),
    );

    // Raw directory listing - every subdirectory under cases/,
    // regardless of whether it has an input.bean. The
    // REQUIRED_FIXTURES check runs against this set so the error
    // message disambiguates "dir missing entirely" from "dir
    // present but unloadable". Per-entry errors panic; silently
    // dropping them via `filter_map(Result::ok)` would shrink
    // fixture coverage if a permission / filesystem fault hit one
    // directory. Matches the convention in `tests/baseline_common`.
    let mut all_subdirs: Vec<PathBuf> = fs::read_dir(&cases_dir)
        .unwrap_or_else(|e| panic!("read_dir({}): {e}", cases_dir.display()))
        .map(|entry| {
            entry.unwrap_or_else(|e| {
                panic!("read_dir entry under {} failed: {e}", cases_dir.display())
            })
        })
        .map(|e| e.path())
        .filter(|p| p.is_dir())
        .collect();
    all_subdirs.sort();

    // Name-set coverage floor: every required bug-class fixture
    // must exist as a directory. Non-UTF-8 directory names are
    // included via `to_string_lossy`, matching the harness body
    // and the bootstrap example - silently dropping them via
    // `to_str()` was a recall hole that would have wrongly reported
    // a present-but-non-UTF-8-named REQUIRED fixture as missing.
    let present_names: std::collections::BTreeSet<String> = all_subdirs
        .iter()
        .filter_map(|p| p.file_name().map(|n| n.to_string_lossy().into_owned()))
        .collect();
    let missing_required: Vec<&str> = REQUIRED_FIXTURES
        .iter()
        .copied()
        .filter(|name| !present_names.contains(*name))
        .collect();
    assert!(
        missing_required.is_empty(),
        "format_compat coverage dropped: required fixture(s) missing from cases dir: {missing_required:?}. \
         Each name in REQUIRED_FIXTURES is a load-bearing bug-class pin; \
         removing one is a deliberate change to that constant, not a silent deletion.",
    );

    // MIRROR_PAIRS: every file-pair side must be a directory.
    // The matrix side is checked from the inline unit test
    // `idempotence_matrix_mirrors_format_compat_pairs`.
    let mirror_pair_missing: Vec<&str> = MIRROR_PAIRS
        .iter()
        .filter(|(file_pair, _)| !present_names.contains(*file_pair))
        .map(|(file_pair, _)| *file_pair)
        .collect();
    assert!(
        mirror_pair_missing.is_empty(),
        "MIRROR_PAIRS lists file-pair fixture(s) absent from cases dir: {mirror_pair_missing:?}. \
         Either add the fixture or update the MIRROR_PAIRS constant in tests/format_compat.rs.",
    );

    // Now narrow to directories that actually contain an
    // `input.bean`. An empty subdir would otherwise hit the
    // body and emit a misleading per-fixture error.
    let fixtures: Vec<PathBuf> = all_subdirs
        .iter()
        .filter(|p| p.join("input.bean").is_file())
        .cloned()
        .collect();

    let mut failures: Vec<String> = Vec::new();
    for fixture in &fixtures {
        let name = fixture.file_name().map_or_else(
            || fixture.display().to_string(),
            |n| n.to_string_lossy().into_owned(),
        );
        let input_path = fixture.join("input.bean");
        let expected_path = fixture.join("expected.bean");
        let input = match fs::read_to_string(&input_path) {
            Ok(s) => s,
            Err(e) => {
                failures.push(format!(
                    "[{name}] missing input.bean ({}): {e}",
                    input_path.display(),
                ));
                continue;
            }
        };
        let expected = match fs::read_to_string(&expected_path) {
            Ok(s) => s,
            Err(e) => {
                failures.push(format!(
                    "[{name}] missing expected.bean ({}): {e}",
                    expected_path.display(),
                ));
                continue;
            }
        };

        // Run all three stages independently. A stage-1 mismatch
        // does NOT skip stages 2 and 3 - otherwise an unparsable
        // expected.bean paired with a non-matching formatter output
        // surfaces only as a format mismatch, hiding the bad
        // golden file from the reviewer. Stages 2 and 3 run inside
        // `catch_unwind` so a panic on pathological input is
        // recorded as a fixture failure instead of aborting the
        // whole test and discarding already-recorded failures.

        // (1) format_source(input) == expected
        let formatted = format_source(&input);
        if formatted != expected {
            failures.push(format!(
                "[{name}] format_source(input) != expected\n--- input ---\n{}\n--- expected ---\n{}\n--- got ---\n{}",
                escape_for_diff(&input),
                escape_for_diff(&expected),
                escape_for_diff(&formatted),
            ));
        }

        // (2) idempotence: format_source(expected) == expected
        match catch_unwind(AssertUnwindSafe(|| format_source(&expected))) {
            Ok(twice) => {
                if twice != expected {
                    failures.push(format!(
                        "[{name}] idempotence broken: format_source(expected) != expected\n--- expected ---\n{}\n--- got ---\n{}",
                        escape_for_diff(&expected),
                        escape_for_diff(&twice),
                    ));
                }
            }
            Err(_panic) => {
                failures.push(format!(
                    "[{name}] stage-2 panicked: format_source(expected) raised a panic. \
                     The formatter is contracted to be total over arbitrary input; this is a bug.",
                ));
            }
        }

        // (3) the canonical output parses cleanly
        match catch_unwind(AssertUnwindSafe(|| parse(&expected))) {
            Ok(parsed) => {
                if !parsed.errors.is_empty() {
                    failures.push(format!(
                        "[{name}] expected.bean does not parse cleanly ({} error(s)): {:?}",
                        parsed.errors.len(),
                        parsed.errors,
                    ));
                }
            }
            Err(_panic) => {
                failures.push(format!(
                    "[{name}] stage-3 panicked: parse(expected) raised a panic. \
                     The parser is contracted to be total over arbitrary input; this is a bug.",
                ));
            }
        }
    }

    assert!(
        failures.is_empty(),
        "{} format_compat fixture(s) failed (of {}):\n\n{}",
        failures.len(),
        fixtures.len(),
        failures.join("\n\n"),
    );
}

/// Render a string with visible escape codes for ALL whitespace,
/// control characters, AND invisible-but-printable Unicode (BOM,
/// zero-width spaces, C1 control range, etc.) so a fixture-mismatch
/// diff makes the byte-level difference legible.
///
/// LF still gets the `\n\n` rendering (escape token followed by a
/// real newline) so multi-line strings remain visually aligned in
/// the diff. ASCII printable (U+0020..=U+007E) passes through
/// verbatim. Everything else - including the BOM (U+FEFF, the very
/// byte sequence the `bom_dropped` fixture exists to pin), C1
/// controls (U+0080..=U+009F), zero-width characters
/// (U+200B..=U+200D, U+2060, U+FEFF), and other format-category
/// codepoints - routes through `char::escape_debug`, which renders
/// them as `\u{NN}` so an invisible regression cannot render as a
/// byte-identical diff in the failure output.
///
/// Printable non-ASCII Unicode (Cyrillic, CJK, Greek, etc.) passes
/// through `escape_debug` unchanged because those characters are
/// in the Unicode printable categories.
fn escape_for_diff(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 16);
    for ch in s.chars() {
        match ch {
            '\n' => out.push_str("\\n\n"),
            // ASCII printable passes through unchanged.
            c if (' '..='~').contains(&c) => out.push(c),
            // Everything else routes through escape_debug, which:
            // - escapes CR / tab as `\r` / `\t`
            // - escapes BOM and zero-width chars as `\u{...}`
            // - escapes C0/C1 controls as `\u{...}`
            // - preserves printable non-ASCII Unicode verbatim
            c => {
                for esc in c.escape_debug() {
                    out.push(esc);
                }
            }
        }
    }
    out
}
