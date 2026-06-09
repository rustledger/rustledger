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
//! file invisible.
//!
//! New fixtures land here whenever a destructive-formatting bug is
//! reported, fixed, or its absence merits a regression pin.
//!
//! **Coverage floor.** Bug-class coverage is asserted by a
//! [`REQUIRED_FIXTURES`] name-set check, not a fixture count. A
//! count floor (e.g. `len >= 24`) doesn't notice when a critical
//! fixture is swapped for an inert one, and tempts contributors to
//! delete cases up to the floor "to clean up." The name-set check
//! forces the deletion of a load-bearing fixture (BOM, CRLF, #1252
//! repro, etc.) to be a deliberate, reviewable change to this
//! constant - not silent disappearance from the cases directory.

use std::fs;
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

    // Discover only directories that actually contain an
    // `input.bean`. An empty subdir (a `mkdir` without a
    // corresponding `git add` of the file content) would otherwise
    // count toward the fixture set and silently absorb the
    // "missing input.bean" failure alongside a quiet coverage drop
    // elsewhere.
    let mut fixtures: Vec<PathBuf> = fs::read_dir(&cases_dir)
        .unwrap_or_else(|e| panic!("read_dir({}): {e}", cases_dir.display()))
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.is_dir() && p.join("input.bean").is_file())
        .collect();
    fixtures.sort();

    // Name-set coverage floor: every required bug-class fixture
    // must exist, regardless of how many other fixtures are
    // present.
    let present_names: std::collections::BTreeSet<String> = fixtures
        .iter()
        .filter_map(|p| p.file_name().and_then(|n| n.to_str()).map(String::from))
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

    let mut failures: Vec<String> = Vec::new();
    for fixture in &fixtures {
        let name = fixture
            .file_name()
            .and_then(|n| n.to_str())
            .map_or_else(|| fixture.display().to_string(), String::from);
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
        // golden file from the reviewer.

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
        let twice = format_source(&expected);
        if twice != expected {
            failures.push(format!(
                "[{name}] idempotence broken: format_source(expected) != expected\n--- expected ---\n{}\n--- got ---\n{}",
                escape_for_diff(&expected),
                escape_for_diff(&twice),
            ));
        }

        // (3) the canonical output parses cleanly
        let parsed = parse(&expected);
        if !parsed.errors.is_empty() {
            failures.push(format!(
                "[{name}] expected.bean does not parse cleanly ({} error(s)): {:?}",
                parsed.errors.len(),
                parsed.errors,
            ));
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

/// Render a string with visible escape codes for ALL whitespace and
/// control characters so a fixture-mismatch diff makes the byte-
/// level difference legible. The earlier shape only escaped `\n`,
/// `\r`, and `\t`; a mismatch where one side had a stray NUL / BEL
/// / VT / FF would print identically on both sides and the reviewer
/// would chase a phantom bug.
///
/// LF still gets the `\n\n` rendering (escape token followed by a
/// real newline) so multi-line strings remain visually aligned in
/// the diff. CR, tab, and every other control byte are rendered
/// via Rust's `char::escape_debug`, which preserves printable
/// characters verbatim and escapes the rest as `\u{NN}` /
/// `\xNN` / etc.
fn escape_for_diff(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 16);
    for ch in s.chars() {
        match ch {
            '\n' => out.push_str("\\n\n"),
            // Pass printable ASCII verbatim - escape_debug would
            // turn `'` into `\'` and `"` into `\"`, which is more
            // noise than signal in a Beancount fixture diff.
            c if c >= ' ' && c != '\x7f' => out.push(c),
            // Every other control character (CR, tab, NUL, BEL,
            // VT, FF, DEL, etc.) gets a visible escape sequence.
            c => {
                for esc in c.escape_debug() {
                    out.push(esc);
                }
            }
        }
    }
    out
}
