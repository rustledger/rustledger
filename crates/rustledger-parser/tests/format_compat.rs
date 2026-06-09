//! Format-compat suite — phase 4.2 of the CST migration (#1262).
//!
//! Pins the formatter's promise on the historical destructive-formatting
//! bug classes (#1142, #1156, #1157, #1252, plus the regressions surfaced
//! during PR #1284's seven review rounds). Each subdirectory of
//! `tests/format_compat/cases/` is one fixture:
//!
//! - `input.bean` — what the user typed (or an editor stored).
//! - `expected.bean` — the byte-exact output `format_source` MUST emit.
//!
//! The harness asserts:
//!
//! 1. `format_source(input) == expected` — the formatter renders the
//!    fixture exactly as documented.
//! 2. `format_source(expected) == expected` — idempotence: re-formatting
//!    canonical text is a no-op.
//! 3. The parser produces zero errors on `expected` — the canonical
//!    output is itself parseable.
//!
//! New fixtures land here whenever a destructive-formatting bug is
//! reported, fixed, or its absence merits a regression pin. The fixture
//! count is asserted against a floor so a future contributor deleting
//! cases by accident fails CI instead of silently dropping coverage.

use std::fs;
use std::path::{Path, PathBuf};

use rustledger_parser::format::format_source;
use rustledger_parser::parse;

/// Minimum number of fixtures the harness must discover. The issue
/// #1262 phase 4.2 goal is "the #1252 reproduction plus 20+
/// destructive-formatting fixtures." Adding cases is encouraged;
/// removing them requires either deleting this assert (don't) or
/// lowering the floor with a justification in the PR description.
const MIN_FIXTURES: usize = 24;

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

    let mut fixtures: Vec<PathBuf> = fs::read_dir(&cases_dir)
        .unwrap_or_else(|e| panic!("read_dir({}): {e}", cases_dir.display()))
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.is_dir())
        .collect();
    fixtures.sort();

    assert!(
        fixtures.len() >= MIN_FIXTURES,
        "format_compat coverage dropped: found {} fixtures, expected at least {} \
         (cases dir: {}). Did a recent change delete a regression case?",
        fixtures.len(),
        MIN_FIXTURES,
        cases_dir.display(),
    );

    let mut failures: Vec<String> = Vec::new();
    for fixture in &fixtures {
        let name = fixture
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or("<non-utf8 fixture name>");
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

        // (1) format_source(input) == expected
        let formatted = format_source(&input);
        if formatted != expected {
            failures.push(format!(
                "[{name}] format_source(input) != expected\n--- input ---\n{}\n--- expected ---\n{}\n--- got ---\n{}",
                escape_for_diff(&input),
                escape_for_diff(&expected),
                escape_for_diff(&formatted),
            ));
            continue;
        }

        // (2) idempotence: format_source(expected) == expected
        let twice = format_source(&expected);
        if twice != expected {
            failures.push(format!(
                "[{name}] idempotence broken: format_source(expected) != expected\n--- expected ---\n{}\n--- got ---\n{}",
                escape_for_diff(&expected),
                escape_for_diff(&twice),
            ));
            continue;
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

/// Render a string with visible escape codes for newlines, carriage
/// returns, and tabs so a fixture-mismatch diff makes the whitespace
/// difference legible. Without this, a trailing-newline-vs-no-newline
/// drift looks identical in the test output.
fn escape_for_diff(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 16);
    for ch in s.chars() {
        match ch {
            '\n' => out.push_str("\\n\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c => out.push(c),
        }
    }
    out
}
