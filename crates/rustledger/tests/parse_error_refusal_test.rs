//! `query` and `report` must not report numbers from a file that failed to parse.
//!
//! A deliberate deviation from bean-query (#1908), which prints what it
//! recovered and exits 0. The output there is not merely incomplete, it is
//! *plausible* — a truncated ledger yields figures that look like an answer,
//! with a success status, on stdout another program is probably consuming.
//!
//! The deviation is scoped to PARSE errors. Validation errors leave the entry
//! stream complete and the arithmetic sound, so those must keep reporting
//! exactly as beancount does; a test for that is below, because narrowing the
//! deviation is the whole reason it is acceptable.

use std::process::Command;

mod common;

fn write(name: &str, body: &str) -> (tempfile::TempDir, String) {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join(name);
    std::fs::write(&path, body).expect("write");
    let p = path.to_str().expect("utf8").to_owned();
    (dir, p)
}

const QUERY: &str = "SELECT account, sum(number) AS n GROUP BY account";

#[test]
fn query_refuses_a_file_that_failed_to_parse() {
    let bin = require_rledger!();
    let (_d, path) = write(
        "broken.beancount",
        "2020-01-01 open Assets:A\n\
         this is not valid beancount at all !!!\n\
         2020-01-02 * \"x\"\n  Assets:A  5 USD\n  Assets:A -5 USD\n",
    );

    let out = Command::new(AsRef::<std::path::Path>::as_ref(&bin))
        .args(["query", "--format", "csv", &path, QUERY])
        .output()
        .expect("run");

    assert!(
        !out.status.success(),
        "must not report success on a file that did not parse"
    );
    assert!(
        String::from_utf8_lossy(&out.stdout).trim().is_empty(),
        "must emit NO rows; bean-query prints `Assets:A 0` here, which is the \
         plausible-but-wrong output this exists to prevent: {}",
        String::from_utf8_lossy(&out.stdout)
    );
    assert!(
        String::from_utf8_lossy(&out.stderr).contains("parse error"),
        "the refusal must say why: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn report_refuses_a_file_that_failed_to_parse() {
    let bin = require_rledger!();
    let (_d, path) = write(
        "broken.beancount",
        "2020-01-01 open Assets:A\nnot valid !!!\n",
    );

    let out = Command::new(AsRef::<std::path::Path>::as_ref(&bin))
        .args(["report", &path, "balances"])
        .output()
        .expect("run");

    assert!(
        !out.status.success(),
        "report must refuse too, not just query"
    );
}

/// The other half of the contract, and the reason the deviation is narrow
/// enough to be acceptable: a ledger that PARSES but fails validation still
/// reports, exactly as beancount does. Real ledgers are full of accounts
/// missing an `open`, and refusing those would be a genuine compatibility
/// loss for no safety gain — the entry stream is complete and the arithmetic
/// is sound.
#[test]
fn validation_errors_still_report_as_beancount_does() {
    let bin = require_rledger!();
    let (_d, path) = write(
        "unopened.beancount",
        "2020-01-02 * \"x\"\n  Assets:A  5 USD\n  Assets:A -5 USD\n",
    );

    // Precondition: the fixture must ACTUALLY fail validation, or this test
    // passes while pinning nothing. `check` refuses it; `query` must not.
    let checked = Command::new(AsRef::<std::path::Path>::as_ref(&bin))
        .args(["check", &path])
        .output()
        .expect("run check");
    assert!(
        !checked.status.success(),
        "fixture must fail validation for this test to mean anything"
    );
    assert!(
        !String::from_utf8_lossy(&checked.stdout).contains("parse error")
            && !String::from_utf8_lossy(&checked.stderr).contains("parse error"),
        "...and must fail on VALIDATION, not parsing, or it is testing the \
         other branch: {}{}",
        String::from_utf8_lossy(&checked.stdout),
        String::from_utf8_lossy(&checked.stderr)
    );

    let out = Command::new(AsRef::<std::path::Path>::as_ref(&bin))
        .args(["query", "--format", "csv", &path, QUERY])
        .output()
        .expect("run");

    assert!(
        out.status.success(),
        "a parseable file with validation errors must still report: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        String::from_utf8_lossy(&out.stdout).contains("Assets:A"),
        "and must emit its rows: {}",
        String::from_utf8_lossy(&out.stdout)
    );
}
