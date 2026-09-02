//! `#balances.discrepancy` reports the balance checker's computed difference
//! for a FAILING assertion, and NULL otherwise (#2180).
//!
//! Measured against beanquery 0.2.0 / beancount 3.2.3 on the same ledger:
//!
//! ```text
//! date,account,amount,tolerance,discrepancy
//! 2024-02-01,Assets:Cash, 100.00 USD,,
//! 2024-03-01,Assets:Cash,  90.00 USD,, 10.00 USD
//! ```
//!
//! `discrepancy` is `computed - asserted`, so asserting 90 against an
//! accumulated 100 gives `+10.00`, and asserting 120 gives `-20.00`.
//!
//! It is NULL when the assertion PASSES -- including when it is off by less
//! than its tolerance, which is why the value cannot be derived from the
//! directive or from the raw difference alone. beancount does the same: its
//! checker sets `diff_amount` only on a failing entry.
//!
//! A CLI test because that is where the whole path is exercised: the loader
//! runs the checker, the checker records the difference, and the query command
//! hands it to the executor. A unit test on the executor would only prove the
//! column renders.

mod common;

use std::process::Command;

/// Accumulates 100.00 USD. The first assertion passes; the second is off by
/// 10.00 and fails; the third is off by 0.01 with a 0.05 tolerance, so it
/// passes despite a non-zero difference.
const SRC: &str = r#"option "inferred_tolerance_default" "USD:0.05"

2024-01-01 open Assets:Cash
2024-01-01 open Equity:O

2024-01-02 * "fund"
  Assets:Cash    100.00 USD
  Equity:O      -100.00 USD

2024-02-01 balance Assets:Cash  100.00 USD
2024-03-01 balance Assets:Cash   90.00 USD
2024-04-01 balance Assets:Cash  100.01 USD
"#;

fn query(bin: &std::path::Path, file: &std::path::Path, q: &str) -> String {
    let out = Command::new(bin)
        .arg("query")
        .arg("-f")
        .arg("csv")
        .arg(file)
        .arg(q)
        .output()
        .expect("run rledger query");
    String::from_utf8(out.stdout).expect("utf8")
}

#[test]
fn discrepancy_is_the_checkers_difference_on_failure_and_null_otherwise() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("ledger.beancount");
    std::fs::write(&file, SRC).expect("write ledger");

    let out = query(
        &bin,
        &file,
        "SELECT date, discrepancy FROM #balances ORDER BY date",
    );
    let rows: Vec<&str> = out.lines().collect();

    assert_eq!(rows[0], "date,discrepancy", "the column must exist");
    assert_eq!(
        rows[1], "2024-02-01,",
        "a passing assertion has no discrepancy",
    );
    assert_eq!(
        rows[2], "2024-03-01,10.00 USD",
        "a failing assertion reports computed - asserted",
    );
    assert_eq!(
        rows[3], "2024-04-01,",
        "off by 0.01 within a 0.05 tolerance is a PASS, so still no \
         discrepancy -- this is what makes the value underivable from the \
         raw difference",
    );
}

/// The sign is `computed - asserted`, not its absolute value and not the
/// reverse. Asserted separately because the failing case above is positive,
/// so a sign flip would not show there.
#[test]
fn discrepancy_is_signed_computed_minus_asserted() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("ledger.beancount");
    std::fs::write(
        &file,
        r#"2024-01-01 open Assets:Cash
2024-01-01 open Equity:O

2024-01-02 * "fund"
  Assets:Cash    100.00 USD
  Equity:O      -100.00 USD

2024-03-01 balance Assets:Cash  120.00 USD
"#,
    )
    .expect("write ledger");

    let out = query(&bin, &file, "SELECT discrepancy FROM #balances");
    assert_eq!(
        out.lines().nth(1),
        Some("-20.00 USD"),
        "asserting 120 against an accumulated 100 is -20.00, matching \
         bean-query; got {out}",
    );
}

/// `SELECT *` includes the column, in bean-query's position: after
/// `tolerance`, and `meta` still excluded.
#[test]
fn the_wildcard_includes_discrepancy_last() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("ledger.beancount");
    std::fs::write(&file, SRC).expect("write ledger");

    let out = query(&bin, &file, "SELECT * FROM #balances");
    assert_eq!(
        out.lines().next(),
        Some("date,account,amount,tolerance,discrepancy"),
        "wildcard must match bean-query's column set and order",
    );
}

/// The failing assertion is still REPORTED, on stderr, and stdout is
/// unaffected. Enabling validation on the query path is what computes the
/// discrepancy; this pins that it did not also start polluting stdout, which
/// every consumer parses.
#[test]
fn validation_diagnostics_do_not_reach_stdout() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("ledger.beancount");
    std::fs::write(&file, SRC).expect("write ledger");

    let out = Command::new(&bin)
        .arg("query")
        .arg("-f")
        .arg("csv")
        .arg(&file)
        .arg("SELECT date FROM #balances")
        .output()
        .expect("run rledger query");

    let stdout = String::from_utf8(out.stdout).expect("utf8");
    let stderr = String::from_utf8(out.stderr).expect("utf8");
    assert!(
        !stdout.contains("Balance failed"),
        "stdout must stay pure data; got {stdout}",
    );
    assert!(
        stderr.contains("Balance failed"),
        "the failing assertion must still be reported somewhere; stderr was {stderr}",
    );
    assert!(
        out.status.success(),
        "a failing assertion must not fail the query, matching bean-query",
    );
}

/// Two assertions on the SAME date, account and currency get their own
/// discrepancies. `(date, account, currency)` does not identify an assertion,
/// and keying on it alone made both rows report the second one's difference.
///
/// bean-query returns `10.00 USD` and `-20.00 USD` here, one per row.
#[test]
fn same_date_assertions_do_not_share_a_discrepancy() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("ledger.beancount");
    std::fs::write(
        &file,
        r#"2024-01-01 open Assets:Cash
2024-01-01 open Equity:O

2024-01-02 * "fund"
  Assets:Cash    100.00 USD
  Equity:O      -100.00 USD

2024-03-01 balance Assets:Cash   90.00 USD
2024-03-01 balance Assets:Cash  120.00 USD
"#,
    )
    .expect("write ledger");

    let out = query(&bin, &file, "SELECT amount, discrepancy FROM #balances");
    let rows: Vec<&str> = out.lines().skip(1).collect();
    assert_eq!(
        rows,
        vec!["90.00 USD,10.00 USD", "120.00 USD,-20.00 USD"],
        "each assertion reports its OWN difference; got {out}",
    );
}
