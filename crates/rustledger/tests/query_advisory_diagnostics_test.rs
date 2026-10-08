//! `rledger query` does not print advisory-only diagnostics.
//!
//! Closing an account that still holds a balance is E1004, which is
//! advisory-only: beancount does not flag it, so `bean-check` and `bean-query`
//! print nothing, and `rledger check` skips it too. `query` runs validation
//! (for `#balances.discrepancy`, #2238) and used to print every diagnostic,
//! so the same ledger came out of `check` clean and out of `query` with an
//! error on stderr.
//!
//! Real diagnostics on the same load are still printed.

mod common;

use std::process::Command;

/// `Expenses:Food` is closed holding 12.50 USD.
const CLOSED_WITH_BALANCE: &str = r#"2024-01-01 open Assets:Cash
2024-01-01 open Expenses:Food

2024-01-07 * "lunch"
  Expenses:Food  12.50 USD
  Assets:Cash

2024-02-20 close Expenses:Food
"#;

fn query_stderr(bin: &std::path::Path, src: &str) -> String {
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("ledger.beancount");
    std::fs::write(&file, src).expect("write ledger");
    let out = Command::new(bin)
        .arg("query")
        .arg("--no-cache")
        .arg(&file)
        .arg("SELECT count(*)")
        .output()
        .expect("run rledger query");
    assert!(out.status.success(), "query must succeed: {out:?}");
    String::from_utf8(out.stderr).expect("utf8")
}

#[test]
fn query_does_not_print_close_with_balance() {
    let bin = require_rledger!();
    let stderr = query_stderr(&bin, CLOSED_WITH_BALANCE);
    assert!(
        !stderr.contains("E1004"),
        "E1004 is advisory-only; bean-query and `check` are silent: {stderr}"
    );
    assert!(stderr.trim().is_empty(), "nothing else to report: {stderr}");
}

#[test]
fn query_still_prints_real_diagnostics_next_to_an_advisory_one() {
    let bin = require_rledger!();
    let src = format!("{CLOSED_WITH_BALANCE}2024-01-08 balance Assets:Cash  5 USD\n");
    let stderr = query_stderr(&bin, &src);
    assert!(
        stderr.contains("E2001"),
        "the failing balance is reported: {stderr}"
    );
    assert!(!stderr.contains("E1004"), "the advisory is not: {stderr}");
}
