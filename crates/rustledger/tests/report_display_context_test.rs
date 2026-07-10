//! U4: balance-style reports render numbers through the ledger's
//! `DisplayContext` (per-currency inferred precision), not raw `Decimal`
//! `Display` — whose scale is an artifact of booking arithmetic.
//!
//! The pinned case: a ledger whose USD amounts are conventionally 2dp
//! contains one integer-written posting (`-100 USD`). Pre-U4,
//! `report balances` printed that account's balance as `100 USD` while
//! `bean-query BALANCES` (and our own BQL output, which has used the
//! context since #961/#985) printed `100.00 USD`. The fixture output
//! below was verified byte-identical against beancount 3.2.3's
//! bean-query rendering.

mod common;

use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

// USD samples: four 2dp amounts and two integer-written ones, so the
// per-currency mode (`Precision::MostCommon`, matching bean-query) is 2dp
// and the integer-written transfer must be padded to `100.00`.
const MIXED_PRECISION: &str = r#"2024-01-01 open Assets:Bank
2024-01-01 open Assets:Broker
2024-01-01 open Income:Salary
2024-01-01 open Expenses:Food

2024-01-15 * "salary"
  Assets:Bank    2500.00 USD
  Income:Salary -2500.00 USD

2024-02-01 * "groceries"
  Assets:Bank     -42.35 USD
  Expenses:Food    42.35 USD

2024-02-10 * "integer-written transfer"
  Assets:Bank      -100 USD
  Assets:Broker     100 USD
"#;

fn run_report(binary: &PathBuf, path: &str, args: &[&str]) -> String {
    let out = Command::new(binary)
        .arg("report")
        .arg(path)
        .args(args)
        .arg("--no-pager")
        .output()
        .expect("run rledger report");
    assert!(
        out.status.success(),
        "report failed: {}",
        String::from_utf8_lossy(&out.stderr),
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

#[test]
fn balances_render_at_ledger_precision() {
    let bin = require_rledger!();
    let mut f = tempfile::Builder::new()
        .prefix("display-ctx-")
        .suffix(".beancount")
        .tempfile()
        .expect("tempfile");
    f.write_all(MIXED_PRECISION.as_bytes()).expect("write");
    let path = f.path().to_str().unwrap().to_owned();

    let text = run_report(&bin, &path, &["balances"]);
    assert!(
        text.contains("100.00 USD"),
        "integer-written USD amounts must render at the ledger's 2dp \
         convention (bean-query parity), got: {text}",
    );
    assert!(
        !text.contains(" 100 USD"),
        "raw booking-scale rendering must not leak through: {text}",
    );

    // CSV carries the same formatted numbers (one rendering per report,
    // not per output format).
    let csv = run_report(&bin, &path, &["balances", "--format", "csv"]);
    assert!(
        csv.contains(",100.00,USD"),
        "CSV must use the same context-formatted numbers: {csv}",
    );
}

#[test]
fn income_totals_render_at_ledger_precision() {
    let bin = require_rledger!();
    let mut f = tempfile::Builder::new()
        .prefix("display-ctx-income-")
        .suffix(".beancount")
        .tempfile()
        .expect("tempfile");
    f.write_all(MIXED_PRECISION.as_bytes()).expect("write");
    let path = f.path().to_str().unwrap().to_owned();

    let text = run_report(&bin, &path, &["income"]);
    assert!(
        text.contains("-2500.00 USD") && text.contains("2500.00 USD"),
        "income statement must render at ledger precision: {text}",
    );
}
