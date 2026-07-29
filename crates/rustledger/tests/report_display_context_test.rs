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

#[test]
fn csv_omits_thousands_separators_under_render_commas() {
    // SUPERSEDES `csv_amounts_with_render_commas_are_quoted` (#1750).
    //
    // That test encoded a real review catch: with separators in CSV fields,
    // the fields MUST be quoted (RFC-4180) or a row grows extra columns. The
    // quoting was correct — but #1892 showed that correctly-quoted
    // `"2,357.65"` is still rejected by ordinary decimal parsers, so a
    // consumer could read the row and not the number.
    //
    // CSV now omits separators entirely, which subsumes the original concern:
    // no comma in the field means no quoting, so no column can be split. The
    // column-count assertion below is kept from the original test, since that
    // is the property #1750 actually protected.
    let bin = require_rledger!();
    let source = format!("option \"render_commas\" \"TRUE\"\n{MIXED_PRECISION}");
    let mut f = tempfile::Builder::new()
        .prefix("display-ctx-commas-")
        .suffix(".beancount")
        .tempfile()
        .expect("tempfile");
    f.write_all(source.as_bytes()).expect("write");
    let path = f.path().to_str().unwrap().to_owned();

    let csv = run_report(&bin, &path, &["balances", "--format", "csv"]);
    assert!(
        csv.contains(",2357.65,"),
        "CSV must render the amount unseparated and unquoted: {csv}",
    );
    assert!(
        !csv.contains("2,357.65"),
        "no thousands separator may reach a machine-readable surface: {csv}",
    );
    // Retained from #1750: every data row still has exactly the header's 4
    // columns. Now trivially true (nothing is quoted), which is the point.
    for line in csv.lines().skip(1) {
        let quoted_stripped: String = {
            let mut out = String::new();
            let mut in_q = false;
            for c in line.chars() {
                match c {
                    '\"' => in_q = !in_q,
                    ',' if in_q => out.push('_'),
                    c => out.push(c),
                }
            }
            out
        };
        assert_eq!(
            quoted_stripped.matches(',').count(),
            3,
            "row must have 4 columns outside quotes: {line}",
        );
    }
}
