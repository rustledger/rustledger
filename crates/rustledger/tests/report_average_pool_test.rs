//! `report balances` presents an AVERAGE account as its pool, before a sale
//! and after one, with the per-unit cost rounded for display (#2543).
//!
//! Before the first sale it listed booking's separate dated lots, and after
//! it the pool's per-unit cost at full `Decimal` precision
//! (`{ 166.66666666666666666666666667 USD}`), where BQL renders the same pool
//! through the display context. `report capgains` reads booking's dated lots,
//! which this does not touch, so it is unchanged.

mod common;

use std::path::Path;
use std::process::Command;

const BUYS: &str = r#"2024-01-01 open Assets:Cash USD
2024-01-01 open Assets:Brokerage X "AVERAGE"
2024-01-01 open Income:Gains USD
2024-01-02 * "buy"
  Assets:Brokerage   1 X {100 USD}
  Assets:Cash
2024-01-03 * "buy"
  Assets:Brokerage   2 X {200 USD}
  Assets:Cash
"#;

const SALE: &str = r#"2024-01-04 * "sell"
  Assets:Brokerage  -1 X {} @ 300 USD
  Assets:Cash        300 USD
  Income:Gains
"#;

fn run(bin: &Path, source: &str, args: &[&str]) -> String {
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("ledger.beancount");
    std::fs::write(&file, source).expect("write ledger");
    let out = Command::new(bin)
        .arg("report")
        .arg("--no-cache")
        .arg(&file)
        .args(args)
        .env("HOME", dir.path())
        .env("XDG_CONFIG_HOME", dir.path())
        .output()
        .expect("run rledger report");
    assert!(
        out.status.success(),
        "rledger report {args:?}: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).expect("utf8")
}

/// The brokerage account's rows of `report balances --format csv`.
fn brokerage_rows(bin: &Path, source: &str) -> Vec<String> {
    run(bin, source, &["balances", "--format", "csv"])
        .lines()
        .filter(|l| l.starts_with("Assets:Brokerage,"))
        .map(str::to_string)
        .collect()
}

#[test]
fn the_pool_before_the_sale() {
    let bin = require_rledger!();
    // 1 X at 100 and 2 X at 200 are one pool, 3 X at 500/3, shown at the
    // ledger's USD precision (whole units here).
    assert_eq!(
        brokerage_rows(&bin, BUYS),
        ["Assets:Brokerage,3,X,{ 167 USD}"]
    );
    let text = run(&bin, BUYS, &["balances"]);
    assert!(text.contains("3 X { 167 USD}"), "{text}");
    assert!(!text.contains("2024-01-02"), "no dated lot: {text}");
}

#[test]
fn the_pool_after_the_sale_is_rounded_for_display() {
    let bin = require_rledger!();
    let ledger = format!("{BUYS}{SALE}");
    assert_eq!(
        brokerage_rows(&bin, &ledger),
        ["Assets:Brokerage,2,X,{ 167 USD}"]
    );
    let text = run(&bin, &ledger, &["balances"]);
    assert!(text.contains("2 X { 167 USD}"), "{text}");
    assert!(!text.contains("166.666"), "rounded for display: {text}");
}

/// A dated lot of an account that is not AVERAGE keeps its lots and dates;
/// only its cost is rendered through the display context.
#[test]
fn other_accounts_keep_their_lots() {
    let bin = require_rledger!();
    let ledger = r#"2024-01-01 open Assets:Cash USD
2024-01-01 open Assets:Fifo X "FIFO"
2024-01-02 * "buy"
  Assets:Fifo   1 X {100.00 USD}
  Assets:Cash
2024-01-03 * "buy"
  Assets:Fifo   2 X {200.00 USD}
  Assets:Cash
"#;
    let rows: Vec<String> = run(&bin, ledger, &["balances", "--format", "csv"])
        .lines()
        .filter(|l| l.starts_with("Assets:Fifo,"))
        .map(str::to_string)
        .collect();
    assert_eq!(
        rows,
        [
            "Assets:Fifo,1,X,\"{ 100.00 USD, 2024-01-02}\"",
            "Assets:Fifo,2,X,\"{ 200.00 USD, 2024-01-03}\"",
        ]
    );
}

/// `report capgains` is unchanged: it reads the disposal booking recorded,
/// not the presented pool.
#[test]
fn capgains_is_unchanged() {
    let bin = require_rledger!();
    let ledger = format!("{BUYS}{SALE}");
    let csv = run(&bin, &ledger, &["capgains", "--format", "csv"]);
    assert_eq!(
        csv.lines().collect::<Vec<_>>(),
        [
            "sold,account,commodity,units,acquired,held_days,term,currency,proceeds,cost_basis,gain",
            "2024-01-04,Assets:Brokerage,X,1,,,unknown,USD,300,166.6666666666666666666666667,133.3333333333333333333333333",
        ]
    );
}
