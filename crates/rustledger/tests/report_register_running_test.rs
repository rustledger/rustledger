//! `rledger report register` and `report journal --running` (#2741): the
//! running-balance column.
//!
//! The running total is the mixed inventory of the postings `--account`
//! matched (every posting when there is no filter), shown after each
//! posting. It is computed over the whole report before `--limit` drops rows
//! from the top, and a windowed report's opening-balance summaries sort
//! first among same-date rows so the totals carry the pre-window balances
//! in from the first row.

mod common;

use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

use serde_json::Value;

const LEDGER: &str = r#"option "operating_currency" "USD"

2024-01-01 open Assets:Bank USD
2024-01-01 open Assets:Euro EUR
2024-01-01 open Expenses:Food USD
2024-01-01 open Income:Salary USD

2024-01-05 * "salary"
  Assets:Bank  1000.00 USD
  Income:Salary

2024-01-06 * "groceries"
  Expenses:Food  50.00 USD
  Assets:Bank

2024-01-07 * "fx"
  Assets:Euro  200.00 EUR @@ 220.00 USD
  Assets:Bank  -220.00 USD

2024-01-08 * "lunch"
  Expenses:Food  12.50 USD
  Assets:Bank
"#;

fn write_fixture(source: &str) -> tempfile::NamedTempFile {
    let mut f = tempfile::Builder::new()
        .prefix("report-register-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(source.as_bytes()).expect("write fixture");
    f
}

fn run_raw(binary: &PathBuf, args: &[&str]) -> std::process::Output {
    Command::new(binary)
        .args(args)
        .arg("--no-pager")
        .output()
        .unwrap_or_else(|e| panic!("run rledger {args:?}: {e}"))
}

fn run(binary: &PathBuf, args: &[&str]) -> String {
    let out = run_raw(binary, args);
    assert!(
        out.status.success(),
        "rledger {args:?} failed: {}",
        String::from_utf8_lossy(&out.stderr),
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn json(binary: &PathBuf, args: &[&str]) -> Value {
    let stdout = run(binary, args);
    serde_json::from_str(&stdout).unwrap_or_else(|e| panic!("not JSON ({e}): {stdout}"))
}

/// `(account, running_total)` for every posting row, in order.
fn running_rows(v: &Value) -> Vec<(String, String)> {
    let mut out = Vec::new();
    for txn in v.as_array().expect("journal is an array") {
        for p in txn["postings"].as_array().expect("postings array") {
            out.push((
                p["account"].as_str().expect("account").to_string(),
                p["running_total"]
                    .as_str()
                    .expect("running_total field")
                    .to_string(),
            ));
        }
    }
    out
}

fn rows(pairs: &[(&str, &str)]) -> Vec<(String, String)> {
    pairs
        .iter()
        .map(|(a, r)| (a.to_string(), r.to_string()))
        .collect()
}

#[test]
fn register_is_the_journal_plus_the_running_column() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();

    // No payee in this ledger, so the description lines never contain the
    // payee/narration separator and a `|` can only be the column's.
    let journal = run(&bin, &["report", path, "journal"]);
    assert!(journal.starts_with("Transaction Journal"), "{journal}");
    assert!(
        !journal.contains(" | "),
        "plain journal must stay columnless: {journal}"
    );

    let register = run(&bin, &["report", path, "register"]);
    assert!(register.starts_with("Transaction Register"), "{register}");
    assert!(
        register.contains(" | 1000.00 USD"),
        "register must carry the running column: {register}"
    );

    let journal_running = run(&bin, &["report", path, "journal", "--running"]);
    assert!(
        journal_running.starts_with("Transaction Journal"),
        "{journal_running}"
    );
    assert!(
        journal_running.contains(" | 1000.00 USD"),
        "journal --running must carry the running column: {journal_running}"
    );
}

#[test]
fn running_total_is_the_mixed_inventory_of_every_posting_shown() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();

    let v = json(&bin, &["report", path, "-f", "json", "register"]);
    // Unfiltered, every posting moves the total — so a balanced ledger's
    // column zigzags back to zero like hledger's, and stays non-zero only
    // where a cost/price conversion changed the currency mix (the fx row).
    assert_eq!(
        running_rows(&v),
        rows(&[
            ("Assets:Bank", "1000.00 USD"),
            ("Income:Salary", ""),
            ("Expenses:Food", "50.00 USD"),
            ("Assets:Bank", ""),
            ("Assets:Euro", "200.00 EUR"),
            ("Assets:Bank", "200.00 EUR, -220.00 USD"),
            ("Expenses:Food", "200.00 EUR, -207.50 USD"),
            ("Assets:Bank", "200.00 EUR, -220.00 USD"),
        ])
    );
}

#[test]
fn running_total_counts_only_the_postings_the_account_filter_matched() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();

    // The journal filter keeps whole transactions, so both legs of each are
    // shown — but only the matched legs move the total, which is what makes
    // `--account Assets:Bank` read as the bank balance over time.
    let v = json(
        &bin,
        &[
            "report",
            path,
            "-f",
            "json",
            "register",
            "--account",
            "Assets:Bank",
        ],
    );
    assert_eq!(
        running_rows(&v),
        rows(&[
            ("Assets:Bank", "1000.00 USD"),
            ("Income:Salary", "1000.00 USD"),
            ("Expenses:Food", "1000.00 USD"),
            ("Assets:Bank", "950.00 USD"),
            ("Assets:Euro", "950.00 USD"),
            ("Assets:Bank", "730.00 USD"),
            ("Expenses:Food", "730.00 USD"),
            ("Assets:Bank", "717.50 USD"),
        ])
    );
}

#[test]
fn the_total_as_of_each_row_survives_limit_dropping_rows() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();

    // `--limit` drops rows from the top: the two rows it keeps are fx and
    // lunch, and their totals still carry salary and groceries.
    let v = json(
        &bin,
        &["report", path, "-f", "json", "register", "--limit", "2"],
    );
    assert_eq!(
        running_rows(&v),
        rows(&[
            ("Assets:Euro", "200.00 EUR"),
            ("Assets:Bank", "200.00 EUR, -220.00 USD"),
            ("Expenses:Food", "200.00 EUR, -207.50 USD"),
            ("Assets:Bank", "200.00 EUR, -220.00 USD"),
        ])
    );
}

#[test]
fn windowed_register_carries_the_opening_balances_in() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();

    // The window starts on fx's own date, which is where an opening-balance
    // summary and a real transaction collide: the summary sorts first (it IS
    // the pre-window history), so even the first row's total is the bank's
    // carried-in 950.00 USD and not zero.
    let v = json(
        &bin,
        &[
            "report",
            path,
            "-f",
            "json",
            "register",
            "--from",
            "2024-01-07",
            "--account",
            "Assets:Bank",
        ],
    );
    let txns = v.as_array().expect("journal is an array");
    assert_eq!(txns[0]["flag"], "S", "{v}");
    assert_eq!(txns[0]["narration"], "Opening balance", "{v}");
    assert_eq!(
        running_rows(&v),
        rows(&[
            ("Assets:Bank", "950.00 USD"),
            ("Equity:Opening-Balances", "950.00 USD"),
            ("Assets:Euro", "950.00 USD"),
            ("Assets:Bank", "730.00 USD"),
            ("Expenses:Food", "730.00 USD"),
            ("Assets:Bank", "717.50 USD"),
        ])
    );
}

#[test]
fn csv_carries_the_running_total_column_and_quotes_it() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();

    let csv = run(&bin, &["report", path, "-f", "csv", "register"]);
    assert_eq!(
        csv.lines().next(),
        Some("date,flag,payee,narration,account,amount,currency,running_total"),
        "{csv}"
    );
    // The mixed total contains a comma, so the field must be escaped.
    assert!(
        csv.contains(",\"200.00 EUR, -220.00 USD\""),
        "the running total must be CSV-escaped: {csv}"
    );

    let plain = run(&bin, &["report", path, "-f", "csv", "journal"]);
    assert_eq!(
        plain.lines().next(),
        Some("date,flag,payee,narration,account,amount,currency"),
        "{plain}"
    );
}

#[test]
fn json_running_total_only_when_asked_for() {
    let bin = require_rledger!();
    let f = write_fixture(LEDGER);
    let path = f.path().to_str().unwrap();

    let v = json(&bin, &["report", path, "-f", "json", "journal"]);
    for txn in v.as_array().expect("journal is an array") {
        for p in txn["postings"].as_array().expect("postings array") {
            assert!(
                p.get("running_total").is_none(),
                "plain journal must stay columnless: {v}"
            );
        }
    }
}
