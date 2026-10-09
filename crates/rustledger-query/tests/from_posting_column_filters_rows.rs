//! A posting column in `FROM` filters ROWS on the posting statements, and is
//! an error in `PRINT` (#2414).
//!
//! beanquery 0.2 compiles the `FROM` expression into the `WHERE` clause
//! (`compiler.py`, `_select`: `c_where = EvalAnd([c_from_expr, c_where])`),
//! after `OPEN` / `CLOSE` / `CLEAR` have rewritten the stream. `PRINT` prints
//! entries, and both bean-query versions reject a posting column there.
//! rledger evaluated the filter once per transaction, against its FIRST
//! posting.
//!
//! Every expected value is beanquery 0.2.0's (beancount 3.2.3) on the same
//! ledger, except the `PRINT` error text, which is rledger's own, and the
//! AVERAGE ledger, which beancount does not book ("AVERAGE method is not
//! supported").

use std::path::Path;

use rustledger_loader::{LoadOptions, Loader, VirtualFileSystem, process};
use rustledger_query::executor::SummaryAccounts;
use rustledger_query::{Executor, Value, parse};

/// The issue's repro plus a second rent payment, on the card. `Assets:Bank`
/// is the first posting of one transaction and the second of two.
const LEDGER: &str = r#"
2024-01-01 open Assets:Bank USD
2024-01-01 open Income:Salary USD
2024-01-01 open Expenses:Rent USD
2024-01-01 open Liabilities:Card USD
2024-01-05 * "pay"
  Assets:Bank      3000.00 USD
  Income:Salary   -3000.00 USD
2024-01-10 * "rent"
  Expenses:Rent    1200.00 USD
  Assets:Bank     -1200.00 USD
2024-02-10 * "rent2"
  Expenses:Rent    1200.00 USD
    pk: "post"
  Liabilities:Card  -1200.00 USD
2024-03-01 * "card payment"
  Liabilities:Card  125.75 USD
  Assets:Bank      -125.75 USD
"#;

/// Two buys and a sale out of an AVERAGE pool: a sale books at the merged
/// cost, a key no buy has, so the account's total must come from booking.
const AVERAGE: &str = r#"
2024-01-01 open Assets:Broker "AVERAGE"
2024-01-01 open Assets:Cash USD
2024-01-01 open Income:Gains USD
2024-01-03 * "buy"
  Assets:Broker   10 X {100.00 USD}
  Assets:Cash  -1000.00 USD
2024-01-04 * "buy"
  Assets:Broker   10 X {200.00 USD}
  Assets:Cash  -2000.00 USD
2024-01-20 * "sell"
  Assets:Broker   -5 X {}
  Assets:Cash    900.00 USD
  Income:Gains   -150.00 USD
"#;

fn cell(value: &Value) -> String {
    match value {
        Value::String(s) => s.clone(),
        Value::Number(n) => n.to_string(),
        Value::Integer(i) => i.to_string(),
        Value::Date(d) => d.to_string(),
        Value::Amount(a) => a.to_string(),
        Value::Position(p) => p.to_string(),
        Value::Inventory(inv) => inv.to_string(),
        Value::Null => String::new(),
        other => format!("{other:?}"),
    }
}

fn run(source: &str, query: &str) -> Result<Vec<Vec<String>>, String> {
    let mut vfs = VirtualFileSystem::new();
    vfs.add_file("main.beancount", source);
    let raw = Loader::new()
        .with_filesystem(Box::new(vfs))
        .load(Path::new("main.beancount"))
        .expect("loads");
    let ledger = process(raw, &LoadOptions::default()).expect("processes");
    assert!(ledger.errors.is_empty(), "{:?}", ledger.errors);
    let mut executor = Executor::new_with_sources(&ledger.directives, &ledger.source_map);
    executor.set_account_types(ledger.options.to_account_types());
    executor.set_booking_method(ledger.booking_method);
    executor.set_summary_accounts(SummaryAccounts::from_options(&ledger.options));
    let result = executor
        .execute(&parse(query).expect("parses"))
        .map_err(|e| e.to_string())?;
    Ok(result
        .rows
        .iter()
        .map(|row| row.iter().map(cell).collect())
        .collect())
}

fn rows(source: &str, query: &str) -> Vec<Vec<String>> {
    run(source, query).unwrap_or_else(|e| panic!("{query}: {e}"))
}

fn table(expected: &[&[&str]]) -> Vec<Vec<String>> {
    expected
        .iter()
        .map(|row| row.iter().map(ToString::to_string).collect())
        .collect()
}

#[test]
fn select_from_a_posting_column_keeps_the_matching_postings() {
    assert_eq!(
        rows(
            LEDGER,
            "SELECT date, account, position FROM account ~ 'Bank'"
        ),
        table(&[
            &["2024-01-05", "Assets:Bank", "3000.00 USD"],
            &["2024-01-10", "Assets:Bank", "-1200.00 USD"],
            &["2024-03-01", "Assets:Bank", "-125.75 USD"],
        ])
    );
    assert_eq!(
        rows(LEDGER, "SELECT sum(position) FROM account ~ 'Bank'"),
        table(&[&["1674.25 USD"]])
    );
    // `balance` runs over the rows FROM and WHERE keep, as beanquery's does.
    assert_eq!(
        rows(LEDGER, "SELECT date, balance FROM number < 0"),
        table(&[
            &["2024-01-05", "-3000.00 USD"],
            &["2024-01-10", "-4200.00 USD"],
            &["2024-02-10", "-5400.00 USD"],
            &["2024-03-01", "-5525.75 USD"],
        ])
    );
    // Posting metadata, not the first posting's.
    assert_eq!(
        rows(LEDGER, "SELECT account FROM meta('pk') = 'post'"),
        table(&[&["Expenses:Rent"]])
    );
    // Joined with WHERE.
    assert_eq!(
        rows(
            LEDGER,
            "SELECT account, sum(position) FROM account ~ 'Bank' WHERE number < 0 GROUP BY account"
        ),
        table(&[&["Assets:Bank", "-1325.75 USD"]])
    );
}

/// The bare-name spelling (#2435) is the same filter.
#[test]
fn a_bare_posting_column_counts_its_rows() {
    assert_eq!(
        rows(LEDGER, "SELECT count(*) FROM number"),
        table(&[&["8"]])
    );
    assert_eq!(rows(LEDGER, "SELECT count(*) FROM id"), table(&[&["8"]]));
    assert_eq!(
        rows(
            LEDGER,
            "SELECT count(*) FROM currency = 'USD' AND number > 0"
        ),
        table(&[&["4"]])
    );
}

/// The filter applies after `OPEN ON` / `CLOSE` / `CLEAR` rewrote the stream,
/// so it sees the summaries.
#[test]
fn the_row_filter_applies_to_the_rewritten_stream() {
    assert_eq!(
        rows(
            LEDGER,
            "SELECT date, account, position FROM account ~ 'Bank' OPEN ON 2024-02-01"
        ),
        table(&[
            &["2024-01-31", "Assets:Bank", "1800.00 USD"],
            &["2024-03-01", "Assets:Bank", "-125.75 USD"],
        ])
    );
    assert_eq!(
        rows(
            LEDGER,
            "SELECT date, account, position FROM account ~ 'Income|Expenses' CLOSE ON 2024-02-15 CLEAR"
        ),
        table(&[
            &["2024-01-05", "Income:Salary", "-3000.00 USD"],
            &["2024-01-10", "Expenses:Rent", "1200.00 USD"],
            &["2024-02-10", "Expenses:Rent", "1200.00 USD"],
            &["2024-02-10", "Expenses:Rent", "-2400.00 USD"],
            &["2024-02-10", "Income:Salary", "3000.00 USD"],
        ])
    );
}

#[test]
fn balances_from_a_posting_column_sums_the_matching_postings() {
    assert_eq!(
        rows(LEDGER, "BALANCES FROM account ~ 'Bank'"),
        table(&[&["Assets:Bank", "1674.25 USD"]])
    );
    assert_eq!(
        rows(LEDGER, "BALANCES FROM number < 0"),
        table(&[
            &["Assets:Bank", "-1325.75 USD"],
            &["Liabilities:Card", "-1200.00 USD"],
            &["Income:Salary", "-3000.00 USD"],
        ])
    );
    assert_eq!(
        rows(
            LEDGER,
            "BALANCES FROM account ~ 'Equity|Bank' OPEN ON 2024-02-01"
        ),
        table(&[
            &["Assets:Bank", "1674.25 USD"],
            &["Equity:Earnings:Previous", "-1800.00 USD"],
            &["Equity:Opening-Balances", "(empty)"],
        ])
    );
}

/// An account whose every posting is selected keeps its booked total; one
/// with some selected is the sum of those, as `SUM(position)` computes it
/// (an AVERAGE pool merged).
#[test]
fn balances_keeps_booking_for_a_wholly_selected_account() {
    assert_eq!(
        rows(AVERAGE, "BALANCES FROM account ~ 'Broker'"),
        table(&[&["Assets:Broker", "15 X { 150.00 USD}"]])
    );
    let partial = rows(AVERAGE, "BALANCES FROM number > 0");
    assert_eq!(
        partial,
        table(&[
            &["Assets:Broker", "20 X { 150.00 USD}"],
            &["Assets:Cash", "900.00 USD"],
        ])
    );
    // The plain sum is `SUM(position)`'s, which BALANCES is sugar for.
    assert_eq!(
        partial,
        rows(
            AVERAGE,
            "SELECT account, sum(position) FROM number > 0 GROUP BY account ORDER BY account"
        )
    );
}

#[test]
fn journal_from_a_posting_column_keeps_the_matching_postings() {
    assert_eq!(
        rows(LEDGER, "JOURNAL 'Bank' FROM account ~ 'Bank'")
            .iter()
            .map(|r| r[6].clone())
            .collect::<Vec<_>>(),
        ["3000.00 USD", "1800.00 USD", "1674.25 USD"]
    );
    assert!(rows(LEDGER, "JOURNAL 'Rent' FROM account ~ 'Bank'").is_empty());
    assert_eq!(
        rows(LEDGER, "JOURNAL FROM number > 0")
            .iter()
            .map(|r| r[4].clone())
            .collect::<Vec<_>>(),
        [
            "Assets:Bank",
            "Expenses:Rent",
            "Expenses:Rent",
            "Liabilities:Card"
        ]
    );
}

#[test]
fn print_rejects_a_posting_column_and_points_at_has_account() {
    for query in [
        "PRINT FROM account ~ 'Bank'",
        "PRINT FROM number > 0",
        "PRINT FROM year = 2024 AND position IS NOT NULL",
    ] {
        let err = run(LEDGER, query).expect_err(query);
        assert!(err.contains("posting column"), "{query}: {err}");
        assert!(err.contains("has_account"), "{query}: {err}");
    }
    // Also on a ledger with nothing to evaluate it on, as beanquery's
    // compiler rejects it.
    let err = run("", "PRINT FROM account ~ 'Bank'").expect_err("empty ledger");
    assert!(err.contains("posting column"), "{err}");
    // An entry predicate is still fine.
    assert!(run(LEDGER, "PRINT FROM has_account('Bank')").is_ok());
}

/// Entry columns keep or drop whole transactions, as before.
#[test]
fn entry_predicates_are_unchanged() {
    assert_eq!(
        rows(LEDGER, "SELECT count(*) FROM has_account('Bank')"),
        table(&[&["6"]])
    );
    assert_eq!(
        rows(LEDGER, "SELECT count(*) FROM narration ~ 'rent'"),
        table(&[&["4"]])
    );
    // A comparison other than `=` on `year` / `month` read as `!=`.
    assert_eq!(
        rows(LEDGER, "SELECT count(*) FROM month >= 2"),
        table(&[&["4"]])
    );
    assert_eq!(
        rows(LEDGER, "SELECT count(*) FROM year < 2024"),
        table(&[&["0"]])
    );
    assert_eq!(
        rows(LEDGER, "SELECT count(*) FROM month = 1"),
        table(&[&["4"]])
    );
}

/// A transaction without postings is printed by an entry filter, and no
/// longer panics (it indexed the first posting).
#[test]
fn a_transaction_without_postings_does_not_panic() {
    let source = "2024-01-01 open Assets:Bank USD\n2024-01-02 * \"empty one\"\n";
    let printed = rows(source, "PRINT FROM narration ~ 'empty'");
    assert!(
        printed.iter().any(|r| r[0].contains("empty one")),
        "{printed:?}"
    );
    assert!(rows(source, "SELECT account FROM narration ~ 'empty'").is_empty());
}
