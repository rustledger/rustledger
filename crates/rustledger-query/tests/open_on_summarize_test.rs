//! `FROM ... OPEN ON` summarizes the ledger before the date, as beanquery does
//! with beancount's `summarize.open` (#2401).
//!
//! Every expected value below is bean-query's (beanquery 0.2.0, beancount
//! 3.2.3) on the same ledger, except where a test says otherwise.

use std::path::Path;

use rustledger_loader::{LoadOptions, Loader, VirtualFileSystem, process};
use rustledger_query::executor::SummaryAccounts;
use rustledger_query::{Executor, Value, parse};

/// A cell as a string: the core types' own `Display`, empty for NULL.
fn cell(value: &Value) -> String {
    match value {
        Value::String(s) => s.clone(),
        Value::Number(n) => n.to_string(),
        Value::Integer(i) => i.to_string(),
        Value::Date(d) => d.to_string(),
        Value::Boolean(b) => b.to_string(),
        Value::Amount(a) => a.to_string(),
        Value::Position(p) => p.to_string(),
        Value::Inventory(inv) => inv.to_string(),
        Value::Null => String::new(),
        other => format!("{other:?}"),
    }
}

/// A booked ledger, as the CLI queries it.
fn load(source: &str) -> rustledger_loader::Ledger {
    let mut vfs = VirtualFileSystem::new();
    vfs.add_file("main.beancount", source);
    let raw = Loader::new()
        .with_filesystem(Box::new(vfs))
        .load(Path::new("main.beancount"))
        .expect("loads");
    let ledger = process(raw, &LoadOptions::default()).expect("processes");
    assert!(
        ledger.errors.is_empty(),
        "fixture must be clean: {:?}",
        ledger.errors
    );
    ledger
}

/// Every row of `query` as its cells' `Display` strings.
fn rows(source: &str, query: &str) -> Vec<Vec<String>> {
    let ledger = load(source);
    // The source-aware constructor, as the CLI builds it, so real rows carry
    // a location and a summary row's missing one is observable.
    let mut executor = Executor::new_with_sources(&ledger.directives, &ledger.source_map);
    executor.set_account_types(ledger.options.to_account_types());
    executor.set_booking_method(ledger.booking_method);
    executor.set_summary_accounts(SummaryAccounts::from_options(&ledger.options));
    let result = executor
        .execute(&parse(query).expect("parses"))
        .unwrap_or_else(|e| panic!("{query}: {e}"));
    result
        .rows
        .iter()
        .map(|row| row.iter().map(cell).collect())
        .collect()
}

const OPENING: &str = r#"
2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD
2024-01-01 open Equity:Opening USD

2024-01-05 * "opening"
  Assets:Bank      1000.00 USD
  Equity:Opening  -1000.00 USD

2024-02-10 * "lunch"
  Expenses:Food      20.00 USD
  Assets:Bank       -20.00 USD
"#;

const LOTS: &str = r#"
2024-01-01 open Assets:Broker
2024-01-01 open Assets:Cash USD
2024-01-01 open Income:Gains USD
2024-01-01 open Expenses:Fees USD
2024-01-03 * "buy a"
  Assets:Broker   10 AAPL {150.00 USD, "a"}
  Assets:Cash  -1500.00 USD
2024-01-04 * "buy b"
  Assets:Broker   5 AAPL {160.00 USD}
  Assets:Cash   -800.00 USD
2024-01-20 * "sell part of a"
  Assets:Broker   -4 AAPL {150.00 USD, "a"} @ 170.00 USD
  Assets:Cash    675.00 USD
  Expenses:Fees    5.00 USD
  Income:Gains   -80.00 USD
2024-02-10 * "buy c"
  Assets:Broker   2 AAPL {165.00 USD}
  Assets:Cash   -330.00 USD
2024-02-20 * "sell b"
  Assets:Broker   -5 AAPL {160.00 USD} @ 172.00 USD
  Assets:Cash    860.00 USD
  Income:Gains   -60.00 USD
"#;

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

const EARNINGS: &str = r#"
2024-01-01 open Assets:Bank USD
2024-01-01 open Income:Salary USD
2024-01-01 open Expenses:Food USD
2024-01-01 open Expenses:Rent USD
2024-01-01 open Liabilities:Card USD
2024-01-05 * "pay"
  Assets:Bank      3000.00 USD
  Income:Salary   -3000.00 USD
2024-01-10 * "rent"
  Expenses:Rent    1200.00 USD
  Assets:Bank     -1200.00 USD
2024-01-20 * "dinner" #food
  Expenses:Food      45.50 USD
  Liabilities:Card  -45.50 USD
2024-02-05 * "pay"
  Assets:Bank      3000.00 USD
  Income:Salary   -3000.00 USD
2024-02-12 * "groceries"
  Expenses:Food      80.25 USD
  Liabilities:Card  -80.25 USD
2024-03-01 * "card payment"
  Liabilities:Card  125.75 USD
  Assets:Bank      -125.75 USD
"#;

const CONVERSIONS: &str = r#"
2024-01-01 open Assets:USD USD
2024-01-01 open Assets:EUR EUR
2024-01-01 open Equity:Opening USD
2024-01-01 open Expenses:Travel EUR
2024-01-02 * "fund"
  Assets:USD       1000.00 USD
  Equity:Opening  -1000.00 USD
2024-01-10 * "exchange"
  Assets:EUR   100.00 EUR @ 1.10 USD
  Assets:USD  -110.00 USD
2024-01-15 * "spend"
  Expenses:Travel  30.00 EUR
  Assets:EUR      -30.00 EUR
2024-02-10 * "exchange back"
  Assets:USD    55.00 USD
  Assets:EUR   -50.00 EUR @ 1.10 USD
2024-02-20 * "spend"
  Expenses:Travel  10.00 EUR
  Assets:EUR      -10.00 EUR
"#;

/// Compare rows to `expected`, cell for cell.
fn assert_rows(actual: &[Vec<String>], expected: &[&[&str]], what: &str) {
    let actual: Vec<Vec<&str>> = actual
        .iter()
        .map(|row| row.iter().map(String::as_str).collect())
        .collect();
    let expected: Vec<Vec<&str>> = expected.iter().map(|row| row.to_vec()).collect();
    assert_eq!(actual, expected, "{what}");
}

/// The issue's shape: the period's rows start with one summary per account,
/// dated the day before, and the running `balance` carries them in.
#[test]
fn rows_start_from_the_summarized_balances() {
    assert_rows(
        &rows(
            OPENING,
            "SELECT date, flag, account, position, balance FROM OPEN ON 2024-02-01",
        ),
        &[
            &[
                "2024-01-31",
                "S",
                "Assets:Bank",
                "1000.00 USD",
                "1000.00 USD",
            ],
            &[
                "2024-01-31",
                "S",
                "Equity:Opening-Balances",
                "-1000.00 USD",
                "(empty)",
            ],
            &[
                "2024-01-31",
                "S",
                "Equity:Opening",
                "-1000.00 USD",
                "-1000.00 USD",
            ],
            &[
                "2024-01-31",
                "S",
                "Equity:Opening-Balances",
                "1000.00 USD",
                "(empty)",
            ],
            &["2024-02-10", "*", "Expenses:Food", "20.00 USD", "20.00 USD"],
            &["2024-02-10", "*", "Assets:Bank", "-20.00 USD", "(empty)"],
        ],
        "bean-query's rows",
    );
    assert_rows(
        &rows(
            OPENING,
            "SELECT account, sum(position) FROM OPEN ON 2024-02-01 GROUP BY account ORDER BY account",
        ),
        &[
            &["Assets:Bank", "980.00 USD"],
            &["Equity:Opening", "-1000.00 USD"],
            &["Equity:Opening-Balances", "(empty)"],
            &["Expenses:Food", "20.00 USD"],
        ],
        "a balance-sheet account's period total includes its opening balance",
    );
    assert_rows(
        &rows(
            OPENING,
            "SELECT DISTINCT narration FROM OPEN ON 2024-02-01 WHERE flag = 'S'",
        ),
        &[
            &["Opening balance for 'Assets:Bank' (Summarization)"],
            &["Opening balance for 'Equity:Opening' (Summarization)"],
        ],
        "beancount's summary narration",
    );
}

/// Income and expenses before the date are cleared to
/// `account_previous_earnings`, so the period's income statement starts at
/// zero. rledger used to carry them in the income-statement accounts.
#[test]
fn income_and_expenses_before_the_date_move_to_previous_earnings() {
    assert_rows(
        &rows(
            EARNINGS,
            "SELECT flag, account, position FROM OPEN ON 2024-02-01 WHERE flag = 'S'",
        ),
        &[
            &["S", "Assets:Bank", "1800.00 USD"],
            &["S", "Equity:Opening-Balances", "-1800.00 USD"],
            &["S", "Equity:Earnings:Previous", "-1754.50 USD"],
            &["S", "Equity:Opening-Balances", "1754.50 USD"],
            &["S", "Liabilities:Card", "-45.50 USD"],
            &["S", "Equity:Opening-Balances", "45.50 USD"],
        ],
        "bean-query's summaries",
    );
    let balances = rows(EARNINGS, "BALANCES FROM OPEN ON 2024-02-01");
    let find = |account: &str| {
        balances
            .iter()
            .find(|row| row[0] == account)
            .map(|row| row[1].as_str())
    };
    assert_eq!(
        find("Income:Salary"),
        Some("-3000.00 USD"),
        "the period's pay only"
    );
    assert_eq!(
        find("Expenses:Food"),
        Some("80.25 USD"),
        "the period's food only"
    );
    assert_eq!(
        find("Expenses:Rent"),
        None,
        "rent was all before the period"
    );
    assert_eq!(find("Equity:Earnings:Previous"), Some("-1754.50 USD"));
}

/// A lot held at cost is summarized at its cost, date and label, balanced by
/// its cost against the opening-balances account.
#[test]
fn lots_are_summarized_at_their_cost() {
    assert_rows(
        &rows(
            LOTS,
            "SELECT date, account, position FROM OPEN ON 2024-02-01 WHERE flag = 'S'",
        ),
        &[
            &[
                "2024-01-31",
                "Assets:Broker",
                "6 AAPL { 150.00 USD, 2024-01-03, \"a\"}",
            ],
            &["2024-01-31", "Equity:Opening-Balances", "-900.00 USD"],
            &[
                "2024-01-31",
                "Assets:Broker",
                "5 AAPL { 160.00 USD, 2024-01-04}",
            ],
            &["2024-01-31", "Equity:Opening-Balances", "-800.00 USD"],
            &["2024-01-31", "Assets:Cash", "-1625.00 USD"],
            &["2024-01-31", "Equity:Opening-Balances", "1625.00 USD"],
            &["2024-01-31", "Equity:Earnings:Previous", "-75.00 USD"],
            &["2024-01-31", "Equity:Opening-Balances", "75.00 USD"],
        ],
        "bean-query's summaries (its rendering omits the lot date and label)",
    );
    // The period's sale reduces the summarized lot.
    assert_rows(
        &rows(
            LOTS,
            "SELECT account, sum(position) FROM OPEN ON 2024-02-01 WHERE account = 'Assets:Broker' GROUP BY account",
        ),
        &[&[
            "Assets:Broker",
            "6 AAPL { 150.00 USD, 2024-01-03, \"a\"}, 2 AAPL { 165.00 USD, 2024-02-10}",
        ]],
        "the lot sold in the period is gone",
    );
}

/// A price conversion leaves the balances unequal at cost; the residual is
/// summarized to `account_previous_conversions`.
#[test]
fn a_conversion_residual_is_summarized_to_previous_conversions() {
    assert_rows(
        &rows(
            CONVERSIONS,
            "SELECT account, position FROM OPEN ON 2024-02-01 WHERE flag = 'S'",
        ),
        &[
            &["Assets:EUR", "70.00 EUR"],
            &["Equity:Opening-Balances", "-70.00 EUR"],
            &["Assets:USD", "890.00 USD"],
            &["Equity:Opening-Balances", "-890.00 USD"],
            &["Equity:Conversions:Previous", "-100.00 EUR"],
            &["Equity:Opening-Balances", "100.00 EUR"],
            &["Equity:Conversions:Previous", "110.00 USD"],
            &["Equity:Opening-Balances", "-110.00 USD"],
            &["Equity:Earnings:Previous", "30.00 EUR"],
            &["Equity:Opening-Balances", "-30.00 EUR"],
            &["Equity:Opening", "-1000.00 USD"],
            &["Equity:Opening-Balances", "1000.00 USD"],
        ],
        "bean-query's summaries",
    );
}

/// Unset, the summary accounts live under the ledger's own equity root, as
/// beancount's `get_previous_accounts` builds them.
#[test]
fn unset_summary_accounts_use_the_ledgers_equity_root() {
    let source = "option \"name_equity\" \"Eigenkapital\"\n\
                  2024-01-01 open Assets:Bank USD\n\
                  2024-01-01 open Income:Salary USD\n\
                  2024-01-05 * \"pay\"\n  Assets:Bank  10 USD\n  Income:Salary\n";
    let accounts: Vec<String> = rows(
        source,
        "SELECT account FROM OPEN ON 2024-02-01 WHERE flag = 'S'",
    )
    .into_iter()
    .map(|row| row[0].clone())
    .collect();
    assert_eq!(
        accounts,
        [
            "Assets:Bank",
            "Eigenkapital:Opening-Balances",
            "Eigenkapital:Earnings:Previous",
            "Eigenkapital:Opening-Balances",
        ],
        "bean-query's accounts"
    );
}

/// Set, a summary account is the full name written. beancount would join the
/// equity root onto it (`Equity:Equity:Anfang`); rledger takes these options
/// as full names, a parsing divergence tracked in #2408.
#[test]
fn set_summary_accounts_are_the_names_written() {
    let source = "option \"account_previous_balances\" \"Equity:Anfang\"\n\
                  option \"account_previous_earnings\" \"Equity:Vorjahr\"\n\
                  2024-01-01 open Assets:Bank USD\n\
                  2024-01-01 open Income:Salary USD\n\
                  2024-01-05 * \"pay\"\n  Assets:Bank  10 USD\n  Income:Salary\n";
    let accounts: Vec<String> = rows(
        source,
        "SELECT account FROM OPEN ON 2024-02-01 WHERE flag = 'S'",
    )
    .into_iter()
    .map(|row| row[0].clone())
    .collect();
    assert_eq!(
        accounts,
        [
            "Assets:Bank",
            "Equity:Anfang",
            "Equity:Vorjahr",
            "Equity:Anfang"
        ]
    );
}

/// Opening on a date nothing precedes summarizes nothing: the same rows as
/// no `OPEN ON` at all (bean-query counts 12 postings either way).
#[test]
fn opening_before_every_transaction_changes_nothing() {
    let plain = rows(EARNINGS, "SELECT date, account, position, balance");
    let opened = rows(
        EARNINGS,
        "SELECT date, account, position, balance FROM OPEN ON 2024-01-01",
    );
    assert_eq!(opened, plain);
    assert_eq!(opened.len(), 12);
}

/// AVERAGE, which beancount lacks: the summary is the pool the account holds,
/// realized through the booking engine as `BALANCES` realizes it. Plain
/// inventory addition, beancount's method, would leave the sale booked at the
/// pooled cost as a third, negative lot (#1985). The pool is undated in the
/// engine, so its summary lot takes the summary's date.
#[test]
fn an_average_pool_is_summarized_as_the_account_holds_it() {
    assert_rows(
        &rows(
            AVERAGE,
            "SELECT account, position FROM OPEN ON 2024-02-01 WHERE flag = 'S'",
        ),
        &[
            &["Assets:Broker", "15 X { 150.00 USD, 2024-01-31}"],
            &["Equity:Opening-Balances", "-2250.00 USD"],
            &["Assets:Cash", "-2100.00 USD"],
            &["Equity:Opening-Balances", "2100.00 USD"],
            &["Equity:Earnings:Previous", "-150.00 USD"],
            &["Equity:Opening-Balances", "150.00 USD"],
        ],
        "the realized pool, not three lots",
    );
}

/// `account_balance` (rledger's; beanquery has no such column) starts from
/// the summary too, and a summary row has no source location.
#[test]
fn account_balance_and_location_of_summary_rows() {
    assert_rows(
        &rows(
            OPENING,
            "SELECT date, account_balance, filename FROM OPEN ON 2024-02-01 WHERE account = 'Assets:Bank'",
        ),
        &[
            &["2024-01-31", "1000.00 USD", ""],
            &["2024-02-10", "980.00 USD", "main.beancount"],
        ],
        "account_balance carries the opening balance; a summary has no file",
    );
}

/// JOURNAL takes its date window from the same place `SELECT` does. It used
/// to walk the ledger itself and applied only the `FROM` filter expression,
/// so `OPEN ON` and `CLOSE ON` were silently ignored and the pre-date posting
/// showed as itself.
#[test]
fn journal_honors_the_from_date_window() {
    assert_rows(
        &rows(OPENING, "JOURNAL 'Assets:Bank' FROM OPEN ON 2024-02-01"),
        &[
            &[
                "2024-01-31",
                "S",
                "",
                "Opening balance for 'Assets:Bank' (Summarization)",
                "Assets:Bank",
                "1000.00 USD",
                "1000.00 USD",
            ],
            &[
                "2024-02-10",
                "*",
                "",
                "lunch",
                "Assets:Bank",
                "-20.00 USD",
                "980.00 USD",
            ],
        ],
        "bean-query's journal",
    );
    assert_rows(
        &rows(OPENING, "JOURNAL 'Assets:Bank' FROM CLOSE ON 2024-02-01"),
        &[&[
            "2024-01-05",
            "*",
            "",
            "opening",
            "Assets:Bank",
            "1000.00 USD",
            "1000.00 USD",
        ]],
        "bean-query's journal: nothing from the close date on",
    );
}

/// beanquery refuses a `CLOSE ON` before the `OPEN ON`; the window would
/// otherwise be empty and the query would answer with nothing, silently.
#[test]
fn a_close_before_the_open_is_refused() {
    let ledger = load(OPENING);
    let directives: Vec<_> = ledger.directives.into_iter().map(|s| s.value).collect();
    for query in [
        "SELECT date FROM OPEN ON 2024-03-01 CLOSE ON 2024-02-01",
        "BALANCES FROM OPEN ON 2024-03-01 CLOSE ON 2024-02-01",
        "JOURNAL 'Assets' FROM OPEN ON 2024-03-01 CLOSE ON 2024-02-01",
    ] {
        let err = Executor::new(&directives)
            .execute(&parse(query).expect("parses"))
            .expect_err(query);
        assert!(
            err.to_string().contains("CLOSE date must follow OPEN date"),
            "{query}: {err}"
        );
    }
    // Equal dates are an empty period, not an error, as in beanquery.
    assert!(
        rows(
            OPENING,
            "SELECT date FROM OPEN ON 2024-02-01 CLOSE ON 2024-02-01"
        )
        .iter()
        .all(|r| r[0] != "2024-02-10")
    );
}
