//! `MIN` and `MAX` as window functions (`OVER (...)`, #2521).
//!
//! Window functions are a rustledger extension: beanquery 0.2.0 rejects
//! `OVER` as a syntax error, so there is no bean-query answer to match. The
//! values follow SQL's default frame (the whole partition without an
//! `ORDER BY`, a running frame through the current row's peers with one), and
//! compare as the aggregate `MIN` / `MAX` do (#2447), which these tests check
//! by running both on the same rows.

use std::path::Path;

use rustledger_loader::{LoadOptions, Loader, VirtualFileSystem, process};
use rustledger_query::{Executor, QueryError, Value, parse};

const LEDGER: &str = r#"2024-01-01 open Assets:Bank
2024-01-01 open Assets:Wallet
2024-01-01 open Expenses:Food
2024-01-01 open Income:Salary

2024-01-05 * "Employer" "salary"
  Assets:Bank      100 USD
  Income:Salary   -100 USD

2024-01-07 * "shop"
  Expenses:Food     30 USD
  Assets:Bank      -30 USD

2024-01-07 * "Cafe" "coffee"
  Expenses:Food      5 EUR
  Assets:Wallet     -5 EUR

2024-01-09 * "market"
  Expenses:Food     20 USD
  Assets:Bank      -20 USD

2024-01-12 * "Bakery" "bread"
  Expenses:Food      3 EUR
  Assets:Wallet     -3 EUR
"#;

fn cell(value: &Value) -> String {
    match value {
        Value::String(s) => s.clone(),
        Value::Number(n) => n.to_string(),
        Value::Integer(i) => i.to_string(),
        Value::Date(d) => d.to_string(),
        Value::Amount(a) => a.to_string(),
        Value::Position(p) => p.to_string(),
        Value::Null => "NULL".to_string(),
        other => format!("{other:?}"),
    }
}

fn execute(query: &str) -> Result<Vec<Vec<String>>, QueryError> {
    let mut vfs = VirtualFileSystem::new();
    vfs.add_file("main.beancount", LEDGER);
    let raw = Loader::new()
        .with_filesystem(Box::new(vfs))
        .load(Path::new("main.beancount"))
        .expect("loads");
    let ledger = process(raw, &LoadOptions::default()).expect("processes");
    assert!(ledger.errors.is_empty(), "{:?}", ledger.errors);
    let mut executor = Executor::new_with_sources(&ledger.directives, &ledger.source_map);
    let result = executor.execute(&parse(query).expect("parses"))?;
    Ok(result
        .rows
        .iter()
        .map(|row| row.iter().map(cell).collect())
        .collect())
}

fn rows(query: &str) -> Vec<Vec<String>> {
    execute(query).unwrap_or_else(|e| panic!("{query}: {e}"))
}

fn table(expected: &[&[&str]]) -> Vec<Vec<String>> {
    expected
        .iter()
        .map(|row| row.iter().map(ToString::to_string).collect())
        .collect()
}

/// With no `ORDER BY` in the window, the frame is the whole partition, so
/// every row of an account carries the account's aggregate `MIN` and `MAX`.
#[test]
fn whole_partition_matches_the_aggregate() {
    let windowed = rows(
        "SELECT account, MIN(number) OVER (PARTITION BY account), \
         MAX(number) OVER (PARTITION BY account) ORDER BY account",
    );
    let aggregate =
        rows("SELECT account, MIN(number), MAX(number) GROUP BY account ORDER BY account");
    let mut distinct = windowed.clone();
    distinct.dedup();
    assert_eq!(distinct, aggregate);
    assert_eq!(
        aggregate,
        table(&[
            &["Assets:Bank", "-30", "100"],
            &["Assets:Wallet", "-5", "-3"],
            &["Expenses:Food", "3", "30"],
            &["Income:Salary", "-100", "-100"],
        ])
    );
    // Every posting gets a row, not one per partition.
    assert_eq!(windowed.len(), 10);
}

/// With an `ORDER BY`, the frame runs from the partition's first row through
/// the current one: a running minimum and maximum, here per account by date.
#[test]
fn ordered_window_is_a_running_min_and_max() {
    assert_eq!(
        rows(
            "SELECT date, number, MIN(number) OVER (PARTITION BY account ORDER BY date), \
             MAX(number) OVER (PARTITION BY account ORDER BY date) \
             WHERE account = 'Assets:Bank' ORDER BY date"
        ),
        table(&[
            &["2024-01-05", "100", "100", "100"],
            &["2024-01-07", "-30", "-30", "100"],
            &["2024-01-09", "-20", "-30", "100"],
        ])
    );
    // Descending: the frame grows from the latest date backwards.
    assert_eq!(
        rows(
            "SELECT date, number, MAX(number) OVER (ORDER BY date DESC) \
             WHERE account = 'Assets:Bank' ORDER BY date"
        ),
        table(&[
            &["2024-01-05", "100", "100"],
            &["2024-01-07", "-30", "-20"],
            &["2024-01-09", "-20", "-20"],
        ])
    );
}

/// Rows whose window `ORDER BY` values tie are peers and share a frame, as
/// they share a `RANK`: both 2024-01-07 food postings see each other.
#[test]
fn peers_share_the_frame() {
    assert_eq!(
        rows(
            "SELECT date, units(position), RANK() OVER (ORDER BY date), \
             MIN(number) OVER (ORDER BY date), MAX(number) OVER (ORDER BY date) \
             WHERE account = 'Expenses:Food' ORDER BY date, number"
        ),
        table(&[
            &["2024-01-07", "5 EUR", "1", "5", "30"],
            &["2024-01-07", "30 USD", "1", "5", "30"],
            &["2024-01-09", "20 USD", "3", "5", "30"],
            &["2024-01-12", "3 EUR", "4", "3", "30"],
        ])
    );
}

/// NULLs are skipped, as in the aggregate, and a frame of nothing but NULLs
/// is NULL. `payee` is NULL on the two transactions written without one.
#[test]
fn nulls_are_skipped() {
    assert_eq!(
        rows(
            "SELECT date, payee, MIN(payee) OVER (ORDER BY date), \
             MAX(payee) OVER (ORDER BY date), MIN(payee) OVER () \
             WHERE account = 'Expenses:Food' ORDER BY date, number"
        ),
        table(&[
            &["2024-01-07", "Cafe", "Cafe", "Cafe", "Bakery"],
            &["2024-01-07", "NULL", "Cafe", "Cafe", "Bakery"],
            &["2024-01-09", "NULL", "Cafe", "Cafe", "Bakery"],
            &["2024-01-12", "Bakery", "Bakery", "Cafe", "Bakery"],
        ])
    );
    assert_eq!(
        rows(
            "SELECT MIN(cost_number) OVER (PARTITION BY account), \
             MAX(payee) OVER (PARTITION BY account ORDER BY date) \
             WHERE account = 'Assets:Bank' ORDER BY date LIMIT 2"
        ),
        table(&[&["NULL", "Employer"], &["NULL", "Employer"]])
    );
    assert_eq!(
        rows("SELECT DISTINCT MIN(payee) OVER (PARTITION BY narration) WHERE narration = 'shop'"),
        table(&[&["NULL"]])
    );
}

/// Amounts of several currencies compare as the aggregate compares them,
/// by currency and then number (#2447), so the windowed and aggregate
/// answers are the same values.
#[test]
fn mixed_currency_amounts_compare_as_the_aggregate() {
    let windowed = rows(
        "SELECT DISTINCT MIN(units(position)) OVER (), MAX(units(position)) OVER (), \
         MIN(position) OVER (), MAX(position) OVER () WHERE account = 'Expenses:Food'",
    );
    let aggregate = rows(
        "SELECT MIN(units(position)), MAX(units(position)), MIN(position), MAX(position) \
         WHERE account = 'Expenses:Food'",
    );
    assert_eq!(windowed, aggregate);
    // Positions follow the position order, which ranks currencies as
    // `ORDER BY position` does (USD before EUR here), not alphabetically.
    assert_eq!(aggregate, table(&[&["3 EUR", "30 USD", "20 USD", "5 EUR"]]));
    // Running: EUR sorts before USD, so the first EUR row lowers the minimum
    // and the maximum stays the USD amount.
    assert_eq!(
        rows(
            "SELECT date, MIN(units(position)) OVER (ORDER BY date), \
             MAX(units(position)) OVER (ORDER BY date) \
             WHERE account = 'Expenses:Food' ORDER BY date, number"
        ),
        table(&[
            &["2024-01-07", "5 EUR", "30 USD"],
            &["2024-01-07", "5 EUR", "30 USD"],
            &["2024-01-09", "5 EUR", "30 USD"],
            &["2024-01-12", "3 EUR", "30 USD"],
        ])
    );
}

/// Each window function is computed over its own `OVER` clause. They all
/// used the first one's: the second `ROW_NUMBER` here numbered within
/// accounts too, and a second `MIN` read the first's values.
#[test]
fn each_window_uses_its_own_over_clause() {
    assert_eq!(
        rows(
            "SELECT ROW_NUMBER() OVER (PARTITION BY account ORDER BY date), \
             ROW_NUMBER() OVER (ORDER BY date, account, number) \
             WHERE account ~ '^Assets' ORDER BY date, account, number"
        ),
        table(&[
            &["1", "1"],
            &["2", "2"],
            &["1", "3"],
            &["3", "4"],
            &["2", "5"]
        ])
    );
    assert_eq!(
        rows(
            "SELECT account, ROW_NUMBER() OVER (PARTITION BY account ORDER BY date), \
             ROW_NUMBER() OVER (ORDER BY date, account, number), \
             MIN(number) OVER (PARTITION BY account), MIN(number) OVER () \
             WHERE account ~ '^Assets' ORDER BY date, account, number"
        ),
        table(&[
            &["Assets:Bank", "1", "1", "-30", "-30"],
            &["Assets:Bank", "2", "2", "-30", "-30"],
            &["Assets:Wallet", "1", "3", "-5", "-30"],
            &["Assets:Bank", "3", "4", "-30", "-30"],
            &["Assets:Wallet", "2", "5", "-5", "-30"],
        ])
    );
}

/// `MIN` and `MAX` take one argument, as the aggregates do, and the other
/// aggregates are still not window functions.
#[test]
fn arguments_are_checked() {
    for query in [
        "SELECT MIN() OVER ()",
        "SELECT MAX(number, number) OVER ()",
        "SELECT MIN(*) OVER ()",
    ] {
        assert!(
            matches!(execute(query), Err(QueryError::InvalidArguments(..))),
            "{query}: {:?}",
            execute(query)
        );
    }
    let err = execute("SELECT SUM(number) OVER ()").unwrap_err();
    assert!(err.to_string().contains("not yet implemented"), "{err}");
    // Checked up front, so even when no row matches.
    assert!(matches!(
        execute("SELECT MIN() OVER () WHERE account = 'Nope'"),
        Err(QueryError::InvalidArguments(..))
    ));
}

/// Values the comparison refuses are refused here too, not ordered: a
/// string against a number is an error in the aggregate, and so here.
#[test]
fn incomparable_values_are_an_error_as_in_the_aggregate() {
    let grouped = execute("SELECT MIN(coalesce(payee, number)) WHERE account = 'Assets:Bank'");
    let windowed =
        execute("SELECT MIN(coalesce(payee, number)) OVER () WHERE account = 'Assets:Bank'");
    assert!(grouped.is_err(), "{grouped:?}");
    assert_eq!(
        windowed.map_err(|e| e.to_string()),
        grouped.map_err(|e| e.to_string())
    );
}

/// A window function in the outer `ORDER BY` only, not among the targets, is
/// computed too: it was a hidden column with no window values, an error.
#[test]
fn a_window_function_can_order_the_result() {
    assert_eq!(
        rows(
            "SELECT account, number WHERE account ~ '^Assets' \
             ORDER BY MIN(number) OVER (PARTITION BY account) DESC, number"
        ),
        table(&[
            &["Assets:Wallet", "-5"],
            &["Assets:Wallet", "-3"],
            &["Assets:Bank", "-30"],
            &["Assets:Bank", "-20"],
            &["Assets:Bank", "100"],
        ])
    );
}
