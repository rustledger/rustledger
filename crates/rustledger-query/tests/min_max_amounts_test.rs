//! `MIN` and `MAX` over amounts, positions and inventories follow `ORDER BY`'s
//! order (#2447). They failed with "cannot compare values".
//!
//! MIN agrees with bean-query, except over positions in unlisted currencies,
//! which follow ORDER BY's own alphabetical currency rank (see the last
//! test). MAX deliberately diverges where
//! bean-query's `>` falls back to plain tuple comparison (number first) on
//! beancount's `Amount` / `Position` named tuples, which define only `__lt__`:
//! over `5 EUR` and `3 USD` bean-query answers `5 EUR` for BOTH MIN and MAX,
//! though its own ORDER BY sorts `5 EUR` first. See
//! docs/reference/compatibility.md section 15. Expected values below are
//! bean-query 0.2.0 / beancount 3.2.3 output unless marked as the divergence.

use rustledger_booking::BookingEngine;
use rustledger_core::{BookingMethod, Directive};
use rustledger_query::{Executor, Value, parse};

/// The ledger from #2447.
const MIXED: &str = r#"
2024-01-01 open Assets:A
2024-01-01 open Assets:B

2024-03-01 * "usd"
  Assets:A  5 USD
  Assets:B  -5 USD

2024-03-02 * "eur"
  Assets:A  5.00 EUR
  Assets:B  -5.00 EUR
"#;

/// `Assets:A` holds `5 EUR` and `3 USD`: the case where bean-query's MAX
/// disagrees with its own ORDER BY.
const DIVERGENT: &str = r#"
2024-01-01 open Assets:A
2024-01-01 open Assets:B

2024-03-01 * "eur"
  Assets:A  5 EUR
  Assets:B  -5 EUR

2024-03-02 * "usd"
  Assets:A  3 USD
  Assets:B  -3 USD
"#;

/// Lots at cost, an EUR lot among USD ones, and one posting with a price
/// annotations (so `price` is NULL on every other posting).
const LOTS: &str = r#"
2024-01-01 open Assets:Cash
2024-01-01 open Assets:Stock "FIFO"
2024-01-01 open Equity:Open

2024-02-01 * "buy1"
  Assets:Stock  2 X {20 USD}
  Assets:Cash  -40 USD

2024-02-02 * "buy2"
  Assets:Stock  3 X {10 USD}
  Assets:Cash  -30 USD

2024-02-03 * "buy3"
  Assets:Stock  1 Y {15 EUR}
  Assets:Cash  -15 EUR

2024-02-04 * "fx"
  Assets:Cash  10 EUR @ 1.1 USD
  Equity:Open  -11 USD

2024-02-05 * "fx2"
  Assets:Cash  5 EUR @ 1.2 USD
  Equity:Open  -6 USD
"#;

fn render(value: &Value) -> String {
    match value {
        Value::Amount(a) => a.to_string(),
        Value::Position(p) => p.to_string(),
        Value::Inventory(i) => i.to_string(),
        Value::String(s) => s.clone(),
        Value::Date(d) => d.to_string(),
        Value::Boolean(b) => b.to_string(),
        Value::Null => "NULL".to_string(),
        other => panic!("unexpected {other:?}"),
    }
}

fn rows(ledger: &str, bql: &str) -> Vec<Vec<String>> {
    let parsed = rustledger_parser::parse(ledger);
    let mut directives: Vec<Directive> = parsed.directives.iter().map(|d| (**d).clone()).collect();
    let mut engine = BookingEngine::with_method(BookingMethod::Strict);
    engine.register_account_methods(directives.iter());
    for directive in &mut directives {
        if let Directive::Transaction(txn) = directive {
            engine
                .book_interpolate_apply(txn)
                .expect("the fixture books");
        }
    }
    let query = parse(bql).unwrap_or_else(|e| panic!("{bql}: {e:?}"));
    Executor::new(&directives)
        .execute(&query)
        .unwrap_or_else(|e| panic!("{bql}: {e}"))
        .rows
        .iter()
        .map(|r| r.iter().map(render).collect())
        .collect()
}

#[test]
fn amounts_min_and_max_are_order_by_ends_across_currencies() {
    assert_eq!(
        rows(MIXED, "SELECT min(units(position)), max(units(position))"),
        vec![vec!["-5.00 EUR", "5 USD"]],
    );
}

#[test]
fn positions_min_matches_beanquery_and_max_is_order_by_last() {
    // MIN matches bean-query (`-5 USD`). MAX is the last position in ORDER
    // BY's order: USD ranks before EUR in beancount's `Position.sortkey`, so
    // that is `5.00 EUR`. bean-query's tuple fallback answers `5 USD`.
    assert_eq!(
        rows(MIXED, "SELECT min(position), max(position)"),
        vec![vec!["-5 USD", "5.00 EUR"]],
    );
    // Per account. MIN agrees with bean-query on both. MAX agrees on
    // Assets:A (`5 EUR`); on Assets:B, holding `-5 EUR` and `-3 USD`, ORDER BY
    // puts `-3 USD` first and `-5 EUR` last, while bean-query's number-first
    // `>` keeps `-3 USD` for both.
    assert_eq!(
        rows(
            DIVERGENT,
            "SELECT min(position), max(position) GROUP BY account ORDER BY account"
        ),
        vec![vec!["3 USD", "5 EUR"], vec!["-3 USD", "-5 EUR"]],
    );
}

#[test]
fn inventories_max_is_order_by_last() {
    // The running `balance` holds 5 USD, then nothing, then 5.00 EUR, then
    // nothing. bean-query also answers 5.00 EUR for the MAX.
    let got = rows(MIXED, "SELECT max(balance)");
    assert_eq!(got, vec![vec!["5.00 EUR"]]);
}

/// The deliberate divergence: MAX is ORDER BY's last value, `3 USD`, where
/// bean-query answers `5 EUR` for both MIN and MAX.
#[test]
fn max_follows_order_by_not_beanquery_tuple_fallback() {
    let bql = "SELECT min(units(position)), max(units(position)) WHERE account = 'Assets:A'";
    assert_eq!(rows(DIVERGENT, bql), vec![vec!["5 EUR", "3 USD"]]);

    let ordered = rows(
        DIVERGENT,
        "SELECT units(position) AS u WHERE account = 'Assets:A' ORDER BY u",
    );
    assert_eq!(ordered, vec![vec!["5 EUR"], vec!["3 USD"]]);
}

/// NULLs are skipped, so a column that is mostly NULL still answers; a group
/// holding only NULLs answers NULL. Matches bean-query.
#[test]
fn min_max_skip_nulls_among_amounts() {
    assert_eq!(
        rows(LOTS, "SELECT min(price), max(price)"),
        vec![vec!["1.1 USD", "1.2 USD"]],
    );
    assert_eq!(
        rows(
            LOTS,
            "SELECT account, min(price), max(price) GROUP BY account ORDER BY account"
        ),
        vec![
            vec!["Assets:Cash", "1.1 USD", "1.2 USD"],
            vec!["Assets:Stock", "NULL", "NULL"],
            vec!["Equity:Open", "NULL", "NULL"],
        ],
    );
}

/// No rows at all: NULL, not an error. (bean-query returns no row for an
/// aggregate over nothing, for every aggregate; rustledger returns one row,
/// as SQL does. That is not specific to amounts.)
#[test]
fn min_max_over_no_rows_is_null() {
    assert_eq!(
        rows(
            LOTS,
            "SELECT min(position), max(position) WHERE account = 'Nope'"
        ),
        vec![vec!["NULL", "NULL"]],
    );
}

/// MIN and MAX over lots held at cost, and over running-balance inventories
/// of those lots, are exactly the first and last value ORDER BY gives.
#[test]
fn min_max_are_order_by_first_and_last_for_lots_and_inventories() {
    for column in ["position", "balance", "cost(position)", "units(position)"] {
        let ordered = rows(
            LOTS,
            &format!("SELECT {column} AS v WHERE account = 'Assets:Stock' ORDER BY v"),
        );
        let first = ordered.first().unwrap()[0].clone();
        let last = ordered.last().unwrap()[0].clone();
        assert_eq!(
            rows(
                LOTS,
                &format!("SELECT min({column}), max({column}) WHERE account = 'Assets:Stock'"),
            ),
            vec![vec![first, last]],
            "{column}",
        );
    }
    // The values themselves, so the loop above cannot pass vacuously.
    // bean-query answers `3 X {10 USD}` for BOTH (its MAX compares the units
    // number first), though its own ORDER BY puts `3 X {10 USD}` first.
    assert_eq!(
        rows(
            LOTS,
            "SELECT min(position), max(position) WHERE account = 'Assets:Stock'"
        ),
        vec![vec![
            "3 X { 10 USD, 2024-02-02}",
            "1 Y { 15 EUR, 2024-02-03}"
        ]],
    );
}

/// The aggregate also works where HAVING evaluates it.
#[test]
fn max_over_amounts_works_in_having() {
    assert_eq!(
        rows(
            LOTS,
            "SELECT account, max(units(position)) GROUP BY account \
             HAVING currency(max(units(position))) = 'USD' ORDER BY account"
        ),
        // bean-query keeps only Equity:Open: its MAX for Assets:Cash is
        // `10 EUR` (number first), ours is `-30 USD` (currency first).
        vec![
            vec!["Assets:Cash", "-30 USD"],
            vec!["Equity:Open", "-6 USD"]
        ],
    );
}

/// Strings, accounts, dates and booleans keep their order; only amounts,
/// positions and inventories are new (#2447). Values are bean-query's.
#[test]
fn min_max_over_strings_dates_and_booleans_unchanged() {
    assert_eq!(
        rows(
            LOTS,
            "SELECT min(account), max(account), min(date), max(date), \
             min(narration), max(narration), max(number > 0), min(number > 0)"
        ),
        vec![vec![
            "Assets:Cash",
            "Equity:Open",
            "2024-02-01",
            "2024-02-05",
            "buy1",
            "fx2",
            "true",
            "false",
        ]],
    );
}

/// MIN over positions follows ORDER BY's position order, divergence included:
/// unlisted currencies rank alphabetically here and by name LENGTH in
/// beancount (compatibility.md section 15), so `X` sorts before `Y` and the
/// `X` lot is the minimum. bean-query ties `X` and `Y`, compares the cost,
/// and answers `1 Y {5 USD}`.
#[test]
fn min_over_positions_inherits_order_by_currency_rank() {
    const UNLISTED: &str = r#"
2024-01-01 open Assets:Stock
2024-01-01 open Assets:Cash
2024-02-01 * "x"
  Assets:Stock  2 X {20 USD}
  Assets:Cash  -40 USD
2024-02-02 * "y"
  Assets:Stock  1 Y {5 USD}
  Assets:Cash  -5 USD
"#;
    let bql = "SELECT min(position), max(position) WHERE account = 'Assets:Stock'";
    let got = rows(UNLISTED, bql);
    let ordered = rows(
        UNLISTED,
        "SELECT position WHERE account = 'Assets:Stock' ORDER BY position",
    );
    assert_eq!(
        got,
        vec![vec![ordered[0][0].clone(), ordered[1][0].clone()]]
    );
    assert!(got[0][0].starts_with("2 X"), "{got:?}");
}

/// The table aggregation path (`FROM #postings`, and a subquery's rows) is a
/// separate MIN/MAX implementation from the default table's; both compare
/// with the same function, so both follow ORDER BY. Over `5 EUR` and `3 USD`
/// MIN is `5 EUR` (bean-query too) and MAX is `3 USD` (bean-query: `5 EUR`,
/// the documented divergence).
#[test]
fn min_max_over_amounts_on_tables_and_subqueries() {
    for bql in [
        "SELECT min(units(position)), max(units(position)) FROM #postings \
         WHERE account = 'Assets:A'",
        "SELECT min(u), max(u) FROM (SELECT units(position) AS u WHERE account = 'Assets:A')",
    ] {
        assert_eq!(rows(DIVERGENT, bql), vec![vec!["5 EUR", "3 USD"]], "{bql}");
    }
    assert_eq!(
        rows(
            DIVERGENT,
            "SELECT account, max(units(position)) FROM #postings GROUP BY account ORDER BY account"
        ),
        // Assets:B holds `-5 EUR` and `-3 USD`: amounts sort by currency, so
        // `-3 USD` is last here, and bean-query agrees (number first).
        vec![vec!["Assets:A", "3 USD"], vec!["Assets:B", "-3 USD"]],
    );
}

/// MIN/MAX over account names are string order, not the account-type order
/// `BALANCES` uses (#2409): `Liabilities:Card` sorts after `Equity:Opening`
/// as text, though before it by account type. bean-query agrees.
#[test]
fn min_max_over_accounts_is_string_order_not_account_type_order() {
    const TYPES: &str = r#"
2024-01-01 open Equity:Opening
2024-01-01 open Liabilities:Card
2024-01-02 * "x"
  Liabilities:Card  -5 USD
  Equity:Opening     5 USD
"#;
    assert_eq!(
        rows(TYPES, "SELECT min(account), max(account)"),
        vec![vec!["Equity:Opening", "Liabilities:Card"]],
    );
}
