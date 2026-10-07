//! `MIN` and `MAX` over amounts, positions and inventories follow `ORDER BY`'s
//! order (#2447). They failed with "cannot compare values".
//!
//! MIN agrees with bean-query everywhere. MAX deliberately diverges where
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

fn render(value: &Value) -> String {
    match value {
        Value::Amount(a) => a.to_string(),
        Value::Position(p) => p.to_string(),
        Value::Inventory(i) => i.to_string(),
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
fn min_max_over_amounts_across_currencies() {
    assert_eq!(
        rows(MIXED, "SELECT min(units(position)), max(units(position))"),
        vec![vec!["-5.00 EUR", "5 USD"]],
    );
}

#[test]
fn min_max_over_positions() {
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
fn min_max_over_inventories() {
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
