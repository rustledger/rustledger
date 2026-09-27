//! ORDER BY on amounts and positions groups by currency (#2445).
//!
//! Amounts sorted by number alone, so `5 USD` and `5 EUR` compared equal and
//! one currency's values scattered through another's. Amounts now sort by
//! currency, then number, as beancount's `amount.sortkey` and so bean-query
//! do. Positions sort by units currency, cost number, cost currency, then
//! units number: beancount's `Position.sortkey` but for its first key, which
//! ranks a fixed currency list and then the rest by name LENGTH (a deliberate
//! divergence; see `position_order`).

use rustledger_booking::BookingEngine;
use rustledger_core::{BookingMethod, Directive};
use rustledger_query::{Executor, Value, parse};

const LEDGER: &str = r#"
2024-01-01 open Assets:A
2024-01-01 open Assets:B
2024-01-01 open Assets:S "FIFO"

2024-03-01 * "usd"
  Assets:A  5 USD
  Assets:B  -5 USD

2024-03-02 * "eur"
  Assets:A  5.00 EUR
  Assets:B  -5.00 EUR

2024-03-03 * "gld"
  Assets:A  7 GLD
  Assets:B  -7 GLD

2024-03-04 * "lot at 20"
  Assets:S  2 X {20 USD}
  Assets:B

2024-03-05 * "lot at 10"
  Assets:S  3 X {10 USD}
  Assets:B
"#;

fn rows(bql: &str) -> Vec<String> {
    let parsed = rustledger_parser::parse(LEDGER);
    let mut directives: Vec<Directive> = parsed.directives.iter().map(|d| (**d).clone()).collect();
    let mut engine = BookingEngine::with_method(BookingMethod::Fifo);
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
        .map(|r| match &r[0] {
            Value::Amount(a) => a.to_string(),
            Value::Position(p) => p.to_string(),
            Value::Inventory(i) => i.to_string(),
            other => panic!("{bql}: unexpected {other:?}"),
        })
        .collect()
}

#[test]
fn amounts_sort_by_currency_then_number() {
    // The three single-currency legs of Assets:A and Assets:B.
    let got = rows("SELECT units(position) AS u WHERE narration ~ '^(usd|eur|gld)$' ORDER BY u");
    assert_eq!(
        got,
        vec![
            "-5.00 EUR",
            "5.00 EUR",
            "-7 GLD",
            "7 GLD",
            "-5 USD",
            "5 USD"
        ]
    );
    let got =
        rows("SELECT units(position) AS u WHERE narration ~ '^(usd|eur|gld)$' ORDER BY u DESC");
    assert_eq!(
        got,
        vec![
            "5 USD",
            "-5 USD",
            "7 GLD",
            "-7 GLD",
            "5.00 EUR",
            "-5.00 EUR"
        ]
    );
}

/// Positions: currency first, then the cost, then the units.
#[test]
fn positions_sort_by_currency_then_cost_then_units() {
    let got = rows("SELECT position WHERE account = 'Assets:S' ORDER BY position");
    // Both lots are X; the one at 10 USD sorts before the one at 20 USD,
    // though it has more units.
    assert_eq!(got.len(), 2);
    assert!(got[0].contains("10 USD"), "{got:?}");
    assert!(got[1].contains("20 USD"), "{got:?}");
    let legs = rows("SELECT position WHERE narration ~ '^(usd|eur|gld)$' ORDER BY position");
    assert_eq!(
        legs,
        vec![
            "-5.00 EUR",
            "5.00 EUR",
            "-7 GLD",
            "7 GLD",
            "-5 USD",
            "5 USD"
        ]
    );
}

/// Inventories by their positions sorted, compared in turn, as beancount's
/// `Inventory.__lt__` (`sorted(self) < sorted(other)`). They compared their
/// FIRST positions in ledger order, so `Assets:A`, which got USD before EUR,
/// sorted after `Assets:B`'s lone `3 EUR`. bean-query gives C, A, B here.
#[test]
fn inventories_sort_by_their_positions_sorted() {
    let ledger = r#"
2024-01-01 open Assets:A
2024-01-01 open Assets:B
2024-01-01 open Assets:C
2024-01-01 open Assets:D
2024-01-01 open Equity:O

2024-02-01 * "A gets USD first"
  Assets:A  9 USD
  Equity:O

2024-02-02 * "A gets EUR second"
  Assets:A  1 EUR
  Equity:O

2024-02-03 * "B gets only EUR"
  Assets:B  3 EUR
  Equity:O

2024-02-04 * "C gets EUR first"
  Assets:C  1 EUR
  Equity:O

2024-02-05 * "C gets USD second"
  Assets:C  2 USD
  Equity:O
"#;
    let directives: Vec<Directive> = rustledger_parser::parse(ledger)
        .directives
        .iter()
        .map(|d| (**d).clone())
        .collect();
    let accounts = |order: &str| -> Vec<String> {
        let bql = format!(
            "SELECT account, sum(position) AS s WHERE account ~ '^Assets' \
             GROUP BY account ORDER BY s {order}"
        );
        Executor::new(&directives)
            .execute(&parse(&bql).expect("parses"))
            .expect("runs")
            .rows
            .iter()
            .map(|r| match &r[0] {
                Value::String(a) => a.clone(),
                other => panic!("unexpected {other:?}"),
            })
            .collect()
    };
    assert_eq!(accounts(""), vec!["Assets:C", "Assets:A", "Assets:B"]);
    assert_eq!(accounts("DESC"), vec!["Assets:B", "Assets:A", "Assets:C"]);
}
