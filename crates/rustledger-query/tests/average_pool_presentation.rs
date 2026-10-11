//! An AVERAGE account is presented as its pool on every query surface,
//! before a sale and after one (#2543).
//!
//! Booking merges an AVERAGE account's lots only when a sale runs. Read off
//! booking's inventory, `BALANCES` listed the separate lots until the first
//! sale and the pool after it, while `sum(position)` showed the pool all
//! along, and the running `balance` column was never realized at all: after
//! the sale it listed both lots bought plus the sale as a negative lot, which
//! the account never held. The pool key is the commodity, the cost currency
//! and the side; the pool is undated and keeps its exact total cost.
//!
//! Python beancount has no AVERAGE booking, so rledger's own definition is
//! the reference.

use rustledger_booking::BookingEngine;
use rustledger_core::{BookingMethod, Decimal, Directive, Inventory};
use rustledger_query::{Executor, Value, parse};
use std::str::FromStr;

const OPENS: &str = r#"2024-01-01 open Assets:Cash
2024-01-01 open Assets:Brokerage X "AVERAGE"
2024-01-01 open Income:Gains
"#;

const BUYS: &str = r#"
2024-01-02 * "buy"
  Assets:Brokerage   1 X {100 USD}
  Assets:Cash

2024-01-03 * "buy"
  Assets:Brokerage   2 X {200 USD}
  Assets:Cash
"#;

const SALE: &str = r#"
2024-01-04 * "sell"
  Assets:Brokerage  -1 X {} @ 300 USD
  Assets:Cash        300 USD
  Income:Gains
"#;

/// Parse `source` and book it as the loader does.
fn booked(source: &str) -> Vec<Directive> {
    let parsed = rustledger_parser::parse(source);
    assert!(parsed.errors.is_empty(), "parses: {:?}", parsed.errors);
    let mut directives: Vec<Directive> = parsed.directives.iter().map(|d| (**d).clone()).collect();
    let mut engine = BookingEngine::with_method(BookingMethod::Strict);
    engine.register_account_methods(directives.iter());
    for directive in &mut directives {
        if let Directive::Transaction(txn) = directive {
            engine.book_interpolate_apply(txn).expect("books");
        }
    }
    directives
}

/// A lot as compared: units, commodity, per-unit cost, cost currency and
/// cost date.
type Lot = (Decimal, String, Option<(Decimal, String, Option<String>)>);

fn lots_of(inv: &Inventory, commodity: &str) -> Vec<Lot> {
    let mut lots: Vec<Lot> = inv
        .positions()
        .filter(|p| p.units.currency.as_str() == commodity)
        .map(|p| {
            (
                p.units.number,
                p.units.currency.to_string(),
                p.cost.as_ref().map(|c| {
                    (
                        c.number,
                        c.currency.to_string(),
                        c.date.map(|d| d.to_string()),
                    )
                }),
            )
        })
        .collect();
    lots.sort();
    lots
}

/// The rows of `bql`.
fn rows(directives: &[Directive], bql: &str) -> Vec<Vec<Value>> {
    Executor::new(directives)
        .execute(&parse(bql).expect("parses"))
        .unwrap_or_else(|e| panic!("{bql}: {e}"))
        .rows
}

/// The inventory in column `col` of `bql`'s last row.
fn last_inventory(directives: &[Directive], bql: &str, col: usize) -> Inventory {
    let rows = rows(directives, bql);
    match rows.last().map(|r| &r[col]) {
        Some(Value::Inventory(inv)) => (**inv).clone(),
        other => panic!("{bql}: no inventory in the last row: {other:?}"),
    }
}

fn d(s: &str) -> Decimal {
    Decimal::from_str(s).expect("literal")
}

/// One undated `units X {cost USD}` pool.
fn pool(units: &str, cost: Decimal) -> Vec<Lot> {
    vec![(d(units), "X".into(), Some((cost, "USD".into(), None)))]
}

/// Every query surface's view of the brokerage account.
fn surfaces(directives: &[Directive]) -> Vec<(&'static str, Vec<Lot>)> {
    let account = "account = 'Assets:Brokerage'";
    vec![
        (
            "BALANCES",
            lots_of(
                &last_inventory(directives, &format!("BALANCES WHERE {account}"), 1),
                "X",
            ),
        ),
        (
            "sum(position)",
            lots_of(
                &last_inventory(
                    directives,
                    &format!("SELECT account, sum(position) WHERE {account} GROUP BY account"),
                    1,
                ),
                "X",
            ),
        ),
        (
            "running balance",
            lots_of(
                &last_inventory(directives, &format!("SELECT balance WHERE {account}"), 0),
                "X",
            ),
        ),
        (
            "JOURNAL balance",
            lots_of(
                &last_inventory(directives, "JOURNAL 'Assets:Brokerage'", 6),
                "X",
            ),
        ),
        (
            "account_balance",
            lots_of(
                &last_inventory(
                    directives,
                    &format!("SELECT account_balance WHERE {account}"),
                    0,
                ),
                "X",
            ),
        ),
    ]
}

#[test]
fn before_the_sale_every_surface_shows_the_pool() {
    // 1 X at 100 and 2 X at 200: 3 X costing 500, 500/3 a unit.
    let directives = booked(&format!("{OPENS}{BUYS}"));
    let want = pool("3", d("500") / d("3"));
    for (surface, got) in surfaces(&directives) {
        assert_eq!(got, want, "{surface} before the sale");
    }
}

#[test]
fn after_the_sale_every_surface_shows_the_pool() {
    // The sale takes one unit at the average; 2 X remain at 500/3.
    let directives = booked(&format!("{OPENS}{BUYS}{SALE}"));
    let want = pool("2", d("500") / d("3"));
    for (surface, got) in surfaces(&directives) {
        assert_eq!(got, want, "{surface} after the sale");
    }
}

/// The running `balance` column after the sale is the pool, not the two lots
/// bought plus the sale as a negative lot.
#[test]
fn the_running_balance_after_the_sale_is_one_pool() {
    let directives = booked(&format!("{OPENS}{BUYS}{SALE}"));
    let rows = rows(
        &directives,
        "SELECT balance WHERE account = 'Assets:Brokerage'",
    );
    let shapes: Vec<Vec<Lot>> = rows
        .iter()
        .map(|r| match &r[0] {
            Value::Inventory(inv) => lots_of(inv, "X"),
            other => panic!("not an inventory: {other:?}"),
        })
        .collect();
    assert_eq!(
        shapes,
        vec![
            // One lot is a pool too, undated like any other.
            pool("1", d("100")),
            pool("3", d("500") / d("3")),
            pool("2", d("500") / d("3")),
        ]
    );
}

/// The running balance across accounts: a FIFO account's lots stay lots, the
/// AVERAGE account is its pool, and the two do not mix.
#[test]
fn the_running_balance_pools_only_the_average_account() {
    let directives = booked(&format!(
        "{OPENS}2024-01-01 open Assets:Fifo X \"FIFO\"\n{BUYS}{SALE}
2024-01-05 * \"fifo buys\"
  Assets:Fifo  1 X {{100 USD}}
  Assets:Fifo  1 X {{200 USD}}
  Assets:Cash
"
    ));
    let got = lots_of(
        &last_inventory(
            &directives,
            "SELECT balance WHERE account ~ '^Assets:(Brokerage|Fifo)$'",
            0,
        ),
        "X",
    );
    let mut want = pool("2", d("500") / d("3"));
    want.push((
        d("1"),
        "X".into(),
        Some((d("100"), "USD".into(), Some("2024-01-05".into()))),
    ));
    want.push((
        d("1"),
        "X".into(),
        Some((d("200"), "USD".into(), Some("2024-01-05".into()))),
    ));
    want.sort();
    assert_eq!(got, want);
}

/// X held at a USD cost and at a EUR cost are two pools: each pools its own
/// lots, and they never pool together.
#[test]
fn each_cost_currency_is_its_own_pool() {
    let directives = booked(&format!(
        "{OPENS}
2024-01-02 * \"buy\"
  Assets:Brokerage   1 X {{100 USD}}
  Assets:Cash

2024-01-03 * \"buy\"
  Assets:Brokerage   2 X {{90 EUR}}
  Assets:Cash

2024-01-04 * \"buy\"
  Assets:Brokerage   2 X {{200 USD}}
  Assets:Cash

2024-01-05 * \"buy\"
  Assets:Brokerage   2 X {{110 EUR}}
  Assets:Cash
"
    ));
    let mut want = vec![
        (
            d("3"),
            "X".to_string(),
            Some((d("500") / d("3"), "USD".to_string(), None)),
        ),
        (d("4"), "X".into(), Some((d("100"), "EUR".into(), None))),
    ];
    want.sort();
    for (surface, got) in surfaces(&directives) {
        assert_eq!(got, want, "{surface}");
    }
}

/// A WHERE that keeps the sale but not what it sold from leaves the running
/// balance the plain sum of the rows, as `sum(position)` is: booking cannot
/// realize a sale from nothing.
#[test]
fn an_unrealizable_selection_keeps_the_plain_sum() {
    let directives = booked(&format!("{OPENS}{BUYS}{SALE}"));
    let filter = "WHERE account = 'Assets:Brokerage' AND number < 0";
    let running = lots_of(
        &last_inventory(&directives, &format!("SELECT balance {filter}"), 0),
        "X",
    );
    let sum = lots_of(
        &last_inventory(
            &directives,
            &format!("SELECT account, sum(position) {filter} GROUP BY account"),
            1,
        ),
        "X",
    );
    assert_eq!(running, sum);
    assert_eq!(running.len(), 1, "the sale alone: {running:?}");
    assert_eq!(running[0].0, d("-1"));
}
