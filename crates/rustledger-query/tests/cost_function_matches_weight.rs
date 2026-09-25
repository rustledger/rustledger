//! `COST(position)` and the `cost` column agree with `weight` (#2425).
//!
//! A lot bought as `3 X {{500 USD}}` resolves to a per-unit cost of 500/3,
//! rounded, and the booked posting carries the 500 itself
//! (`PerUnitFromTotal`), as does the sale that empties such a lot. `weight`
//! reads the posting and gave 500; `COST(position)` read the `Position` value,
//! which holds only the per-unit cost, and gave `3 × 166.66…67` =
//! 500.00…01. So an emptied account's `sum(cost(position))` printed `-0 USD`.
//! Both now take the posting's booked cost through the canonical weight rule.

use rustledger_booking::BookingEngine;
use rustledger_core::{BookingMethod, Decimal, Directive};
use rustledger_query::{Executor, Value, parse};

/// Parse `source` and book it the way the loader does, so postings carry the
/// costs booking writes.
fn booked(source: &str) -> Vec<Directive> {
    let parsed = rustledger_parser::parse(source);
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
    directives
}

fn number(value: &Value) -> Decimal {
    match value {
        Value::Amount(a) => a.number,
        // `sum()` of amounts is an inventory: its USD units.
        Value::Inventory(inv) => inv
            .positions()
            .filter(|p| p.units.currency.as_str() == "USD")
            .map(|p| p.units.number)
            .sum(),
        other => panic!("expected an amount, got {other:?}"),
    }
}

fn query(directives: &[Directive], bql: &str) -> Vec<Vec<Value>> {
    let mut executor = Executor::new(directives);
    executor
        .execute(&parse(bql).expect("query parses"))
        .expect("query runs")
        .rows
}

/// A `{{T}}` lot sold whole and sold down, per-unit lots, and an AVERAGE
/// pool sold whole: every cost-bearing posting.
const LEDGER: &str = r#"
2024-01-01 open Assets:T X "FIFO"
2024-01-01 open Assets:D Y "FIFO"
2024-01-01 open Assets:U Z "FIFO"
2024-01-01 open Assets:A W "AVERAGE"
2024-01-01 open Assets:C

2024-01-02 * "total lot"
  Assets:T  3 X {{500 USD}}
  Assets:C

2024-01-02 * "total lot to sell down"
  Assets:D  19 Y {{55505 USD}}
  Assets:C

2024-01-02 * "per-unit lot"
  Assets:U  4 Z {12.50 USD}
  Assets:C

2024-01-02 * "pool a"
  Assets:A  1 W {100 USD}
  Assets:C

2024-01-03 * "pool b"
  Assets:A  2 W {200 USD}
  Assets:C

2024-02-01 * "sell the total lot"
  Assets:T  -3 X {}
  Assets:C

2024-02-01 * "sell down 1"
  Assets:D  -18 Y {}
  Assets:C

2024-02-02 * "sell down 2"
  Assets:D  -1 Y {}
  Assets:C

2024-02-01 * "sell per-unit"
  Assets:U  -4 Z {}
  Assets:C

2024-02-01 * "sell the pool"
  Assets:A  -3 W {}
  Assets:C
"#;

#[test]
fn cost_of_position_is_the_posting_weight() {
    let directives = booked(LEDGER);
    let rows = query(
        &directives,
        "SELECT narration, cost(position), weight, cost WHERE account != 'Assets:C'",
    );
    assert_eq!(rows.len(), 10);
    for row in &rows {
        let (cost_fn, weight, cost_col) = (number(&row[1]), number(&row[2]), number(&row[3]));
        assert_eq!(
            cost_fn, weight,
            "{:?}: cost(position) is the weight",
            row[0]
        );
        assert_eq!(
            cost_col,
            weight.abs(),
            "{:?}: the cost column is |weight|",
            row[0]
        );
    }
}

#[test]
fn an_emptied_account_costs_exactly_nothing() {
    let directives = booked(LEDGER);
    for account in ["Assets:T", "Assets:D", "Assets:U", "Assets:A"] {
        let rows = query(
            &directives,
            &format!("SELECT sum(cost(position)) WHERE account = '{account}'"),
        );
        assert_eq!(rows.len(), 1, "{account}");
        assert_eq!(number(&rows[0][0]), Decimal::ZERO, "{account}");
    }
}

/// Only the position COLUMN takes the posting route; `COST` of an
/// expression is still the value path's `units × per-unit`.
#[test]
fn cost_of_an_expression_is_still_units_times_per_unit() {
    let directives = booked(LEDGER);
    let rows = query(
        &directives,
        "SELECT cost(sum(position)) WHERE narration = 'total lot' AND account = 'Assets:T'",
    );
    let per_unit = Decimal::from(500) / Decimal::from(3);
    assert_eq!(number(&rows[0][0]), Decimal::from(3) * per_unit);
}

/// Per row, too: `cost(units(position))` is `COST` of an amount, which is
/// the amount itself, not the posting's cost. Only the bare position column
/// takes the posting route.
#[test]
fn cost_of_another_row_expression_is_not_the_postings_cost() {
    let directives = booked(LEDGER);
    let rows = query(
        &directives,
        "SELECT cost(units(position)) WHERE narration = 'total lot' AND account = 'Assets:T'",
    );
    match &rows[0][0] {
        Value::Amount(a) => {
            assert_eq!(a.number, Decimal::from(3));
            assert_eq!(a.currency.as_str(), "X");
        }
        other => panic!("expected an amount, got {other:?}"),
    }
}
