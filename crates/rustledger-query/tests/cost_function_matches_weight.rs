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

/// `cost(sum(position))` is `sum(cost(position))` (#2430): `sum(position)`
/// records each lot with the exact total its posting carries, and `cost()` of
/// the inventory reads it. It multiplied the rounded per-unit cost back out,
/// 500.00…01 for a `{{500 USD}}` lot.
#[test]
fn cost_of_the_sum_is_the_sum_of_the_costs() {
    let directives = booked(LEDGER);
    for account in ["Assets:T", "Assets:D", "Assets:U", "Assets:A"] {
        for (date, lots) in [
            ("2024-01-31", "held"),
            ("2024-02-01", "part sold"),
            ("2025-01-01", "sold"),
        ] {
            let filter = format!("WHERE account = '{account}' AND date <= {date}");
            let of_sum = query(&directives, &format!("SELECT cost(sum(position)) {filter}"));
            let sum_of = query(&directives, &format!("SELECT sum(cost(position)) {filter}"));
            assert_eq!(
                number(&of_sum[0][0]),
                number(&sum_of[0][0]),
                "{account}, {lots}"
            );
        }
    }
    let held = query(
        &directives,
        "SELECT cost(sum(position)) WHERE account = 'Assets:T' AND date < 2024-02-01",
    );
    assert_eq!(number(&held[0][0]), Decimal::from(500));
}

/// `cost()` of an inventory is per currency (#2430): it summed every lot's
/// cost into one number in the first currency it met, so 30 USD and 207 EUR
/// of cost came out `237 USD`. bean-query's `cost(inventory)` is an inventory.
#[test]
fn cost_of_a_mixed_currency_sum_keeps_its_currencies() {
    let directives = booked(
        r#"
2024-01-01 open Assets:M
2024-01-01 open Assets:C

2024-01-02 * "usd lot"
  Assets:M  3 X {10 USD}
  Assets:C

2024-01-03 * "eur lot"
  Assets:M  2 Y {100 EUR}
  Assets:C

2024-01-04 * "eur cash"
  Assets:M  7 EUR
  Assets:C
"#,
    );
    let rows = query(
        &directives,
        "SELECT cost(sum(position)), number(cost(sum(position))) WHERE account = 'Assets:M'",
    );
    match &rows[0][0] {
        Value::Inventory(inv) => assert_eq!(inv.to_string(), "207 EUR, 30 USD"),
        other => panic!("expected an inventory, got {other:?}"),
    }
    // One number for two currencies would be meaningless.
    assert_eq!(rows[0][1], Value::Null);
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

/// `BALANCES AT COST` values a held `{{T}}` lot at its total: the balances
/// come from the booking engine's replay, whose inventories keep each lot's
/// exact total (#2425), and `at_cost` reads it.
#[test]
fn balances_at_cost_values_a_held_total_cost_lot_at_its_total() {
    let directives = booked(
        r#"
2024-01-01 open Assets:H X "FIFO"
2024-01-01 open Assets:C

2024-01-02 * "total lot"
  Assets:H  3 X {{500 USD}}
  Assets:C
"#,
    );
    let rows = query(&directives, "BALANCES AT COST WHERE account = 'Assets:H'");
    assert_eq!(number(&rows[0][1]), Decimal::from(500));
}

/// `JOURNAL ... AT COST`: each row's position is its posting's cost, and the
/// balance is the running sum of those, exact for a `{{T}}` lot. It was
/// `at_cost` of the running balance, which multiplied the rounded per-unit
/// cost back out: 500.00…01 on the buy and on its balance.
#[test]
fn journal_at_cost_is_exact_for_a_total_cost_lot() {
    let directives = booked(LEDGER);
    let rows = query(&directives, "JOURNAL 'Assets:T' AT COST");
    let columns: Vec<(Decimal, Decimal)> = rows
        .iter()
        .map(|r| (number(&r[5]), number(&r[6])))
        .collect();
    assert_eq!(
        columns,
        vec![
            (Decimal::from(500), Decimal::from(500)),
            (Decimal::from(-500), Decimal::ZERO)
        ]
    );
}
