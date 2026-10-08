//! `MIN`/`MAX` over amounts, positions and inventories follow `ORDER BY`'s
//! order instead of failing on `cannot compare values` (#2447).
//!
//! bean-query is not a model here, and not only because it errors on nothing:
//! its `Min` updates on `value < cur` and its `Max` on `value > cur`
//! (`beanquery/query_env.py:866`, `:880`), while beancount defines `__lt__`
//! alone on `Amount`/`Position` -- the sortkey, currency first -- and inherits
//! `>` from tuple comparison, number first for `Amount(number, currency)`.
//! Over `5 EUR` and `3 USD` its two aggregates answer the SAME value,
//! `5 EUR`, which is the FIRST of its own `ORDER BY`: its `MAX` disagrees with
//! its own sort. Here both ends come from the order `ORDER BY` uses, so
//! `min()`/`max()` agree with it and with each other.
//!
//! Numbers and booleans are unchanged; their orders are pinned by
//! `boolean_minmax_test.rs`.

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, NaiveDate, Open, Posting, Transaction};
use rustledger_query::{Executor, Value, parse};

fn date(year: i32, month: u32, day: u32) -> NaiveDate {
    rustledger_core::naive_date(year, month, day).unwrap()
}

/// `Assets:A` holds `5 EUR` and `3 USD`. The two orders disagree about which
/// of the two comes first -- the amount order is by currency (`EUR` before
/// `USD`), the position order is beancount's currency rank (`USD` before
/// `EUR`) -- so one ledger pins both.
fn fixture() -> Vec<Directive> {
    vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:A")),
        Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 2), "both")
                .with_synthesized_posting(Posting::new("Assets:A", Amount::new(dec!(5), "EUR")))
                .with_synthesized_posting(Posting::new("Assets:A", Amount::new(dec!(3), "USD")))
                .with_synthesized_posting(Posting::new(
                    "Equity:Opening",
                    Amount::new(dec!(-5), "EUR"),
                ))
                .with_synthesized_posting(Posting::new(
                    "Equity:Opening",
                    Amount::new(dec!(-3), "USD"),
                )),
        ),
    ]
}

fn run_rows(query_str: &str) -> Vec<Vec<String>> {
    let dirs = fixture();
    let query = parse(query_str).unwrap_or_else(|e| panic!("{query_str}: {e:?}"));
    Executor::new(&dirs)
        .execute(&query)
        .unwrap_or_else(|e| panic!("{query_str}: {e}"))
        .rows
        .iter()
        .map(|row| {
            row.iter()
                .map(|v| match v {
                    Value::Amount(a) => a.to_string(),
                    Value::Position(p) => p.to_string(),
                    Value::Inventory(i) => i.to_string(),
                    other => panic!("{query_str}: unexpected {other:?}"),
                })
                .collect()
        })
        .collect()
}

/// The single row of an aggregate query.
fn run(query_str: &str) -> Vec<String> {
    let rows = run_rows(query_str);
    assert_eq!(rows.len(), 1, "{query_str}: one aggregate row");
    rows.into_iter().next().unwrap_or_default()
}

/// `units(position)` is an amount, and amounts sort by currency, then number,
/// so `5 EUR` is first and `3 USD` last.
#[test]
fn min_max_over_amounts_follow_the_amount_order() {
    assert_eq!(
        run("SELECT min(units(position)), max(units(position)) WHERE account = 'Assets:A'"),
        vec!["5 EUR", "3 USD"],
    );
}

/// A position sorts by beancount's currency rank first, where `USD` comes
/// before `EUR`: the opposite end from the amount order, over the same rows.
#[test]
fn min_max_over_positions_follow_the_position_order() {
    assert_eq!(
        run("SELECT min(position), max(position) WHERE account = 'Assets:A'"),
        vec!["3 USD", "5 EUR"],
    );
}

/// The whole point of the change: the aggregates are the ends of the rows
/// `ORDER BY` produces, so a reader who sorted to find them gets the same
/// answer.
#[test]
fn the_aggregates_are_the_ends_of_order_by() {
    let sorted: Vec<String> =
        run_rows("SELECT position WHERE account = 'Assets:A' ORDER BY position")
            .into_iter()
            .flatten()
            .collect();
    assert_eq!(sorted, vec!["3 USD", "5 EUR"]);
    let ends = run("SELECT min(position), max(position) WHERE account = 'Assets:A'");
    assert_eq!(ends, vec![sorted[0].clone(), sorted[1].clone()]);
}

/// Inventories sort as `Inventory.__lt__` does, by their positions sorted,
/// compared in turn, so the running balance after both postings (`5 EUR` and
/// `3 USD`) sorts before the one after the `5 EUR` posting alone: sorted, its
/// first position is `3 USD`, whose currency ranks below `EUR`.
#[test]
fn min_max_over_inventories_follow_the_inventory_order() {
    assert_eq!(
        run("SELECT min(balance), max(balance) WHERE account = 'Assets:A'"),
        vec!["5 EUR, 3 USD", "5 EUR"],
    );
}
