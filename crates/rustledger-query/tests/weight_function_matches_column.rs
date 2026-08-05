//! `WEIGHT(position)` and the `weight` column must be ONE computation (#1966).
//!
//! CLAUDE.md's canonical-function rule names this pair: a consumer surfacing a
//! per-posting weight calls `rustledger_booking::posting_weight` rather than
//! re-deriving it. The column always did. The function did not, because it was
//! dispatched through the shared value registry, and by the time the registry
//! sees a `Value::Position` the posting is gone — a `Position` carries units and
//! cost and no PRICE.
//!
//! So the function implemented two rungs of a three-rung ladder (cost, price,
//! units) and silently returned the units for the middle case. `10 EUR @ 1.10
//! USD` gave `10 EUR` where the column gives `11.00 USD`: a different number in
//! a different currency, which made any SUM over a priced ledger a
//! currency-mixed total.
//!
//! These pin the two spellings together across every rung, so the function
//! cannot drift from the canonical again.

use rustledger_query::{Executor, parse};

/// `(weight column, WEIGHT(position))` per row, as rendered values.
fn column_and_function(source: &str) -> Vec<(String, String)> {
    let parsed = rustledger_parser::parse(source);
    let directives: Vec<rustledger_core::Directive> =
        parsed.directives.iter().map(|d| (**d).clone()).collect();
    let mut executor = Executor::new(&directives);
    let table = executor
        .execute(&parse("SELECT weight, WEIGHT(position)").expect("query parses"))
        .expect("query runs");
    table
        .rows
        .iter()
        .map(|r| (format!("{:?}", r[0]), format!("{:?}", r[1])))
        .collect()
}

fn assert_agrees(source: &str, what: &str) {
    let rows = column_and_function(source);
    assert!(!rows.is_empty(), "{what}: fixture produced no rows");
    let disagreements: Vec<String> = rows
        .iter()
        .filter(|(column, function)| column != function)
        .map(|(column, function)| format!("column={column} function={function}"))
        .collect();
    assert!(
        disagreements.is_empty(),
        "{what}: {} of {} rows disagree:\n{}",
        disagreements.len(),
        rows.len(),
        disagreements.join("\n"),
    );
}

/// The PRICE rung — the one that was missing entirely.
///
/// A posting with a price and no cost took the units fallthrough, so the
/// function reported `10 EUR` against the column's `11.00 USD`.
#[test]
fn a_price_annotation_is_weighed_like_the_column() {
    assert_agrees(
        "2024-01-01 open Assets:Bank\n2024-01-01 open Assets:Cash\n\
         2024-02-01 * \"per-unit price\"\n  Assets:Bank    10 EUR @ 1.10 USD\n\
         \x20 Assets:Cash  -11.00 USD\n",
        "@ per-unit price",
    );
}

/// `@@` too, whose sign handling is its own trap (#1052).
#[test]
fn a_total_price_is_weighed_like_the_column() {
    assert_agrees(
        "2024-01-01 open Assets:Bank\n2024-01-01 open Assets:Cash\n\
         2024-02-01 * \"total price\"\n  Assets:Bank   -10 EUR @@ 11.00 USD\n\
         \x20 Assets:Cash   11.00 USD\n",
        "@@ total price on a negative posting",
    );
}

/// The COST rung, including the total-cost shape that #1963 was about.
///
/// This also pins the residual gap #1963 documented as unfixed: the function
/// re-derived `100` where the column reports `100.00`. Routing to the canonical
/// closes it, because there is no longer a re-derivation to lose scale in.
#[test]
fn a_cost_is_weighed_like_the_column() {
    assert_agrees(
        "2024-01-01 open Assets:Broker\n2024-01-01 open Assets:Cash\n\
         2024-02-01 * \"per-unit cost\"\n  Assets:Broker  2 HOOL {5.25 USD}\n\
         \x20 Assets:Cash  -10.50 USD\n",
        "per-unit cost",
    );
    assert_agrees(
        "2024-01-01 open Assets:Broker\n2024-01-01 open Assets:Cash\n\
         2024-02-01 * \"total cost\"\n  Assets:Broker  3 HOOL {{100.00 USD}}\n\
         \x20 Assets:Cash  -100.00 USD\n",
        "total cost — the #1963 scale case",
    );
}

/// The UNITS rung, so the fix cannot have been "always take the price".
#[test]
fn a_plain_posting_is_weighed_like_the_column() {
    assert_agrees(
        "2024-01-01 open Assets:Bank\n2024-01-01 open Expenses:Food\n\
         2024-02-01 * \"plain\"\n  Assets:Bank   -10.00 USD\n\
         \x20 Expenses:Food  10.00 USD\n",
        "no cost and no price",
    );
}

/// Cost AND price on one posting: cost wins, per the ladder's order.
///
/// This one asserts the VALUE, not just agreement. Agreement alone cannot see
/// the ladder order at all — both sides now route through the same canonical,
/// so swapping cost and price inside `posting_weight` moves them together and
/// every `assert_agrees` above stays green. Verified by doing exactly that.
///
/// `2 HOOL {5.25 USD} @ 6.00 USD` weighs by its COST: 10.50 USD, not the
/// 12.00 USD the price would give.
#[test]
fn a_cost_outranks_a_price_as_the_column_does() {
    let source = "2024-01-01 open Assets:Broker\n2024-01-01 open Assets:Cash\n\
                  2024-02-01 * \"cost and price\"\n\
                  \x20 Assets:Broker  2 HOOL {5.25 USD} @ 6.00 USD\n\
                  \x20 Assets:Cash  -10.50 USD\n";
    assert_agrees(source, "cost outranks price");

    let rows = column_and_function(source);
    let broker = &rows[0].1;
    assert!(
        broker.contains("10.50"),
        "a posting with both a cost and a price must weigh by its COST \
         (10.50 USD), not its price (12.00 USD); got {broker}",
    );
    assert!(
        !broker.contains("12.00"),
        "the price weight leaked through: {broker}",
    );
}
