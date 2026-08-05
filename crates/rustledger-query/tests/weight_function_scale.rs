//! `WEIGHT()` must not invent precision the `weight` column does not (#1963).
//!
//! Found by the canonical-function drift sweep (#1902 Phase 2). CLAUDE.md names
//! this pair specifically: a consumer surfacing a per-posting weight must call
//! `rustledger_booking::posting_weight` rather than re-derive it. The `weight`
//! COLUMN does; the `WEIGHT()` FUNCTION cannot, because it receives a
//! `Position` whose cost is already resolved to a per-unit `Decimal` — the
//! preserved total that makes the canonical exact is gone by then.
//!
//! So the two cannot be made byte-identical without a wider change. What they
//! CAN be is numerically equal and free of invented scale, which is what these
//! pin.

use rustledger_query::{Executor, parse};

/// The `number:` field out of a `Value`'s debug rendering, as a `Decimal`.
fn number_of(rendered: &str) -> rust_decimal::Decimal {
    let after = rendered.split("number: ").nth(1).expect("a number field");
    let text: String = after
        .chars()
        .take_while(|c| c.is_ascii_digit() || *c == '.' || *c == '-')
        .collect();
    text.parse().expect("a parsable decimal")
}

fn numbers(source: &str, query: &str) -> Vec<(String, String)> {
    let parsed = rustledger_parser::parse(source);
    let directives: Vec<rustledger_core::Directive> =
        parsed.directives.iter().map(|d| (**d).clone()).collect();
    let mut executor = Executor::new(&directives);
    let table = executor
        .execute(&parse(query).expect("query parses"))
        .expect("query runs");
    table
        .rows
        .iter()
        .map(|r| (format!("{:?}", r[0]), format!("{:?}", r[1])))
        .collect()
}

/// A TOTAL cost that does not divide evenly is where the re-derivation shows.
///
/// `3 HOOL {{100.00 USD}}` resolves to a per-unit of 33.333…, and multiplying
/// back produced `100.00000000000000000000000000` — the same value the column
/// reports as `100.00`, carrying 26 digits of scale the multiplication invented.
#[test]
fn a_total_cost_does_not_produce_invented_precision() {
    let src = "2024-01-01 open Assets:Broker\n2024-01-01 open Assets:Cash\n\
               2024-02-01 * \"t\"\n  Assets:Broker  3 HOOL {{100.00 USD}}\n\
               \x20 Assets:Cash  -100.00 USD\n";
    let rows = numbers(
        src,
        "SELECT weight, WEIGHT(position) WHERE currency = 'HOOL'",
    );
    assert_eq!(rows.len(), 1, "one HOOL posting");
    let (column, function) = (&rows[0].0, &rows[0].1);

    // The scale the multiplication invents is the defect; 26 digits of it is
    // what this test exists to prevent coming back.
    assert!(
        function.len() < column.len() + 4,
        "WEIGHT() invented precision: column={column} function={function}",
    );
    // And they must still describe the same amount. Compared as `Decimal`,
    // whose equality is numeric — `100 == 100.00` — so this asserts the VALUE
    // while the length check above covers the scale.
    assert_eq!(
        number_of(function),
        number_of(column),
        "WEIGHT() and the weight column must agree numerically",
    );
}

/// The ordinary case must be untouched.
///
/// This is the guard that matters most here. Normalizing unconditionally was
/// tried first and fixed the case above while turning this one from `10.50`
/// into `10.5` — trading a rare cosmetic problem for a frequent one. Any future
/// attempt to close the remaining scale gap has to keep this passing.
#[test]
fn an_ordinary_per_unit_cost_keeps_its_trailing_zeros() {
    let src = "2024-01-01 open Assets:Broker\n2024-01-01 open Assets:Cash\n\
               2024-02-01 * \"t\"\n  Assets:Broker  2 HOOL {5.25 USD}\n\
               \x20 Assets:Cash  -10.50 USD\n";
    let rows = numbers(
        src,
        "SELECT weight, WEIGHT(position) WHERE currency = 'HOOL'",
    );
    assert_eq!(rows.len(), 1, "one HOOL posting");
    assert_eq!(
        rows[0].1, rows[0].0,
        "on a plain per-unit cost the function and the column must match exactly",
    );
}
