//! `MIN`/`MAX` order booleans as `false < true`; the comparison OPERATORS
//! still refuse them (#2183).
//!
//! bean-query gets the aggregate behavior for free: Python orders `False <
//! True`, so `max` over booleans is `any` and `min` is `all`. It does NOT
//! extend that to the operators —
//!
//! ```text
//! $ bean-query f.bean "SELECT (number > 0) < (number > 5) FROM #postings"
//! CompilationError: operator "less(bool, bool)" not supported
//! ```
//!
//! — so the order is defined for the aggregate path only. Measured against
//! beanquery 0.2.0 / beancount 3.2.3.

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, NaiveDate, Open, Posting, Transaction};
use rustledger_query::{Executor, Value, parse};

fn date(year: i32, month: u32, day: u32) -> NaiveDate {
    rustledger_core::naive_date(year, month, day).unwrap()
}

/// One posting is positive and one is negative, so `number > 0` yields both
/// booleans -- an aggregate over a single value would pass whatever the
/// ordering did.
fn fixture() -> Vec<Directive> {
    vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 2), "in")
                .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(10), "USD")))
                .with_synthesized_posting(Posting::new(
                    "Equity:Opening",
                    Amount::new(dec!(-10), "USD"),
                )),
        ),
    ]
}

fn run(query_str: &str) -> Result<Value, String> {
    let dirs = fixture();
    let query = parse(query_str).expect("query should parse");
    let mut executor = Executor::new(&dirs);
    executor
        .execute(&query)
        .map_err(|e| e.to_string())
        .map(|r| {
            r.rows
                .first()
                .and_then(|row| row.first())
                .cloned()
                .unwrap_or(Value::Null)
        })
}

#[test]
fn min_max_order_booleans_false_before_true() {
    assert_eq!(
        run("SELECT max(number > 0)").expect("max over booleans must work"),
        Value::Boolean(true),
        "one posting is positive, so MAX is true -- MAX over booleans is `any`",
    );
    assert_eq!(
        run("SELECT min(number > 0)").expect("min over booleans must work"),
        Value::Boolean(false),
        "one posting is negative, so MIN is false -- MIN over booleans is `all`",
    );
}

/// The order stops at the aggregates. Defining it for the operators too would
/// accept a query bean-query rejects at compile time, which is a divergence in
/// the opposite direction from the one being fixed.
#[test]
fn comparison_operators_still_refuse_booleans() {
    let err = run("SELECT (number > 0) < (number > 5)")
        .expect_err("`<` on two booleans must stay an error");
    assert!(
        err.contains("cannot compare"),
        "expected a type error, got {err}",
    );
}

/// Numbers still aggregate, so the new arm did not shadow the existing ones.
#[test]
fn min_max_over_numbers_are_unchanged() {
    assert_eq!(
        run("SELECT max(number)").expect("max over numbers"),
        Value::Number(dec!(10)),
    );
    assert_eq!(
        run("SELECT min(number)").expect("min over numbers"),
        Value::Number(dec!(-10)),
    );
}
