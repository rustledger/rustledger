//! Typed scalar functions propagate NULL instead of raising a type error
//! (SQL semantics, matching beanquery) — rustledger#1699.
//!
//! The user-facing shape: rustfava's Holdings queries run expressions like
//! `abs(sum(number(value(position))))` where the inner aggregate yields NULL
//! for cost-less groups; `only()` was fixed in v0.20.0, and this locks the
//! rest of the scalar surface.

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, NaiveDate, Open, Posting, Transaction};
use rustledger_query::{Executor, Value, parse};

fn date(year: i32, month: u32, day: u32) -> NaiveDate {
    rustledger_core::naive_date(year, month, day).unwrap()
}

fn ledger() -> Vec<Directive> {
    vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 2), "no payee")
                .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-5), "USD")))
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(5), "USD"),
                )),
        ),
    ]
}

/// Run a one-column query and return the first cell.
fn first_cell(query_str: &str) -> Value {
    let dirs = ledger();
    let query = parse(query_str).expect("query should parse");
    let mut executor = Executor::new(&dirs);
    let result = executor.execute(&query).expect("query should execute");
    result
        .rows
        .first()
        .and_then(|row| row.first())
        .cloned()
        .expect("one cell")
}

/// Every typed scalar applied to a NULL argument yields NULL, not a type
/// error. `payee` is NULL on the fixture's postings.
#[test]
fn scalars_propagate_null() {
    // string functions over NULL payee
    for func in [
        "upper",
        "lower",
        "trim",
        "length",
        "parent",
        "leaf",
        "root",
        "account_sortkey",
    ] {
        let cell = first_cell(&format!("SELECT {func}(payee) LIMIT 1"));
        assert_eq!(cell, Value::Null, "{func}(NULL) must be NULL");
    }
    // date functions over NULL (payee is not a date; use a NULL-yielding
    // expression: first() over an empty-ish... simplest: year(date) is fine,
    // so feed NULL via upper(payee) which is now NULL)
    for func in ["year", "month", "day", "quarter"] {
        let cell = first_cell(&format!("SELECT {func}(upper(payee)) LIMIT 1"));
        assert_eq!(cell, Value::Null, "{func}(NULL) must be NULL");
    }
    // numeric functions
    for func in ["abs", "neg"] {
        let cell = first_cell(&format!("SELECT {func}(upper(payee)) LIMIT 1"));
        assert_eq!(cell, Value::Null, "{func}(NULL) must be NULL");
    }
    // EMPTY deliberately treats NULL as an empty inventory (pre-existing
    // semantic; a missing inventory IS empty) rather than propagating.
    let cell = first_cell("SELECT empty(upper(payee)) LIMIT 1");
    assert_eq!(cell, Value::Boolean(true), "empty(NULL) is true by design");
}

/// The rustfava Holdings shape that motivated the fix: abs() over an
/// aggregate that can be NULL.
#[test]
fn abs_over_null_aggregate_is_null_not_error() {
    let cell = first_cell("SELECT abs(sum(number(value(position)))) GROUP BY currency LIMIT 1");
    assert!(
        matches!(cell, Value::Null | Value::Number(_)),
        "abs over aggregate must not type-error, got {cell:?}"
    );
}

/// Two-argument functions propagate NULL from the second argument too.
#[test]
fn two_arg_scalars_propagate_null_second_arg() {
    let cell = first_cell("SELECT filter_currency(balance, payee) LIMIT 1");
    assert_eq!(cell, Value::Null, "filter_currency(_, NULL) must be NULL");
    let cell = first_cell("SELECT possign(position, payee) LIMIT 1");
    assert_eq!(cell, Value::Null, "possign(_, NULL) must be NULL");
}
