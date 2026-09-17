//! `date ± days` and `date - date`, end to end through the executor (#2324).
//!
//! The operators landed with unit tests inside `rustledger-query` and nothing
//! else: no corpus or compatibility fixture exercises them, so the parity
//! suites say nothing about this surface (#2328). These cases are the ones
//! that were verified by hand against beanquery 0.2.0 / beancount 3.2.3 while
//! the operators were written, pinned here so the next change to the rule has
//! to break a test rather than a reviewer's memory.
//!
//! Measured against bean-query for each case below:
//!
//! ```text
//! SELECT 2026-07-01 + 365            -> 2027-07-01
//! SELECT 365 + 2026-07-01            -> 2027-07-01
//! SELECT 2026-07-01 - 365            -> 2025-07-01
//! SELECT 2026-07-01 - 2026-06-01     -> 30
//! SELECT 2025-03-01 - 2024-02-01     -> 394      (spans a leap day)
//! SELECT 365 - 2026-07-01            -> operator "sub(int, date)" not supported
//! SELECT 2026-07-01 + 2026-06-01     -> operator "add(date, date)" not supported
//! SELECT 2026-07-01 + 0.5            -> operator "add(date, decimal)" not supported
//! ```
//!
//! Two deliberate divergences, both documented in CHANGELOG:
//!
//! - `2026-07-01 + 30.0` is accepted here and refused by bean-query, which
//!   takes only its `int` type. A whole-valued decimal names a whole number of
//!   days unambiguously.
//! - `date_add(d, 0.5)` is refused here and silently truncated before #2324 --
//!   it added no days at all, and `1.9` added one.

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, NaiveDate, Open, Posting, Transaction};
use rustledger_query::{Executor, Value, parse};

fn date(year: i32, month: u32, day: u32) -> NaiveDate {
    rustledger_core::naive_date(year, month, day).unwrap()
}

/// Two transactions 67 days apart, so the aggregate case below has a span to
/// measure rather than a single date compared with itself.
fn fixture() -> Vec<Directive> {
    vec![
        Directive::Open(Open::new(date(2026, 1, 1), "Expenses:Food")),
        Directive::Open(Open::new(date(2026, 1, 1), "Assets:Cash")),
        Directive::Transaction(
            Transaction::new(date(2026, 7, 15), "a")
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(25.00), "USD"),
                ))
                .with_synthesized_posting(Posting::new(
                    "Assets:Cash",
                    Amount::new(dec!(-25.00), "USD"),
                )),
        ),
        Directive::Transaction(
            Transaction::new(date(2026, 9, 20), "b")
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(10.00), "USD"),
                ))
                .with_synthesized_posting(Posting::new(
                    "Assets:Cash",
                    Amount::new(dec!(-10.00), "USD"),
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
fn a_day_count_shifts_a_date_from_either_side() {
    for (query, expected) in [
        ("SELECT 2026-07-01 + 365 LIMIT 1", date(2027, 7, 1)),
        ("SELECT 365 + 2026-07-01 LIMIT 1", date(2027, 7, 1)),
        ("SELECT 2026-07-01 - 365 LIMIT 1", date(2025, 7, 1)),
        ("SELECT 2026-07-01 + -1 LIMIT 1", date(2026, 6, 30)),
        // A whole-valued decimal names a whole number of days. bean-query
        // refuses every decimal here; answering this one loses nothing.
        ("SELECT 2026-07-01 + 30.0 LIMIT 1", date(2026, 7, 31)),
        // Leap day, both directions.
        ("SELECT 2024-02-29 + 365 LIMIT 1", date(2025, 2, 28)),
        ("SELECT 2024-03-01 - 1 LIMIT 1", date(2024, 2, 29)),
    ] {
        assert_eq!(
            run(query).unwrap_or_else(|e| panic!("{query}: {e}")),
            Value::Date(expected),
            "{query}",
        );
    }
}

#[test]
fn subtracting_two_dates_counts_the_days_between() {
    for (query, expected) in [
        ("SELECT 2026-07-01 - 2026-06-01 LIMIT 1", 30),
        // Reversed, so the sign is pinned rather than assumed.
        ("SELECT 2026-06-01 - 2026-07-01 LIMIT 1", -30),
        // Spans 2024-02-29: an off-by-one in leap handling shows here.
        ("SELECT 2025-03-01 - 2024-02-01 LIMIT 1", 394),
        // The aggregate shape people actually write, over the fixture's
        // 2026-07-15 and 2026-09-20.
        ("SELECT max(date) - min(date)", 67),
    ] {
        assert_eq!(
            run(query).unwrap_or_else(|e| panic!("{query}: {e}")),
            Value::Integer(expected),
            "{query}",
        );
    }
}

#[test]
fn the_operator_and_the_function_agree() {
    let by_operator = run("SELECT 2025-03-01 - 2024-02-01 LIMIT 1").expect("operator");
    let by_function = run("SELECT date_diff(2025-03-01, 2024-02-01) LIMIT 1").expect("function");
    assert_eq!(
        by_operator, by_function,
        "`date - date` is computed the way date_diff computes it; if these \
         ever disagree, one of them has been changed alone",
    );
}

#[test]
fn a_date_takes_only_whole_days_and_only_on_one_side() {
    for query in [
        // A date has day resolution, so a fraction has no answer to give.
        "SELECT 2026-07-01 + 0.5 LIMIT 1",
        "SELECT 2026-07-01 - 0.5 LIMIT 1",
        // bean-query refuses both of these too.
        "SELECT 365 - 2026-07-01 LIMIT 1",
        "SELECT 2026-07-01 + 2026-06-01 LIMIT 1",
        // DATE_ADD truncated a fraction before #2324: 0.5 added no days.
        "SELECT date_add(2026-07-01, 0.5) LIMIT 1",
        "SELECT date_add(2026-07-01, 1.9) LIMIT 1",
    ] {
        assert!(
            run(query).is_err(),
            "{query} must be refused rather than guessed at",
        );
    }
}

#[test]
fn an_out_of_range_shift_is_an_error_not_a_panic() {
    for query in [
        "SELECT 9999-12-31 + 1 LIMIT 1",
        "SELECT 2026-07-01 + 999999999999 LIMIT 1",
        "SELECT 2026-07-01 - 999999999999 LIMIT 1",
    ] {
        assert!(run(query).is_err(), "{query} must report, not panic");
    }
}
