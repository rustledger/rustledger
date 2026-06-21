//! Regression: `COUNT(column)` counts only non-NULL values (SQL semantics,
//! matching beanquery), while `COUNT(*)` counts every row.

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, NaiveDate, Open, Posting, Transaction};
use rustledger_query::{Executor, Value, parse};

fn date(year: i32, month: u32, day: u32) -> NaiveDate {
    rustledger_core::naive_date(year, month, day).unwrap()
}

fn count(query_str: &str, directives: &[Directive]) -> i64 {
    let query = parse(query_str).expect("query should parse");
    let mut executor = Executor::new(directives);
    let result = executor.execute(&query).expect("query should execute");
    match result.rows.first().and_then(|row| row.first()) {
        Some(Value::Integer(n)) => *n,
        other => panic!("expected an integer count, got {other:?}"),
    }
}

/// One transaction has a payee, one does not (payee is NULL). `COUNT(*)` counts
/// all four postings; `COUNT(payee)` counts only the two with a payee.
#[test]
fn count_column_excludes_nulls() {
    let dirs = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 2), "with payee")
                .with_payee("Alpha")
                .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-5), "USD")))
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(5), "USD"),
                )),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 3), "no payee")
                .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-7), "USD")))
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(7), "USD"),
                )),
        ),
    ];

    assert_eq!(
        count("SELECT count(*)", &dirs),
        4,
        "COUNT(*) counts all rows"
    );
    assert_eq!(
        count("SELECT count(payee)", &dirs),
        2,
        "COUNT(payee) counts only non-NULL payees"
    );
}
