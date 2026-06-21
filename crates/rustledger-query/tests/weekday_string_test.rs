//! Regression: `WEEKDAY(date)` returns the day-name string (`Mon`..`Sun`),
//! matching beanquery (whose `weekday()` yields a string, not an integer).

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, NaiveDate, Open, Posting, Transaction};
use rustledger_query::{Executor, Value, parse};

fn date(y: i32, m: u32, d: u32) -> NaiveDate {
    rustledger_core::naive_date(y, m, d).unwrap()
}

fn weekday_of(day: u32) -> Value {
    // 2024-01-01 is a Monday, so day 1..7 covers Mon..Sun.
    let dirs = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:X")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, day), "t")
                .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-1), "USD")))
                .with_synthesized_posting(Posting::new("Expenses:X", Amount::new(dec!(1), "USD"))),
        ),
    ];
    let q = parse("SELECT weekday(date) LIMIT 1").expect("parse");
    let mut ex = Executor::new(&dirs);
    let r = ex.execute(&q).expect("execute");
    r.rows[0][0].clone()
}

#[test]
fn weekday_returns_day_name_string() {
    assert_eq!(weekday_of(1), Value::String("Mon".into()));
    assert_eq!(weekday_of(3), Value::String("Wed".into()));
    assert_eq!(weekday_of(7), Value::String("Sun".into()));
}
