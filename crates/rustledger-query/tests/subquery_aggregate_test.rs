//! Regression: aggregates over a subquery (`SELECT agg() FROM (SELECT ...)`)
//! must aggregate to a single value, not evaluate per inner row — and
//! `COUNT(col)` in that path must exclude NULLs.

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, NaiveDate, Open, Posting, Transaction};
use rustledger_query::{Executor, Value, parse};

fn date(y: i32, m: u32, d: u32) -> NaiveDate {
    rustledger_core::naive_date(y, m, d).unwrap()
}

fn dirs() -> Vec<Directive> {
    let txn = |d: u32, payee: Option<&str>, narr: &str| {
        let mut t = Transaction::new(date(2024, 1, d), narr);
        if let Some(p) = payee {
            t = t.with_payee(p);
        }
        Directive::Transaction(
            t.with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-1), "USD")))
                .with_synthesized_posting(Posting::new("Expenses:X", Amount::new(dec!(1), "USD"))),
        )
    };
    vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:X")),
        txn(2, Some("Alpha"), "a"),
        txn(3, None, "no payee"),
    ]
}

fn one(query_str: &str) -> Value {
    let q = parse(query_str).expect("parse");
    let d = dirs();
    let mut ex = Executor::new(&d);
    let r = ex.execute(&q).expect("execute");
    assert_eq!(
        r.rows.len(),
        1,
        "aggregate must produce exactly one row: {query_str}"
    );
    r.rows[0][0].clone()
}

#[test]
fn aggregate_over_subquery_collapses_to_one_row() {
    // 4 postings; 2 have a payee.
    assert_eq!(
        one("SELECT count(*) FROM (SELECT account)"),
        Value::Integer(4),
        "COUNT(*) over a subquery aggregates to one row"
    );
    assert_eq!(
        one("SELECT count(payee) FROM (SELECT payee)"),
        Value::Integer(2),
        "COUNT(payee) over a subquery excludes NULLs"
    );
    // SUM was affected by the same per-row dispatch bug — exercise it too.
    // The 4 postings net to zero (-1/+1 per transaction).
    assert_eq!(
        one("SELECT sum(number) FROM (SELECT number)"),
        Value::Number(dec!(0)),
        "SUM(number) over a subquery aggregates to one row"
    );
}
