//! Regression: NULL sorts as the smallest value (matching beanquery) — ORDER BY
//! ASC places NULLs first, DESC places them last.

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, NaiveDate, Open, Posting, Transaction};
use rustledger_query::{Executor, Value, parse};

fn date(year: i32, month: u32, day: u32) -> NaiveDate {
    rustledger_core::naive_date(year, month, day).unwrap()
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
        txn(4, Some("Beta"), "b"),
    ]
}

/// The payee column, one entry per result row (`None` = NULL).
fn payee_order(query_str: &str) -> Vec<Option<String>> {
    let query = parse(query_str).expect("parse");
    let directives = dirs();
    let mut ex = Executor::new(&directives);
    let result = ex.execute(&query).expect("execute");
    result
        .rows
        .iter()
        .map(|row| match row.first() {
            Some(Value::String(s)) => Some(s.clone()),
            _ => None,
        })
        .collect()
}

#[test]
fn order_by_asc_puts_nulls_first() {
    let order = payee_order("SELECT payee ORDER BY payee");
    assert_eq!(
        order,
        vec![
            None,
            None,
            Some("Alpha".into()),
            Some("Alpha".into()),
            Some("Beta".into()),
            Some("Beta".into()),
        ],
        "ASC: NULLs first, then ascending"
    );
}

#[test]
fn order_by_desc_puts_nulls_last() {
    let order = payee_order("SELECT payee ORDER BY payee DESC");
    assert_eq!(
        order,
        vec![
            Some("Beta".into()),
            Some("Beta".into()),
            Some("Alpha".into()),
            Some("Alpha".into()),
            None,
            None,
        ],
        "DESC: descending, then NULLs last"
    );
}
