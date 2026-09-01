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

/// A pure aggregate over ZERO matching rows still produces one row:
/// `COUNT(*)` is 0, `SUM` is NULL. A `GROUP BY` query over zero rows produces
/// none, because there are no groups to produce them for.
///
/// `execute_aggregate_from_table` states this contract in a comment and
/// nothing pinned it: every other `count(*)` test here runs on data that
/// matches. It is worth pinning because the branch is one arm of an if/else
/// whose other arm was rewritten for #2216, and only a hand comparison against
/// `main` caught that it still held.
///
/// This is also a deliberate divergence: bean-query returns NO row for
/// `SELECT count(*)` over an empty filter, where we return 0. Recorded here so
/// a future reader meets the choice rather than assuming it is a bug.
#[test]
fn a_pure_aggregate_over_no_rows_still_returns_a_row() {
    let dirs = vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 2), "only")
                .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-5), "USD")))
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(5), "USD"),
                )),
        ),
    ];

    let rows = |q: &str| {
        let query = parse(q).expect("query should parse");
        let mut executor = Executor::new(&dirs);
        executor.execute(&query).expect("query should execute").rows
    };

    // `FROM #postings` on purpose: without it these route through
    // `execute_select`, and the branch under test lives in
    // `execute_aggregate_from_table`. Written without it first, the test
    // passed against both mutations of that branch -- protection that was not
    // there.
    let counted = rows("SELECT count(*) FROM #postings WHERE account = 'Nope:Nope'");
    assert_eq!(counted.len(), 1, "a pure aggregate always yields one row");
    assert_eq!(counted[0][0], Value::Integer(0), "COUNT(*) of nothing is 0");

    let summed = rows("SELECT sum(number) FROM #postings WHERE account = 'Nope:Nope'");
    assert_eq!(summed.len(), 1);
    assert_eq!(summed[0][0], Value::Null, "SUM of nothing is NULL, not 0");

    let grouped = rows(
        "SELECT account, count(*) FROM #postings WHERE account = 'Nope:Nope' GROUP BY account",
    );
    assert!(
        grouped.is_empty(),
        "GROUP BY over no rows has no groups, so no rows: {grouped:?}",
    );
}
