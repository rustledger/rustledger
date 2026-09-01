//! Regression: `SUM` over a boolean counts the true rows (#2214).
//!
//! Python sums booleans as integers, so `sum(number > 0)` is a meaningful
//! number in beanquery. We used to reject it as a type error.
//!
//! We match bean-query's VALUE, not its output. Its CLI prints `TRUE` for this
//! query -- the result column is typed from the argument, so the integer is
//! rendered through the boolean formatter -- while the API returns `2`.
//! Verified directly against beanquery 0.2.0:
//!
//! ```text
//! conn.execute("SELECT sum(number > 0) FROM #postings").fetchall()  # [(2,)]
//! bean-query -f csv ... "SELECT sum(number > 0) FROM #postings"     # TRUE
//! ```
//!
//! Reproducing the rendering would mean reproducing a display bug, so the
//! outputs deliberately differ. `docs/reference/compatibility.md` records it.

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, NaiveDate, Open, Posting, Transaction};
use rustledger_query::{Executor, Value, parse};

fn date(year: i32, month: u32, day: u32) -> NaiveDate {
    rustledger_core::naive_date(year, month, day).unwrap()
}

/// Four postings: two negative (Assets:Cash), two positive (Expenses:Food).
fn two_transactions() -> Vec<Directive> {
    vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 2), "a")
                .with_synthesized_posting(Posting::new(
                    "Assets:Cash",
                    Amount::new(dec!(-10.00), "USD"),
                ))
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(10.00), "USD"),
                )),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 3), "b")
                .with_synthesized_posting(Posting::new(
                    "Assets:Cash",
                    Amount::new(dec!(-20.00), "USD"),
                ))
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(20.00), "USD"),
                )),
        ),
    ]
}

fn rows(query_str: &str, directives: &[Directive]) -> Vec<Vec<Value>> {
    let query = parse(query_str).expect("query should parse");
    let mut executor = Executor::new(directives);
    executor.execute(&query).expect("query should execute").rows
}

/// The value bean-query's API returns, as an Integer rather than a Decimal:
/// this is a count, and `COUNT` answers with an Integer too.
#[test]
fn sum_over_a_boolean_counts_the_true_rows() {
    let dirs = two_transactions();
    let result = rows("SELECT sum(number > 0) FROM #postings", &dirs);
    assert_eq!(
        result,
        vec![vec![Value::Integer(2)]],
        "two of the four postings are positive",
    );
}

/// The accumulator is duplicated, and the split is NOT grouped-vs-ungrouped as
/// it looks: one copy serves queries written WITHOUT `FROM`, the other serves
/// every `FROM #postings` form, grouped or not. Established by marking one copy
/// and seeing which queries moved -- the first version of this file tested the
/// same copy twice while claiming to cover both. `sum_without_a_from_clause`
/// below is the one that reaches the other copy.
///
/// bean-query's API returns `[('Assets:Cash', 0), ('Expenses:Food', 2)]` here.
#[test]
fn the_grouped_sum_path_counts_booleans_too() {
    let dirs = two_transactions();
    let result = rows(
        "SELECT account, sum(number > 0) FROM #postings GROUP BY account ORDER BY account",
        &dirs,
    );
    assert_eq!(
        result,
        vec![
            vec![Value::String("Assets:Cash".to_string()), Value::Integer(0)],
            vec![
                Value::String("Expenses:Food".to_string()),
                Value::Integer(2)
            ],
        ],
        "a group with no TRUE rows sums to 0, not NULL",
    );
}

/// Summing actual numbers must be untouched -- in particular the Python scale
/// semantics that make a total passing through zero render `0.00`, not `0`.
/// Accepting booleans by widening the numeric arm would quietly break this.
#[test]
fn summing_numbers_is_unchanged() {
    let dirs = two_transactions();
    let result = rows("SELECT sum(number) FROM #postings", &dirs);
    assert_eq!(
        result,
        vec![vec![Value::Number(dec!(0.00))]],
        "the numeric sum keeps its scale and stays a Number, not an Integer",
    );
}

/// `AVG` over a boolean still refuses, which is what bean-query does
/// (`CompilationError: no function matches "avg(bool)"`). Agreeing by
/// rejecting is still agreeing, and widening SUM must not widen AVG.
#[test]
fn avg_over_a_boolean_still_refuses() {
    let dirs = two_transactions();
    let query = parse("SELECT avg(number > 0) FROM #postings").expect("query should parse");
    let mut executor = Executor::new(&dirs);
    let err = executor
        .execute(&query)
        .expect_err("AVG over a boolean must stay an error");
    let text = err.to_string();
    assert!(
        text.contains("AVG"),
        "the error should name AVG, got {text:?}",
    );
}

/// The no-`FROM` form, which is the OTHER copy of the accumulator. Both must
/// agree; bean-query's API returns `[(2,)]` for this too.
#[test]
fn sum_without_a_from_clause_counts_booleans() {
    let dirs = two_transactions();
    let result = rows("SELECT sum(number > 0)", &dirs);
    assert_eq!(
        result,
        vec![vec![Value::Integer(2)]],
        "the no-FROM accumulator must count true rows like the table one",
    );
}
