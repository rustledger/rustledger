//! `PIVOT BY` applies when the query names a table (#2216).
//!
//! There are four execution paths that run ORDER BY and LIMIT, and only one of
//! them ran PIVOT:
//!
//! | path | sort | pivot | limit |
//! |---|---|---|---|
//! | `execute_select` (no FROM) | yes | **yes** | yes |
//! | `execute_select_from_table` | yes | no | yes |
//! | `execute_aggregate_from_table` | yes | no | yes |
//! | `execute_select_from_subquery` | yes | no | yes |
//!
//! So a query with a `FROM` clause parsed its `PIVOT BY`, validated it, and
//! then returned the un-pivoted result with no error. Since `rledger query` is
//! normally written with an explicit table, that was the form users hit.
//!
//! The subquery path is left alone: our parser rejects `FROM (SELECT ...)`
//! outright, so nothing can reach it carrying a pivot, and an untestable branch
//! is worse than a documented gap.

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, NaiveDate, Open, Posting, Transaction};
use rustledger_query::{Executor, parse};

fn date(year: i32, month: u32, day: u32) -> NaiveDate {
    rustledger_core::naive_date(year, month, day).unwrap()
}

fn fixture() -> Vec<Directive> {
    vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 2), "x")
                .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(10), "USD")))
                .with_synthesized_posting(Posting::new(
                    "Equity:Opening",
                    Amount::new(dec!(-10), "USD"),
                )),
        ),
    ]
}

fn columns_of(query_str: &str) -> Result<Vec<String>, String> {
    let dirs = fixture();
    let query = parse(query_str).expect("query should parse");
    let mut executor = Executor::new(&dirs);
    executor
        .execute(&query)
        .map(|r| r.columns)
        .map_err(|e| e.to_string())
}

/// The reported case: aggregate query, explicit table. `year` collapses into
/// column headers, so the result is two columns rather than three.
#[test]
fn pivot_applies_with_a_from_clause() {
    let with_from = columns_of(
        "SELECT account, year, sum(number) FROM #postings \
         GROUP BY account, year PIVOT BY account, year",
    )
    .expect("pivot with FROM must execute");
    assert_eq!(
        with_from,
        vec!["account".to_string(), "2024".to_string()],
        "the spread column's values must become the headers",
    );
}

/// Same query without the table, which already worked. Pinned so the two
/// cannot drift apart again -- the bug was precisely that they had.
#[test]
fn pivot_output_is_the_same_with_and_without_from() {
    let without = columns_of(
        "SELECT account, year, sum(number) GROUP BY account, year PIVOT BY account, year",
    )
    .expect("pivot without FROM");
    let with = columns_of(
        "SELECT account, year, sum(number) FROM #postings \
         GROUP BY account, year PIVOT BY account, year",
    )
    .expect("pivot with FROM");
    assert_eq!(with, without, "a FROM clause must not change the shape");
}

/// The non-aggregate table path. `PIVOT BY` requires `GROUP BY`, so this
/// cannot pivot -- but it must SAY so rather than ignore the clause, which is
/// what it did. The no-FROM form already errored; now both agree.
#[test]
fn pivot_without_group_by_errors_with_a_from_clause_too() {
    let err = columns_of("SELECT account, number FROM #postings PIVOT BY account, number")
        .expect_err("PIVOT BY without GROUP BY must be refused, not dropped");
    assert!(
        err.contains("PIVOT BY requires an explicit GROUP BY"),
        "expected the same message the no-FROM path gives, got {err}",
    );
    let without = columns_of("SELECT account, number PIVOT BY account, number")
        .expect_err("the no-FROM form errors too");
    assert_eq!(err, without, "both paths must give the same diagnostic");
}

/// An empty result must still be pivoted, and both ways of emptying it must
/// agree.
///
/// The aggregate path returned early when GROUP BY produced no groups, which
/// skipped ORDER BY, PIVOT and LIMIT. The first and last are no-ops on zero
/// rows; PIVOT is not, because it reshapes the COLUMNS. So a query emptied by
/// WHERE reported the un-pivoted header while the same query emptied by HAVING
/// reported the pivoted one. bean-query gives the pivoted shape for both.
#[test]
fn an_empty_result_is_pivoted_the_same_way_however_it_emptied() {
    let by_where = columns_of(
        "SELECT account, year, sum(number) FROM #postings WHERE account = 'nope' \
         GROUP BY account, year PIVOT BY account, year",
    )
    .expect("empty by WHERE");
    let by_having = columns_of(
        "SELECT account, year, sum(number) FROM #postings \
         GROUP BY account, year HAVING sum(number) > 100 PIVOT BY account, year",
    )
    .expect("empty by HAVING");

    assert_eq!(
        by_where, by_having,
        "how a result became empty must not change its shape",
    );
    assert_eq!(
        by_where,
        vec!["account".to_string()],
        "the pivoted shape: the row key, with no spread values to add",
    );

    // Without a pivot the same empty query keeps its projected columns, so
    // the change above did not simply drop columns from every empty result.
    let no_pivot = columns_of(
        "SELECT account, year, sum(number) FROM #postings WHERE account = 'nope' \
         GROUP BY account, year",
    )
    .expect("empty, no pivot");
    assert_eq!(
        no_pivot,
        vec![
            "account".to_string(),
            "year".to_string(),
            "sum(number)".to_string()
        ],
    );
}
