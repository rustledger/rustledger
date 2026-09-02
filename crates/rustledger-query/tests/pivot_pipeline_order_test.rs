//! `ORDER BY` and `LIMIT` apply to the PIVOTED rows (#2219).
//!
//! Our pipeline is `ORDER BY -> pivot -> LIMIT`. bean-query's is
//! `ORDER BY -> LIMIT -> pivot`, and its pivot then re-sorts, so an explicit
//! `ORDER BY` never reaches the output. Measured against beanquery 0.2.0:
//!
//! ```text
//! ORDER BY account DESC LIMIT 2
//!   bean-query   Equity:O                      <- 1 row, DESC not visible
//!   rustledger   Equity:O, Assets:B            <- 2 rows, DESC honored
//! ```
//!
//! We keep ours, and the two clauses are ONE decision rather than two:
//!
//! * bean-query's `ORDER BY` loss is an artifact, not a policy.
//!   `EvalPivot.__call__` does `rows.sort(key=itemgetter(col1))` immediately
//!   before `itertools.groupby(rows, key=itemgetter(col1))` -- the sort is a
//!   precondition of `groupby`, which only groups ADJACENT equal keys. It
//!   destroys the requested order as a side effect. No upstream test covers
//!   `PIVOT BY` with either clause.
//!
//! * bean-query's `LIMIT` is coherent under its own model -- pivot as a
//!   display reshape over a finished query -- but that model is what discards
//!   `ORDER BY`. Once the requested order is honored on the pivoted rows,
//!   `LIMIT` has to count those same rows: ordering one row set and limiting a
//!   different one would be incoherent.
//!
//! So matching bean-query here is a package deal that includes silently
//! ignoring an explicit clause. Recorded in `docs/reference/compatibility.md`.

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, NaiveDate, Open, Posting, Transaction};
use rustledger_query::{Executor, QueryResult, parse};

fn date(y: i32, m: u32, d: u32) -> NaiveDate {
    rustledger_core::naive_date(y, m, d).unwrap()
}

/// Three accounts; `Assets:A` only in 2024, `Assets:B` only in 2025,
/// `Equity:O` in both. The lopsidedness is the point: it makes the column set
/// depend on WHICH rows survive a limit, which is how bean-query drops a
/// column here.
fn ledger() -> Vec<Directive> {
    vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:A")),
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:B")),
        Directive::Open(Open::new(date(2024, 1, 1), "Equity:O")),
        Directive::Transaction(
            Transaction::new(date(2024, 6, 1), "a")
                .with_synthesized_posting(Posting::new("Assets:A", Amount::new(dec!(10), "USD")))
                .with_synthesized_posting(Posting::new("Equity:O", Amount::new(dec!(-10), "USD"))),
        ),
        Directive::Transaction(
            Transaction::new(date(2025, 6, 1), "b")
                .with_synthesized_posting(Posting::new("Assets:B", Amount::new(dec!(5), "USD")))
                .with_synthesized_posting(Posting::new("Equity:O", Amount::new(dec!(-5), "USD"))),
        ),
    ]
}

fn run(q: &str) -> QueryResult {
    let dirs = ledger();
    let query = parse(q).expect("parse");
    let mut ex = Executor::new(&dirs);
    ex.execute(&query).expect("execute")
}

fn keys(r: &QueryResult) -> Vec<String> {
    r.rows
        .iter()
        .map(|row| match row.first() {
            Some(rustledger_query::Value::String(s)) => s.clone(),
            other => format!("{other:?}"),
        })
        .collect()
}

/// `ORDER BY` precedes `PIVOT BY` in the grammar, and `LIMIT` follows it, so
/// the query text cannot be assembled by appending clauses in pipeline order.
/// Built here so each test names only the parts it varies.
fn query(order_by: &str, limit: &str) -> String {
    format!(
        "SELECT account, year, sum(number) FROM #postings \
         GROUP BY account, year {order_by} PIVOT BY account, year {limit}"
    )
}

/// The same query WITHOUT `FROM #postings`.
///
/// The pipeline is written out at three sites, and they are not
/// interchangeable: this one routes through `execute_select`, the `FROM`
/// form through `finish_aggregate_result`. (The third, in
/// `execute_select_from_table`, cannot reach a pivot -- `PIVOT BY` requires
/// `GROUP BY`, which routes elsewhere.) Established by moving `LIMIT` ahead of
/// the pivot at one site and seeing which tests moved: the first attempt
/// mutated `execute_select` and nothing failed, because every test here used
/// the `FROM` form.
fn query_without_from(order_by: &str, limit: &str) -> String {
    format!(
        "SELECT account, year, sum(number) \
         GROUP BY account, year {order_by} PIVOT BY account, year {limit}"
    )
}

/// `ORDER BY` reaches the output. bean-query's pivot re-sorts by the key and
/// loses it; ours does not.
#[test]
fn order_by_survives_the_pivot() {
    let desc = run(&query("ORDER BY account DESC", ""));
    assert_eq!(
        keys(&desc),
        vec!["Equity:O", "Assets:B", "Assets:A"],
        "DESC must be visible in the pivoted output",
    );
    let asc = run(&query("ORDER BY account ASC", ""));
    assert_eq!(
        keys(&asc),
        vec!["Assets:A", "Assets:B", "Equity:O"],
        "and ASC must differ from it, or the test proves nothing",
    );
}

/// `LIMIT` counts PIVOTED rows, so `LIMIT 2` yields exactly 2. Under
/// bean-query's order the same query yields 1, because both surviving
/// pre-pivot rows belong to one account.
#[test]
fn limit_counts_pivoted_rows() {
    let limited = run(&query("ORDER BY account DESC", "LIMIT 2"));
    assert_eq!(
        keys(&limited),
        vec!["Equity:O", "Assets:B"],
        "LIMIT 2 must yield 2 output rows, in the requested order",
    );
}

/// The column set does not depend on `LIMIT`. This is the property that makes
/// the pipeline predictable: bean-query drops the 2025 column from this query
/// because neither surviving pre-pivot row carries that year, so the result's
/// SHAPE changes with the limit.
#[test]
fn the_column_set_does_not_depend_on_the_limit() {
    let unlimited = run(&query("", ""));
    for limit in [1, 2, 3] {
        let limited = run(&query("", &format!("LIMIT {limit}")));
        assert_eq!(
            limited.columns, unlimited.columns,
            "LIMIT {limit} must not change which columns exist",
        );
        assert!(
            limited.rows.len() <= limit,
            "LIMIT {limit} returned {} rows",
            limited.rows.len(),
        );
    }
}

/// Both reachable pipelines must agree. Asserted against each other rather
/// than restated, so a change to either is caught even if it moves both
/// expectations.
#[test]
fn the_no_from_pipeline_orders_and_limits_the_same_way() {
    for (order_by, limit) in [
        ("ORDER BY account DESC", ""),
        ("ORDER BY account DESC", "LIMIT 2"),
        ("ORDER BY account ASC", "LIMIT 2"),
    ] {
        let with_from = run(&query(order_by, limit));
        let without = run(&query_without_from(order_by, limit));
        assert_eq!(
            keys(&without),
            keys(&with_from),
            "a FROM clause must not change the pipeline order ({order_by} / {limit})",
        );
        assert_eq!(
            without.columns, with_from.columns,
            "nor the column set ({order_by} / {limit})",
        );
    }

    // Every case above names an ORDER BY on purpose. WITHOUT one the two
    // paths return DIFFERENT rows for the same LIMIT -- `Assets:A, Equity:O`
    // with `FROM`, `Assets:A, Assets:B` without -- because they order groups
    // differently and the limit then keeps different ones. That is a real
    // inconsistency, pre-existing on main and unrelated to the pipeline
    // ORDER this file pins, so it is tracked separately rather than asserted
    // here (#2235); asserting today's answer would pin a bug. The column set does
    // agree, which is what #2216 pinned, so only the row identity differs.
    let with_from = run(&query("", "LIMIT 2"));
    let without = run(&query_without_from("", "LIMIT 2"));
    assert_eq!(
        without.columns, with_from.columns,
        "the column set must agree even where row identity does not",
    );
}
