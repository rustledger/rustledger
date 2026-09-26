//! `weight`, `cost` and `sum` of a posting column read through a subquery
//! agree with the query written without it (#2432).
//!
//! All three need the posting: `weight` ranks a price second, and a `{{T}}`
//! cost carries its total, neither of which a `Position` value holds. A
//! subquery's rows are values, so over one `weight(position)` of
//! `10 EUR @ 1.10 USD` gave `10 EUR` where the query without the subquery
//! gives `11.00 USD`, and a `{{500 USD}}` lot weighed and cost
//! 500.00…01. The subquery now computes them where it can reach the
//! posting and carries them in hidden columns.

use rustledger_booking::BookingEngine;
use rustledger_core::{BookingMethod, Directive};
use rustledger_query::{Executor, Value, parse};

const LEDGER: &str = r#"
2024-01-01 open Assets:E
2024-01-01 open Assets:C
2024-01-01 open Assets:B X "FIFO"
2024-01-01 open Assets:U Z "FIFO"

2024-01-02 * "priced"
  Assets:E  10 EUR @ 1.10 USD
  Assets:C

2024-01-03 * "priced again"
  Assets:E  10 EUR @ 1.20 USD
  Assets:C

2024-01-04 * "total lot"
  Assets:B  3 X {{500 USD}}
  Assets:C

2024-01-05 * "per-unit lot"
  Assets:U  4 Z {12.50 USD}
  Assets:C
"#;

fn booked(source: &str) -> Vec<Directive> {
    let parsed = rustledger_parser::parse(source);
    let mut directives: Vec<Directive> = parsed.directives.iter().map(|d| (**d).clone()).collect();
    let mut engine = BookingEngine::with_method(BookingMethod::Fifo);
    engine.register_account_methods(directives.iter());
    for directive in &mut directives {
        if let Directive::Transaction(txn) = directive {
            engine
                .book_interpolate_apply(txn)
                .expect("the fixture books");
        }
    }
    directives
}

fn run(directives: &[Directive], bql: &str) -> Result<(Vec<String>, Vec<Vec<Value>>), String> {
    let query = parse(bql).map_err(|e| format!("{bql}: {e:?}"))?;
    Executor::new(directives)
        .execute(&query)
        .map(|r| (r.columns, r.rows))
        .map_err(|e| e.to_string())
}

fn rows(directives: &[Directive], bql: &str) -> Vec<Vec<Value>> {
    run(directives, bql)
        .unwrap_or_else(|e| panic!("{bql}: {e}"))
        .1
}

/// Every way a subquery can hand the posting column through: named, from
/// `SELECT *`, renamed, nested, and over `#postings`.
#[test]
fn a_subquery_passes_the_posting_through() {
    let directives = booked(LEDGER);
    let direct = rows(
        &directives,
        "SELECT date, account, weight(position), cost(position) ORDER BY date, account",
    );
    assert_eq!(direct.len(), 8);
    for bql in [
        "SELECT date, account, weight(position), cost(position) \
         FROM (SELECT date, account, position) ORDER BY date, account",
        "SELECT date, account, weight(position), cost(position) \
         FROM (SELECT *) ORDER BY date, account",
        "SELECT date, account, weight(p), cost(p) \
         FROM (SELECT date, account, position AS p) ORDER BY date, account",
        "SELECT date, account, weight(position), cost(position) \
         FROM (SELECT date, account, position FROM (SELECT date, account, position)) \
         ORDER BY date, account",
        "SELECT date, account, weight(p), cost(p) \
         FROM (SELECT date, account, p FROM (SELECT date, account, position AS p)) \
         ORDER BY date, account",
        "SELECT date, account, weight(position), cost(position) \
         FROM (SELECT date, account, position FROM #postings) \
         ORDER BY date, account",
        "SELECT date, account, weight(position), cost(position) \
         FROM (SELECT * FROM #postings) ORDER BY date, account",
        "SELECT date, account, weight(position), cost(position) \
         FROM (SELECT * FROM (SELECT date, account, position)) ORDER BY date, account",
    ] {
        assert_eq!(rows(&directives, bql), direct, "{bql}");
    }
}

/// And in the outer query's other clauses, and its aggregates.
#[test]
fn every_clause_of_the_outer_query_reads_the_posting() {
    let directives = booked(LEDGER);
    let select = "SELECT account, sum(weight(position)), cost(sum(position))";
    let tail = "WHERE number(weight(position)) > 11 GROUP BY account ORDER BY account";
    let direct = rows(&directives, &format!("{select} {tail}"));
    let through = rows(
        &directives,
        &format!("{select} FROM (SELECT account, position) {tail}"),
    );
    assert_eq!(through, direct);
    // 11.00 and 12.00 USD for Assets:E pass the filter; `10 EUR` did not.
    assert!(
        direct
            .iter()
            .any(|r| r[0] == Value::String("Assets:E".into())),
        "{direct:?}"
    );
}

/// A column the subquery computes is a value, even named `position`: it has
/// no posting to read.
#[test]
fn a_computed_column_keeps_the_value_path() {
    let directives = booked(LEDGER);
    let got = rows(
        &directives,
        "SELECT weight(position) FROM (SELECT account, units(position) AS position) \
         WHERE account = 'Assets:B'",
    );
    match &got[0][0] {
        Value::Amount(a) => assert_eq!(a.to_string(), "3 X"),
        other => panic!("expected an amount, got {other:?}"),
    }
}

/// An inner query whose rows are not one per posting is left alone: an extra
/// column would change which rows it returns, and a row that stands for
/// several postings has no one posting to read. `Assets:E`'s two postings are
/// the same position at different prices.
#[test]
fn a_distinct_or_grouped_inner_query_keeps_the_value_path() {
    let directives = booked(LEDGER);
    for inner in [
        "SELECT DISTINCT account, position WHERE account = 'Assets:E'",
        "SELECT account, position WHERE account = 'Assets:E' GROUP BY account, position",
    ] {
        let got = rows(
            &directives,
            &format!("SELECT weight(position) FROM ({inner})"),
        );
        // One row, not one per weight; its units, not either price.
        assert_eq!(got.len(), 1, "{inner}: {got:?}");
        match &got[0][0] {
            Value::Amount(a) => assert_eq!(a.to_string(), "10 EUR", "{inner}"),
            other => panic!("{inner}: expected an amount, got {other:?}"),
        }
    }
}

/// A column the subquery does not return is still missing: the hidden values
/// ride beside a column, never in place of one.
#[test]
fn a_column_the_subquery_does_not_return_is_still_unknown() {
    let directives = booked(LEDGER);
    for inner in [
        "SELECT account",
        "SELECT account FROM #postings",
        "SELECT * FROM (SELECT account)",
        "SELECT * FROM #accounts",
    ] {
        let err = run(
            &directives,
            &format!("SELECT weight(position) FROM ({inner})"),
        )
        .expect_err("position is not a column of the subquery");
        assert!(err.contains("position"), "{inner}: {err}");
    }
}

/// `sum(position)` records each lot's exact total through every layer, so the
/// held `{{500 USD}}` lot costs 500, not 500.00…01.
#[test]
fn cost_of_the_sum_is_exact_through_nested_subqueries_and_postings() {
    let directives = booked(LEDGER);
    let tail = "GROUP BY account ORDER BY account";
    let direct = rows(
        &directives,
        &format!("SELECT account, cost(sum(position)) {tail}"),
    );
    for inner in [
        "SELECT account, position",
        "SELECT account, position FROM (SELECT account, position)",
        "SELECT account, position FROM #postings",
        "SELECT account, position FROM (SELECT account, position FROM #postings)",
    ] {
        let got = rows(
            &directives,
            &format!("SELECT account, cost(sum(position)) FROM ({inner}) {tail}"),
        );
        assert_eq!(got, direct, "{inner}");
    }
    let held = direct
        .iter()
        .find(|r| r[0] == Value::String("Assets:B".into()))
        .expect("Assets:B has a row");
    match &held[1] {
        Value::Inventory(inv) => assert_eq!(inv.to_string(), "500 USD"),
        other => panic!("expected an inventory, got {other:?}"),
    }
}

/// The hidden columns stay out of an outer `SELECT *`.
#[test]
fn select_star_over_a_subquery_does_not_show_them() {
    let directives = booked(LEDGER);
    let (columns, _) = run(
        &directives,
        "SELECT * FROM (SELECT account, position) WHERE number(weight(position)) > 0",
    )
    .expect("query runs");
    assert_eq!(columns, vec!["account", "position"]);
}

/// The subquery computes a cost for every row, so an overflowing one fails
/// only a query that reads it, as without the subquery.
#[test]
fn an_overflowing_cost_fails_only_the_query_that_reads_it() {
    let directives: Vec<Directive> = rustledger_parser::parse(
        r#"
2024-01-01 open Assets:A
2024-01-01 open Assets:C

2024-01-02 * "huge"
  Assets:A  10 X {79228162514264337593543950335 USD}
  Assets:C  -1 USD
"#,
    )
    .directives
    .iter()
    .map(|d| (**d).clone())
    .collect();
    for inner in [
        "SELECT account, position",
        "SELECT account, position FROM #postings",
    ] {
        let filtered = run(
            &directives,
            &format!("SELECT cost(position) FROM ({inner}) WHERE account = 'Assets:C'"),
        )
        .expect("the overflowing row is filtered out");
        assert_eq!(filtered.1.len(), 1, "{inner}");
        let err = run(
            &directives,
            &format!("SELECT cost(position) FROM ({inner})"),
        )
        .expect_err("the lot overflows");
        assert!(
            err.contains("exceeds the representable range"),
            "{inner}: {err}"
        );
    }
}

/// The subquery computes each value for every row, but whether it fails is
/// the outer query's business: `weight` or `cost` of a column that is no
/// position fails only for a row the outer query reads, and with the error
/// it gives without a subquery, not for rows its WHERE drops.
#[test]
fn a_failing_value_fails_only_for_a_row_the_outer_query_reads() {
    let directives = booked(LEDGER);
    for function in ["weight", "cost"] {
        for inner in ["SELECT account", "SELECT account FROM #postings"] {
            let filtered = run(
                &directives,
                &format!("SELECT {function}(account) FROM ({inner}) WHERE account = 'none'"),
            )
            .unwrap_or_else(|e| panic!("{function}, {inner}: {e}"));
            assert!(filtered.1.is_empty(), "{function}, {inner}");
            let err = run(
                &directives,
                &format!("SELECT {function}(account) FROM ({inner})"),
            )
            .expect_err("an account is not a position");
            assert!(err.starts_with("type error"), "{function}, {inner}: {err}");
        }
    }
}
