//! `weight(position)` and `cost(position)` over `FROM #postings` agree with
//! the default FROM (#2429).
//!
//! Both need the posting: `weight` ranks a price second, and a `{{T}}` cost
//! carries its total, neither of which a `Position` value holds. The default
//! FROM routes them to the posting (#1966, #2428). `#postings` materializes its
//! rows as values, so it answered from the `Position`: `10 EUR @ 1.10 USD`
//! weighed `10 EUR` where the `weight` column says `11.00 USD`, and a
//! `{{500 USD}}` lot cost 500.00…01. It now computes both from the posting into
//! hidden columns.

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

2024-01-03 * "total lot"
  Assets:B  3 X {{500 USD}}
  Assets:C

2024-01-04 * "per-unit lot"
  Assets:U  4 Z {12.50 USD}
  Assets:C

2024-02-01 * "sell the total lot"
  Assets:B  -3 X {}
  Assets:C

2024-02-02 * "sell per-unit"
  Assets:U  -4 Z {}
  Assets:C
"#;

fn booked() -> Vec<Directive> {
    let parsed = rustledger_parser::parse(LEDGER);
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

fn query(directives: &[Directive], bql: &str) -> (Vec<String>, Vec<Vec<Value>>) {
    let mut executor = Executor::new(directives);
    let result = executor
        .execute(&parse(bql).expect("query parses"))
        .expect("query runs");
    (result.columns, result.rows)
}

/// Every posting, both spellings, both FROM clauses: one computation.
#[test]
fn weight_and_cost_of_position_agree_across_from_clauses() {
    let directives = booked();
    let select = "SELECT narration, account, weight, weight(position), cost(position)";
    let order = "ORDER BY date, account";
    let (_, default_from) = query(&directives, &format!("{select} {order}"));
    let (_, postings) = query(&directives, &format!("{select} FROM #postings {order}"));
    assert_eq!(default_from.len(), 10);
    assert_eq!(postings, default_from);
    for row in &postings {
        assert_eq!(
            row[2], row[3],
            "{:?}: weight(position) is the weight",
            row[0]
        );
    }
}

/// An inventory's non-zero positions, rendered. A cost-less position that nets
/// to zero keeps its slot (#2378) where a lot that nets to zero is dropped, so
/// `sum(cost(position))` of an emptied account holds `0 USD` and
/// `cost(sum(position))` holds nothing: the same amount.
fn held_amounts(value: &Value) -> Vec<String> {
    match value {
        Value::Inventory(inv) => inv
            .positions()
            .filter(|p| !p.units.number.is_zero())
            .map(ToString::to_string)
            .collect(),
        other => panic!("expected an inventory, got {other:?}"),
    }
}

/// `cost(sum(position))` too (#2430): the table's `sum(position)` records each
/// lot's exact total from a hidden column, as the default FROM records it
/// from the posting.
#[test]
fn cost_of_sum_of_position_agrees_across_from_clauses() {
    let directives = booked();
    let select = "SELECT account, cost(sum(position)), sum(cost(position))";
    let tail = "GROUP BY account ORDER BY account";
    // Before the sales, while the `{{500 USD}}` lot is held, and after.
    for filter in ["WHERE date < 2024-02-01", ""] {
        let (_, default_from) = query(&directives, &format!("{select} {filter} {tail}"));
        let (_, postings) = query(
            &directives,
            &format!("{select} FROM #postings {filter} {tail}"),
        );
        assert_eq!(postings, default_from, "{filter:?}");
        for row in &default_from {
            assert_eq!(
                held_amounts(&row[1]),
                held_amounts(&row[2]),
                "{filter:?}: cost of the sum is the sum of costs"
            );
        }
    }
    let (_, held) = query(
        &directives,
        "SELECT cost(sum(position)) FROM #postings WHERE account = 'Assets:B' AND date < 2024-02-01",
    );
    match &held[0][0] {
        Value::Inventory(inv) => assert_eq!(inv.to_string(), "500 USD"),
        other => panic!("expected an inventory, got {other:?}"),
    }
}

/// The hidden columns stay out of `SELECT *`: its columns are exactly the
/// table's visible ones.
#[test]
fn select_star_does_not_show_the_hidden_columns() {
    let directives = booked();
    let (columns, _) = query(&directives, "SELECT * FROM #postings LIMIT 1");
    assert_eq!(
        columns,
        [
            "type",
            "id",
            "date",
            "year",
            "month",
            "day",
            "filename",
            "lineno",
            "location",
            "flag",
            "payee",
            "narration",
            "description",
            "tags",
            "links",
            "posting_flag",
            "account",
            "other_accounts",
            "number",
            "currency",
            "cost_number",
            "cost_currency",
            "cost_date",
            "cost_label",
            "position",
            "price",
            "weight",
            "balance",
            "account_balance",
            "meta",
            "accounts",
        ]
    );
}

/// A subquery that aliases another value as `position` (and `weight`) takes
/// the value path: its table carries no hidden column to route to.
#[test]
fn a_subquery_aliasing_position_takes_the_value_path() {
    let directives = booked();
    let (_, rows) = query(
        &directives,
        "SELECT weight(position) FROM (SELECT units(position) AS position, 0 AS weight \
         FROM #postings WHERE account = 'Assets:E')",
    );
    match &rows[0][0] {
        Value::Amount(a) => assert_eq!(a.to_string(), "10 EUR"),
        other => panic!("expected an amount, got {other:?}"),
    }
}

/// `#postings` computes every row's `cost(position)` whether or not the query
/// asks for it, so a lot whose cost overflows must fail only a query that
/// reads it, as on the default FROM, which computes it only when asked.
#[test]
fn an_overflowing_cost_fails_only_the_query_that_reads_it() {
    let parsed = rustledger_parser::parse(
        r#"
2024-01-01 open Assets:A
2024-01-01 open Assets:C

2024-01-02 * "huge"
  Assets:A  10 X {79228162514264337593543950335 USD}
  Assets:C  -1 USD
"#,
    );
    let directives: Vec<Directive> = parsed.directives.iter().map(|d| (**d).clone()).collect();
    let run = |bql: &str| Executor::new(&directives).execute(&parse(bql).expect("query parses"));
    for from in ["", " FROM #postings"] {
        let rows = run(&format!("SELECT account{from}")).expect("no cost is read");
        assert_eq!(rows.rows.len(), 2, "{from:?}");
        let rows = run(&format!(
            "SELECT cost(position){from} WHERE account = 'Assets:C'"
        ))
        .expect("the overflowing row is filtered out");
        assert_eq!(rows.rows.len(), 1, "{from:?}");
        let err = run(&format!("SELECT cost(position){from}")).expect_err("the lot overflows");
        assert!(
            err.to_string().contains("exceeds the representable range"),
            "{from:?}: {err}"
        );
    }
}
