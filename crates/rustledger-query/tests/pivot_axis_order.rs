//! The order of a pivot's columns and rows (#2440).
//!
//! Columns are the spread values sorted by value, whatever the ORDER BY, as
//! bean-query (`sorted(keys)`) and `DuckDB` lay them out. They used to follow
//! the values' first appearance in the sorted rows, so with no ORDER BY on the
//! spread column they came out in ledger order. Rows follow the ORDER BY (a
//! deliberate divergence, #2219) and are sorted by key without one, as in
//! bean-query. A NULL spread value is a column, sorted first; bean-query
//! crashes on it.

use rustledger_core::Directive;
use rustledger_query::{Executor, Value, parse};

/// Currencies appear out of alphabetical order (VHT, USD, GLD) and years out
/// of order (2025 first), so an order that followed the data would show.
const LEDGER: &str = r#"
2024-01-01 open Assets:A
2024-01-01 open Assets:B

2025-03-01 * "Shop" "v"
  Assets:A  1 VHT
  Assets:B  -1 VHT

2024-03-01 * "u"
  Assets:A  2 USD
  Assets:B  -2 USD

2024-04-01 * "Cafe" "g"
  Assets:A  3 GLD
  Assets:B  -3 GLD

2025-04-01 * "Shop" "u2"
  Assets:A  4 USD
  Assets:B  -4 USD
"#;

fn run(bql: &str) -> (Vec<String>, Vec<Vec<Value>>) {
    run_on(LEDGER, bql)
}

fn run_on(ledger: &str, bql: &str) -> (Vec<String>, Vec<Vec<Value>>) {
    let directives: Vec<Directive> = rustledger_parser::parse(ledger)
        .directives
        .iter()
        .map(|d| (**d).clone())
        .collect();
    let query = parse(bql).unwrap_or_else(|e| panic!("{bql}: {e:?}"));
    let result = Executor::new(&directives)
        .execute(&query)
        .unwrap_or_else(|e| panic!("{bql}: {e}"));
    (result.columns, result.rows)
}

fn row_keys(rows: &[Vec<Value>]) -> Vec<String> {
    rows.iter()
        .map(|r| match &r[0] {
            Value::Integer(n) => n.to_string(),
            Value::String(s) => s.clone(),
            other => panic!("unexpected key {other:?}"),
        })
        .collect()
}

#[test]
fn columns_are_the_spread_values_sorted_whatever_the_order_by() {
    let want = vec!["year/currency", "GLD", "USD", "VHT"];
    for from in [
        "",
        " FROM #postings",
        " FROM (SELECT year, currency, account)",
    ] {
        for order_by in [
            "",
            "ORDER BY currency DESC",
            "ORDER BY year DESC",
            "ORDER BY count(*) DESC",
        ] {
            let bql = format!(
                "SELECT year, currency, count(*){from} WHERE account = 'Assets:A' \
                 GROUP BY year, currency {order_by} PIVOT BY year, currency"
            );
            assert_eq!(run(&bql).0, want, "{bql}");
        }
    }
}

#[test]
fn rows_follow_the_order_by_and_are_sorted_by_key_without_one() {
    for from in ["", " FROM #postings"] {
        let select = format!("SELECT year, currency, count(*){from} WHERE account = 'Assets:A'");
        let pivot = "PIVOT BY year, currency";
        let unordered = run(&format!("{select} GROUP BY year, currency {pivot}")).1;
        assert_eq!(row_keys(&unordered), vec!["2024", "2025"], "{from:?}");
        let descending = run(&format!(
            "{select} GROUP BY year, currency ORDER BY year DESC {pivot}"
        ))
        .1;
        assert_eq!(row_keys(&descending), vec!["2025", "2024"], "{from:?}");
    }
}

/// bean-query fails on a NULL among the spread values; here it is a column,
/// first, as ORDER BY sorts NULL.
#[test]
fn a_null_spread_value_is_the_first_column() {
    let (columns, rows) = run("SELECT year, payee, count(*) WHERE account = 'Assets:A' \
         GROUP BY year, payee PIVOT BY year, payee");
    assert_eq!(columns, vec!["year/payee", "NULL", "Cafe", "Shop"]);
    assert_eq!(row_keys(&rows), vec!["2024", "2025"]);
}

/// Amounts sort by currency, then number, as bean-query's do (#2445): USD is
/// written first here and EUR still leads.
#[test]
fn amount_spread_values_sort_by_currency_then_number() {
    let ledger = r#"
2024-01-01 open Assets:A
2024-01-01 open Assets:B

2024-03-01 * "usd"
  Assets:A  5 USD
  Assets:B  -5 USD

2024-03-02 * "eur"
  Assets:A  5 EUR
  Assets:B  -5 EUR
"#;
    let (columns, _) = run_on(
        ledger,
        "SELECT account, units(position) AS u, count(*) GROUP BY account, u PIVOT BY account, u",
    );
    assert_eq!(
        columns,
        vec!["account/u", "-5 EUR", "5 EUR", "-5 USD", "5 USD"]
    );
}

/// Values the ORDER BY comparison cannot order against each other (here a
/// number and strings, from metadata) are ordered by their rendering, not by
/// which came first: the number is written second and still sorts first.
#[test]
fn ties_between_distinct_values_do_not_depend_on_the_data_order() {
    let ledger = r#"
2024-01-01 open Assets:A
2024-01-01 open Assets:B

2024-03-01 * "b"
  Assets:A  1 USD
    key: "b"
  Assets:B

2024-03-02 * "two"
  Assets:A  1 USD
    key: 2
  Assets:B

2024-03-03 * "a"
  Assets:A  1 USD
    key: "a"
  Assets:B
"#;
    let (columns, _) = run_on(
        ledger,
        "SELECT account, meta('key') AS k, count(*) WHERE account = 'Assets:A' \
         GROUP BY account, k PIVOT BY account, k",
    );
    assert_eq!(columns, vec!["account/k", "2", "a", "b"]);
}
