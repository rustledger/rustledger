//! ORDER BY an expression the query does not select, over every source
//! (#2436).
//!
//! The default FROM evaluates such an expression as a hidden trailing column,
//! sorts on it, and strips it. A subquery never did, so `SELECT account FROM
//! (SELECT date, account) ORDER BY date` failed with `column 'date' not
//! found`; and an aggregate over a table or a subquery could not sort by an
//! aggregate it did not select (`GROUP BY account ORDER BY count(*)`). All
//! three are what beanquery answers.

use rustledger_core::Directive;
use rustledger_query::{Executor, Value, parse};

const LEDGER: &str = r#"
2024-01-01 open Assets:A
2024-01-01 open Assets:B
2024-01-01 open Assets:C

2024-01-02 * "first"
  Assets:B  1 USD
  Assets:A

2024-01-03 * "second"
  Assets:B  1 USD
  Assets:A

2024-01-05 * "third"
  Assets:C  1 USD
  Assets:A
"#;

fn run(bql: &str) -> (Vec<String>, Vec<Vec<Value>>) {
    let directives: Vec<Directive> = rustledger_parser::parse(LEDGER)
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

fn strings(rows: &[Vec<Value>]) -> Vec<String> {
    rows.iter()
        .map(|r| match &r[0] {
            Value::String(s) => s.clone(),
            other => panic!("expected a string, got {other:?}"),
        })
        .collect()
}

/// A column the outer query leaves out still sorts it, and is not returned.
#[test]
fn a_subquery_column_the_outer_query_leaves_out_sorts_it() {
    for (bql, want) in [
        (
            "SELECT narration FROM (SELECT date, narration) ORDER BY date DESC",
            vec!["third", "third", "second", "second", "first", "first"],
        ),
        (
            "SELECT DISTINCT narration FROM (SELECT date, narration) ORDER BY date",
            vec!["first", "second", "third"],
        ),
        // DISTINCT over the visible column only: `Assets:A` is on every
        // date, and a hidden `date` must not split it into three rows. Each
        // keeps the first row seen, so it sorts by that row's date.
        (
            "SELECT DISTINCT account FROM (SELECT date, account) ORDER BY date",
            vec!["Assets:B", "Assets:A", "Assets:C"],
        ),
        (
            "SELECT narration FROM (SELECT date, narration FROM (SELECT date, narration)) \
             ORDER BY date LIMIT 2",
            vec!["first", "first"],
        ),
    ] {
        let (columns, rows) = run(bql);
        // Only the selected column comes back, never the hidden sort key.
        let selected = bql
            .trim_start_matches("SELECT ")
            .trim_start_matches("DISTINCT ")
            .split_whitespace()
            .next()
            .expect("a target");
        assert_eq!(columns, vec![selected], "{bql}");
        assert_eq!(strings(&rows), want, "{bql}");
    }
}

/// An aggregate the query does not select sorts the groups, over every
/// source alike.
#[test]
fn an_unselected_aggregate_sorts_the_groups_over_every_source() {
    let want = vec!["Assets:A", "Assets:B", "Assets:C"];
    for from in ["", " FROM #postings", " FROM (SELECT account)"] {
        let bql = format!("SELECT account{from} GROUP BY account ORDER BY count(*) DESC");
        let (columns, rows) = run(&bql);
        assert_eq!(columns, vec!["account"], "{bql}");
        assert_eq!(strings(&rows), want, "{bql}");
    }
}

/// A selected ORDER BY still sorts by its own column, positionally too.
#[test]
fn a_selected_or_positional_order_by_is_unchanged() {
    for bql in [
        "SELECT account FROM (SELECT date, account) ORDER BY account DESC LIMIT 1",
        "SELECT account FROM (SELECT date, account) ORDER BY 1 DESC LIMIT 1",
    ] {
        assert_eq!(strings(&run(bql).1), vec!["Assets:C"], "{bql}");
    }
}
