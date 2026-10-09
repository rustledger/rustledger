//! `weight`, `cost` and `sum` of a posting column read from a table made by
//! `CREATE TABLE ... AS SELECT` (or filled by `INSERT ... SELECT`) agree with
//! the query written without it (#2441).
//!
//! All three need the posting: `weight` ranks a price second, and a `{{T}}`
//! cost carries its total, neither of which a `Position` value holds. A
//! stored table's rows are values, so `weight(position)` of
//! `10 EUR @ 1.10 USD` gave `10 EUR` where the default FROM gives
//! `11.00 USD`, and a `{{500 USD}}` lot weighed and cost 500.00…01. The table
//! now keeps them beside the posting column, as `#postings` (#2429) and a
//! subquery (#2432) do.

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

/// Run `statements` in order on ONE executor, and return the last result.
fn run(
    directives: &[Directive],
    statements: &[&str],
) -> Result<(Vec<String>, Vec<Vec<Value>>), String> {
    let mut executor = Executor::new(directives);
    let mut last = None;
    for bql in statements {
        let query = parse(bql).map_err(|e| format!("{bql}: {e:?}"))?;
        last = Some(executor.execute(&query).map_err(|e| e.to_string())?);
    }
    let result = last.expect("at least one statement");
    Ok((result.columns, result.rows))
}

fn rows(directives: &[Directive], statements: &[&str]) -> Vec<Vec<Value>> {
    run(directives, statements)
        .unwrap_or_else(|e| panic!("{statements:?}: {e}"))
        .1
}

fn amount(value: &Value) -> String {
    match value {
        Value::Amount(a) => a.to_string(),
        other => panic!("expected an amount, got {other:?}"),
    }
}

/// The issue's table: the priced posting weighs 11.00 USD, and the `{{500}}`
/// lot weighs and costs exactly 500 USD.
#[test]
fn the_issue_example() {
    let directives = booked(LEDGER);
    let got = rows(
        &directives,
        &[
            "CREATE TABLE t AS SELECT account, position WHERE account != 'Assets:C'",
            "SELECT account, weight(position), cost(position) FROM t \
             WHERE account = 'Assets:E' OR account = 'Assets:B' ORDER BY account",
        ],
    );
    let got: Vec<(String, String)> = got.iter().map(|r| (amount(&r[1]), amount(&r[2]))).collect();
    assert_eq!(
        got,
        [
            ("500 USD".to_string(), "500 USD".to_string()),
            ("11.00 USD".to_string(), "10 EUR".to_string()),
            ("12.00 USD".to_string(), "10 EUR".to_string()),
        ]
    );
}

/// Every way a table can take the posting column: named, from `SELECT *`,
/// renamed, from `#postings`, from a subquery, and from another such table.
#[test]
fn a_created_table_passes_the_posting_through() {
    let directives = booked(LEDGER);
    let direct = rows(
        &directives,
        &["SELECT date, account, weight(position), cost(position) ORDER BY date, account"],
    );
    assert_eq!(direct.len(), 8);
    let read =
        "SELECT date, account, weight(position), cost(position) FROM t ORDER BY date, account";
    let read_p = "SELECT date, account, weight(p), cost(p) FROM t ORDER BY date, account";
    for statements in [
        &["CREATE TABLE t AS SELECT date, account, position", read][..],
        &["CREATE TABLE t AS SELECT *", read],
        &[
            "CREATE TABLE t AS SELECT date, account, position AS p",
            read_p,
        ],
        &[
            "CREATE TABLE t AS SELECT date, account, position FROM #postings",
            read,
        ],
        &["CREATE TABLE t AS SELECT * FROM #postings", read],
        &[
            "CREATE TABLE t AS SELECT date, account, position FROM (SELECT date, account, position)",
            read,
        ],
        &[
            "CREATE TABLE t AS SELECT date, account, p FROM (SELECT date, account, position AS p)",
            read_p,
        ],
        &[
            "CREATE TABLE t0 AS SELECT date, account, position AS p",
            "CREATE TABLE t AS SELECT date, account, p FROM t0",
            read_p,
        ],
        &[
            "CREATE TABLE t0 AS SELECT date, account, position",
            "CREATE TABLE t AS SELECT date, account, position AS p FROM t0",
            read_p,
        ],
        // A subquery over the table reads it too.
        &[
            "CREATE TABLE t0 AS SELECT date, account, position",
            "SELECT date, account, weight(position), cost(position) \
             FROM (SELECT date, account, position FROM t0) ORDER BY date, account",
        ],
    ] {
        assert_eq!(rows(&directives, statements), direct, "{statements:?}");
    }
}

/// And in the reading query's other clauses and aggregates: `sum(position)`
/// records each lot's exact total, so the held `{{500 USD}}` lot costs 500.
#[test]
fn every_clause_and_aggregate_reads_the_posting() {
    let directives = booked(LEDGER);
    let select = "SELECT account, sum(weight(position)), cost(sum(position))";
    let tail = "WHERE number(weight(position)) > 11 GROUP BY account ORDER BY account";
    let direct = rows(&directives, &[&format!("{select} {tail}")]);
    let through = rows(
        &directives,
        &[
            "CREATE TABLE t AS SELECT account, position",
            &format!("{select} FROM t {tail}"),
        ],
    );
    assert_eq!(through, direct);

    let tail = "GROUP BY account ORDER BY account";
    let direct = rows(
        &directives,
        &[&format!("SELECT account, cost(sum(position)) {tail}")],
    );
    let through = rows(
        &directives,
        &[
            "CREATE TABLE t AS SELECT account, position",
            &format!("SELECT account, cost(sum(position)) FROM t {tail}"),
        ],
    );
    assert_eq!(through, direct);
    let held = through
        .iter()
        .find(|r| r[0] == Value::String("Assets:B".into()))
        .expect("Assets:B has a row");
    match &held[1] {
        Value::Inventory(inv) => assert_eq!(inv.to_string(), "500 USD"),
        other => panic!("expected an inventory, got {other:?}"),
    }
}

/// `INSERT ... SELECT` keeps them for the rows it adds, by position or by
/// named column, or the added rows would answer from the value.
#[test]
fn insert_select_keeps_them_for_the_rows_it_adds() {
    let directives = booked(LEDGER);
    let direct = rows(
        &directives,
        &["SELECT date, account, weight(position), cost(position) ORDER BY date, account"],
    );
    let read =
        "SELECT date, account, weight(position), cost(position) FROM t ORDER BY date, account";
    for insert in [
        "INSERT INTO t SELECT date, account, position WHERE date >= 2024-01-03",
        "INSERT INTO t SELECT date, account, position AS q WHERE date >= 2024-01-03",
        "INSERT INTO t (date, account, position) \
         SELECT date, account, position WHERE date >= 2024-01-03",
        "INSERT INTO t (account, date, position) \
         SELECT account, date, position FROM #postings WHERE date >= 2024-01-03",
    ] {
        let got = rows(
            &directives,
            &[
                "CREATE TABLE t AS SELECT date, account, position WHERE date < 2024-01-03",
                insert,
                read,
            ],
        );
        assert_eq!(got, direct, "{insert}");
    }
}

/// A row with no posting behind it takes the value path: one inserted by
/// `VALUES`, one whose posting column an `INSERT` leaves out, and one taken
/// from a column that is no posting's position.
#[test]
fn a_row_without_a_posting_takes_the_value_path() {
    let directives = booked(LEDGER);
    let create = "CREATE TABLE t AS SELECT account, position WHERE account = 'Assets:E'";

    // `weight` of an inserted NULL is NULL, as the value path gives, not a
    // stale or default hidden value.
    let got = rows(
        &directives,
        &[
            create,
            "INSERT INTO t (account) VALUES ('Assets:X')",
            "SELECT weight(position), cost(position) FROM t WHERE account = 'Assets:X'",
        ],
    );
    assert_eq!(got, vec![vec![Value::Null, Value::Null]]);

    // A copied position with no posting behind it weighs its units.
    let got = rows(
        &directives,
        &[
            create,
            "INSERT INTO t SELECT account, units(position) WHERE account = 'Assets:B'",
            "SELECT weight(position) FROM t WHERE account = 'Assets:B'",
        ],
    );
    assert_eq!(amount(&got[0][0]), "3 X");

    // VALUES needs the visible columns only.
    let got = rows(
        &directives,
        &[
            create,
            "INSERT INTO t VALUES ('Assets:Y', NULL)",
            "SELECT count(*) FROM t",
        ],
    );
    assert_eq!(got, vec![vec![Value::Integer(3)]]);
}

/// A column the table computes is a value, even named `position`, and a
/// grouped or DISTINCT table has no one posting per row.
#[test]
fn a_computed_or_grouped_column_keeps_the_value_path() {
    let directives = booked(LEDGER);
    let got = rows(
        &directives,
        &[
            "CREATE TABLE t AS SELECT account, units(position) AS position WHERE account = 'Assets:B'",
            "SELECT weight(position) FROM t",
        ],
    );
    assert_eq!(amount(&got[0][0]), "3 X");
    for create in [
        "CREATE TABLE t AS SELECT DISTINCT account, position WHERE account = 'Assets:E'",
        "CREATE TABLE t AS SELECT account, position WHERE account = 'Assets:E' \
         GROUP BY account, position",
    ] {
        let got = rows(&directives, &[create, "SELECT weight(position) FROM t"]);
        assert_eq!(got.len(), 1, "{create}: {got:?}");
        assert_eq!(amount(&got[0][0]), "10 EUR", "{create}");
    }
}

/// The kept values stay out of `SELECT *` and do not count as columns for
/// `INSERT`.
#[test]
fn select_star_does_not_show_them() {
    let directives = booked(LEDGER);
    let (columns, rows) = run(
        &directives,
        &[
            "CREATE TABLE t AS SELECT account, position",
            "SELECT * FROM t",
        ],
    )
    .expect("runs");
    assert_eq!(columns, vec!["account", "position"]);
    assert!(rows.iter().all(|r| r.len() == 2), "{rows:?}");

    let err = run(
        &directives,
        &[
            "CREATE TABLE t AS SELECT account, position",
            "INSERT INTO t SELECT account",
        ],
    )
    .expect_err("one column for two");
    assert!(
        err.contains("table has 2 columns but SELECT returns 1 columns"),
        "{err}"
    );
}

/// The table computes a cost for every row, so an overflowing one fails only
/// a query that reads it, as on the default FROM.
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
    let create = "CREATE TABLE t AS SELECT account, position";
    let filtered = run(
        &directives,
        &[
            create,
            "SELECT cost(position) FROM t WHERE account = 'Assets:C'",
        ],
    )
    .expect("the overflowing row is filtered out");
    assert_eq!(filtered.1.len(), 1);
    let err =
        run(&directives, &[create, "SELECT cost(position) FROM t"]).expect_err("the lot overflows");
    assert!(err.contains("exceeds the representable range"), "{err}");
}

/// `SELECT *`'s `position` is the position column, cost included, as in
/// bean-query: it gave the units alone, so a table or subquery built from
/// `SELECT *` summed `4 Z` where the posting column sums `4 Z {12.50 USD}`.
#[test]
fn select_star_position_is_the_position_column() {
    let directives = booked(LEDGER);
    let star: Vec<Value> = rows(&directives, &["SELECT * ORDER BY date, account"])
        .into_iter()
        .map(|r| r[5].clone())
        .collect();
    let position: Vec<Value> = rows(&directives, &["SELECT position ORDER BY date, account"])
        .into_iter()
        .map(|r| r[0].clone())
        .collect();
    assert_eq!(star, position);

    let tail = "GROUP BY account ORDER BY account";
    let direct = rows(
        &directives,
        &[&format!(
            "SELECT account, sum(position), cost(sum(position)) {tail}"
        )],
    );
    for statements in [
        &[
            "CREATE TABLE t AS SELECT *",
            &format!("SELECT account, sum(position), cost(sum(position)) FROM t {tail}"),
        ][..],
        &[&format!(
            "SELECT account, sum(position), cost(sum(position)) FROM (SELECT *) {tail}"
        )],
    ] {
        assert_eq!(rows(&directives, statements), direct, "{statements:?}");
    }
}

/// A table made with explicit columns keeps the posting values of the rows
/// `INSERT ... SELECT` adds, as one made by `CREATE TABLE ... AS SELECT`
/// does, and rows inserted before them still take the value path.
#[test]
fn a_table_with_explicit_columns_keeps_them_too() {
    let directives = booked(LEDGER);
    let direct = rows(
        &directives,
        &["SELECT account, weight(position), cost(position) ORDER BY account, date"],
    );
    let got = rows(
        &directives,
        &[
            "CREATE TABLE t (account, position, date)",
            "INSERT INTO t SELECT account, position, date",
            "SELECT account, weight(position), cost(position) FROM t ORDER BY account, date",
        ],
    );
    assert_eq!(got, direct);

    let got = rows(
        &directives,
        &[
            "CREATE TABLE t (account, position)",
            "INSERT INTO t VALUES ('Assets:A', NULL)",
            "INSERT INTO t SELECT account, position WHERE account = 'Assets:E'",
            "SELECT account, weight(position) FROM t ORDER BY account",
        ],
    );
    let weights: Vec<Value> = got.iter().map(|r| r[1].clone()).collect();
    assert_eq!(weights[0], Value::Null, "{got:?}");
    assert_eq!(amount(&weights[1]), "11.00 USD");
    assert_eq!(amount(&weights[2]), "12.00 USD");
}
