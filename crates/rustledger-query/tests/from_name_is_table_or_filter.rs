//! A bare name after FROM is a table when one has that name, else the FROM
//! filter expression, as beanquery reads it (#2435).
//!
//! The parser cannot tell the two apart. It read `FROM payee` as a table and
//! failed ("table 'payee' does not exist"), but `FROM payee;` and a
//! subquery's `FROM payee)` as filters, only because it could not parse a
//! table name before `;` or `)`. Now every spelling is a table if one exists
//! and a filter otherwise.

use rustledger_core::Directive;
use rustledger_query::{Executor, Value, parse};

/// Two of three transactions have a payee: four postings pass `FROM payee`.
const LEDGER: &str = r#"
2024-01-01 open Assets:A
2024-01-01 open Assets:B

2024-01-02 * "Shop" "with a payee"
  Assets:A  1 USD
  Assets:B

2024-01-03 * "no payee"
  Assets:A  2 USD
  Assets:B

2024-01-04 * "Cafe" "with a payee"
  Assets:A  3 USD
  Assets:B
"#;

fn directives() -> Vec<Directive> {
    rustledger_parser::parse(LEDGER)
        .directives
        .iter()
        .map(|d| (**d).clone())
        .collect()
}

fn count(bql: &str) -> Result<i64, String> {
    let directives = directives();
    let query = parse(bql).map_err(|e| format!("{bql}: {e:?}"))?;
    let result = Executor::new(&directives)
        .execute(&query)
        .map_err(|e| e.to_string())?;
    match result.rows.first().and_then(|r| r.first()) {
        Some(Value::Integer(n)) => Ok(*n),
        other => panic!("{bql}: expected a count, got {other:?}"),
    }
}

#[test]
fn a_bare_column_name_is_the_from_filter_in_every_spelling() {
    for bql in [
        "SELECT count(*) FROM payee",
        "SELECT count(*) FROM payee;",
        "SELECT count(*) FROM (SELECT account FROM payee)",
        "SELECT count(*) FROM (SELECT account FROM payee );",
    ] {
        assert_eq!(count(bql), Ok(4), "{bql}");
    }
    assert_eq!(count("SELECT count(*)"), Ok(6));
}

#[test]
fn a_name_that_is_neither_is_a_missing_table() {
    for bql in [
        "SELECT count(*) FROM nosuchthing",
        "SELECT count(*) FROM nosuchthing;",
        "SELECT count(*) FROM (SELECT account FROM nosuchthing)",
    ] {
        let err = count(bql).expect_err("no table and no column has that name");
        assert!(
            err.contains("table 'nosuchthing' does not exist"),
            "{bql}: {err}"
        );
    }
}

/// A table of that name wins, and a `#` name is only ever a table.
#[test]
fn a_table_of_that_name_wins() {
    assert_eq!(
        count("SELECT count(*) FROM (SELECT account FROM #postings)"),
        Ok(6)
    );
    assert_eq!(
        count("SELECT count(*) FROM (SELECT * FROM transactions)"),
        Ok(3)
    );
    let err = count("SELECT count(*) FROM #payee").expect_err("no such system table");
    assert!(err.contains("table '#payee' does not exist"), "{err}");
}

/// Only the FROM name itself missing makes it a missing table: another
/// unknown column in the query is reported as that column.
#[test]
fn another_unknown_column_keeps_its_own_error() {
    let directives = directives();
    let query = parse("SELECT nosuchcol FROM payee").expect("parses");
    let err = Executor::new(&directives)
        .execute(&query)
        .expect_err("nosuchcol is no column")
        .to_string();
    assert!(err.contains("nosuchcol"), "{err}");
    assert!(!err.contains("table 'payee'"), "{err}");
}
