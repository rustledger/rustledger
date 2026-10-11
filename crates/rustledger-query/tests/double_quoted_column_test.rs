//! A double-quoted string that names a column is that column (#2596).
//!
//! bean-query 0.2.0's compiler (`_constant`): "Strings delimited by double
//! quotes are treated as column names when they resolve to an existing column
//! in the current table." rledger kept every one a string, so `SELECT
//! "account"` returned the text `account` on every row. Every expectation
//! below was measured against bean-query 0.2.0 on the same ledger:
//!
//! ```text
//! 2023-01-02 * "Shop" "lunch"
//!   Expenses:Food  10 USD
//!   Assets:Cash
//! 2023-01-03 * "Boss" "pay"
//!   Assets:Cash  100 USD
//!   Income:Job
//! ```

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, NaiveDate, Open, Posting, Transaction};
use rustledger_query::{Executor, QueryResult, Value, parse};

fn date(y: i32, m: u32, d: u32) -> NaiveDate {
    rustledger_core::naive_date(y, m, d).unwrap()
}

fn ledger() -> Vec<Directive> {
    vec![
        Directive::Open(Open::new(date(2023, 1, 1), "Assets:Cash")),
        Directive::Open(Open::new(date(2023, 1, 1), "Expenses:Food")),
        Directive::Open(Open::new(date(2023, 1, 1), "Income:Job")),
        Directive::Transaction(
            Transaction::new(date(2023, 1, 2), "lunch")
                .with_flag('*')
                .with_payee("Shop")
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(10), "USD"),
                ))
                .with_synthesized_posting(Posting::new(
                    "Assets:Cash",
                    Amount::new(dec!(-10), "USD"),
                )),
        ),
        Directive::Transaction(
            Transaction::new(date(2023, 1, 3), "pay")
                .with_flag('*')
                .with_payee("Boss")
                .with_synthesized_posting(Posting::new(
                    "Assets:Cash",
                    Amount::new(dec!(100), "USD"),
                ))
                .with_synthesized_posting(Posting::new(
                    "Income:Job",
                    Amount::new(dec!(-100), "USD"),
                )),
        ),
    ]
}

fn run_all(queries: &[&str]) -> QueryResult {
    let directives = ledger();
    let mut executor = Executor::new(&directives);
    let mut last = None;
    for q in queries {
        last = Some(
            executor
                .execute(&parse(q).unwrap_or_else(|e| panic!("{q} parses: {e}")))
                .unwrap_or_else(|e| panic!("{q} executes: {e}")),
        );
    }
    last.expect("at least one query")
}

fn run(query: &str) -> QueryResult {
    run_all(&[query])
}

fn strings(result: &QueryResult, column: usize) -> Vec<String> {
    result
        .rows
        .iter()
        .map(|row| match &row[column] {
            Value::String(s) => s.clone(),
            other => panic!("expected a string, got {other:?}"),
        })
        .collect()
}

const ACCOUNTS: [&str; 4] = ["Expenses:Food", "Assets:Cash", "Assets:Cash", "Income:Job"];

#[test]
fn a_double_quoted_column_name_selects_the_column_and_keeps_its_header() {
    let result = run("SELECT \"account\"");
    assert_eq!(strings(&result, 0), ACCOUNTS);
    // bean-query heads it with the source text, quotes included.
    assert_eq!(result.columns, vec!["\"account\""]);

    // An alias still names it.
    let result = run("SELECT \"account\" AS \"acct\"");
    assert_eq!(strings(&result, 0), ACCOUNTS);
    assert_eq!(result.columns, vec!["acct"]);

    // Beside the bare column, under each one's own header.
    let result = run("SELECT account, \"account\" AS b");
    assert_eq!(strings(&result, 0), strings(&result, 1));
    assert_eq!(result.columns, vec!["account", "b"]);
}

#[test]
fn a_string_no_column_is_named_by_stays_a_string() {
    // Single quotes are always a string.
    assert_eq!(strings(&run("SELECT 'account'"), 0), ["account"; 4]);
    // The match is exact: column names are lower case.
    assert_eq!(strings(&run("SELECT \"ACCOUNT\""), 0), ["ACCOUNT"; 4]);
    assert_eq!(strings(&run("SELECT \"nosuch\""), 0), ["nosuch"; 4]);
    // A regex pattern is no column either.
    let result = run("SELECT account WHERE account = \"Assets:Cash\"");
    assert_eq!(strings(&result, 0), ["Assets:Cash"; 2]);
}

#[test]
fn every_clause_reads_the_column() {
    // WHERE.
    let result = run("SELECT date WHERE \"account\" ~ \"Cash\"");
    assert_eq!(
        result.rows,
        vec![
            vec![Value::Date(date(2023, 1, 2))],
            vec![Value::Date(date(2023, 1, 3))],
        ]
    );

    // GROUP BY, as the column, not a constant that would make one group.
    let result = run("SELECT \"account\", sum(number) GROUP BY \"account\"");
    let mut groups: Vec<(String, Value)> = result
        .rows
        .iter()
        .map(|row| (format!("{:?}", row[0]), row[1].clone()))
        .collect();
    groups.sort_by(|a, b| a.0.cmp(&b.0));
    assert_eq!(groups.len(), 3, "{groups:?}");
    assert_eq!(
        groups.iter().map(|g| g.1.clone()).collect::<Vec<_>>(),
        vec![
            Value::Number(dec!(90)),
            Value::Number(dec!(10)),
            Value::Number(dec!(-100)),
        ]
    );

    // ORDER BY the column...
    let result = run("SELECT account AS a, position ORDER BY \"account\" DESC");
    assert_eq!(
        strings(&result, 0),
        ["Income:Job", "Expenses:Food", "Assets:Cash", "Assets:Cash"]
    );
    // ...but an alias is no column of the table, so `"a"` is a constant and
    // the rows keep their order.
    let result = run("SELECT account AS a, position ORDER BY \"a\" DESC");
    assert_eq!(strings(&result, 0), ACCOUNTS);

    // DISTINCT with ORDER BY.
    let result = run("SELECT DISTINCT \"account\" ORDER BY \"account\"");
    assert_eq!(
        strings(&result, 0),
        ["Assets:Cash", "Expenses:Food", "Income:Job"]
    );

    // Function arguments and operands.
    let result = run("SELECT length(\"account\")");
    assert_eq!(
        result.rows,
        [13, 11, 11, 10].map(|n| vec![Value::Integer(n)]).to_vec()
    );
    assert_eq!(result.columns, vec!["length(\"account\")"]);
    let result = run("SELECT \"number\" + 1");
    assert_eq!(
        result.rows,
        [dec!(11), dec!(-9), dec!(101), dec!(-99)]
            .map(|n| vec![Value::Number(n)])
            .to_vec()
    );
    assert_eq!(result.columns, vec!["\"number\" + 1"]);
    let result = run("SELECT count(*) WHERE \"account\" = account");
    assert_eq!(result.rows, vec![vec![Value::Integer(4)]]);
}

#[test]
fn a_subquery_resolves_against_its_own_output_names() {
    let result = run("SELECT \"x\" FROM (SELECT account AS x)");
    assert_eq!(strings(&result, 0), ACCOUNTS);
    assert_eq!(result.columns, vec!["\"x\""]);

    // A quoted alias (#2577) names a column the outer query can quote back.
    let result = run("SELECT \"2023\" FROM (SELECT account AS \"2023\")");
    assert_eq!(strings(&result, 0), ACCOUNTS);

    // `account` is a posting column, but not one of the subquery's.
    let result = run("SELECT \"account\" FROM (SELECT date AS x)");
    assert_eq!(strings(&result, 0), ["account"; 4]);
}

#[test]
fn a_table_resolves_against_its_columns() {
    let result = run("SELECT \"account\" FROM #accounts");
    assert_eq!(
        strings(&result, 0),
        ["Assets:Cash", "Expenses:Food", "Income:Job"]
    );

    let result = run("SELECT date FROM #postings WHERE \"account\" ~ \"Food\"");
    assert_eq!(result.rows, vec![vec![Value::Date(date(2023, 1, 2))]]);

    let result = run_all(&[
        "CREATE TABLE t AS SELECT account AS name",
        "SELECT \"name\" FROM t",
    ]);
    assert_eq!(strings(&result, 0), ACCOUNTS);
}

#[test]
fn a_double_quoted_pivot_column_is_a_quoted_identifier() {
    // PIVOT BY takes identifiers in bean-query's grammar, so `"account"`
    // there is the `account` target, exactly as the bare name is.
    let quoted =
        run("SELECT account, year, sum(number) GROUP BY account, year PIVOT BY \"account\", year");
    let bare =
        run("SELECT account, year, sum(number) GROUP BY account, year PIVOT BY account, year");
    assert_eq!(quoted.columns, bare.columns);
    assert_eq!(quoted.rows, bare.rows);
    assert_eq!(quoted.rows.len(), 3);
}

#[test]
fn journal_balances_and_print_read_the_column_too() {
    // bean-query compiles these clauses as it does a SELECT's. (`FROM "x"`
    // directly is a syntax error there; parenthesized it is an expression.)
    let quoted = run("JOURNAL 'Assets' FROM (\"narration\" = \"pay\")");
    let bare = run("JOURNAL 'Assets' FROM (narration = \"pay\")");
    assert_eq!(quoted.rows.len(), 1);
    assert_eq!(quoted.rows, bare.rows);

    let quoted = run("BALANCES FROM (\"narration\" = \"pay\")");
    let bare = run("BALANCES FROM (narration = \"pay\")");
    assert_eq!(quoted.rows.len(), 2);
    assert_eq!(quoted.rows, bare.rows);

    let quoted = run("BALANCES WHERE \"account\" ~ \"Cash\"");
    assert_eq!(strings(&quoted, 0), ["Assets:Cash"]);

    let quoted = run("PRINT FROM (\"narration\" = \"pay\")");
    let bare = run("PRINT FROM (narration = \"pay\")");
    assert_eq!(quoted.rows.len(), 1);
    assert_eq!(quoted.rows, bare.rows);
}

#[test]
fn order_by_the_expression_of_a_target_grouped_by_position() {
    // `SELECT "account"` heads its column `"account"`, so `ORDER BY
    // "account"` has to find it by expression, as bean-query does. With
    // `GROUP BY 1` that failed as "column 'account' not found", and so did
    // the same query written with an alias, before any quoting.
    for query in [
        "SELECT \"account\", count(*) GROUP BY 1 ORDER BY \"account\"",
        "SELECT account AS a, count(*) GROUP BY 1 ORDER BY account",
        "SELECT account AS a, count(*) GROUP BY a ORDER BY account",
        "SELECT account AS a, count(*) GROUP BY 1 ORDER BY account DESC",
    ] {
        let result = run(query);
        let mut want = vec!["Assets:Cash", "Expenses:Food", "Income:Job"];
        if query.ends_with("DESC") {
            want.reverse();
        }
        assert_eq!(strings(&result, 0), want, "{query}");
        assert_eq!(result.columns.len(), 2, "{query}: no hidden column shows");
    }
}
