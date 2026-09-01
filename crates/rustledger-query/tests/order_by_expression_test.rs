//! `ORDER BY <expression>` finds its target (#2177).
//!
//! The header and the lookup used to spell the same expression two different
//! ways. `ast::header_name` produces `number + 1`; `Display` parenthesizes and
//! produces `(number + 1)`, and `sort_results` looked up by `Display`. So a
//! query bean-query answers failed here:
//!
//! ```text
//! $ bean-query -f csv f.bean "SELECT number + 1 FROM #postings ORDER BY number + 1"
//! number + 1
//! -9.00
//! ...
//!
//! $ rledger query f.bean "SELECT number + 1 FROM #postings ORDER BY number + 1"
//! error: ORDER BY expression not found in SELECT: (number + 1)
//! ```
//!
//! `find_column`'s case-insensitive fallback cannot bridge it: the two
//! spellings differ by punctuation, not case. Before #2175 the header was
//! `col0`, so the lookup missed for a different reason -- the query has never
//! worked.

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, NaiveDate, Open, Posting, Transaction};
use rustledger_query::{Executor, Value, parse};

fn date(year: i32, month: u32, day: u32) -> NaiveDate {
    rustledger_core::naive_date(year, month, day).unwrap()
}

fn fixture() -> Vec<Directive> {
    vec![
        Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
        Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 2), "one")
                .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(10), "USD")))
                .with_synthesized_posting(Posting::new(
                    "Equity:Opening",
                    Amount::new(dec!(-10), "USD"),
                )),
        ),
        Directive::Transaction(
            Transaction::new(date(2024, 1, 3), "two")
                .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-3), "USD")))
                .with_synthesized_posting(Posting::new(
                    "Equity:Opening",
                    Amount::new(dec!(3), "USD"),
                )),
        ),
    ]
}

fn run(query_str: &str) -> Result<(Vec<String>, Vec<Vec<Value>>), String> {
    let dirs = fixture();
    let query = parse(query_str).expect("query should parse");
    let mut executor = Executor::new(&dirs);
    executor
        .execute(&query)
        .map(|r| (r.columns, r.rows))
        .map_err(|e| e.to_string())
}

#[test]
fn order_by_a_binary_expression_finds_its_column() {
    let (columns, rows) = run("SELECT number + 1 ORDER BY number + 1")
        .expect("ORDER BY on the selected expression must resolve");
    assert_eq!(columns, vec!["number + 1".to_string()]);
    let got: Vec<String> = rows
        .iter()
        .map(|r| match &r[0] {
            Value::Number(n) => n.to_string(),
            other => panic!("expected a number, got {other:?}"),
        })
        .collect();
    assert_eq!(
        got,
        vec!["-9", "-2", "4", "11"],
        "rows must come back sorted by the expression",
    );
}

/// The comparison target is a boolean here, which the sort comparator already
/// handled -- this is the lookup, not the ordering.
#[test]
fn order_by_a_comparison_expression_finds_its_column() {
    let (_, rows) = run("SELECT number > 0 ORDER BY number > 0")
        .expect("ORDER BY on a comparison must resolve");
    let got: Vec<bool> = rows
        .iter()
        .map(|r| match &r[0] {
            Value::Boolean(b) => *b,
            other => panic!("expected a boolean, got {other:?}"),
        })
        .collect();
    assert_eq!(got, vec![false, false, true, true], "false sorts first");
}

/// The hidden-column path: the SELECT target is aliased, so the ORDER BY
/// expression is not reachable by name and a synthetic column is appended.
/// That column is named by the same function the lookup uses -- naming it one
/// way and looking it up the other is exactly the bug, moved.
#[test]
fn order_by_an_expression_not_in_select_uses_a_hidden_column() {
    let (columns, rows) = run("SELECT account AS a ORDER BY number + 1")
        .expect("ORDER BY on an unselected expression must resolve");
    assert_eq!(
        columns,
        vec!["a".to_string()],
        "the hidden sort column must not surface in the output",
    );
    assert_eq!(rows.len(), 4);
}

/// A FUNCTION whose argument is compound. The `Expr::Function` arm had its own
/// `Display` lookup, so this stayed broken after the binary-expression arm was
/// fixed: `abs(number + 1)` looked for `abs((number + 1))`.
///
/// `abs(number)` resolves either way, which is why the gap hid -- an argument
/// has to be compound before the two spellings part company. Flagged in review
/// on #2177.
#[test]
fn order_by_a_function_over_an_expression_finds_its_column() {
    let (columns, rows) = run("SELECT abs(number + 1) ORDER BY abs(number + 1)")
        .expect("ORDER BY on a function over an expression must resolve");
    assert_eq!(columns, vec!["abs(number + 1)".to_string()]);
    let got: Vec<String> = rows
        .iter()
        .map(|r| match &r[0] {
            Value::Number(n) => n.to_string(),
            other => panic!("expected a number, got {other:?}"),
        })
        .collect();
    // bean-query answers 2.00, 4.00, 9.00, 11.00 for the same query.
    assert_eq!(got, vec!["2", "4", "9", "11"]);
}

/// The simple-argument form, which resolved before this change too. Here so a
/// regression that breaks it is distinguishable from one that only breaks the
/// compound case above.
#[test]
fn order_by_a_function_over_a_bare_column_still_resolves() {
    let (columns, _) =
        run("SELECT abs(number) ORDER BY abs(number)").expect("ORDER BY abs(number)");
    assert_eq!(columns, vec!["abs(number)".to_string()]);
}

/// Ordinals resolve by position and must not be turned into a hidden constant
/// column; regression cover for the path this change walks past.
#[test]
fn order_by_ordinal_still_resolves_by_position() {
    let (_, rows) = run("SELECT account, number ORDER BY 2").expect("ORDER BY 2");
    let got: Vec<String> = rows
        .iter()
        .map(|r| match &r[1] {
            Value::Number(n) => n.to_string(),
            other => panic!("expected a number, got {other:?}"),
        })
        .collect();
    assert_eq!(got, vec!["-10", "-3", "3", "10"]);
}
