//! BQL literals, signs, syntax-error positions (#2830) and the postings
//! wildcard (#2829), each against beanquery 0.2.0 / beancount 3.2.3.

use rust_decimal::Decimal;
use rustledger_core::Directive;
use rustledger_query::{Executor, Value, parse};
use std::str::FromStr;

const LEDGER: &str = "
2024-01-01 open Assets:Bank
2024-01-01 open Equity:Opening
2024-01-02 *
  Assets:Bank     10 USD
  Equity:Opening
2024-01-03 * \"Acme\" \"second\"
  Assets:Bank      5 USD
  Equity:Opening
";

fn directives() -> Vec<Directive> {
    rustledger_parser::parse(LEDGER)
        .directives
        .iter()
        .map(|d| (**d).clone())
        .collect()
}

fn run(bql: &str) -> (Vec<String>, Vec<Vec<Value>>) {
    let directives = directives();
    let mut executor = Executor::new(&directives);
    let result = executor
        .execute(&parse(bql).unwrap_or_else(|e| panic!("{bql:?}: {e}")))
        .unwrap_or_else(|e| panic!("{bql:?}: {e}"));
    (result.columns, result.rows)
}

/// The one value `SELECT <expr> LIMIT 1` gives, as a decimal string
/// normalized to drop trailing zeros (an integer and a decimal of the same
/// value read alike).
fn scalar(expr: &str) -> String {
    let (_, rows) = run(&format!("SELECT {expr} LIMIT 1"));
    match &rows[0][0] {
        Value::Integer(i) => i.to_string(),
        Value::Number(n) => n.normalize().to_string(),
        other => panic!("{expr}: expected a number, got {other:?}"),
    }
}

/// A character the lexer cannot start an expression with is reported where
/// it is, naming it. Before, every one of these read `syntax error at
/// position 0: unexpected token 'SELECT'`.
#[test]
fn test_parse_reports_a_bad_leading_character_where_it_is() {
    for (query, position, token) in [
        ("SELECT `payee` FROM postings", 7, '`'),
        ("SELECT [payee] FROM postings", 7, '['),
        ("SELECT @payee FROM postings", 7, '@'),
        ("SELECT $payee FROM postings", 7, '$'),
        ("SELECT ?payee FROM postings", 7, '?'),
        ("  SELECT `x`", 9, '`'),
        ("JOURNAL `x`", 8, '`'),
        ("BALANCES WHERE `x`", 15, '`'),
        ("PRINT FROM `x`", 11, '`'),
    ] {
        let err = parse(query).expect_err(query);
        assert_eq!(err.position, position, "{query:?}: {err}");
        assert!(
            err.to_string().contains(&format!("found '{token}'")),
            "{query:?}: {err}"
        );
    }
    // A word that names no statement is still reported at the start.
    let err = parse("FETCH x").expect_err("FETCH");
    assert_eq!(err.position, 0);
    assert!(err.to_string().contains("FETCH"), "{err}");
}

/// A dot may start or end a decimal, as in beanquery: `.5` is 0.5, `5.` is 5.
#[test]
fn test_parse_reads_a_decimal_with_a_leading_or_trailing_dot() {
    assert_eq!(scalar(".5"), "0.5");
    assert_eq!(scalar("5."), "5");
    assert_eq!(scalar("-.5"), "-0.5");
    assert_eq!(scalar("1 + .25"), "1.25");
    assert_eq!(scalar("5. * 2"), "10");
    // A lone dot is not a number.
    assert!(parse("SELECT . LIMIT 1").is_err());
}

/// Unary minus stacks, as in beanquery: `---6` is -6, `-+6` is -6, `-- 6` is 6.
/// A `+` takes a bare atom only (`uplus: '+' atom`), as there.
#[test]
fn test_parse_stacks_unary_signs() {
    for (expr, value) in [
        ("--6", "6"),
        ("-- 6", "6"),
        ("---6", "-6"),
        ("-+6", "-6"),
        ("+6", "6"),
        ("+ 6", "6"),
        ("+abs(-2)", "2"),
        ("3--2", "5"),
        ("3 - -2", "5"),
        ("3+-2", "1"),
        ("-(1+2)", "-3"),
    ] {
        assert_eq!(scalar(expr), value, "{expr}");
    }
    // bean-query refuses each of these with a syntax error.
    for expr in ["++6", "+-6", "+-+6", "+(1)", "-+(1)", "+date.year"] {
        let query = format!("SELECT {expr} LIMIT 1");
        assert!(parse(&query).is_err(), "{query}");
    }
}

/// A run of signs counts toward the same nesting bound as the brackets around
/// it, so neither alone nor together can they nest an expression deep enough
/// to threaten the stack: past the bound it is a parse error, not a crash.
#[test]
fn test_parse_refuses_a_run_of_signs_past_the_nesting_bound() {
    let long = format!("SELECT {}6 LIMIT 1", "-".repeat(10_000));
    assert!(parse(&long).is_err());
    assert_eq!(scalar(&format!("{}6", "-".repeat(64))), "6");
    // Signs and brackets multiply: 20 brackets each behind 128 signs.
    let mixed = format!(
        "SELECT {}1{} LIMIT 1",
        format!("{}(", "-".repeat(128)).repeat(20),
        ")".repeat(20)
    );
    assert!(parse(&mixed).is_err());
    // Within the bound together, they still parse.
    assert_eq!(
        scalar(&format!("{}1{}", "-(".repeat(60), ")".repeat(60))),
        "1"
    );
}

/// A trailing `; text` stays an error, deliberately (#2403): beanquery's
/// end-of-input comment drops it without a word, so `SELECT 1;2` runs
/// `SELECT 1`. The position names the text after the `;`.
#[test]
fn test_parse_still_refuses_text_after_a_semicolon() {
    let err = parse("SELECT 2 LIMIT 1; garbage").expect_err("trailing text");
    assert_eq!(err.position, 18, "{err}");
    assert!(parse("SELECT 2 LIMIT 1;").is_ok());
}

/// `SELECT *` over the postings is bean-query's `PostingsTable.wildcard_columns`
/// in every form: the default FROM, `FROM #postings`, and a subquery over
/// either. Before, the default gave `account` too and `#postings` gave all 31
/// of its visible columns.
#[test]
fn test_select_star_is_the_postings_wildcard_in_every_form() {
    let five = ["date", "flag", "payee", "narration", "position"];
    for query in [
        "SELECT * LIMIT 1",
        "SELECT * FROM #postings LIMIT 1",
        "SELECT * FROM postings LIMIT 1",
        "SELECT * FROM (SELECT * FROM #postings) LIMIT 1",
        "SELECT * FROM (SELECT *) LIMIT 1",
    ] {
        let (columns, rows) = run(query);
        assert_eq!(columns, five, "{query}");
        assert_eq!(rows[0].len(), 5, "{query}");
        assert!(
            matches!(&rows[0][4], Value::Position(p) if p.units.number == Decimal::from_str("10").unwrap()),
            "{query}: {:?}",
            rows[0][4]
        );
    }
    // Every other column is still there by name.
    let (columns, rows) = run("SELECT account, balance, meta FROM #postings LIMIT 1");
    assert_eq!(columns, ["account", "balance", "meta"]);
    assert_eq!(rows[0][0], Value::String("Assets:Bank".into()));
    // A subquery that names its columns keeps them.
    let (columns, _) = run("SELECT * FROM (SELECT account, position FROM #postings) LIMIT 1");
    assert_eq!(columns, ["account", "position"]);
    // A table created from the wildcard holds the same five.
    let directives = directives();
    let mut executor = Executor::new(&directives);
    executor
        .execute(&parse("CREATE TABLE t AS SELECT * FROM #postings").unwrap())
        .unwrap();
    let result = executor
        .execute(&parse("SELECT * FROM t").unwrap())
        .unwrap();
    assert_eq!(result.columns, five);
}

/// A bracket or quote left open is named at the end, where its closer is
/// missing, rather than as the offending character at its opener.
#[test]
fn test_parse_names_an_unclosed_bracket_or_quote_at_the_end() {
    for (query, message) in [
        ("SELECT (1", "expected ')' to close the '(' at position 7"),
        ("SELECT 'abc", "expected ''' to close the ''' at position 7"),
        (
            "SELECT \"abc",
            "expected '\"' to close the '\"' at position 7",
        ),
    ] {
        let err = parse(query).expect_err(query);
        assert_eq!(err.position, query.len(), "{query:?}: {err}");
        assert!(err.to_string().contains(message), "{query:?}: {err}");
    }
}
