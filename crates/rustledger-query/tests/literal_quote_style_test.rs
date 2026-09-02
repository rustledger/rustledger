//! Regression: a string-literal header echoes the quote the query wrote
//! (#2176).
//!
//! bean-query names such a column by reproducing the literal as typed, quote
//! character included. Measured against beanquery 0.2.0:
//!
//! ```text
//! SELECT 'plain'    ->  'plain'
//! SELECT "dq"       ->  "dq"
//! SELECT "o'clock"  ->  "o'clock"
//! SELECT 'it''s'    ->  'it''s'
//! ```
//!
//! We rendered every literal single-quoted unless it contained a single
//! quote, so `"dq"` headed `'dq'`. `Literal::String` now carries the source
//! quote (`QuotedString`) instead of the header guessing one.
//!
//! The body is reproduced VERBATIM, matching bean-query: `'it''s'` heads
//! `'it''s'`, the doubled quote left as written rather than re-escaped or
//! collapsed. That is consistent with the value semantics pinned in
//! `string_literal_escapes_test.rs`, where `''` stays in the value.

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, NaiveDate, Open, Posting, Transaction};
use rustledger_query::ast::{Expr, Literal, QuoteStyle, QuotedString};
use rustledger_query::{Executor, Value, parse};

fn date(y: i32, m: u32, d: u32) -> NaiveDate {
    rustledger_core::naive_date(y, m, d).unwrap()
}

fn ledger() -> Vec<Directive> {
    vec![
        Directive::Open(Open::new(date(2026, 7, 1), "Assets:Cash")),
        Directive::Open(Open::new(date(2026, 7, 1), "Expenses:X")),
        Directive::Transaction(
            Transaction::new(date(2026, 7, 1), "t")
                .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-1), "USD")))
                .with_synthesized_posting(Posting::new("Expenses:X", Amount::new(dec!(1), "USD"))),
        ),
    ]
}

/// The column NAME the executor reports for `SELECT <expr>`.
fn header(expr: &str) -> String {
    let dirs = ledger();
    let q = parse(&format!("SELECT {expr} LIMIT 1")).expect("parse");
    let mut ex = Executor::new(&dirs);
    ex.execute(&q).expect("execute").columns[0].clone()
}

fn value(expr: &str) -> Value {
    let dirs = ledger();
    let q = parse(&format!("SELECT {expr} LIMIT 1")).expect("parse");
    let mut ex = Executor::new(&dirs);
    ex.execute(&q).expect("execute").rows[0][0].clone()
}

/// Both quote characters, each echoed. The double-quoted case is the one that
/// was wrong; the single-quoted case is included so a fix that simply flipped
/// the default cannot pass.
#[test]
fn a_header_echoes_the_source_quote() {
    assert_eq!(header("'plain'"), "'plain'");
    assert_eq!(header("\"dq\""), "\"dq\"");
}

/// A quote of the OTHER kind inside the body does not change the choice: the
/// source style still wins, and the body is copied through.
#[test]
fn the_body_is_reproduced_verbatim() {
    assert_eq!(header("\"o'clock\""), "\"o'clock\"");
    assert_eq!(header("'say \"hi\"'"), "'say \"hi\"'");
    // `''` continues a single-quoted string and stays in the value, so it
    // stays in the header too -- bean-query prints `'it''s'`.
    assert_eq!(header("'it''s'"), "'it''s'");
    assert_eq!(value("'it''s'"), Value::String("it''s".into()));
}

/// Nested literals are named the same way, since `header_fragment` recurses.
#[test]
fn a_literal_inside_a_call_keeps_its_quote() {
    assert_eq!(header("length('abc')"), "length('abc')");
    assert_eq!(header("length(\"abc\")"), "length(\"abc\")");
}

/// Quote style is source provenance, NOT part of the value. Two literals
/// spelling the same text must compare and hash alike, or query equality
/// would depend on typing style.
#[test]
fn quote_style_does_not_affect_equality() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let single = QuotedString::parsed("x".to_string(), QuoteStyle::Single);
    let double = QuotedString::parsed("x".to_string(), QuoteStyle::Double);
    let none = QuotedString::synthetic("x");

    assert_eq!(single, double, "'x' and \"x\" are the same string");
    assert_eq!(single, none, "and so is one built in code");
    assert_eq!(
        Literal::String(single.clone()),
        Literal::String(double.clone()),
        "the enum around them agrees",
    );

    let hash = |q: &QuotedString| {
        let mut h = DefaultHasher::new();
        q.hash(&mut h);
        h.finish()
    };
    assert_eq!(
        hash(&single),
        hash(&double),
        "Hash must agree with Eq, or a HashMap keyed on literals splits",
    );

    // The styles are still distinguishable where it matters.
    assert_eq!(single.quote(), Some(QuoteStyle::Single));
    assert_eq!(double.quote(), Some(QuoteStyle::Double));
    assert_eq!(
        none.quote(),
        None,
        "a synthetic literal has no source style"
    );
}

/// `Display` round-trips a parsed literal as written, so re-parsing its output
/// yields the same value. Double quotes remain the fallback when there is no
/// source style.
#[test]
fn display_round_trips_a_parsed_literal() {
    for src in [
        "'plain'",
        "\"dq\"",
        "\"o'clock\"",
        "'say \"hi\"'",
        "'it''s'",
    ] {
        let q = parse(&format!("SELECT {src} LIMIT 1")).expect("parse");
        let rendered = format!("{}", first_target(&q));
        assert_eq!(
            rendered, src,
            "Display must reproduce the literal as written",
        );
        assert_eq!(
            value(&rendered),
            value(src),
            "and re-parsing it must yield the same value",
        );
    }

    assert_eq!(
        Literal::String(QuotedString::synthetic("test")).to_string(),
        "\"test\"",
        "no source style falls back to double quotes",
    );
}

/// The first target expression of a parsed `SELECT`.
fn first_target(q: &rustledger_query::ast::Query) -> &Expr {
    match q {
        rustledger_query::ast::Query::Select(s) => &s.targets[0].expr,
        _ => panic!("expected a SELECT"),
    }
}
