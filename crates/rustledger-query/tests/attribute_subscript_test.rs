//! Regression for #1796: dotted attribute access (`entry.meta`) and
//! string-keyed subscript (`meta['key']`) — upstream bql.ebnf:
//!
//! ```text
//! attribute = operand:primary '.' name:identifier
//! subscript = operand:primary '[' key:string ']'
//! ```
//!
//! Three gaps closed together: the parser had no postfix `.`/`[`, the
//! executor had no attribute/subscript evaluation (though `entry` as a
//! structured object and GETITEM's lookup machinery already existed),
//! and the `#postings`/`FROM postings` table projection lacked the
//! `entry` column entirely.

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, MetaValue, NaiveDate, Open, Posting, Transaction};
use rustledger_query::{Executor, Value, parse};

fn date(y: i32, m: u32, d: u32) -> NaiveDate {
    rustledger_core::naive_date(y, m, d).unwrap()
}

fn ledger() -> Vec<Directive> {
    let mut txn = Transaction::new(date(2026, 7, 1), "coffee")
        .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-1), "USD")))
        .with_synthesized_posting(Posting::new("Expenses:X", Amount::new(dec!(1), "USD")));
    txn.payee = Some("Shop".into());
    txn.meta
        .insert("note".into(), MetaValue::String("hello".into()));
    vec![
        Directive::Open(Open::new(date(2026, 7, 1), "Assets:Cash")),
        Directive::Open(Open::new(date(2026, 7, 1), "Expenses:X")),
        Directive::Transaction(txn),
    ]
}

fn run(query: &str) -> Vec<Vec<Value>> {
    let dirs = ledger();
    let q = parse(query).expect("parse");
    let mut ex = Executor::new(&dirs);
    ex.execute(&q).expect("execute").rows
}

/// The issue's verbatim query shape (mkshp Obsidian plugin's Journal
/// view), through the `FROM postings` table path.
#[test]
fn issue_1796_entry_meta_from_postings() {
    let rows = run("SELECT id, date, entry.meta as entry_meta FROM postings");
    assert_eq!(rows.len(), 2);
    let Value::Object(meta) = &rows[0][2] else {
        panic!(
            "entry.meta must be a structured object, got {:?}",
            rows[0][2]
        );
    };
    assert_eq!(meta.get("note"), Some(&Value::String("hello".into())));
}

/// Attribute access on the default (no-FROM) path, including chaining
/// into a subscript: `entry.meta['note']`.
#[test]
fn attribute_and_subscript_chain() {
    let rows = run("SELECT entry.narration, entry.payee, entry.meta['note'] LIMIT 1");
    assert_eq!(rows[0][0], Value::String("coffee".into()));
    assert_eq!(rows[0][1], Value::String("Shop".into()));
    assert_eq!(rows[0][2], Value::String("hello".into()));
}

/// Subscript on the posting-level `meta` column (a `Value::Metadata`):
/// the transaction's meta is NOT the posting's, so this is NULL here,
/// while GETITEM-equivalent lookup works where posting meta exists.
#[test]
fn subscript_on_posting_meta() {
    let rows = run("SELECT meta['note'] LIMIT 1");
    // `note` lives on the transaction, not the posting — upstream's
    // getitem returns None for a missing key, i.e. NULL, not an error.
    assert_eq!(rows[0][0], Value::Null);
}

/// A missing attribute is NULL. Deliberate divergence nuance (Python
/// Compatibility Policy): upstream errors at COMPILE time for an unknown
/// attribute on a structured type but yields None for a present-but-empty
/// field; rustledger's dynamic `entry` object omits empty fields, making
/// the two cases indistinguishable — NULL reproduces upstream for the
/// common case (absent payee) and is lenient for typos.
#[test]
fn missing_attribute_is_null() {
    let mut dirs = ledger();
    // A transaction without payee: entry.payee must be NULL, not an error.
    if let Directive::Transaction(t) = &mut dirs[2] {
        t.payee = None;
    }
    let q = parse("SELECT entry.payee LIMIT 1").expect("parse");
    let mut ex = Executor::new(&dirs);
    assert_eq!(ex.execute(&q).expect("execute").rows[0][0], Value::Null);

    // Typo'd attribute: also NULL (see divergence note above).
    let rows = run("SELECT entry.naration LIMIT 1");
    assert_eq!(rows[0][0], Value::Null);
}

/// Attribute access on a non-structured operand is a type error,
/// matching upstream's "column type is not structured".
#[test]
fn attribute_on_non_object_errors() {
    let dirs = ledger();
    let q = parse("SELECT account.foo LIMIT 1").expect("parse");
    let mut ex = Executor::new(&dirs);
    let err = ex.execute(&q).expect_err("must be a type error");
    assert!(err.to_string().contains("not structured"), "{err}");
}

/// Number literals keep their decimal point — `1.5` is a decimal, never
/// `1 . 5` attribute access.
#[test]
fn decimal_literals_unaffected() {
    let rows = run("SELECT 1.5 LIMIT 1");
    assert_eq!(rows[0][0], Value::Number(dec!(1.5)));
}

/// Attribute/subscript work in WHERE and aggregate contexts too — every
/// evaluator path grew the arms.
#[test]
fn attribute_in_where_and_group_by() {
    let rows = run("SELECT count(*) WHERE entry.payee = 'Shop'");
    assert_eq!(rows[0][0], Value::Integer(2));
    let rows = run("SELECT entry.narration, count(*) GROUP BY entry.narration");
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0][0], Value::String("coffee".into()));
}
