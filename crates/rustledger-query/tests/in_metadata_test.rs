//! `'key' IN meta` tests a metadata map for a KEY, as bean-query's
//! `meta.__contains__(key)` does (#2701).
//!
//! Every metadata value used to fall through `IN`'s scalar-equality arm,
//! which compared the key string with the whole map: `'k' IN meta` matched
//! nothing and `'k' NOT IN meta` matched every row, with no error. The cases
//! here cover each representation a metadata map has in the executor: the
//! posting `meta` column on the default path (`Value::Metadata`) and
//! `entry.meta` and the system tables' `meta` columns (`Value::Object`).
//! Expected rows are bean-query's (beanquery 0.2.0 on beancount 3.2.3).

use rust_decimal_macros::dec;
use rustledger_core::{
    Amount, Balance, Commodity, Directive, MetaValue, NaiveDate, Open, Posting, Transaction,
};
use rustledger_query::{Executor, Value, parse};

fn date(m: u32, d: u32) -> NaiveDate {
    rustledger_core::naive_date(2026, m, d).unwrap()
}

/// The issue's ledger, plus a commodity and a balance assertion with
/// metadata of their own.
fn ledger() -> Vec<Directive> {
    let mut shop = Transaction::new(date(1, 2), "Groceries")
        .with_synthesized_posting(Posting::new("Assets:Bank", Amount::new(dec!(-10), "EUR")))
        .with_synthesized_posting(Posting::new("Expenses:Food", Amount::new(dec!(10), "EUR")));
    shop.payee = Some("Shop".into());
    shop.meta
        .insert("concept".into(), MetaValue::String("SHOP 123".into()));

    let mut priced = Posting::new("Assets:Bank", Amount::new(dec!(-100), "MAD"));
    priced
        .meta
        .insert("note".into(), MetaValue::String("priced".into()));
    let mut market = Transaction::new(date(1, 3), "Fruit")
        .with_synthesized_posting(priced)
        .with_synthesized_posting(Posting::new("Expenses:Food", Amount::new(dec!(100), "MAD")));
    market.payee = Some("Market".into());

    let mut eur = Commodity::new(date(1, 1), "EUR");
    eur.meta
        .insert("name".into(), MetaValue::String("Euro".into()));
    let mut balance = Balance::new(date(1, 4), "Assets:Bank", Amount::new(dec!(-10), "EUR"));
    balance.meta.insert("checked".into(), MetaValue::Bool(true));

    vec![
        Directive::Commodity(eur),
        Directive::Open(Open::new(date(1, 1), "Assets:Bank")),
        Directive::Open(Open::new(date(1, 1), "Expenses:Food")),
        Directive::Transaction(shop),
        Directive::Transaction(market),
        Directive::Balance(balance),
    ]
}

fn rows(query: &str) -> Vec<Vec<Value>> {
    let directives = ledger();
    let mut executor = Executor::new(&directives);
    executor
        .execute(&parse(query).expect("parse"))
        .unwrap_or_else(|e| panic!("{query}: {e}"))
        .rows
}

fn strings(query: &str) -> Vec<String> {
    rows(query)
        .into_iter()
        .map(|row| match &row[0] {
            Value::String(s) => s.clone(),
            other => panic!("{query}: expected a string, got {other:?}"),
        })
        .collect()
}

/// The issue's query: only the posting that carries `note` matches.
#[test]
fn key_in_posting_meta() {
    assert_eq!(strings("SELECT narration WHERE 'note' IN meta"), ["Fruit"]);
    assert_eq!(
        strings("SELECT narration FROM #postings WHERE 'note' IN meta"),
        ["Fruit"]
    );
}

/// The negations are the dangerous half: they matched every row.
#[test]
fn key_not_in_posting_meta() {
    let expected = ["Groceries", "Groceries", "Fruit"];
    for query in [
        "SELECT narration WHERE 'note' NOT IN meta",
        "SELECT narration WHERE NOT 'note' IN meta",
        "SELECT narration FROM #postings WHERE 'note' NOT IN meta",
    ] {
        assert_eq!(strings(query), expected, "{query}");
    }
}

/// As a column the test is a boolean per row, not only a filter.
#[test]
fn key_in_meta_as_a_column() {
    let flags: Vec<Value> = rows("SELECT 'note' IN meta")
        .into_iter()
        .map(|row| row[0].clone())
        .collect();
    assert_eq!(
        flags,
        [false, false, true, false].map(Value::Boolean).to_vec()
    );
}

/// `entry.meta` is the transaction's metadata, which carries `concept`
/// and the source location, never the posting's `note`.
#[test]
fn key_in_entry_meta() {
    assert_eq!(
        strings("SELECT DISTINCT narration WHERE 'concept' IN entry.meta"),
        ["Groceries"]
    );
    assert_eq!(
        strings("SELECT DISTINCT narration WHERE 'concept' NOT IN entry.meta"),
        ["Fruit"]
    );
    assert!(strings("SELECT narration WHERE 'note' IN entry.meta").is_empty());
}

/// The system tables' `meta` columns.
#[test]
fn key_in_system_table_meta() {
    assert_eq!(
        strings("SELECT type FROM #entries WHERE 'concept' IN meta"),
        ["transaction"]
    );
    assert_eq!(
        strings("SELECT name FROM #commodities WHERE 'name' IN meta"),
        ["EUR"]
    );
    assert_eq!(
        strings("SELECT account FROM #balances WHERE 'checked' IN meta"),
        ["Assets:Bank"]
    );
    assert_eq!(
        strings("SELECT narration FROM #transactions WHERE 'concept' NOT IN meta"),
        ["Fruit"]
    );
}

/// The FROM filter goes through the same operator.
#[test]
fn key_in_meta_as_from_filter() {
    assert_eq!(
        strings("SELECT narration FROM 'concept' IN entry.meta"),
        ["Groceries", "Groceries"]
    );
}

/// Keys are strings, so any other value is absent, as in Python; a NULL
/// operand is NULL, which `WHERE` drops.
#[test]
fn non_string_and_null_keys() {
    assert!(strings("SELECT narration WHERE 5 IN meta").is_empty());
    assert_eq!(strings("SELECT narration WHERE 5 NOT IN meta").len(), 4);
    assert!(strings("SELECT narration WHERE NULL IN meta").is_empty());
    assert!(strings("SELECT narration WHERE NULL NOT IN meta").is_empty());
}

/// A key written with no value (`empty:`) is present, with a NULL value, so
/// `IN` finds it, as bean-query does: membership asks about the key, never
/// about the value.
#[test]
fn key_with_no_value_is_present() {
    let mut txn = Transaction::new(date(1, 5), "Blank")
        .with_synthesized_posting(Posting::new("Assets:Bank", Amount::new(dec!(-1), "EUR")))
        .with_synthesized_posting(Posting::new("Expenses:Food", Amount::new(dec!(1), "EUR")));
    txn.meta.insert("empty".into(), MetaValue::None);
    txn.postings[0].meta.insert("blank".into(), MetaValue::None);
    let directives = vec![Directive::Transaction(txn)];
    let mut executor = Executor::new(&directives);
    let mut flags = |query: &str| -> Vec<Value> {
        executor
            .execute(&parse(query).unwrap())
            .unwrap()
            .rows
            .into_iter()
            .map(|row| row[0].clone())
            .collect()
    };
    assert_eq!(
        flags("SELECT 'empty' IN entry.meta"),
        [true, true].map(Value::Boolean).to_vec()
    );
    assert_eq!(
        flags("SELECT 'blank' IN meta"),
        [true, false].map(Value::Boolean).to_vec()
    );
}
