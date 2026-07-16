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

/// An aggregate wrapped in postfix access is still an aggregate:
/// `first(entry).payee` must produce ONE aggregated row, not a NULL per
/// posting (pre-review, `is_aggregate_expr` didn't recurse into the new
/// variants and the query was silently misrouted down the per-row path).
#[test]
fn aggregate_under_postfix_access() {
    let rows = run("SELECT first(entry).payee");
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0][0], Value::String("Shop".into()));
}

/// ORDER BY on a selected attribute expression resolves (pre-review the
/// target was named "colN" and ORDER BY string lookup missed it), and
/// the output column is named by its source spelling.
#[test]
fn order_by_attribute_and_column_naming() {
    let dirs = ledger();
    let q = parse("SELECT entry.narration ORDER BY entry.narration").expect("parse");
    let mut ex = Executor::new(&dirs);
    let result = ex.execute(&q).expect("execute");
    assert_eq!(result.rows.len(), 2);
    assert_eq!(result.columns[0], "entry.narration");
}

/// Drift guard: `balance['USD']` and `getitem(balance, 'USD')` are two
/// spellings of the same canonical lookup and must agree on every row —
/// including the Inventory arm the first draft omitted.
#[test]
fn subscript_agrees_with_getitem_on_inventory() {
    let rows = run("SELECT balance['USD'], getitem(balance, 'USD')");
    assert_eq!(rows.len(), 2);
    for row in &rows {
        assert_eq!(row[0], row[1], "subscript/getitem drift: {row:?}");
    }
    // And at least one row has a real amount (not vacuous agreement).
    assert!(rows.iter().any(|r| matches!(r[0], Value::Amount(_))));
}

/// `SELECT * FROM postings` hides the structured `entry` column (matching
/// upstream's wildcard) and the underscore helper columns — which leaked
/// into the wildcard before this PR. All stay addressable by name.
#[test]
fn select_star_hides_structured_and_helper_columns() {
    let dirs = ledger();
    let q = parse("SELECT * FROM postings LIMIT 1").expect("parse");
    let mut ex = Executor::new(&dirs);
    let result = ex.execute(&q).expect("execute");
    for hidden in ["entry", "_entry_meta", "_posting_meta"] {
        assert!(
            !result.columns.iter().any(|c| c == hidden),
            "column '{hidden}' must be hidden from SELECT *: {:?}",
            result.columns
        );
    }
    // Column names and row width stay in lockstep.
    assert_eq!(result.columns.len(), result.rows[0].len());
    // Explicit selection still works.
    let rows = run("SELECT entry FROM postings LIMIT 1");
    assert!(matches!(rows[0][0], Value::Object(_)));
}

/// `entry.meta` carries the filename/lineno augmentation, agreeing with
/// `entry_meta('lineno')` — the two lookup paths cannot drift. Uses a
/// source-mapped executor so real locations exist (programmatic
/// directives have none, which would make the presence assert vacuous).
#[test]
fn entry_meta_carries_source_location() {
    use rustledger_loader::SourceMap;
    use rustledger_parser::{Span, Spanned};
    use std::sync::Arc;

    let mut source_map = SourceMap::new();
    let source: Arc<str> =
        "2026-07-01 open Assets:Cash\n2026-07-01 * \"Shop\" \"coffee\"\n  Assets:Cash  -1.00 USD\n"
            .into();
    let file_id = source_map.add_file("test.beancount".into(), source);
    let spanned: Vec<Spanned<Directive>> = ledger()
        .into_iter()
        .map(|d| Spanned {
            value: d,
            // Offset of the transaction line (line 2) — close enough for a
            // stable, non-zero lineno.
            span: Span::new(28, 60),
            file_id: u16::try_from(file_id).expect("single test file"),
        })
        .collect();

    let mut ex = rustledger_query::Executor::new_with_sources(&spanned, &source_map);
    let q = parse("SELECT entry.meta['lineno'], entry_meta('lineno') LIMIT 1").expect("parse");
    let rows = ex.execute(&q).expect("execute").rows;
    assert_eq!(rows[0][0], rows[0][1], "entry.meta vs entry_meta drift");
    assert!(!matches!(rows[0][0], Value::Null), "lineno must be present");
}

/// Whitespace is allowed around the postfix dot, as in upstream's
/// whitespace-skipping grammar.
#[test]
fn whitespace_around_postfix_dot() {
    for q in [
        "SELECT entry.narration LIMIT 1",
        "SELECT entry .narration LIMIT 1",
        "SELECT entry. narration LIMIT 1",
        "SELECT entry . narration LIMIT 1",
    ] {
        let rows = run(q);
        assert_eq!(rows[0][0], Value::String("coffee".into()), "query: {q}");
    }
}
