//! Regression for #1797: BQL string literals must match upstream
//! beanquery's quote-stripping-ONLY semantics.
//!
//! Upstream's grammar (`bql.ebnf`) is
//! `string = /\"[^\"]*\"|\'(?:[^\']|\'\')*\'/` with semantics
//! `value[1:-1]` — a backslash is an ordinary byte, and a doubled `''`
//! continues a single-quoted string while staying VERBATIM in the value
//! (pinned by upstream's own `parser_test.py`: `'rainy''day'` →
//! `rainy''day`). rustledger's parser used to consume `\` as a C-style
//! escape introducer, so `subst('[ ,]*\)$', …)` reached the regex engine
//! as `[ ,]*)$` — "unopened group" on a regex that works in beanquery.

use rust_decimal_macros::dec;
use rustledger_core::{Amount, Directive, NaiveDate, Open, Posting, Transaction};
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

fn eval_scalar(expr: &str) -> Value {
    let dirs = ledger();
    let q = parse(&format!("SELECT {expr} LIMIT 1")).expect("parse");
    let mut ex = Executor::new(&dirs);
    let r = ex.execute(&q).expect("execute");
    r.rows[0][0].clone()
}

/// The issue's minimal repro: `\)` must survive to the regex engine as a
/// literal-paren escape instead of collapsing to an unbalanced `)`.
#[test]
fn backslash_survives_into_subst_regex() {
    assert_eq!(
        eval_scalar(r"subst('[ ,]*\)$', ')', 'foo   )')"),
        Value::String("foo)".into())
    );
}

/// The real-world template from #1797 (mkshp's Obsidian plugin): three
/// nested `subst()` calls with `\(`/`\)` escapes over a converted balance.
#[test]
fn issue_1797_multi_currency_formatting_template() {
    let expr = r"subst('^\([ ,]*', '(', subst('[ ,]*\)$', ')', subst(', *[-.0-9]+ GBP|[-.0-9]+ GBP *,?', '', '(10.00 USD, 5.00 GBP)')))";
    assert_eq!(eval_scalar(expr), Value::String("(10.00 USD)".into()));
}

/// Backslash is an ordinary byte in BOTH quote styles — `'\n'` is the two
/// characters backslash-n, not a newline.
#[test]
fn backslash_is_a_literal_byte() {
    assert_eq!(eval_scalar(r"'a\nb'"), Value::String(r"a\nb".into()));
    assert_eq!(eval_scalar(r#""a\nb""#), Value::String(r"a\nb".into()));
    // A lone trailing backslash is a complete, one-character string —
    // pre-fix it consumed the closing quote and broke the parse.
    assert_eq!(eval_scalar(r"'\'"), Value::String(r"\".into()));
}

/// Upstream-pinned `''` behavior: continues the string, kept verbatim.
#[test]
fn doubled_quote_continues_single_quoted_string_verbatim() {
    assert_eq!(
        eval_scalar("'rainy''day'"),
        Value::String("rainy''day".into())
    );
}

/// Drift guard: the paren-nesting pre-scan must lex strings identically
/// to the parser — a string whose body pre-fix "escaped" the closing
/// quote (trailing `\`) followed by deep parens must parse fine, and a
/// `''`-continued string containing parens must not count them.
#[test]
fn nesting_scan_agrees_with_string_literal_lexing() {
    // A trailing-backslash string followed by real parens: the OLD
    // pre-scan treated `\` as escaping the closing quote and swallowed
    // the rest of the query as string body, desynchronizing its paren
    // count from the parser's.
    assert_eq!(eval_scalar(r"length(('\'))"), Value::Integer(1));
    // Parens inside a ''-continued string body are opaque bytes, and a
    // `\)` regex escape deletes a literal paren from a parenthesized
    // string argument.
    assert_eq!(
        eval_scalar(r"subst('\)', '', ('y)'))"),
        Value::String("y".into())
    );
    assert_eq!(eval_scalar("length('(((''((( ')"), Value::Integer(9));
}
