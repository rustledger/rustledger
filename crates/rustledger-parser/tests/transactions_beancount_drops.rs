//! `transactions_beancount_drops`: the transactions beancount's grammar
//! discards, asked only where a parse error is.

use rustledger_parser::{parse, transactions_beancount_drops};

fn dropped(src: &str) -> Vec<usize> {
    transactions_beancount_drops(src, &parse(src))
}

#[test]
fn test_transactions_beancount_drops_an_invalid_token_in_a_posting() {
    let src = "2024-01-01 open Assets:A\n2024-01-02 * \"x\"\n  Assets:A  1 $ USD\n  Assets:B  -1 USD\n2024-01-03 * \"y\"\n  Assets:A  1 USD\n  Assets:B  -1 USD\n";
    // The directives are the open, then the two transactions.
    assert_eq!(dropped(src), [1]);
}

#[test]
fn test_transactions_beancount_drops_nothing_without_errors() {
    let src = "2024-01-02 * \"x\"\n  Assets:A  1 USD\n  Assets:B  -1 USD\n";
    assert!(parse(src).errors.is_empty());
    assert_eq!(dropped(src), [] as [usize; 0]);
}

#[test]
fn test_transactions_beancount_drops_keeps_one_its_builder_rejects() {
    // A repeated key is a builder error on a transaction beancount builds.
    let src = "2024-01-02 * \"x\"\n  kk: 1\n  kk: 2\n  Assets:A  1 USD\n  Assets:B  -1 USD\n";
    assert!(!parse(src).errors.is_empty());
    assert_eq!(dropped(src), [] as [usize; 0]);
}

#[test]
fn test_transactions_beancount_drops_only_transactions() {
    // A balance beancount discards is no transaction; the validator handles it.
    let src = "2024-01-01 open Assets:A\n2024-01-02 balance Assets:A 1 USD ~ 0.1\n";
    assert!(!parse(src).errors.is_empty());
    assert_eq!(dropped(src), [] as [usize; 0]);
}

#[test]
fn test_transactions_beancount_drops_keeps_one_a_later_line_fails() {
    // beancount drops an entry whose next column-0 line starts with an
    // invalid token; rledger keeps it on purpose (P7, overlay
    // `kept-entries`).
    let src =
        "2024-01-02 * \"x\"\n  Assets:A  1 USD\n  Assets:B  -1 USD\nthis line is not beancount\n";
    assert!(!parse(src).errors.is_empty());
    assert_eq!(dropped(src), [] as [usize; 0]);
}
