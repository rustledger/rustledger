//! A transaction whose own lines hold a parse error, or that a directive with
//! a date that is no calendar date follows (#2987).
//!
//! bean-check 3.2.3 fails the statement at any error on the transaction's
//! lines, a grammar error as well as one of its lexer's, and its recovery
//! discards the transaction: no balance residual is reported. Two of the
//! errors it reports there are its builder's, which still builds the
//! transaction: a tag or link line after the first posting, and a repeated
//! metadata key; there the residual is reported. Every expectation here was
//! checked against `beancount.loader.load_string` (bean-check 3.2.3).

use rustledger_parser::transaction_holds_invalid_token;

/// An unbalanced transaction (residual -1 USD) followed by `tail`.
fn txn(tail: &str) -> String {
    format!("2024-01-02 * \"x\"\n  Assets:A  1 USD\n  Equity:E  -2 USD\n{tail}")
}

/// An indented line with a parse error ends the statement in beancount.
#[test]
fn test_transaction_holds_invalid_token_counts_a_parse_error_on_its_lines() {
    for line in [
        // beancount's lexer raises.
        "  2024-13-45\n",
        "  2024-02-30\n",
        "  1,50\n",
        // beancount's grammar fails.
        "  1,,000 USD\n",
        "  5\n",
        "  \"s\"\n",
        "  T\n",
        "  !\n",
        "  USD\n",
        "  TRUE\n",
        "  ~\n",
    ] {
        let src = txn(line);
        assert!(transaction_holds_invalid_token(&src), "{src:?}");
        // After an indented comment, which does not end the block.
        let src = txn(&format!("  ; c\n{line}"));
        assert!(transaction_holds_invalid_token(&src), "{src:?}");
        let src = txn(line).replace('\n', "\r\n");
        assert!(transaction_holds_invalid_token(&src), "{src:?}");
    }
}

/// A column-0 directive whose date is no calendar date is beancount's lexer
/// error right where the statement goes on, so the transaction is discarded,
/// directly after the block or after an indented comment, but not after a
/// blank line.
#[test]
fn test_transaction_holds_invalid_token_counts_an_invalid_date_directive_after_it() {
    for line in [
        "2024-02-30 open Assets:C\n",
        "2024-13-45 * \"y\"\n",
        "2024-00-10 balance Assets:A 0 USD\n",
        "2024-02-30 close Assets:B\n",
        "2024-02-30 open Assets:C",
    ] {
        let src = txn(line);
        assert!(transaction_holds_invalid_token(&src), "{src:?}");
        let src = txn(&format!("  ; c\n{line}"));
        assert!(transaction_holds_invalid_token(&src), "{src:?}");
        let src = txn(&format!("\n{line}"));
        assert!(!transaction_holds_invalid_token(&src), "{src:?}");
    }
}

/// beancount's builder reports these and still builds the transaction, so
/// its residual is reported.
#[test]
fn test_transaction_holds_invalid_token_keeps_a_transaction_its_builder_refuses_a_part_of() {
    for body in [
        // A tag or link line after the first posting.
        "  Assets:A  1 USD\n  Equity:E  -2 USD\n  #t\n",
        "  Assets:A  1 USD\n  ^l\n  Equity:E  -2 USD\n",
        "  Assets:A  1 USD\n  Equity:E  -2 USD\n  #t #u\n",
        // A repeated metadata key, on the transaction and on a posting.
        "  kk: \"1\"\n  kk: \"2\"\n  Assets:A  1 USD\n  Equity:E  -2 USD\n",
        "  Assets:A  1 USD\n    pp: 1\n    pp: 2\n  Equity:E  -2 USD\n",
    ] {
        let src = format!("2024-01-02 * \"x\"\n{body}");
        assert!(!transaction_holds_invalid_token(&src), "{src:?}");
    }
    // Notices beancount does not give at all: the pipe between payee and
    // narration, which its grammar accepts, and a BOM it reads into an
    // account.
    for src in [
        "2024-01-02 * \"p\" | \"n\"\n  Assets:A  1 USD\n  Equity:E  -2 USD\n",
        "2024-01-02 * \"x\"\n  Assets:A  1 USD\n  \u{feff}Equity:E  -2 USD\n",
    ] {
        assert!(!transaction_holds_invalid_token(src), "{src:?}");
    }
    // A tag line after the first posting, then an error: discarded.
    let src = txn("  #t\n  5\n");
    assert!(transaction_holds_invalid_token(&src), "{src:?}");
}
