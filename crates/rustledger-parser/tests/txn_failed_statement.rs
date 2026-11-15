//! A transaction whose own lines hold a parse error, or that a directive with
//! a date that is no calendar date follows (#2987).
//!
//! bean-check 3.2.3 fails the statement at a grammar or lexer error on the
//! transaction's lines (`  5`, `  2024-13-45`), and its recovery
//! discards the transaction: no balance residual is reported. The errors its
//! builder reports while it still builds the transaction (a duplicate cost, a
//! negative price, a tag line after the first posting, a repeated metadata
//! key) and rledger's own diagnostics keep it. Every expectation here was
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

/// beancount's builder reports these and still builds the transaction, and
/// rledger's own diagnostics are none of beancount's: the transaction is kept
/// either way, so its residual is checked.
#[test]
fn test_transaction_holds_invalid_token_keeps_a_transaction_beancount_builds() {
    for line in [
        // A duplicate cost, date or label, cost merging, a duplicate merge
        // spec in a cost spec.
        "  Assets:H  1 HOO {1 USD, 2 USD}",
        "  Assets:H  1 HOO {1 USD, 1 USD}",
        "  Assets:H  1 HOO {1 USD, 2 USD, 3 USD}",
        "  Assets:H  1 HOO {{1 USD, 2 USD}}",
        "  Assets:H  -1 HOO {1 USD, 2 USD}",
        "  Assets:H  1 HOO {1 USD, 2024-01-01, 2024-01-01}",
        "  Assets:H  1 HOO {1 USD, \"a\", \"a\"}",
        "  Assets:H  1 HOO {1 USD, *}",
        "  Assets:H  1 HOO {*, *}",
        // A negative price.
        "  Assets:H  1 HOO @ -1 USD",
        "  Assets:H  1 HOO @@ -1 USD",
        "  Assets:H  1 HOO @ -1*1 USD",
        "  Assets:H  1 HOO @ (-1) USD",
        "  Assets:H  1 HOO @ 1-2 USD",
        // A per-unit cost inside `{{ }}`.
        "  Assets:H  1 HOO {{1 # 2 USD}}",
        // Cost and price currencies that differ.
        "  Assets:H  1 HOO {1 USD} @ 2 EUR",
        "  Assets:H  1 HOO {1 USD} @@ 2 EUR",
        // A tag or link line after the first posting, a repeated metadata
        // key on the transaction and on a posting.
        "  #t",
        "  #t ^l",
        "  kk: \"1\"\n  kk: \"2\"",
        "    pp: 1\n    pp: 2",
        // rledger's own: a number beancount reads (`1,,000` is 1000 there),
        // an amount past `Decimal`'s precision, a BOM beancount reads into
        // an account.
        "  Assets:A  1,,000 USD",
        "  Assets:A  123456789012345678901234567890 USD",
        "  \u{feff}Assets:A  1 USD",
    ] {
        let src = format!("2024-01-02 * \"x\"\n  Assets:A  1 USD\n{line}\n  Equity:E  -2 USD\n");
        assert!(!transaction_holds_invalid_token(&src), "{src:?}");
        let src = src.replace('\n', "\r\n");
        assert!(!transaction_holds_invalid_token(&src), "{src:?}");
    }
    // The deprecated pipe between payee and narration, which beancount's
    // grammar accepts.
    let src = "2024-01-02 * \"p\" | \"n\"\n  Assets:A  1 USD\n  Equity:E  -2 USD\n";
    assert!(!transaction_holds_invalid_token(src), "{src:?}");
    // A tag line after the first posting, then a grammar error: discarded.
    let src = txn("  #t\n  5\n");
    assert!(transaction_holds_invalid_token(&src), "{src:?}");
}
