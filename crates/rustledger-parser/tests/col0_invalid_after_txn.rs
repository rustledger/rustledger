//! A transaction followed directly by a line that starts with a token
//! beancount's lexer rejects (#2976).
//!
//! bean-check 3.2.3 fails the statement at that token, and its recovery
//! discards the transaction before it: no balance residual is reported. With a
//! blank or column-0 comment line between them the transaction is complete,
//! and a line led by a token beancount lexes (an account, a number, `~`, `*`)
//! fails its grammar only once the transaction is reduced, so in both cases
//! the residual is reported. Every expectation here was checked against
//! `beancount.loader.load_string` (bean-check 3.2.3).

use rustledger_parser::transaction_holds_invalid_token;

/// An unbalanced transaction (residual -1 USD) whose last line is `last`.
fn txn(last: &str) -> String {
    format!("2024-01-02 * \"x\"\n  Assets:A  1 USD\n  Equity:E  -2 USD\n{last}")
}

/// Lines led by a token beancount rejects: the transaction is discarded.
#[test]
fn test_transaction_holds_invalid_token_counts_a_column_0_invalid_token_after_it() {
    for lead in [
        "$x\n",
        "$\n",
        "x\n",
        "xx yy\n",
        "k: 1\n",
        "\u{11} junk\n",
        "\u{1}\n",
        "'Z x\n",
        "`\n",
        "^\n",
        "=\n",
        "\\\n",
        "\u{20ac}\n",
        // A date that is no calendar date: beancount's lexer raises there.
        "2024-13-45\n",
        "2024-02-30\n",
        // A number beancount refuses (`ValueError: Invalid number format`).
        "1,50\n",
        "1,0 USD\n",
        // A lone capital glued to what follows it: one invalid run in
        // beancount, whose `CAPITAL` needs a blank after it.
        "T@\n",
        "X(\n",
        "P\"\n",
        // At the end of the input, with no line ending.
        "$x",
    ] {
        let src = txn(lead);
        assert!(transaction_holds_invalid_token(&src), "{src:?}");
        // An indented comment line between them does not end the block.
        let src = txn(&format!("  ; c\n{lead}"));
        assert!(transaction_holds_invalid_token(&src), "{src:?}");
        let src = txn(lead).replace('\n', "\r\n");
        assert!(transaction_holds_invalid_token(&src), "{src:?}");
    }
}

/// Lines led by a token beancount lexes, or after a blank or column-0 comment
/// line: the transaction is kept with its residual.
#[test]
fn test_transaction_holds_invalid_token_keeps_a_transaction_before_a_lexed_token() {
    for lead in [
        "~\n",
        "^l x\n",
        "&\n",
        "?\n",
        "|\n",
        "*x\n",
        "#x\n",
        "Assets:A 1 USD\n",
        "123\n",
        "1.5\n",
        "USD\n",
        "TRUE\n",
        "{\n",
        "\"s\"\n",
        "2024-01-03 bogus\n",
        "2024-02-29\n",
        "1,000\n",
        // beancount's validator takes one doubled comma after a single digit.
        "1,,000\n",
        "T x\n",
        "T\n",
    ] {
        let src = txn(lead);
        assert!(!transaction_holds_invalid_token(&src), "{src:?}");
    }
    for sep in ["\n", "; c\n"] {
        let src = txn(&format!("{sep}$x\n"));
        assert!(!transaction_holds_invalid_token(&src), "{src:?}");
    }
}
