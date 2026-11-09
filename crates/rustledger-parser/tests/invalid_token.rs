//! An invalid token is formed, and reported, as beancount 3.2.3 forms and
//! reports it (#2872).
//!
//! beancount's lexer has one catch-all rule: at a character no other rule
//! takes, it enters its `INVALID` state, which takes everything up to the
//! next space, tab, `\r` or `\n` (`[^ \t\n\r]+`) as ONE token and reports it
//! as `Invalid token: '...'`. The lexer reports every such token, whatever
//! the grammar does with the line; the grammar adds a syntax error only when
//! it fails at a readable token before the first invalid one. Every
//! expectation below is what `beancount.parser.parser.parse_string` reports
//! for the same input: the 1-based line of each error.

use rustledger_parser::cst::parse_red_only;
use rustledger_parser::logos_lexer::{Token, tokenize_lossless};
use rustledger_parser::{ParseResult, parse};

/// The 1-based line of each error, in order.
fn error_lines(src: &str, result: &ParseResult) -> Vec<usize> {
    result
        .errors
        .iter()
        .map(|e| src[..e.span.start].matches('\n').count() + 1)
        .collect()
}

/// `src` parses to errors on exactly `lines`, on the green and red paths alike.
fn check(src: &str, lines: &[usize]) {
    let result = parse(src);
    assert_eq!(
        error_lines(src, &result),
        lines,
        "{src:?}: {:?}",
        result.errors
    );
    let red = parse_red_only(src);
    assert_eq!(
        format!("{:?}", result.errors),
        format!("{:?}", red.errors),
        "{src:?}"
    );
    assert_eq!(
        format!("{:?}", result.directives),
        format!("{:?}", red.directives),
        "{src:?}"
    );
}

/// The error tokens of `src`, as text.
fn error_tokens(src: &str) -> Vec<&str> {
    tokenize_lossless(src)
        .into_iter()
        .filter_map(|(t, _)| match t {
            Token::Error(text) => Some(text),
            _ => None,
        })
        .collect()
}

#[test]
fn test_tokenize_lossless_invalid_token_runs_to_the_next_blank() {
    for (src, want) in [
        // The issue's example: one token, not `Ass`, `'` and `ets:A`.
        ("2024-01-01 open Ass'ets:A\n", &["Ass'ets:A"][..]),
        // A glued `"` or `;` is part of the run: no string, no comment.
        ("x\"a b\"\n", &["x\"a", "b\""][..]),
        ("kk: true;c\n", &["true;c"][..]),
        // An unterminated quote is one run too, and lexing resumes after it.
        ("\"abc def\n", &["\"abc", "def"][..]),
        // A run stops at a tab and at a `\r`.
        ("a$\tb$\r\n", &["a$", "b$"][..]),
        // A lone capital glued to the run starts it, as beancount lexes a
        // capital alone only before a blank: `R\x04` and `Assets:a`.
        ("R\u{4}\u{16}", &["R\u{4}\u{16}"][..]),
        ("  Assets:a 1 USD\n", &["Assets:a"][..]),
        ("U$SD\n", &["U$SD"][..]),
        // A Unicode digit is no number (`[0-9]` there).
        ("\u{96b}$\u{96b}\n", &["\u{96b}$\u{96b}"][..]),
    ] {
        assert_eq!(error_tokens(src), want, "{src:?}");
    }
}

#[test]
fn test_tokenize_lossless_tokens_beancount_rejects_but_rledger_reads_still_lex() {
    // A lone capital glued to tokens that all lex stays a currency: beancount
    // reads each of these as an invalid token (`V,`, `T#!`, `U~SD`), and here
    // they lex as tokens, which the parser's glued one-letter rules then
    // reject.
    for src in ["{1 V, 2024-01-01}\n", "T#!\n", "U~SD\n"] {
        assert_eq!(error_tokens(src), Vec::<&str>::new(), "{src:?}");
    }
    // A mid-file BOM keeps its own extent, so the directive of a
    // concatenated file after it still parses.
    assert_eq!(
        error_tokens("2024-01-01 open Assets:A\n\u{feff}2024-01-02 open Assets:B\n"),
        ["\u{feff}"]
    );
}

#[test]
fn test_parse_invalid_token_is_one_error() {
    for (src, lines) in [
        ("2024-01-01 open Ass'ets:A\n", &[1][..]),
        ("2024-01-01 commodity U$SD\n", &[1][..]),
        ("2024-01-01 event $\"e\" \"v\"\n", &[1][..]),
        ("2024-01-01 *_\n  Assets:A  1 USD\n  Assets:B\n", &[1][..]),
        // Nothing after the invalid token on its line is reported: the
        // bare currency, the tolerance, the cost spec and the expression
        // fail at it, where beancount's grammar never gets.
        ("2024-01-01 custom \"b\" $10 /6J\n", &[1][..]),
        ("2024-01-01 balance Assets:A 1~.00 USD\n", &[1][..]),
        (
            "2024-01-01 *\n  Assets:A  1 HOOL {{2 .USD}} @@ 3 USD\n  Assets:B\n",
            &[2][..],
        ),
        (
            "2024-01-01 *\n  Assets:A  (1\" + 2) * 3 USD\n  Assets:B\n",
            &[2][..],
        ),
        // A metadata value in Unicode digits was dropped with no error.
        ("2024-01-01 open Assets:A\n  kk: \u{96b}\n", &[2][..]),
    ] {
        check(src, lines);
    }
}

#[test]
fn test_parse_reports_each_invalid_token_and_an_earlier_grammar_error() {
    for (src, lines) in [
        // Three invalid tokens.
        ("foo bar$ baz\n", &[1, 1, 1][..]),
        // A string cannot start a line: a syntax error, then `p"`.
        ("\"plugin \"p\" \"c\"\n", &[1, 1][..]),
        // `pushtag` expects a tag at the `#`; `$t` is invalid on top.
        ("pushtag #$t\npoptag #t\n", &[1, 1, 2][..]),
        // An orphan indented line: `unexpected INDENT`, then the token.
        ("  Assets:A 1 U$D\n", &[1, 1][..]),
        // A posting reads up to the invalid tokens, each reported.
        (
            "2024-01-01 *\n  Assets:A 1 U$D x$\n  Assets:B\n",
            &[2, 2][..],
        ),
        // A price expects a currency at the `/`.
        ("2024-01-01 price /6\"E_X 10 /6J\n", &[1, 1][..]),
    ] {
        check(src, lines);
    }
}

#[test]
fn test_parse_directive_with_an_invalid_token_changes_no_tag_state() {
    // beancount's grammar never reduces a header with an invalid token on
    // it, so the push does not happen and the pop is of an absent tag.
    check("pushtag\" #t\npoptag #t\n", &[1, 2]);
    check("pushtag #t $x\npoptag #t\n", &[1, 2]);
    // Nor does the pop: the push stays open, reported at the end.
    let src = "pushtag #t\npoptag #t $x\n";
    let result = parse(src);
    assert!(
        result
            .errors
            .iter()
            .any(|e| e.to_string().contains("was never popped")),
        "{:?}",
        result.errors
    );
}

#[test]
fn test_parse_keeps_a_construct_error_where_the_grammar_fails_before_the_token() {
    for (src, lines) in [
        // `unexpected LCURL` at the second `{`, then `Invalid token: '$'`.
        (
            "2024-01-01 *\n  Assets:A  1 VV {}{$\n  Assets:B\n",
            &[2, 2][..],
        ),
        // `unexpected HASH` inside the cost spec, then the NUL.
        ("2024-01-01 *\n  Assets:A  1 VV {(7# \u{0}\n", &[2, 2][..]),
        // `unexpected LCURL, expecting RCURL or COMMA`, then the NUL.
        (
            "2024-01-01 *\n  Assets:A  1 VV {+5/50+82333333{\u{0}\n",
            &[2, 2][..],
        ),
        // Where the grammar reaches the token, it is the line's only error.
        (
            "2024-01-01 *\n  Assets:A  1 HOOL {2 .USD}\n  Assets:B\n",
            &[2][..],
        ),
    ] {
        check(src, lines);
    }
}

#[test]
fn test_parse_reports_no_booking_method_on_a_header_with_an_invalid_token() {
    // beancount checks the booking method when it builds the directive, which
    // it never does here: `Invalid token: '$;comment'` alone.
    check("2024-01-02 open Assets:C$;comment \"x\"\n", &[1]);
    let result = parse("2024-01-02 open Assets:C$;comment \"x\"\n");
    assert!(
        result.errors.iter().all(|e| e.kind_code() != 25),
        "{:?}",
        result.errors
    );
    // Without the invalid token the booking method is still checked.
    let result = parse("2024-01-02 open Assets:C \"x\"\n");
    assert!(
        result.errors.iter().any(|e| e.kind_code() == 25),
        "{:?}",
        result.errors
    );
}

#[test]
fn test_parse_reports_no_repeated_key_in_a_transaction_with_an_invalid_token() {
    // beancount never builds a transaction with an invalid token in it, so
    // the token is its only error, wherever it stands.
    for (src, lines) in [
        (
            "2024-01-01 * $\n  xn: 1\n  xn: 2\n  Assets:A 1 USD\n  Assets:B\n",
            &[1][..],
        ),
        (
            "2024-01-01 *\n  xn: 1\n  xn: 2\n  Assets:A 1 U$D\n  Assets:B\n",
            &[4][..],
        ),
        (
            "2024-01-01 *\n  xn: 1\n  xn: 2 $\n  xn: 3\n  Assets:A 1 USD\n  Assets:B\n",
            &[3][..],
        ),
    ] {
        check(src, lines);
    }
}
