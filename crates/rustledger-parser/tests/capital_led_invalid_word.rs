//! A lone capital glued to a non-blank is, with the rest of its run, one
//! invalid token, as in beancount, also where the run otherwise lexes (#2982).
//!
//! beancount's lexer takes a capital alone (`CAPITAL`) only before a space, a
//! tab or a `\n` (`[A-Z]/[ \t\n]`). Glued to anything else, and starting no
//! longer `CURRENCY` (`[A-Z][A-Z0-9'._-]*[A-Z0-9]`) or `ACCOUNT`, no rule
//! takes it, and its default rule enters the `INVALID` state, which reads
//! `[^ \t\n\r]+` as one `Invalid token`. So `U~SD`, `U?SD`, `V,` and `T#!` are
//! each one invalid token there. Here they lexed as valid tokens (a
//! one-letter currency, then `~` and `SD`), and the parser's glued
//! one-letter rules reported the capital: one error, which matched on a
//! clean line. After an earlier invalid token on the line, those rules are
//! quieted with the line's other construct checks, so the word went
//! uncounted where beancount counts it.
//!
//! Every expected count below was checked against `bean-check` 3.2.3.

use rustledger_parser::parse;

/// The errors of `src` per line (1-based, counting `\n` only, as
/// `rledger check` does): `(line, count)`, in line order.
fn per_line(src: &str) -> Vec<(usize, usize)> {
    let mut counts: Vec<(usize, usize)> = Vec::new();
    for e in &parse(src).errors {
        let line = 1 + src[..e.span.start].matches('\n').count();
        match counts.iter_mut().find(|(l, _)| *l == line) {
            Some((_, n)) => *n += 1,
            None => counts.push((line, 1)),
        }
    }
    counts.sort_unstable();
    counts
}

/// Two opens, the start of every source below.
const OPENS: &str = "2024-01-01 open Assets:A\n2024-01-01 open Assets:B\n";

/// The issue's posting rows, after a first invalid token on the line, and
/// two glued words on one line: each word is one more invalid token.
#[test]
fn test_parse_capital_led_word_after_an_invalid_token_is_its_own_error() {
    for (posting, n) in [
        ("  Assets:A  $ U~SD", 2),
        ("  Assets:A  ' 1 U%SD", 2),
        ("  Assets:A  x U?SD", 2),
        ("  Assets:A  .5 U~SD", 2),
        ("  Assets:A  ` U%SD", 2),
        ("  Assets:A  \x11 U~SD", 2),
        ("  Assets:A  -$ U~SD", 2),
        ("  Assets:A  $ U~SD  V,", 3),
    ] {
        let src = format!("{OPENS}2024-01-02 *\n  Assets:B  1 USD\n{posting}\n");
        assert_eq!(per_line(&src), vec![(5, n)], "{src:?}");
        let crlf = src.replace('\n', "\r\n");
        assert_eq!(per_line(&crlf), vec![(5, n)], "{crlf:?}");
    }
}

/// The issue's header rows, and lines with no directive.
#[test]
fn test_parse_capital_led_word_after_an_invalid_token_on_a_header() {
    for (line, n) in [
        ("2024-01-02 balance Assets:A 2x U?SD", 2),
        ("2024-01-02 price HOOL 2x U?SD", 2),
        ("2024-01-02 balance Assets:A 1 Z~SD  u#;c E(U", 3),
        ("x U~SD", 2),
        ("$ U~SD", 2),
    ] {
        let src = format!("{OPENS}{line}\n");
        assert_eq!(per_line(&src), vec![(3, n)], "{src:?}");
    }
}

/// The rule's boundaries, unchanged: a capital-led word with no earlier
/// invalid token is one error, as before; a capital that starts a longer
/// currency (`US~D`, `USD~`, `U.SD`) or stands before a blank is no invalid
/// run of its own; a word inside a cost spec or after a currency list's
/// comma is still one error.
#[test]
fn test_parse_capital_led_word_rule_boundaries() {
    for (posting, want) in [
        ("  Assets:A  1 U~SD", vec![(5, 1)]),
        ("  Assets:A  1 US~D", vec![(5, 1)]),
        ("  Assets:A  1 USD~", vec![(5, 1)]),
        ("  Assets:A  1 U.SD", vec![]),
        ("  Assets:A  1 U @ 2 USD", vec![]),
        ("  Assets:A  1 V{2 USD}", vec![(5, 1)]),
        ("  Assets:A  1 USD {T@ 2 USD}", vec![(5, 1)]),
        ("  Assets:A  1 USD {2 USD, V, 2024-01-01}", vec![(5, 1)]),
    ] {
        let src = format!("{OPENS}2024-01-02 *\n  Assets:B  1 USD\n{posting}\n");
        assert_eq!(per_line(&src), want, "{src:?}");
    }
    for (line, n) in [
        ("2024-01-02 open Assets:C USD,U~SD", 1),
        ("U~SD", 1),
        ("U", 1),
    ] {
        let src = format!("{OPENS}{line}\n");
        assert_eq!(per_line(&src), vec![(3, n)], "{src:?}");
    }
}

/// A transaction's flag position is left to the rules that already handle
/// it, unchanged: one error on the header, and its postings quiet, as
/// beancount's recovery keeps them. `P;c` keeps its transaction there
/// (`txn_header`'s glued-flag rule).
#[test]
fn test_parse_glued_flag_position_is_unchanged() {
    for header in ["2024-01-02 T~x \"n\"", "2024-01-02 P;c"] {
        let src = format!("{OPENS}{header}\n  Assets:A  1 USD\n  Assets:B  -1 USD\n");
        assert_eq!(per_line(&src), vec![(3, 1)], "{src:?}");
    }
    let src = format!("{OPENS}2024-01-02 P;c\n  Assets:A  1 USD\n  Assets:B  -1 USD\n");
    assert_eq!(parse(&src).directives.len(), 3, "{src:?}");
}
