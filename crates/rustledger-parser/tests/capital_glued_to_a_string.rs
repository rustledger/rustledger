//! A lone capital glued to a string or comment that reaches past its run of
//! non-blank characters is, with that run, one invalid token, as in
//! beancount (#2977).
//!
//! beancount lexes a lone capital only before a blank (`[A-Z]/[ \t\n]`);
//! glued to anything else, its invalid token `[^ \t\n\r]+` takes the run up
//! to the next blank, quote and `;` included, so the quote opens no string
//! and the `;` no comment, and the next line lexes on its own. The lexer here
//! kept the capital as a token whenever the rest of its run lexed, and a `"`
//! whose string ran on past the blank (or to a later line) lexed: the string
//! swallowed the lines after it, each of which beancount reports.
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

/// Two opens, the start of every source below but the issue's.
const OPENS: &str = "2024-01-01 open Assets:A\n2024-01-01 open Assets:B\n";

/// `(source, bean-check's errors per line)`.
fn cases() -> Vec<(String, Vec<(usize, usize)>)> {
    let txn = format!("{OPENS}2024-01-02 * \"x\"\n  Assets:B  1 USD\n");
    vec![
        // The issue: the quote's string closes on the next line.
        ("A@\"x\nfoo\"\n".to_string(), vec![(1, 1), (2, 1)]),
        // At the end of the input.
        ("A@\"x\nfoo\"".to_string(), vec![(1, 1), (2, 1)]),
        // A string closing on its line, past a blank: `T"x` and `y"`.
        (format!("{OPENS}T\"x y\" 1\n"), vec![(3, 2)]),
        // A tab, and an escaped quote, inside the string.
        (format!("{OPENS}A@\"x\ty\"\n"), vec![(3, 2)]),
        (format!("{OPENS}A@\"x\\\" y\"\n"), vec![(3, 2)]),
        // A metadata value.
        (
            format!("{txn}  Assets:A  -1 USD\n  k: T\"a b\"\n"),
            vec![(6, 3)],
        ),
        // At column 0, the string closing two lines on.
        (
            format!("{OPENS}T\"x\n2024-01-03 open Assets:C\n\"\n"),
            vec![(3, 1), (5, 1)],
        ),
        // Three lines on.
        (
            format!("{OPENS}A@\"x\n2024-01-03 open Assets:C\n2024-01-04 open Assets:D\n\"\n"),
            vec![(3, 1), (6, 1)],
        ),
        // A `;` glued to the capital starts no comment.
        (
            format!("{OPENS}2024-01-02 open Assets:C T;x y\n"),
            vec![(3, 2)],
        ),
        (format!("{txn}  Assets:A  -1 USD\n  X;c d\n"), vec![(6, 2)]),
        // A parenthesis, then a string with a blank in it.
        (format!("{OPENS}X(\"a b\")\n"), vec![(3, 2)]),
    ]
}

#[test]
fn test_parse_capital_glued_to_a_string_past_its_run_is_one_invalid_token() {
    for (src, want) in cases() {
        assert_eq!(per_line(&src), want, "{src:?}");
        let crlf = src.replace('\n', "\r\n");
        assert_eq!(per_line(&crlf), want, "{crlf:?}");
    }
}

/// In a transaction's flag position the run is the header's invalid token,
/// and the postings under it are quiet, as after any failed dated line
/// (#2979): `2024-01-02 T"x y"` is `T"x` and `y"` there, two errors.
#[test]
fn test_parse_capital_glued_to_a_string_in_the_flag_position() {
    let postings = "  Assets:A  1 USD\n  Assets:B\n";
    let src = format!("{OPENS}2024-01-02 T\"x y\"\n{postings}");
    assert_eq!(per_line(&src), vec![(3, 2)], "{src:?}");
    // The string closing on a later line: beancount reads the run as the
    // header's token, then the posting lines, then the line holding the
    // quote that opens a string of its own.
    let src = format!("{OPENS}2024-01-02 T\"x\n  Assets:A  1 USD\n  Assets:B \"\n");
    assert_eq!(per_line(&src), vec![(3, 1), (5, 1)], "{src:?}");
    // A `%` comment glued to the capital, past a blank: `T%x` and `y`.
    for src in [
        format!("{OPENS}2024-01-02 T%x y\n{postings}"),
        format!("{OPENS}2024-01-02 T%x y\n{postings}").replace('\n', "\r\n"),
    ] {
        assert_eq!(per_line(&src), vec![(3, 2)], "{src:?}");
    }
}

/// A ` T(` inside a string is no lone capital: the dated window over a failed
/// line (#2979) is not given up for it, so the postings under
/// `2024-01-02 ~ "a T("` are quiet, as in beancount, where they were each
/// reported.
#[test]
fn test_parse_capital_inside_a_string_does_not_end_the_dated_window() {
    for src in [
        format!("{OPENS}2024-01-02 ~ \"a T(\"\n  Assets:A  1 USD\n  Assets:B\n"),
        format!("{OPENS}2024-01-02 ~ \"a T(\"\n  Assets:A  1 USD\n  Assets:B\n")
            .replace('\n', "\r\n"),
    ] {
        assert_eq!(per_line(&src), vec![(3, 1)], "{src:?}");
    }
}

/// What did not change: a string that closes inside the run keeps the
/// capital a token of its own (`T"x"`), which the glued one-letter rules
/// report, one error as in beancount; and a capital after a blank, or inside
/// a currency or an account, is no lone capital.
#[test]
fn test_parse_capital_glued_to_a_string_inside_its_run_is_unchanged() {
    for (src, want) in [
        (format!("{OPENS}T\"x\" 1\n"), vec![(3, 1)]),
        (
            format!("{OPENS}2024-01-02 T\"x\"\n  Assets:A  1 USD\n  Assets:B\n"),
            vec![(3, 1)],
        ),
    ] {
        assert_eq!(per_line(&src), want, "{src:?}");
    }
}
