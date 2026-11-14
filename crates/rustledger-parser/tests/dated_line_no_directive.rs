//! A column-0 dated line that opens no directive is one error, as in
//! beancount (#2979).
//!
//! When the token after a line's date is no directive keyword and no
//! transaction flag (a second date, a number, an account, a currency, ...),
//! beancount reads the date and fails at that token, and bison's recovery
//! stays quiet about the indented lines under it until its grammar has read
//! three tokens again (`quiet_after_failed_line_starts`). Each of those lines
//! was an orphan `unexpected input` here. When the line holds a transaction's
//! header after a blank (`2024-01-02 2024-01-03 * "n"`), bison shifts that
//! header and builds the transaction, so the lines under it are its body and
//! count as a transaction's body does.
//!
//! Every expected count below was checked against `bean-check` 3.2.3.

use rustledger_parser::cst::parse_red_only;
use rustledger_parser::{ParseErrorKind, parse};

/// The errors of `src` per line (1-based, counting `\n` only, as
/// `rledger check` does): `(line, count)`, in line order. The green and the
/// red converter agree on them.
fn per_line(src: &str) -> Vec<(usize, usize)> {
    let count = |errors: &[rustledger_parser::ParseError]| {
        let mut counts: Vec<(usize, usize)> = Vec::new();
        for e in errors {
            let line = 1 + src[..e.span.start].matches('\n').count();
            match counts.iter_mut().find(|(l, _)| *l == line) {
                Some((_, n)) => *n += 1,
                None => counts.push((line, 1)),
            }
        }
        counts.sort_unstable();
        counts
    };
    let green = count(&parse(src).errors);
    assert_eq!(green, count(&parse_red_only(src).errors), "{src:?}");
    green
}

/// Two opens and a blank line, the start of every source below, as in the
/// issue: the dated line is line 4.
const OPENS: &str = "2024-01-01 open Assets:A\n2024-01-01 open Expenses:B\n\n";

/// Two postings, the body under each dated line below.
const POSTINGS: &str = "  Assets:A  -1 USD\n  Expenses:B  1 USD\n";

fn assert_counts(cases: &[(String, Vec<(usize, usize)>)]) {
    for (src, expected) in cases {
        assert_eq!(&per_line(src), expected, "{src:?}");
    }
}

/// The issue's rows: the dated line is the one error, its postings none.
#[test]
fn test_parse_dated_line_opening_no_directive_quiets_its_postings() {
    let cases: Vec<(String, Vec<(usize, usize)>)> = [
        "2024-01-02 2024-01-03 * \"n\"",
        "2024-01-02 2024-01-03 \"n\"",
        "2024-01-02 123 * \"n\"",
        "2024-01-02 Assets:A * \"n\"",
        "2024-01-02 USD * \"n\"",
    ]
    .iter()
    .map(|head| (format!("{OPENS}{head}\n{POSTINGS}"), vec![(4, 1)]))
    .collect();
    assert_counts(&cases);
}

/// An invalid date right after the line's date is where beancount's grammar
/// fails, so the date's error is the line's one error (the issue's last row,
/// reported twice here before).
#[test]
fn test_parse_dated_line_invalid_second_date_is_one_error() {
    assert_counts(&[
        (
            format!("{OPENS}2024-01-02 2024-13-45 \"n\"\n{POSTINGS}"),
            vec![(4, 1)],
        ),
        (format!("{OPENS}2024-01-02 2024-02-30\n"), vec![(4, 1)]),
    ]);
}

/// The lexer's own errors under the line are still reported: beancount
/// reads `k:` as an invalid token and builds dates in its lexer.
#[test]
fn test_parse_dated_line_keeps_lexer_errors_under_it() {
    assert_counts(&[
        (
            format!("{OPENS}2024-01-02 123\n  k: \"v\"\n{POSTINGS}"),
            vec![(4, 1), (5, 1)],
        ),
        (
            format!("{OPENS}2024-01-02 123\n  2024-02-30 5\n{POSTINGS}"),
            vec![(4, 1), (5, 1)],
        ),
    ]);
}

/// CRLF line endings, tab indentation and a body that ends the file read the
/// same, and the quiet ends at the next directive.
#[test]
fn test_parse_dated_line_variants() {
    assert_counts(&[
        (
            format!("{OPENS}2024-01-02 123 * \"n\"\n{POSTINGS}").replace('\n', "\r\n"),
            vec![(4, 1)],
        ),
        (
            format!("{OPENS}2024-01-02 123 * \"n\"\n\tAssets:A  -1 USD\n\tExpenses:B  1 USD\n"),
            vec![(4, 1)],
        ),
        (
            format!("{OPENS}2024-01-02 123 * \"n\"\n  Assets:A  -1 USD"),
            vec![(4, 1)],
        ),
        // The orphan posting after the `close` is reported again.
        (
            format!(
                "{OPENS}2024-01-02 123\n{POSTINGS}2024-01-05 close Assets:A\n  Assets:A 1 USD\n"
            ),
            vec![(4, 1), (8, 1)],
        ),
    ]);
}

/// A transaction header after the line's date is the one beancount builds:
/// the lines under it are its body, so a line no transaction takes is an
/// error (`  "s"`), postings are none, and the body ends at a blank or
/// column-0 line, after which an indented line is an error again.
#[test]
fn test_parse_dated_line_resynchronized_transaction_body() {
    assert_counts(&[
        (
            format!("{OPENS}2024-01-02 2024-01-03 * \"n\"\n  \"s\"\n  Assets:A  -1 USD\n"),
            vec![(4, 1), (5, 1)],
        ),
        (
            format!("{OPENS}2024-01-02 2024-01-03 * \"n\"\n* h\n  Assets:A  -1 USD\n"),
            vec![(4, 1), (6, 1)],
        ),
        (
            format!(
                "{OPENS}2024-01-02 2024-01-03 * \"n\"\n  Assets:A  -1 USD\n\n  Expenses:B  1 USD\n"
            ),
            vec![(4, 1), (7, 1)],
        ),
    ]);
}

/// A dated line that opens no directive starts with a date bison shifts: in
/// the window after a failed line, when that date is the last token owed,
/// the line is reported (after a skipped comment line), and otherwise it is
/// quiet too (right after a failed line).
#[test]
fn test_parse_dated_line_in_a_recovery_window() {
    assert_counts(&[
        (
            format!("{OPENS}2024-01-02 USD\n;c\n2024-01-05 2024-01-06\n  Assets:A  1 USD\n"),
            vec![(4, 1), (6, 1)],
        ),
        (
            format!("{OPENS}2024-01-02 123\n2024-01-03 456\n  Assets:A  1 USD\n"),
            vec![(4, 1)],
        ),
    ]);
}

/// The state of a `pushtag` left open at the end of the file is still
/// reported after a resynchronized transaction's body, whose comment line its
/// error's span takes in.
#[test]
fn test_parse_dated_line_keeps_unclosed_pushtag() {
    let src = format!("{OPENS}2024-01-02 2024/01/03 *\n  ; c\npushtag #a");
    let errors = parse(&src).errors;
    assert_eq!(errors.len(), 2, "{errors:?}");
    assert!(
        errors
            .iter()
            .any(|e| matches!(e.kind, ParseErrorKind::UnclosedPushtag(_))),
        "{errors:?}"
    );
}

/// Directives that do open stay as they were: no errors.
#[test]
fn test_parse_dated_line_directives_unchanged() {
    assert_counts(&[
        (format!("{OPENS}2024-01-02 * \"n\"\n{POSTINGS}"), vec![]),
        (
            format!("{OPENS}2024-01-02 open Assets:Z\n2024-01-03 close Assets:Z\n"),
            vec![],
        ),
    ]);
}
