//! A column-0 dated line that opens no directive is one error, as in
//! beancount (#2979).
//!
//! When the token after a line's date is no directive keyword and no
//! transaction flag (a number, an account, a currency, ...), beancount reads
//! the date and fails at that token, and bison's recovery stays quiet about
//! the indented lines under it until its grammar has read three tokens again
//! (`quiet_after_failed_line_starts`). Each of those lines was an orphan
//! `unexpected input` here.
//!
//! Where bison would shift a declaration (a dated header after a blank, or an
//! undated declaration's keyword) its recovery ends and it builds that
//! declaration, which is not modeled: such a line starts no window, and a line
//! holding one ends a window before it, so the errors there stay as main
//! gives them (as they are in beancount for every shape tested below).
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

/// Two opens and a blank line, the start of most sources below, as in the
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

/// A declaration bison would shift on the dated line (a dated header after a
/// blank, an undated declaration's keyword, glued to punctuation too) starts
/// no window: the line and the lines under it keep their errors, as in
/// beancount for these shapes.
#[test]
fn test_parse_dated_line_shifted_declaration_starts_no_window() {
    assert_counts(&[
        (
            "2024-01-02 option \"a\" \"b\"\n  Assets:A 1 USD\n".to_string(),
            vec![(1, 1), (2, 1)],
        ),
        (
            "2024-01-02 include \"n\"\n  Assets:A 1 USD\n".to_string(),
            vec![(1, 1), (2, 1)],
        ),
        (
            "2024-01-02 plugin \"n\"\n  !\n".to_string(),
            vec![(1, 1), (2, 1)],
        ),
        (
            "2024-01-02 ~,option \"a\" \"b\"\n  Assets:A 1 USD\n".to_string(),
            vec![(1, 1), (2, 1)],
        ),
        ("2024-01-02 2024-01-03 open x\n".to_string(), vec![(1, 2)]),
        (
            "2024-01-02 2024-01-03 price USD x\n".to_string(),
            vec![(1, 2)],
        ),
        (
            "2024-01-02 2024-01-03 open ^l USD #t\n".to_string(),
            vec![(1, 1)],
        ),
        (
            "2024-01-02 $x #t 2024-1-3 open \"s\" Assets:Z @\n".to_string(),
            vec![(1, 1)],
        ),
        (
            "2024-01-02 2024-01-03 * \"n\"\n  k: \"abc\noption \"title\" \"x\"\n".to_string(),
            vec![(1, 1), (2, 1), (3, 1)],
        ),
        (
            format!("{OPENS}2024-01-02 2024-01-03 * \"n\"\n  k: \"abc\nx\n\"\n"),
            vec![(4, 1), (5, 1)],
        ),
    ]);
}

/// An invalid second date followed by a declaration bison shifts keeps the
/// line's error beside the date's: two, as in beancount.
#[test]
fn test_parse_dated_line_invalid_date_then_a_shifted_declaration() {
    let opens = "2024-01-01 open Assets:A\n2024-01-01 open Expenses:B\n";
    assert_counts(&[
        (
            format!("{opens}2024-01-02 2024-13-45 2024-01-04 open Assets:Q *\n"),
            vec![(3, 2)],
        ),
        (
            format!("{opens}2024-01-02 2024-02-30 2024-01-04 open Assets:Q \"x\"\n"),
            vec![(3, 2)],
        ),
        (
            "2024-01-02 2024-13-45 poptag #t\n".to_string(),
            vec![(1, 2)],
        ),
        (
            "2024-01-02 2024-02-30 * 2024-01-03 price A USD\n".to_string(),
            vec![(1, 2)],
        ),
    ]);
}

/// A line holding a declaration bison shifts ends the window before it, and
/// keeps its errors (the `open` after `custom "x" 1`; the `poptag` of a tag
/// never pushed).
#[test]
fn test_parse_dated_line_window_ends_at_a_shifted_declaration() {
    assert_counts(&[
        (
            "2024-01-02 123\n  ; c\n2024-01-03 , 2024-01-04 custom \"x\" 1 open Assets:Z\n"
                .to_string(),
            vec![(1, 1), (3, 1)],
        ),
        (
            "2024-01-02 123\n2024-01-03 2024-01-04 poptag #t\n".to_string(),
            vec![(1, 1), (2, 1)],
        ),
    ]);
}

/// The state of a `pushtag` left open at the end of the file is still
/// reported after a dated line.
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

/// A line a BOM starts inside a dated line's window starts its own window
/// there, under the BOM line's rules (#2956), which keep the line after it
/// quiet even when that line holds a declaration bison would shift.
#[test]
fn test_parse_dated_line_window_hands_over_to_a_bom_line() {
    let cases: Vec<(String, Vec<(usize, usize)>)> = [
        "  option \"a\" \"b\"",
        "  ~,option \"a\" \"b\"",
        "  2024-01-04 * \"x\"",
    ]
    .iter()
    .map(|third| {
        (
            format!("2024-01-02 123\n\u{feff}  Assets:A 1 USD\n{third}\n"),
            vec![(1, 1), (2, 1)],
        )
    })
    .collect();
    assert_counts(&cases);
}

/// A date alone on its line, where the window owes its last token, is a
/// date bison shifts: the window ends and the line keeps its error.
#[test]
fn test_parse_dated_line_lone_date_at_the_last_owed_token() {
    assert_counts(&[
        (
            "2024-01-02 123\n\n2024-01-02".to_string(),
            vec![(1, 1), (3, 1)],
        ),
        (
            "2024-01-02 123\n;c\n2024-01-02".to_string(),
            vec![(1, 1), (3, 1)],
        ),
        (
            "\n2024-01-02 { $x\n\n2024-01-02".to_string(),
            vec![(2, 2), (4, 1)],
        ),
    ]);
}

/// A BOM line's window is left as #2956 has it: a failed dated line inside it
/// is walked there, so its invalid second date, a declaration on it and the
/// lines after it count as before.
#[test]
fn test_parse_dated_line_inside_a_bom_window_is_unchanged() {
    let start = "; a\n\u{feff}x\n";
    assert_counts(&[
        (
            format!("{start}\n2024-01-02 2024-13-45 include \"x\"\n"),
            vec![(2, 1), (4, 1)],
        ),
        (
            format!("{start};c\n2024-01-02 2024-13-45 popmeta k:\n"),
            vec![(2, 1), (4, 2)],
        ),
        (
            format!("{start};c\n2024-01-02 $x pushmeta k: 1\n;c\n#comment\n"),
            vec![(2, 1), (4, 2)],
        ),
        (
            format!("{start};c\n2024-01-02 'x\n2024-01-02\n  ~,option \"a\" \"b\"\n"),
            vec![(2, 1), (4, 1)],
        ),
        (
            format!("{start};c\n2024-01-02 'x\n  k: 1\n  option \"a\" \"b\"\n"),
            vec![(2, 1), (4, 1), (5, 1)],
        ),
    ]);
}

/// A declaration bison shifts on an indented line in a dated line's window
/// is no error of its own, and ends the window: the line after it is
/// reported.
#[test]
fn test_parse_dated_line_indented_declaration_ends_the_window_after_it() {
    assert_counts(&[
        (
            "2024-01-02 'x\n2024-01-02\n  ~,option \"a\" \"b\"\n".to_string(),
            vec![(1, 1)],
        ),
        (
            "2024-01-02 123\n  ~,option \"a\" \"b\"\n  Assets:A 1 USD\n".to_string(),
            vec![(1, 1), (3, 1)],
        ),
    ]);
}

/// A date with a comment glued to it is alone on its line too.
#[test]
fn test_parse_dated_line_lone_date_with_a_glued_comment() {
    assert_counts(&[
        (
            "2024-01-02 123\n;c\n2024-01-02;c".to_string(),
            vec![(1, 1), (3, 1)],
        ),
        (
            "2024-01-02 123\n;c\n2024-01-02%x".to_string(),
            vec![(1, 1), (3, 1)],
        ),
    ]);
}

/// After a line with an error of its own, which beancount may report on the
/// dated line (a flag-only posting `  !`), the dated line keeps both its
/// errors: two there, as beancount counts that line.
#[test]
fn test_parse_dated_line_invalid_second_date_after_an_error_line() {
    let src = "2024-01-02 * \"x\"\n  !\n2024-01-02 2024-02-30 \"n\"\n";
    let counts = per_line(src);
    assert!(counts.contains(&(3, 2)), "{counts:?}");
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
