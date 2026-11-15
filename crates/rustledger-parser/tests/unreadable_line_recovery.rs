//! A column-0 line beancount cannot read keeps the lines after it as quiet as
//! beancount keeps them (#2993, part A).
//!
//! beancount's grammar has one error rule, `declarations: declarations
//! error`. After a statement fails, bison discards every token but one a
//! `declarations` can take next (an end of line, a date, an undated
//! declaration's keyword) and reports no syntax error until it has shifted
//! three tokens. So after a line whose statement fails (a line whose first
//! token it cannot read, `$`, `2<BOM>?02`; a marker alone on its line, `!`;
//! an undated declaration holding an invalid token, `pushmeta k: "v"`), the
//! lines after it report only the lexer's own errors until that window ends.
//! `quiet_after_failed_line_starts` models it for these lines with the rules
//! of a dated line's window (#2979).
//!
//! Where a line in the window holds a date or an undated keyword, bison
//! shifts it and may end its recovery inside the line, which is not modeled:
//! such a line keeps its errors, as main gives them. So does a line right
//! after another failed line, where beancount may still be recovering from
//! that one. The tests pin those shapes at main's count.
//!
//! Every expected count below was checked against `bean-check` 3.2.3.

use rustledger_parser::cst::parse_red_only;
use rustledger_parser::parse;

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

fn assert_counts(cases: &[(String, Vec<(usize, usize)>)]) {
    for (src, expected) in cases {
        assert_eq!(&per_line(src), expected, "{src:?}");
    }
}

/// One open, the prefix of the issue's marker rows.
const P: &str = "2024-01-01 open Assets:A\n";
/// Two opens.
const O2: &str = "2024-01-01 open Assets:A\n2024-01-01 open Assets:B\n";
/// An indented invalid date, whose own (lexer) error beancount reports.
const S: &str = "  2024-02-30 5\n";
const BOM: &str = "\u{feff}";

/// The issue's rows: bare markers in a row are one error, the first.
#[test]
fn test_parse_marker_lines_after_a_marker_line_are_quiet() {
    assert_counts(&[
        (format!("{P}!\n!\n{S}"), vec![(2, 1), (4, 1)]),
        (format!("{P}*\n:\n{S}"), vec![(2, 1), (4, 1)]),
        (format!("{P}!\n!\n!\n"), vec![(2, 1)]),
        (format!("{P}#\n#\n"), vec![(2, 1)]),
        (format!("{P}!\n!\n2024-01-02 open Assets:B\n"), vec![(2, 1)]),
        // Control: one marker line, then a directive.
        (format!("{P}!\n2024-01-02 open Assets:B\n"), vec![(2, 1)]),
    ]);
}

/// The issue's comment rows: an invalid run right after a line beancount
/// cannot read is the run's own error alone, where the grammar error beside
/// it was one more.
#[test]
fn test_parse_invalid_run_after_an_unreadable_line_is_one_error() {
    assert_counts(&[
        (format!("$\n2{BOM}?02"), vec![(1, 1), (2, 1)]),
        (format!("$\n2{BOM}?02\n"), vec![(1, 1), (2, 1)]),
        (format!("$\r\n2{BOM}?02\r\n"), vec![(1, 1), (2, 1)]),
        (format!("1-2-3#x\n2{BOM}?02"), vec![(1, 1), (2, 1)]),
        (
            format!("{O2}pushmeta k: \"v\"\n2{BOM}024-01-02 close Assets:A\npopmeta k:\n"),
            vec![(3, 1), (4, 1), (5, 1)],
        ),
        (
            format!("{O2}pushmeta k: \"v\"\n2$024-01-02 close Assets:A\npopmeta k:\n"),
            vec![(3, 1), (4, 1), (5, 1)],
        ),
    ]);
}

/// The postings and metadata under a line beancount cannot read are no
/// errors of their own: bison discards them in its recovery.
#[test]
fn test_parse_lines_under_an_unreadable_line_are_quiet() {
    assert_counts(&[
        (
            format!("{O2}$\n  Assets:A  1 USD\n  Assets:B  -1 USD\n"),
            vec![(3, 1)],
        ),
        (
            format!("{O2}$\n  Assets:A  1 USD\n  Assets:B  -1 USD\n").replace('\n', "\r\n"),
            vec![(3, 1)],
        ),
        (
            format!("{O2}'Z\n  k: \"v\"\n  Assets:A 1 USD\n"),
            vec![(3, 1), (4, 1)],
        ),
        // The window ends after two blank or skipped lines, or at a
        // directive; an invalid token's own error stays inside it.
        (format!("{O2}$\n\nx\n"), vec![(3, 1), (5, 1)]),
        (format!("{O2}$\n\n\nx\n"), vec![(3, 1), (6, 1)]),
        (format!("{O2}$\n; c\nx\n"), vec![(3, 1), (5, 1)]),
        (
            format!("{O2}$\nx\n2024-01-02 close Assets:A\nx\n"),
            vec![(3, 1), (4, 1), (6, 1)],
        ),
        ("$\nx".to_string(), vec![(1, 1), (2, 1)]),
    ]);
}

/// A stray `\r` before a comment (`\r;c`) is a blank line to beancount, though
/// this parser reports an error there (a pre-existing difference): it starts
/// no window, is no line with tokens inside one, and is looked past, so the
/// line after it keeps its errors, as main gives them. beancount reports one
/// error fewer on each (the `\r;c` line's).
#[test]
fn test_parse_stray_cr_before_a_comment_starts_no_window() {
    assert_counts(&[
        ("\r;c\n02\n".to_string(), vec![(1, 1), (2, 1)]),
        ("\r;c\r\n02\r\n".to_string(), vec![(1, 1), (2, 1)]),
        ("\r;c\n-\n".to_string(), vec![(1, 1), (2, 1)]),
        ("\r;c\n  Assets:A 1 USD\n".to_string(), vec![(1, 1), (2, 1)]),
        (
            "\r;c\n\r;c\n  Assets:A 1 USD\n".to_string(),
            vec![(1, 1), (2, 1), (3, 1)],
        ),
        (
            "#tag\n \r;c\n!x\n  #tag\n".to_string(),
            vec![(1, 1), (2, 1), (4, 1)],
        ),
        // Unchanged neighbors.
        ("\r\n02\n".to_string(), vec![(2, 1)]),
        ("\r$\n  Assets:A 1 USD\n".to_string(), vec![(1, 1), (2, 1)]),
        (" \r;c\n02\n".to_string(), vec![(1, 1), (2, 1)]),
        ("\t\r;c\n02\n".to_string(), vec![(1, 1), (2, 1)]),
    ]);
}

/// Shapes the window does not model keep main's count: a line holding a date
/// or an undated keyword (bison may end its recovery there), a line right
/// after another failed line, a line a BOM or a date starts (their own
/// windows), and an indented line after a failed header with a blank line
/// between (#2993's part B).
#[test]
fn test_parse_unmodeled_recovery_shapes_keep_their_errors() {
    assert_counts(&[
        // beancount 1 and 2 errors; main and here the same.
        ("$\n\t1poptag #t\n".to_string(), vec![(1, 1), (2, 1)]),
        (
            format!("{O2}{{ 2024-13-45  ^l Assets:A\n\t1poptag #t\n"),
            vec![(3, 2), (4, 1)],
        ),
        (
            format!("{O2}$ option \"t\" \"x\"\n  Assets:A 1 USD\n"),
            vec![(3, 1), (4, 1)],
        ),
        (
            format!("{P}2024-01-02 open Assets:B $\n$\nx\n"),
            vec![(2, 1), (3, 1), (4, 1)],
        ),
        (
            format!("{O2}$\n{BOM}x\n  Assets:A 1 USD\n"),
            vec![(3, 1), (4, 1)],
        ),
        (format!("{P}pushtag #a $\nx\n"), vec![(2, 1), (3, 1)]),
        // beancount differs (1 error fewer, or its count elsewhere); kept as
        // main has them, not modeled.
        (
            "AB-C\nkey:2024/01/03  P | 1\n".to_string(),
            vec![(1, 1), (2, 1)],
        ),
        (
            format!("{O2}$ 2024-01-02 * \"y\"\n  Assets:A 1 USD\n"),
            vec![(3, 1), (4, 1)],
        ),
        (
            format!("{O2}$\n  Assets:A 1 USD 2024-01-02\n"),
            vec![(3, 1), (4, 1)],
        ),
        (
            format!("{O2}$\n2024-01-02 123\n  Assets:A 1 USD\n"),
            vec![(3, 1), (4, 1)],
        ),
        (format!("{P}pushtag #a $\n\n{S}"), vec![(2, 1), (4, 2)]),
    ]);
}
