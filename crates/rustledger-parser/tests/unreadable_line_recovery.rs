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

/// A line holding a stray `\r` (one not right before a `\n`) is read here in
/// ways that differ from beancount's by context (`\r;c` is an error here, a
/// blank line there, a pre-existing difference): it starts no window, ends one
/// before it, and counts as a failed line when deciding whether the line after
/// it starts one. So every line around it keeps its errors, as main gives them.
#[test]
fn test_parse_stray_cr_lines_keep_their_errors() {
    assert_counts(&[
        ("\r;c\n02\n".to_string(), vec![(1, 1), (2, 1)]),
        ("\r;c\r\n02\r\n".to_string(), vec![(1, 1), (2, 1)]),
        ("\r;c\n-\n".to_string(), vec![(1, 1), (2, 1)]),
        ("\r;c\n  Assets:A 1 USD\n".to_string(), vec![(1, 1), (2, 1)]),
        (
            "\r;c\n\r;c\n  Assets:A 1 USD\n".to_string(),
            vec![(1, 1), (2, 1), (3, 1)],
        ),
        // beancount: the `!x` line is a comment, and the indented line after
        // it is reported (#2993's model, which reads beancount's own tokens).
        (
            "#tag\n \r;c\n!x\n  #tag\n".to_string(),
            vec![(1, 1), (4, 1)],
        ),
        // Unchanged neighbors.
        ("\r\n02\n".to_string(), vec![(2, 1)]),
        ("\r$\n  Assets:A 1 USD\n".to_string(), vec![(1, 1), (2, 1)]),
        (" \r;c\n02\n".to_string(), vec![(1, 1), (2, 1)]),
        ("\t\r;c\n02\n".to_string(), vec![(1, 1), (2, 1)]),
        // A stray `\r` mid-line (beancount: one error fewer, or the same).
        ("option \r;c\n#\n".to_string(), vec![(1, 1), (2, 1)]),
        ("option \r;c\n-\n".to_string(), vec![(1, 1), (2, 1)]),
        ("include \r;c\n-\n".to_string(), vec![(1, 1), (2, 1)]),
        (
            "option \"a\" \"b\"\r;c\n-\n".to_string(),
            vec![(1, 1), (2, 1)],
        ),
        ("2024-01-02\r;c\n-01\n".to_string(), vec![(1, 1), (2, 1)]),
        (
            "pushtag \r;c\n{\nx\n".to_string(),
            vec![(1, 1), (2, 1), (3, 1)],
        ),
        (
            "poptag\t\r#c\nAssets:A #\n".to_string(),
            vec![(1, 1), (2, 1)],
        ),
        (
            "\npoptag\t\r\t#t\n  *USD#t-02\n".to_string(),
            vec![(2, 1), (3, 1)],
        ),
        (
            "   \r;cinclude\t1.5\t-01\npushmeta  \r;c\n  }#\n  \r\r\n".to_string(),
            vec![(1, 1), (2, 1), (3, 1)],
        ),
        (
            "2024-01-02 open Assets:A\r;c\n-\n".to_string(),
            vec![(1, 1), (2, 1)],
        ),
        // No stray `\r` (`\r\n` ends a line): the `#` line is inside bison's
        // recovery from the `option` line's end, as in beancount (#2993).
        ("option \r\n#\n".to_string(), vec![(1, 1)]),
        ("option ;c\n#\n".to_string(), vec![(1, 1)]),
        ("option\n#\n".to_string(), vec![(1, 1)]),
        ("x\r\n-\n".to_string(), vec![(1, 1)]),
    ]);
}

/// Shapes #2993 part A left at main's count, which the token-level model of
/// part B (`cst/recovery.rs`) reads as beancount does: a line holding a date
/// or an undated keyword (where bison may end its recovery), a line right
/// after another failed line, a line a BOM or a date starts, and an indented
/// line after a failed header with a blank line between.
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
        // Modeled since #2993's general model (`cst/recovery.rs`), each as
        // beancount counts it: the date bison shifts mid-line, the pipe it
        // reports once its recovery is over, the entry it builds there.
        (
            "AB-C\nkey:2024/01/03  P | 1\n".to_string(),
            vec![(1, 1), (2, 2)],
        ),
        (
            format!("{O2}$ 2024-01-02 * \"y\"\n  Assets:A 1 USD\n"),
            vec![(3, 1)],
        ),
        (
            format!("{O2}$\n  Assets:A 1 USD 2024-01-02\n"),
            vec![(3, 1)],
        ),
        (
            format!("{O2}$\n2024-01-02 123\n  Assets:A 1 USD\n"),
            vec![(3, 1)],
        ),
        (format!("{P}pushtag #a $\n\n{S}"), vec![(2, 1), (4, 1)]),
    ]);
}

/// A string left unclosed to the end of the input on an unreadable or
/// undated line runs, in beancount's lexer, to the end of the file, so
/// beancount reports only that line. Here the string is cut at its line, and
/// the line starts a window that quiets the lines after it the same way.
#[test]
fn test_parse_lines_after_a_string_unclosed_to_the_end_are_quiet() {
    let cases = [(
        "2024-01-01 open Assets:A\noption \"abc\n)\n)\n2024-01-01 open Assets:B\n".to_string(),
        vec![(2, 1)],
    )];
    assert_counts(&cases);
}
