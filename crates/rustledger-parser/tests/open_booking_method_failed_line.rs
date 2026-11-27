//! An `open` whose body holds a failed line reports no invalid booking
//! method, as in beancount (#2996).
//!
//! beancount checks the booking method in the grammar action that builds the
//! `open`. When a line under the `open` fails (an indented line that is no
//! `key: value`, a metadata line its grammar rejects, a date that is no
//! calendar date), the statement never reduces, so that check never runs and
//! the failed line's error is the only one. A blank line, even an indented
//! one, or a column-0 line ends the statement first: beancount then builds
//! the `open` and reports the booking method, so a failed line after one
//! leaves the error in place. Indented comment lines in between do not.
//!
//! A lowercase account component is reported either way: beancount checks
//! the account when it reads the token, before the statement fails.
//!
//! Every expected count below was checked against `bean-check` 3.2.3
//! (`beancount.parser.parser.parse_string`, the parity harness's ground
//! truth).

use rustledger_core::Directive;
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

fn assert_counts(cases: &[(String, Vec<(usize, usize)>)]) {
    for (src, expected) in cases {
        assert_eq!(&per_line(src), expected, "{src:?}");
    }
}

/// The issue's prefix: one open.
const P: &str = "2024-01-01 open Assets:A\n";
/// The issue's indented line with an invalid date.
const S: &str = "  2024-02-30 5\n";
/// An `open` with an invalid booking method.
const XYZ: &str = "2024-01-02 open Assets:B \"XYZ\"\n";

/// The issue's rows.
#[test]
fn test_parse_open_booking_method_then_failed_line_is_the_line_error() {
    assert_counts(&[
        // bean-check: 4.
        (
            format!("{P}2024-01-02 open Assets:B \"a\nb\"\n{S}"),
            vec![(4, 1)],
        ),
        // bean-check: 3.
        (format!("{P}{XYZ}{S}"), vec![(3, 1)]),
        // bean-check: 3.
        (format!("{P}{XYZ}  $x\n"), vec![(3, 1)]),
    ]);
}

/// The issue's controls: a body that is fine keeps the booking-method error.
#[test]
fn test_parse_open_booking_method_with_a_fine_body_keeps_its_error() {
    assert_counts(&[
        (format!("{P}{XYZ}"), vec![(2, 1)]),
        (format!("{P}{XYZ}  kk: \"v\"\n"), vec![(2, 1)]),
        (
            format!("{P}2024-01-02 open Assets:B \"a\nb\"\n"),
            vec![(2, 1)],
        ),
        (format!("{P}{XYZ}  kk: \"a\nb\"\n"), vec![(2, 1)]),
        (format!("{P}{XYZ}  ; c\n"), vec![(2, 1)]),
        // A valid booking method: only the line's error.
        (
            format!("{P}2024-01-02 open Assets:B \"FIFO\"\n{S}"),
            vec![(3, 1)],
        ),
    ]);
}

/// More failed lines: other indented lines, metadata lines the grammar
/// rejects, invalid dates in metadata, indented directives, and lines after
/// indented comments.
#[test]
fn test_parse_open_booking_method_then_other_failed_lines() {
    assert_counts(&[
        (format!("{P}{XYZ}  hh\n"), vec![(3, 1)]),
        (format!("{P}{XYZ}  hh"), vec![(3, 1)]),
        (format!("{P}{XYZ}  5\n"), vec![(3, 1)]),
        (format!("{P}{XYZ}  Assets:A 1 USD\n"), vec![(3, 1)]),
        (format!("{P}{XYZ}  #t\n"), vec![(3, 1)]),
        (
            format!("{P}{XYZ}  2024-01-03 open Assets:C\n"),
            vec![(3, 1)],
        ),
        (
            format!("{P}{XYZ}\t2024-01-03 open Assets:C\n"),
            vec![(3, 1)],
        ),
        (format!("{P}{XYZ}  2024-01-03 * \"x\"\n"), vec![(3, 1)]),
        (format!("{P}{XYZ}  kk: 2024-02-30\n"), vec![(3, 1)]),
        (format!("{P}{XYZ}  kk: 1 2\n"), vec![(3, 1)]),
        (format!("{P}{XYZ}  kk: USD EUR\n"), vec![(3, 1)]),
        (format!("{P}{XYZ}  kk: \"v\"\n  kk: 1 2\n"), vec![(4, 1)]),
        (format!("{P}{XYZ}  ; c\n  hh\n"), vec![(4, 1)]),
        (format!("{P}{XYZ}  kk: \"v\"\n  hh\n"), vec![(4, 1)]),
        (
            format!("{P}2024-01-02 open Assets:B USD,EUR \"XYZ\" ; c\n  hh\n"),
            vec![(3, 1)],
        ),
        (
            format!("{P}2024-01-02 open Assets:B USD \"XYZ\"\r\n  hh\r\n"),
            vec![(3, 1)],
        ),
    ]);
}

/// A blank line, an indented blank line or a column-0 line ends the
/// statement before the failed line: beancount builds the `open` and reports
/// its booking method. (beancount reports the failed line twice there,
/// bean-check `2 4x2`; that is not this issue.)
#[test]
fn test_parse_open_booking_method_then_line_after_the_statement_keeps_its_error() {
    assert_counts(&[
        (format!("{P}{XYZ}\n  hh\n"), vec![(2, 1), (4, 1)]),
        (format!("{P}{XYZ}  \n  hh\n"), vec![(2, 1), (4, 1)]),
        (format!("{P}{XYZ}\t\n  hh\n"), vec![(2, 1), (4, 1)]),
        (format!("{P}{XYZ}; c\n  hh\n"), vec![(2, 1), (4, 1)]),
        (
            format!("{P}{XYZ}  kk: \"v\"\n\n  hh\n"),
            vec![(2, 1), (5, 1)],
        ),
        // A doubled thousands separator is one number in beancount, which
        // builds the `open` (here it is an error of its own once the `open`
        // is kept, so it is left out of the rule).
        (format!("{P}{XYZ}  kk: 1,,000\n"), vec![(2, 1)]),
    ]);
}

/// A lowercase account component is reported with or without a failed line,
/// as beancount reports it (bean-check `2 3`, `2`).
#[test]
fn test_parse_open_lowercase_account_then_failed_line_keeps_both_errors() {
    assert_counts(&[
        (
            format!("{P}2024-01-02 open Assets:b \"XYZ\"\n{S}"),
            vec![(2, 1), (3, 1)],
        ),
        (
            format!("{P}2024-01-02 open Assets:b\n{S}"),
            vec![(2, 1), (3, 1)],
        ),
        (format!("{P}2024-01-02 open Assets:b\n"), vec![(2, 1)]),
    ]);
}

/// The `open` is kept without its booking method, as one with an invalid
/// token is, and no `InvalidBookingMethod` is reported.
#[test]
fn test_parse_open_booking_method_then_failed_line_keeps_the_open() {
    let src = format!("{P}{XYZ}{S}");
    let result = parse(&src);
    assert!(
        !result
            .errors
            .iter()
            .any(|e| matches!(e.kind, ParseErrorKind::InvalidBookingMethod(_))),
        "{:?}",
        result.errors
    );
    let opens: Vec<_> = result
        .directives
        .iter()
        .filter_map(|d| match &d.value {
            Directive::Open(o) => Some(o),
            _ => None,
        })
        .collect();
    assert_eq!(opens.len(), 2, "{opens:?}");
    assert_eq!(opens[1].account.as_ref(), "Assets:B");
    assert_eq!(opens[1].booking, None);
}

/// An invalid booking method is reported on the `open`'s own line, not on a
/// comment or blank line its node starts with after an earlier directive, as
/// in beancount (#2995's rule for directive-level errors).
#[test]
fn test_parse_open_booking_method_is_reported_on_the_open_line() {
    assert_counts(&[
        (format!("{P};c\n{XYZ}"), vec![(3, 1)]),
        (format!("{P}\n{XYZ}"), vec![(3, 1)]),
        (format!("{P}; a\n; b\n{XYZ}"), vec![(4, 1)]),
    ]);
}
