//! A syntax error at a string that runs over line ends is reported on the
//! line the string ends, as beancount does (#2994).
//!
//! bison reports a syntax error at the lexer's current line, which is where
//! its lookahead token ends: for a multi-line `STRING`, its last line. The
//! parser started such an error at the string, so it was reported on the
//! string's first line. It now starts on the string's last line, so every
//! surface that maps an error's span to a line agrees with beancount.
//!
//! Not moved: an error on an indented line after a gap (a blank line, the top
//! of the file), where beancount fails at the indent, on the line the string
//! starts; and the errors beancount's builder raises for a statement it has
//! reduced, on the statement's first line (too many strings on a transaction
//! header, an invalid booking method).
//!
//! Also here: a column-0 line that fails and holds a multi-line string ends
//! where the string does, so the lines after it are as quiet as after any
//! other failed line, and a header's grammar error before an invalid date on
//! a string's last line is the date's, as when both are on one line.
//!
//! Every expected count below was checked against `bean-check` 3.2.3
//! (`beancount.parser.parser.parse_string`, the parity harness's ground
//! truth), except where a comment names a difference.

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

/// The issue's prefix: one open.
const P: &str = "2024-01-01 open Assets:A\n";
/// The issue's indented line with an invalid date.
const S: &str = "  2024-02-30 5\n";

/// The issue's rows.
#[test]
fn test_parse_multi_line_string_error_is_on_its_last_line() {
    assert_counts(&[
        // bean-check: 3 4.
        (format!("{P}\"a\nb\"\n{S}"), vec![(3, 1), (4, 1)]),
        // bean-check: 3.
        (format!("{P}\"a\nb\"\n"), vec![(3, 1)]),
        // bean-check: 4 5.
        (format!("{P}\"a\nb\nc\"\n{S}"), vec![(4, 1), (5, 1)]),
        // bean-check: 4 5.
        (
            format!("{P}option \"title\" \"a\nb\" \"c\nd\"\n{S}"),
            vec![(4, 1), (5, 1)],
        ),
    ]);
}

/// The string in other places: undated and dated directives, transaction
/// headers, postings, cost specs and metadata values.
#[test]
fn test_parse_multi_line_string_error_in_each_position() {
    assert_counts(&[
        (
            r#""a
b" "c
d"
"#
            .to_string(),
            vec![(2, 1)],
        ),
        // The invalid token after the string is on the string's last line.
        ("\"a\nb\" foo\n".to_string(), vec![(2, 2)]),
        (
            "2024-01-01 note Assets:A \"a\nb\" \"c\nd\"\n".to_string(),
            vec![(3, 1)],
        ),
        // A `note` with no account: its header fails at the string.
        ("2024-01-01 note \"a\nb\"\n".to_string(), vec![(2, 1)]),
        (
            "2024-01-01 event \"a\nb\" \"c\nd\" \"e\nf\"\n".to_string(),
            vec![(4, 1)],
        ),
        (
            "2024-01-01 query \"a\nb\" \"c\nd\" \"e\nf\"\n".to_string(),
            vec![(4, 1)],
        ),
        (
            "2024-01-01 balance Assets:A 1 USD \"a\nb\"\n".to_string(),
            vec![(2, 1)],
        ),
        ("include \"a\nb\" \"c\nd\"\n".to_string(), vec![(3, 1)]),
        (
            "plugin \"a\nb\" \"c\nd\" \"e\nf\"\n".to_string(),
            vec![(4, 1)],
        ),
        ("pushtag \"a\nb\"\n".to_string(), vec![(2, 1)]),
        ("poptag \"a\nb\"\n".to_string(), vec![(2, 1)]),
        // A string after a tag on a transaction header.
        (
            "2024-01-01 * \"a\nb\" \"n\" #t \"c\nd\"\n".to_string(),
            vec![(3, 1)],
        ),
        // In a transaction body: a posting's place, an amount's, a price's
        // and a cost's.
        ("2024-01-01 * \"n\"\n  \"a\nb\"\n".to_string(), vec![(3, 1)]),
        (
            "2024-01-01 * \"a\nb\" \"c\nd\"\n  Assets:A \"e\nf\"\n".to_string(),
            vec![(5, 1)],
        ),
        (
            "2024-01-01 * \"n\"\n  Assets:A 1 USD @ \"a\nb\"\n".to_string(),
            vec![(3, 1)],
        ),
        (
            "2024-01-01 * \"n\"\n  Assets:A 1 USD {1 USD, \"a\nb\" \"c\nd\"}\n".to_string(),
            vec![(4, 1)],
        ),
        // A metadata value with a second string after it.
        (format!("{P}  kk: \"a\nb\" \"c\nd\"\n"), vec![(4, 1)]),
        (
            "2024-01-01 * \"p\" \"n\"\n  kk: \"a\nb\" \"c\nd\"\n".to_string(),
            vec![(4, 1)],
        ),
        ("pushmeta kk: \"a\nb\" \"c\nd\"\n".to_string(), vec![(3, 1)]),
        // An indented string under a directive and under its value.
        (format!("{P}  \"a\nb\"\n"), vec![(3, 1)]),
        (
            "2024-01-01 note Assets:A \"a\nb\"\n  \"c\nd\"\n".to_string(),
            vec![(4, 1)],
        ),
        // `custom` takes any number of strings: only a token after them fails.
        (
            "2024-01-01 custom \"a\nb\" \"c\nd\" 5 USD\n".to_string(),
            vec![],
        ),
        (
            "2024-01-01 custom \"a\nb\" \"c\nd\" foo\n".to_string(),
            vec![(3, 1)],
        ),
    ]);
}

/// Where beancount's grammar fails at the indent, not at the string, the
/// error stays on the string's first line: an indented line at the top of the
/// file or after a blank line. An indented comment line continues the
/// directive above.
#[test]
fn test_parse_multi_line_string_after_a_gap_stays_at_the_indent() {
    assert_counts(&[
        ("  \"a\nb\"\n".to_string(), vec![(1, 1)]),
        (format!("{P}\n  \"a\nb\"\n"), vec![(3, 1)]),
        (format!("{P}  ; c\n  \"a\nb\"\n"), vec![(4, 1)]),
    ]);
}

/// Errors beancount's builder raises for a statement it has reduced are on
/// the statement's first line, whatever strings come before.
#[test]
fn test_parse_multi_line_string_builder_errors_stay_on_the_first_line() {
    assert_counts(&[
        // Too many strings on a transaction header.
        (
            "2024-01-01 * \"a\nb\" \"c\nd\" \"e\nf\"\n".to_string(),
            vec![(1, 1)],
        ),
        (
            "2024-01-01 * \"a\nb\" \"c\" \"d\"\n".to_string(),
            vec![(1, 1)],
        ),
        (
            "2024-01-01 * \"n\" \"a\nb\" \"c\"\n".to_string(),
            vec![(1, 1)],
        ),
        // An invalid booking method.
        (
            "2024-01-01 open Assets:A \"a\nb\"\n".to_string(),
            vec![(1, 1)],
        ),
    ]);
}

/// An invalid date on a string's last line, where the header's grammar
/// fails, is the line's one error, as when it is on the header's own line.
#[test]
fn test_parse_multi_line_string_then_invalid_date_is_one_error() {
    assert_counts(&[
        (
            "2024-01-01 event \"a\" 2024-02-30\n".to_string(),
            vec![(1, 1)],
        ),
        (
            "2024-01-01 event \"a\nb\" 2024-02-30\n".to_string(),
            vec![(2, 1)],
        ),
    ]);
}

/// A column-0 line that fails and holds a multi-line string ends on the
/// string's last line: the indented lines after it are as quiet as after any
/// other failed line, and so is a line inside the recovery from one before.
#[test]
fn test_parse_multi_line_string_failed_line_quiets_the_lines_after_it() {
    assert_counts(&[
        ("\"a\"\n  kk: 5\n  kk: 6\n".to_string(), vec![(1, 1)]),
        ("\"a\nb\"\n  kk: 5\n  kk: 6\n".to_string(), vec![(2, 1)]),
        ("\"a\nb\"\n\n  kk: 5\n".to_string(), vec![(2, 1)]),
        ("$ \"c\nd\"\n  kk: 5\n  kk: 6\n".to_string(), vec![(1, 1)]),
        ("\"a\nb\" $\n  kk: 5\n".to_string(), vec![(2, 2)]),
        ("r\n\"a\nb\"\n".to_string(), vec![(1, 1)]),
        ("$\n\"a\nb\"\n  kk: 5\n".to_string(), vec![(1, 1)]),
    ]);
}

/// CRLF line endings, a BOM, and strings left open to the end of the input.
#[test]
fn test_parse_multi_line_string_crlf_bom_and_unclosed() {
    assert_counts(&[
        (
            "2024-01-01 open Assets:A\r\n\"a\r\nb\"\r\n".to_string(),
            vec![(3, 1)],
        ),
        (
            "2024-01-01 note Assets:A \"a\r\nb\" \"c\"\r\n".to_string(),
            vec![(2, 1)],
        ),
        (format!("\u{feff}{P}\"a\nb\"\n"), vec![(3, 1)]),
        (format!("{P}\"a\nb\" \u{feff}\n"), vec![(3, 2)]),
        // Unclosed: beancount reports the line it starts on and the next.
        (
            "2024-01-01 note Assets:A \"a\nb\n".to_string(),
            vec![(1, 1), (2, 1)],
        ),
        ("\"a\nb".to_string(), vec![(1, 1), (2, 1)]),
    ]);
}

/// A known difference, the same on one line: an error at the end of a line
/// (`unexpected EOL`) is reported on the line it ends, where beancount
/// reports it on the next. With a multi-line string last, the line it ends is
/// the string's last.
#[test]
fn test_parse_multi_line_string_end_of_line_error_on_the_line_it_ends() {
    assert_counts(&[
        // bean-check: 2.
        ("option \"a\"\n".to_string(), vec![(1, 1)]),
        // bean-check: 3.
        ("option \"a\nb\"\n".to_string(), vec![(2, 1)]),
        // bean-check: 3.
        ("2024-01-01 event \"a\nb\"\n".to_string(), vec![(2, 1)]),
    ]);
}

/// The span still covers the string's last line, up to its end, so the
/// message that names the string points at it.
#[test]
fn test_parse_multi_line_string_error_span_is_its_last_line() {
    let src = format!("{P}option \"title\" \"a\nb\" \"c\nd\"\n");
    let errors = parse(&src).errors;
    assert_eq!(errors.len(), 1, "{errors:?}");
    let e = &errors[0];
    assert_eq!(&src[e.span.start..e.span.start + 2], "d\"", "{e:?}");
    assert!(e.message().contains("c\\nd"), "{}", e.message());
}
