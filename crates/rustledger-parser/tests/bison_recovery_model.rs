//! bison's error recovery, modeled on beancount's own tokens (#2993 part B,
//! #2979, and the shapes #2872's earlier rounds left).
//!
//! beancount's grammar has one error rule, `declarations: declarations
//! error`. After a statement fails, bison reports no syntax error until it
//! has shifted three tokens again: it discards every token a `declarations`
//! cannot start with (an indented line is discarded to its end), shifts an
//! end of line, a date or an undated keyword, and its lexer still reports
//! every invalid token, invalid date and malformed number.
//! `cst/recovery.rs` runs that machine over a port of beancount's lexer and
//! keeps, on each line inside the window, as many of rledger's errors as
//! beancount's lexer finds there.
//!
//! Every expected count below was checked against `bean-check` 3.2.3
//! (`beancount.parser.parser.parse_string`), with one deliberate difference
//! the parity harness also normalizes: a syntax error at an end of line is
//! reported by beancount on the NEXT line, and by rledger on the line whose
//! statement fails there.

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

/// One open, the prefix of the issue's rows.
const P: &str = "2024-01-01 open Assets:A\n";
/// An indented invalid date, whose own (lexer) error beancount reports.
const S: &str = "  2024-02-30 5\n";
/// A transaction header.
const T: &str = "2024-01-02 * \"n\"\n";

/// #2993 part B: a header that fails, a blank line, then an indented line.
/// The blank line is one shift of the three, so the indented line is still
/// inside the window: only its invalid date is reported.
#[test]
fn test_parse_indented_line_after_a_failed_header_and_a_blank_line_is_quiet() {
    assert_counts(&[
        (format!("{P}pushtag #a $\n\n{S}"), vec![(2, 1), (4, 1)]),
        (
            format!("{P}pushtag #a 2024-02-30\n\n{S}"),
            vec![(2, 1), (4, 1)],
        ),
        (
            format!("{P}option \"title\" \"x\" $\n\n{S}"),
            vec![(2, 1), (4, 1)],
        ),
        (
            format!("{P}pushmeta kk: \"v\" x\n\n{S}"),
            vec![(2, 1), (4, 1)],
        ),
        (format!("{P}poptag #a $\n\n{S}"), vec![(2, 1), (4, 1)]),
        (
            format!("{P}2024-01-02 open Assets:B $\n\n{S}"),
            vec![(2, 1), (4, 1)],
        ),
        // Control: no blank line.
        (format!("{P}pushtag #a $\n{S}"), vec![(2, 1), (3, 1)]),
        // Two blank lines: three shifts with the header's end of line, so
        // the indented line is reported, its indent and its date.
        (format!("{P}pushtag #a $\n\n\n{S}"), vec![(2, 1), (5, 2)]),
    ]);
}

/// #2993 part B: an unterminated string, then a comment line, then an
/// indented line. The comment line is an end of line, one shift.
#[test]
fn test_parse_indented_line_after_an_unterminated_string_and_a_comment_is_quiet() {
    assert_counts(&[
        (format!("{P}\"abc\n;x\n{S}"), vec![(2, 1), (4, 1)]),
        (
            format!("{P}2024-01-02 * \"abc\n;x\n{S}"),
            vec![(2, 1), (4, 1)],
        ),
        // Control: no comment line.
        (format!("{P}\"abc\n{S}"), vec![(2, 1), (3, 1)]),
    ]);
}

/// #2993 part B: a header that fails at its end of line. The indented line
/// after it is inside the window: no error of its own. beancount reports the
/// header's error on the indented line (its `unexpected EOL`); rledger keeps
/// it on the header's line, on purpose.
#[test]
fn test_parse_indented_line_after_a_header_failing_at_its_end_is_quiet() {
    assert_counts(&[
        (format!("{P}option \"title\"\n  \"a\"\n"), vec![(2, 1)]),
        (
            format!("{P}option \"title\"\n  \"a\nb\"\n{S}"),
            vec![(2, 1), (5, 1)],
        ),
        (format!("{P}option \"a\"\n"), vec![(2, 1)]),
        (format!("{P}option \"a\"\n{S}"), vec![(2, 1), (3, 1)]),
    ]);
}

/// #2979: a second date fails the line, bison shifts it again and reads a
/// transaction (or `open`) from it, whose indented lines are its body. That
/// entry is a recovery artifact and is not built here; its body reports what
/// beancount reports there, nothing for valid postings and metadata.
#[test]
fn test_parse_second_date_resync_body_is_quiet() {
    let ab = "2024-01-01 open Assets:A\n2024-01-01 open Expenses:B\n";
    assert_counts(&[
        (
            format!(
                "{ab}\n2024-01-02 2024-01-03 * \"n\"\n  Assets:A  -1 USD\n  Expenses:B  1 USD\n"
            ),
            vec![(4, 1)],
        ),
        (
            format!("{P}\n2024-01-02 2024-01-03 * \"n\"\n  Assets:A  -1 USD\n"),
            vec![(3, 1)],
        ),
        (
            format!("{P}\n2024-01-02 2024-01-03 open Assets:C\n  kk: \"v\"\n"),
            vec![(3, 1)],
        ),
        // Control: no flag, so bison builds nothing and the postings are
        // inside the window.
        (
            format!("{ab}\n2024-01-02 2024-01-03 \"n\"\n  Assets:A  -1 USD\n  Expenses:B  1 USD\n"),
            vec![(4, 1)],
        ),
        // The body's own defects are that entry's errors: an invalid token
        // in a posting (`$`), a trailing number after an amount.
        (
            format!("{P}2024-01-02 2024-01-03 * \"n\"\n  Assets:A 1 $\n"),
            vec![(2, 1), (3, 1)],
        ),
        (
            format!("{P}2024-01-02 2024-01-03 * \"n\"\n  Assets:A 1 USD 5\n"),
            vec![(2, 1), (3, 1)],
        ),
    ]);
}

/// The entry bison builds at the second date is not emitted: only the opens
/// are parsed directives.
#[test]
fn test_parse_second_date_resync_builds_no_directive() {
    let src = "2024-01-01 open Assets:A\n\n2024-01-02 2024-01-03 * \"n\"\n  Assets:A  -1 USD\n";
    assert_eq!(parse(src).directives.len(), 1);
    assert_eq!(parse_red_only(src).directives.len(), 1);
}

/// The leftovers #3000 kept at main's count: a date or an undated keyword
/// bison shifts mid-line, where its recovery may end inside the line.
#[test]
fn test_parse_mid_line_resync_shapes_count_as_beancount() {
    assert_counts(&[
        // The pipe after the date bison shifts is reported once its window
        // is over, as is the `key:2024/01/03` run's error.
        (
            "AB-C\nkey:2024/01/03  P | 1\n".to_string(),
            vec![(1, 1), (2, 2)],
        ),
        // A transaction bison builds after the unreadable `$`: its posting
        // is its body.
        (
            "$ 2024-01-02 * \"y\"\n  Assets:A 1 USD\n".to_string(),
            vec![(1, 1)],
        ),
        // A date at a posting's end, then the end of the line: no entry.
        ("$\n  Assets:A 1 USD 2024-01-02\n".to_string(), vec![(1, 1)]),
        (
            "$\n2024-01-02 123\n  Assets:A 1 USD\n".to_string(),
            vec![(1, 1)],
        ),
        // An `option` bison builds on an indented line, then a line beancount
        // reads from a `declarations` (rledger's error there stands for
        // beancount's indent error).
        (
            format!("{P}AB-C\n  option \"a\" \"b\"\n#\n"),
            vec![(2, 1), (4, 1)],
        ),
    ]);
}

/// Lines after a failed line inside an entry: bison discards the entry and
/// the lines after the failed one are inside its window too.
#[test]
fn test_parse_lines_after_a_failed_body_line_are_quiet() {
    assert_counts(&[
        (
            format!("{P}{T}  Assets:A 1 USD 5\n  Assets:B 1 USD 5\n"),
            vec![(3, 1)],
        ),
        (
            format!("{P}{T}  Assets:A 1 USD 5\n  Assets:B 1 USD\n  Assets:B 1 USD 5\n"),
            vec![(3, 1)],
        ),
        (
            format!("{P}2024-01-02 open Assets:B\n  kk: 5 5\n  jj: 5 5\n"),
            vec![(3, 1)],
        ),
        // A blank line between: one shift, so the second is still quiet.
        (
            format!("{P}{T}  Assets:A 1 USD 5\n\n  Assets:B 1 USD 5\n"),
            vec![(3, 1)],
        ),
    ]);
}

/// Chains of failed lines: each restarts the count, so a line after another
/// failed line is quiet too, unless it holds a lexer error.
#[test]
fn test_parse_chains_of_failed_lines_are_quiet() {
    assert_counts(&[
        (
            format!("{P}5\n2024-01-02 2024-01-03 \"n\"\npushtag\n  \"a\"\n!\n"),
            vec![(2, 1)],
        ),
        (format!("{P}pushtag #a $\nx\n"), vec![(2, 1), (3, 1)]),
        (format!("{P}option \"title\"\n!\n"), vec![(2, 1)]),
    ]);
}

/// After the third shift reporting resumes: a statement that starts a line
/// there is read as rledger reads it, its own errors included.
#[test]
fn test_parse_window_ends_after_three_shifts() {
    assert_counts(&[
        // `$` fails; its end of line, `2024-01-30` and `open` are the three
        // shifts, and the `open`'s missing account is reported.
        (
            "$\n2024-01-30 open\n  x\n".to_string(),
            vec![(1, 1), (2, 1), (3, 1)],
        ),
        ("$\n2024-01-30 open Assets:Z\n".to_string(), vec![(1, 1)]),
        // Three blank or comment lines end it before the indented line,
        // whose indent is reported.
        ("$\n\n\n  5\n".to_string(), vec![(1, 1), (4, 1)]),
        ("$\n;c\n;c\n  5\n".to_string(), vec![(1, 1), (4, 1)]),
        // Indented comment lines start the count over.
        ("$\n  ;c\n  ;c\n  5\n".to_string(), vec![(1, 1)]),
    ]);
}

/// #3028's leftover: a lone capital glued to a `\r` or to the end of the
/// input is an invalid token of its own to beancount (its `CAPITAL` needs a
/// blank or a `\n` after it), which this parser reads as a currency.
#[test]
fn test_parse_lone_capital_before_cr_or_end_is_an_invalid_token() {
    assert_counts(&[
        (format!("{P}{T}  h1 Z\r\n"), vec![(3, 2)]),
        (format!("{P}{T}  h1 Z"), vec![(3, 2)]),
        // Control: a blank after it is beancount's `CAPITAL`.
        (format!("{P}{T}  h1 Z \n"), vec![(3, 1)]),
    ]);
}

/// The deliberate differences, pinned at rledger's count.
///
/// * beancount drops an entry whose next column-0 line starts with an
///   invalid token (bison pops it unreduced on the lexer's `YYerror`), and
///   with it the errors its builder raises (too many strings, a booking
///   method). rledger keeps the entry and its error: dropping a valid entry
///   is a beancount bug, not copied.
/// * A lone posting flag (`  !`) fails at its end of line, which beancount
///   reports on the next line and rledger on the flag's.
#[test]
fn test_parse_deliberate_differences_keep_rledger_counts() {
    assert_counts(&[
        (
            format!("{P}2024-01-02 * \"a\" \"b\" \"c\"\nfoo\n"),
            vec![(2, 1), (3, 1)],
        ),
        (
            format!("{P}2024-01-02 open Assets:B \"FOO\"\nfoo\n"),
            vec![(2, 1), (3, 1)],
        ),
        (format!("{P}{T}  !\n  Assets:A 1 USD\n"), vec![(3, 1)]),
        (format!("{P}{T}  !\n  h\n"), vec![(3, 1), (4, 1)]),
    ]);
}

/// Both line endings and a missing final newline read the same.
#[test]
fn test_parse_recovery_window_with_crlf_and_no_final_newline() {
    assert_counts(&[
        (
            format!("{P}pushtag #a $\n\n{S}").replace('\n', "\r\n"),
            vec![(2, 1), (4, 1)],
        ),
        (
            format!("{P}pushtag #a $\n\n  2024-02-30 5"),
            vec![(2, 1), (4, 1)],
        ),
    ]);
}
