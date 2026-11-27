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

/// Each shape below, with LF and with CRLF line endings.
fn with_crlf(cases: Vec<(String, Vec<(usize, usize)>)>) -> Vec<(String, Vec<(usize, usize)>)> {
    let crlf: Vec<_> = cases
        .iter()
        .map(|(src, counts)| (src.replace('\n', "\r\n"), counts.clone()))
        .collect();
    cases.into_iter().chain(crlf).collect()
}

/// A BOM beancount's lexer reads into an invalid token (`<BOM>g`, a BOM
/// alone after an indent) is that token's `YYerror`, which starts bison's
/// recovery as `$` does: what follows it on its line and on the lines the
/// window takes is quiet, but for the lexer's own errors. Not a BOM it reads
/// into an account, a string or a comment.
#[test]
fn test_parse_bom_invalid_token_starts_the_recovery_window() {
    assert_counts(&with_crlf(vec![
        // The account after the BOM run is discarded.
        (format!("{P}\u{FEFF}g Ü:A\n"), vec![(2, 1)]),
        // The invalid token after it is the lexer's error.
        (format!("{P}\u{FEFF}12$ Ü:A $n0\n"), vec![(2, 2)]),
        // A BOM alone on a line indented under the `open` fails it, and the
        // next indented line's grammar error is quiet: the entry bison
        // builds at its date fails at the string, reported.
        (
            format!("{P}\t\u{FEFF}\n\tT 2024-01-02 commodity EUR \"a b\"\n"),
            vec![(2, 1), (3, 1)],
        ),
    ]));
}

/// An entry bison builds mid-line (#2979) whose own line holds an invalid
/// token after its first three: the token's `YYerror` drops the entry and
/// starts the recovery over, so the entry's indented lines are quiet.
#[test]
fn test_parse_invalid_token_on_a_mid_line_entry_restarts_the_window() {
    assert_counts(&with_crlf(vec![
        (
            format!("{P}$ 2024-01-02 * \"y\" $\n  Assets:A  1 USD\n  Assets:B\n"),
            vec![(2, 2)],
        ),
        (
            format!("{P}\u{FEFF}g 2024-01-02 * \"n\" $x\n  Assets:A  1 USD\n  Assets:B\n"),
            vec![(2, 2)],
        ),
        // A lone capital before the line end is a `CAPITAL` with `\n`, and
        // an invalid token with `\r\n`; both count two on the line.
        (
            format!("{P}$ 2024-01-02 * \"y\" T\n  Assets:A  1 USD\n"),
            vec![(2, 2)],
        ),
    ]));
}

/// A number beancount's lexer rejects (`1,50`: `ValueError: Invalid number
/// format`) is one of its lexer errors, reported inside the window, where
/// this parser reads a number and a comma.
#[test]
fn test_parse_misgrouped_number_inside_the_window_is_reported() {
    let cases = with_crlf(vec![
        (format!("{P}$\n  x 1,50\n"), vec![(2, 1), (3, 2)]),
        // After a string that runs over a line end, on the line it ends.
        (format!("{P}$\n  \"a\nb\" 1,50\n"), vec![(2, 1), (4, 1)]),
        // Control: thousands separators are a number.
        (format!("{P}$\n  x 1,000\n"), vec![(2, 1), (3, 1)]),
    ]);
    assert_counts(&cases);
    let errors = parse(&format!("{P}$\n  x 1,50\n")).errors;
    assert!(
        errors
            .iter()
            .any(|e| e.kind == rustledger_parser::ParseErrorKind::InvalidNumber("1,50".into())),
        "{errors:?}"
    );
}

/// A header that fails at a token after a string running over a line end
/// fails on the line that token is on, where beancount's lexer then is
/// (`event "x\nb" x`: at the `x`, on line 2).
#[test]
fn test_parse_header_failing_after_a_multi_line_string_reports_its_last_line() {
    assert_counts(&with_crlf(vec![
        ("2024/1/3 event \"x\nb\" x\n".to_string(), vec![(2, 1)]),
        (
            format!("{P}$\n\n2024-01-02 event \"x\nb\" x\n"),
            vec![(2, 1), (5, 1)],
        ),
        // Failing at the string itself: where it ends, as before.
        (format!("{P}2024-01-02 event \"x\nb\"\n"), vec![(3, 1)]),
    ]));
}

/// Deliberate deviation from beancount (Python compatibility policy): an
/// indented `;` comment that no entry continues, after a column-0 comment, a
/// line beancount skips at column 0, a blank line or the top of the file, is
/// a comment. bean-check 3.2.3 reports `syntax error, unexpected INDENT` on
/// each (its grammar takes an indent only inside an entry); rejecting a
/// comment is not copied (`cst/parser.rs`, the top-level trivia loop). The
/// parity harness drops beancount's error there
/// (`is_indented_comment_indent_error`).
#[test]
fn test_parse_indented_comment_after_a_column_0_comment_is_accepted() {
    for src in [
        format!("{P}; note\n  ; continued\n"),
        format!("{P}; note\n  ; continued\n\t; more\n2024-01-02 open Assets:B\n"),
        format!("{P}\n  ; after a blank line\n"),
        format!("{P}* heading\n  ; under an org heading\n"),
        "; note\n  ; at the top\n".to_string(),
    ] {
        for src in [src.clone(), src.replace('\n', "\r\n")] {
            assert_eq!(per_line(&src), vec![], "{src:?}");
            let opens = parse(&src).directives.len();
            assert_eq!(opens, src.matches(" open ").count(), "{src:?}");
        }
    }
    // After a directive that takes no metadata the line is that directive's,
    // and an error as in beancount.
    assert_counts(&[("option \"title\" \"x\"\n  ; c\n".to_string(), vec![(2, 1)])]);
}

/// An orphan indented line (one no entry continues: at the top of the file,
/// after a blank line or a column-0 comment, after a directive that takes no
/// metadata) fails at its indent, `syntax error, unexpected INDENT`, and
/// every lexer error on it is one more error there: `  $x` is two errors, the
/// indent's and `Invalid token: '$x'`. rledger's line error stands for the
/// indent, and the line's first invalid token gets an error of its own,
/// which names it.
#[test]
fn test_parse_orphan_indented_line_reports_its_indent_and_its_invalid_tokens() {
    assert_counts(&with_crlf(vec![
        ("  $x\n".to_string(), vec![(1, 2)]),
        ("  $x".to_string(), vec![(1, 2)]),
        ("\t$\n".to_string(), vec![(1, 2)]),
        ("\n  $x\n".to_string(), vec![(2, 2)]),
        ("; c\n  $x\n".to_string(), vec![(2, 2)]),
        (format!("{P}\n  $x\n"), vec![(3, 2)]),
        ("option \"title\" \"t\"\n  $x\n".to_string(), vec![(2, 2)]),
        ("  $x y\n".to_string(), vec![(1, 3)]),
        ("  \"abc\n".to_string(), vec![(1, 2)]),
        ("  1,50\n".to_string(), vec![(1, 2)]),
        ("  Assets:A 1,50 USD\n".to_string(), vec![(1, 2)]),
        ("  2024-01-01 $\n".to_string(), vec![(1, 2)]),
        // The window from the first line keeps the second to its lexer's.
        ("  $x\n  $y\n".to_string(), vec![(1, 2), (2, 1)]),
        // Controls: no invalid token, and an invalid date, already its own.
        ("  !\n".to_string(), vec![(1, 1)]),
        ("  2024-02-30\n".to_string(), vec![(1, 2)]),
        // Inside an entry the indent is taken: the invalid token alone.
        (format!("{P}  $x\n"), vec![(2, 1)]),
    ]));
    let errors = parse("  $x\n").errors;
    assert!(
        errors
            .iter()
            .any(|e| e.message().contains("invalid token '$x'")),
        "{errors:?}"
    );
}

/// After an indented comment rledger accepts (above), bison is still
/// recovering from that comment's indent: its line end and each gap line
/// after it are shifts, so an orphan indented line within two of them is
/// quiet but for its lexer errors, and one after two reports its indent too.
#[test]
fn test_parse_orphan_indented_line_after_an_accepted_indented_comment() {
    assert_counts(&with_crlf(vec![
        ("  ; c\n  $x\n".to_string(), vec![(2, 1)]),
        ("  ; c\n  ; d\n  $x\n".to_string(), vec![(3, 1)]),
        ("  ; c\n\n  $x\n".to_string(), vec![(3, 1)]),
        ("  ; c\n; d\n  $x\n".to_string(), vec![(3, 1)]),
        ("  ; c\n  Assets:A $\n".to_string(), vec![(2, 1)]),
        ("  ; c\n  !\n".to_string(), vec![]),
        ("  ; c\n\n\n  $x\n".to_string(), vec![(4, 2)]),
        ("  ; c\n* h\n* h\n  $x\n".to_string(), vec![(4, 2)]),
    ]));
}

/// An invalid account is rledger's line error for a line it cannot read,
/// named for the account on it (P0006). beancount's lexer reads that account
/// into an `ACCOUNT` (its account rules admit any non-ASCII character), so
/// its grammar fails on the line as on any other, and bison's recovery keeps
/// the lines after it quiet as after any failure: an indented line, at its
/// indent, a column-0 line after a statement it cannot start, each for three
/// shifts. Not on a line holding a stray `\r`, where no recovery is modeled.
#[test]
fn test_parse_invalid_account_starts_the_recovery_window() {
    assert_counts(&with_crlf(vec![
        (
            "    Assets:FundoInclusão:X 1 BRL\n    Assets:Eventos:Y\n".to_string(),
            vec![(1, 1)],
        ),
        (
            "    Assets:Café 1 BRL\n    Assets:B\n\n  Assets:C\n".to_string(),
            vec![(1, 1)],
        ),
        (format!("{P}  Assets:Café 1 USD\n5 5\n"), vec![(2, 1)]),
        ("Assets:Café 1\n5 5\n5 5\n".to_string(), vec![(1, 1)]),
        ("Ü:A $x\n  Assets:B 1 USD\n".to_string(), vec![(1, 2)]),
    ]));
    let errors = parse("    Assets:Café 1 BRL\n    Assets:B\n").errors;
    assert!(
        errors
            .iter()
            .any(|e| matches!(e.kind, rustledger_parser::ParseErrorKind::InvalidAccount(_))),
        "{errors:?}"
    );
}

/// An `option` bison builds whole inside a transaction's body leaves it at a
/// `declarations`, so the indented line after it fails at its indent
/// (`syntax error, unexpected INDENT`), where rledger reads that line as part
/// of the transaction. On `  $x` that indent error is one more than the
/// invalid token's, which rledger names already: the indent's is added.
#[test]
fn test_parse_indented_line_after_an_option_in_a_body_reports_its_indent() {
    let src = format!("{T}  Assets:A 1 USD\n  option \"title\" \"x\"\n  $x\n  Assets:B\n");
    assert_counts(&with_crlf(vec![
        (src.clone(), vec![(3, 1), (4, 2)]),
        (
            format!("{T}  option \"title\" \"x\"\n  $x\n"),
            vec![(2, 1), (3, 2)],
        ),
        (
            format!("{T}  option \"title\" \"x\"\n  $x $y\n  Assets:B\n"),
            vec![(2, 1), (3, 3)],
        ),
    ]));
    let errors = parse(&src).errors;
    assert!(
        errors
            .iter()
            .any(|e| e.message().contains("unexpected indent")),
        "{errors:?}"
    );
}

/// An undated declaration bison's recovery starts mid-line, once it has
/// shifted its first three tokens, is reported again where it then fails
/// (`popmeta pushmeta kk: @` is two errors: at `pushmeta`, and at the `@`
/// that `pushmeta kk:` cannot take), and the recovery starts over at that
/// token. It builds nothing, so it changes no state.
#[test]
fn test_parse_undated_declaration_failing_mid_line_is_reported() {
    assert_counts(&with_crlf(vec![
        ("popmeta pushmeta kk: @\n".to_string(), vec![(1, 2)]),
        ("~ popmeta kk: } $\n".to_string(), vec![(1, 3)]),
        ("~ popmeta kk: @ x y\n".to_string(), vec![(1, 4)]),
        ("x option \"title\" \"t\" 5\n".to_string(), vec![(1, 2)]),
        ("~ pushmeta kk: \"v\" @\n".to_string(), vec![(1, 2)]),
        ("~ pushmeta kk: TRUE ,\n".to_string(), vec![(1, 2)]),
        ("~ pushmeta kk: price\n".to_string(), vec![(1, 2)]),
        ("~ plugin \"a\" \"b\" \"c\"\n".to_string(), vec![(1, 2)]),
        // The recovery from the second failure keeps the lines after it.
        (
            "popmeta pushmeta kk: @\n\t\n 1,50 2024-13-45\n".to_string(),
            vec![(1, 2), (3, 2)],
        ),
        (
            format!("{P}open ( pushmeta kk: price close\n* $\n Assets:a x\n"),
            vec![(2, 2), (4, 2)],
        ),
    ]));
    let errors = parse("popmeta pushmeta kk: @\n").errors;
    assert!(
        errors
            .iter()
            .any(|e| e.message().contains("unexpected \"@\"")),
        "{errors:?}"
    );
}

/// An indented line inside a recovery on which bison shifts a date that
/// starts no statement (`    date: 2024-01-02`, a metadata line) does not
/// end the recovery: its line end is not taken after the date, so the count
/// is back at three, as after any indented line.
#[test]
fn test_parse_date_on_an_indented_line_does_not_end_the_recovery() {
    assert_counts(&with_crlf(vec![(
        format!(
            "{T}  option \"title\" \"x\"\n  Assets:A 1 USD\n    date: 2024-01-02\n\n  Assets:a 1 USD\n"
        ),
        vec![(2, 1), (6, 1)],
    )]));
}

/// A line's grammar failure is one error beside its lexer's where it is
/// known to be bison's own: a column-0 statement failing among its first
/// three tokens, or a body line failing at its first token (a dated
/// directive's takes a key there, a transaction's also a posting, a tag or a
/// link). So a misgrouped number after it is reported too. A posting whose
/// flag bison takes (`Z`) fails at no token before the number.
#[test]
fn test_parse_grammar_failure_counts_beside_the_invalid_tokens() {
    assert_counts(&with_crlf(vec![
        (
            "Assets:B Assets:a # 1.5 1,50 @@\n".to_string(),
            vec![(1, 3)],
        ),
        (format!("{P}  open $ 1,50\n"), vec![(2, 3)]),
        (format!("{T}  open $ 1,50\n"), vec![(2, 3)]),
        (format!("{T}  Z   1,50  2 HOOL\n"), vec![(2, 1)]),
    ]));
}

/// A stray `\r` (one not part of a CRLF line end) is a blank to beancount's
/// lexer. Bison's recovery from a statement that fails on such a line keeps
/// the lines after it quiet, as from any other failed line: a posting under
/// it, a second-date entry, a body under an `open` that failed past its
/// account (#2980). That holds whether this parser reads the `\r` as a blank
/// too (before an invalid token, `pushtag #a\r$`) or reports it, on purpose,
/// as an error of its own (a `\r` before a token that lexes, or at a line
/// start), where that line keeps its own error.
#[test]
fn test_parse_recovery_runs_through_a_line_holding_a_stray_cr() {
    assert_counts(&[
        ("\r$\n  Assets:A 1 USD\n".to_string(), vec![(1, 1)]),
        (
            "pushtag #a\r$\n2024-01-02 2024-01-03 * \"n\"\n".to_string(),
            vec![(1, 1)],
        ),
        (
            "option \"a\"\r$\n  Assets:A 1 USD\n".to_string(),
            vec![(1, 1)],
        ),
        (
            "\r  5\n2024-01-02 2024-01-03 * \"n\"\n".to_string(),
            vec![(1, 1)],
        ),
        (
            "2024-01-02 open Assets:B \r5\n  \"a\"\n  Assets:A\n".to_string(),
            vec![(1, 1)],
        ),
        // A line whose blanks before its content hold a `\r` has no indent
        // to beancount: its content is a column-0 statement.
        ("\r  $x\n  Assets:A 1 USD\n".to_string(), vec![(1, 1)]),
        (
            " \r$x\n2024-01-02 2024-01-03 * \"n\"\n  Assets:A 1 USD\n".to_string(),
            vec![(1, 1)],
        ),
        (format!("{P}\r  $\n  Assets:A 1 USD\n"), vec![(2, 1)]),
        // CRLF line ends throughout.
        ("\r$\r\n  Assets:A 1 USD\r\n".to_string(), vec![(1, 1)]),
    ]);
}

/// Where this parser reports a stray `\r` before a token that lexes, that
/// error stays (a deliberate difference, #2980:
/// `test_parse_cr_with_more_of_the_line_after_it_stays_an_error`), and the
/// lines after are counted as beancount counts them: here beancount builds
/// the `open` and fails at the string under it, whose window keeps the line
/// after it quiet.
#[test]
fn test_parse_stray_cr_error_stays_and_the_lines_after_follow_beancount() {
    assert_counts(&[(
        "2024-01-02 open\rAssets:B\n  \"a\"\n  Assets:A\n".to_string(),
        vec![(1, 1), (2, 1)],
    )]);
}

/// A misgrouped number inside the recovery is reported on a line with a BOM
/// that is one token on both sides, or none: a BOM-led invalid token, which
/// runs to the next blank in beancount and here (`<BOM>x`), or a BOM inside
/// an account beancount's lexer reads (`Assets:<BOM>A`, an `ACCOUNT` there).
#[test]
fn test_parse_misgrouped_number_beside_a_bom_token_is_reported() {
    assert_counts(&[
        ("$\n  \u{feff}x 1,50\n".to_string(), vec![(1, 1), (2, 2)]),
        (
            "\t2024-01-02 Assets:\u{feff}A pushmeta txn $ 1,50\n".to_string(),
            vec![(1, 3)],
        ),
        (
            format!("{P}Assets:\u{feff}A k: 2024-02-30 1,50\n"),
            vec![(2, 4)],
        ),
        (
            format!("{P}}} popmeta Assets:\u{feff}A\n \u{feff}x 1,50 , : {{\n"),
            vec![(2, 1), (3, 2)],
        ),
    ]);
}

/// A line of the body of an entry bison builds mid-line (#2979) that fails
/// starts a recovery of its own, which goes on past the entry's last indented
/// line: the column-0 lines bison discards after it are quiet, as after any
/// failed line (`"s"` after a phantom transaction's failing posting, after a
/// phantom `open` whose body takes no posting).
#[test]
fn test_parse_recovery_goes_on_past_the_body_of_an_entry_built_mid_line() {
    assert_counts(&[
        (
            "$ 2024-01-02 * \"y\"\n  2024-02-30 5\n\"s\"\n".to_string(),
            vec![(1, 1), (2, 1)],
        ),
        (
            "$ 2024-01-02 * \"y\"\n  2024-02-30 5\n\n\"s\"\n".to_string(),
            vec![(1, 1), (2, 1)],
        ),
        (
            "$ 2024-01-02 * \"y\"\n  2024-02-30 5\n\"s\"\n\"t\"\n\"u\"\n".to_string(),
            vec![(1, 1), (2, 1)],
        ),
        (
            format!("{P}  2024-01-02 open Assets:Z\n  kk: \"v\"\n  Assets:A 1 USD\n\"s\"\n"),
            vec![(2, 1), (4, 1)],
        ),
        (
            "2024-01-02 2024-01-03 open Assets:C\n  Assets:A 1 USD 2024-01-02\ninclude\n"
                .to_string(),
            vec![(1, 1), (2, 1)],
        ),
        (
            "2024-01-02 2024-01-03 * \"n\"\n  Assets:A 1 USD 2024-01-02\n2024-01-02 123\n"
                .to_string(),
            vec![(1, 1), (2, 1)],
        ),
    ]);
}

/// An entry bison builds inside the body of one it built mid-line (`$`, then
/// `  2024-01-02 open Assets:Z` twice: the second fails the first `open`'s
/// body at its date, and bison builds it in turn) is parsed on its own too,
/// up to `MAX_PHANTOM_DEPTH` levels, so the first entry's header line is
/// quiet, as in beancount, where it kept its error.
#[test]
fn test_parse_entry_built_inside_an_entry_built_mid_line_is_modeled() {
    let open = "  2024-01-02 open Assets:Z\n";
    assert_counts(&[
        (format!("$\n{open}{open}"), vec![(1, 1), (3, 1)]),
        (
            format!("$\n{open}{open}{open}  x\n"),
            vec![(1, 1), (3, 1), (4, 1), (5, 1)],
        ),
        (
            format!("$\n{}  x\n", open.repeat(6)),
            vec![(1, 1), (3, 1), (4, 1), (5, 1), (6, 1), (7, 1), (8, 1)],
        ),
        (
            format!("{P}{open}  2024-01-02 * \"n\"\n    Assets:A 1 USD 5\n\"s\"\n"),
            vec![(2, 1), (3, 1), (4, 1)],
        ),
    ]);
}

/// Entries built inside one another, and windows going on past their bodies,
/// cost a bounded number of parses of the input: a large file of them parses
/// in time linear in its size. Each shape is timed at `SMALL` and at eight
/// times as many lines, and the large run must take no more than eight times
/// the small one, with a wide margin for a loaded machine (quadratic work
/// would take about sixty-four times as long).
#[test]
fn test_parse_nested_entries_and_their_tails_parse_in_linear_time() {
    const SMALL: usize = 2_000;
    let shapes: [(&str, &str, &str); 4] = [
        (
            "entries nested in entries",
            "$\n",
            "  2024-01-02 open Assets:Z\n",
        ),
        (
            "nested entries with failing bodies",
            "$\n",
            "  2024-01-02 open Assets:Z\n  x\n",
        ),
        (
            "windows past an entry's body",
            "",
            "$ 2024-01-02 * \"y\"\n  2024-02-30 5\n\"s\"\n",
        ),
        (
            "stray `\\r` lines over nested entries",
            "$\n",
            "  2024-01-02 open\rAssets:Z\n  2024-01-02 open Assets:Z\n",
        ),
    ];
    for (label, head, unit) in shapes {
        let time = |n: usize| {
            let src = format!("{head}{}", unit.repeat(n));
            let start = std::time::Instant::now();
            let errors = parse(&src).errors.len();
            (start.elapsed(), errors)
        };
        // Warm up, then take the faster of two runs of each size.
        let _ = time(SMALL / 4);
        let small = time(SMALL).0.min(time(SMALL).0);
        let (large, errors) = time(8 * SMALL);
        assert!(errors > 0, "{label}: the input has errors to model");
        assert!(
            large <= small * 24 + std::time::Duration::from_secs(2),
            "{label}: {large:?} for {} lines against {small:?} for {SMALL}: not linear",
            8 * SMALL
        );
    }
}
