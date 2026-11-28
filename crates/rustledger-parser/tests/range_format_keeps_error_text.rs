//! Range formatting must keep the text a parse error sits in (#2803).
//!
//! The LSP formats a selection in a file with parse errors through
//! `format_parsed_range`. It rebuilds each directive from its typed values,
//! so text the parser could not read into one (`junk` after a header or a
//! posting, a stray character in a cost) used to vanish from the edit,
//! taking the parse error with it. A directive that holds a parse error is
//! now copied verbatim, by the same rule and the same error ranges as the
//! whole-file error-tolerant formatter (`format_source`, #2794).

use rustledger_parser::format::{
    FormatOptions, GroupingStyle, LineEnding, format_parsed_range,
    format_parsed_range_with_options, format_source, format_source_with_options,
};
use rustledger_parser::{TextRange, TextSize, parse};

/// Broken inputs: each holds a directive with a parse error between two
/// well-formed directives written with extra spaces, so the test can see
/// that those are still formatted.
const CASES: &[(&str, &str)] = &[
    (
        "junk after a header",
        "2024-01-01 open   Assets:A\n2024-01-02 open   Assets:B junk\n2024-01-03 open   Assets:C\n",
    ),
    (
        "junk after a posting",
        "2024-01-01 open   Assets:A\n2024-01-02 * \"x\"\n  Assets:A    1 USD junk\n  Assets:B\n2024-01-03 open   Assets:C\n",
    ),
    (
        "junk in a cost",
        "2024-01-01 open   Assets:A\n2024-01-02 * \"x\"\n  Assets:A    1 HOOL {1 USD junk}\n  Assets:B\n2024-01-03 open   Assets:C\n",
    ),
    (
        "a stray quote",
        "2024-01-01 open   Assets:A\n2024-01-02 open   Assets:B \"\n2024-01-03 open   Assets:C\n",
    ),
    (
        "junk at the end of the file with no newline",
        "2024-01-01 open   Assets:A\n2024-01-02 open   Assets:B junk",
    ),
];

fn ts(n: usize) -> TextSize {
    TextSize::try_from(n).expect("offset fits")
}

fn non_whitespace(s: &str) -> String {
    s.chars().filter(|c| !c.is_whitespace()).collect()
}

/// Format the whole file as a range, returning the snap and the new text.
fn format_all(src: &str) -> (TextRange, String) {
    let parsed = parse(src);
    assert!(!parsed.errors.is_empty(), "{src:?} must have parse errors");
    format_parsed_range(
        &parsed,
        TextRange::new(ts(0), ts(src.len())),
        GroupingStyle::default(),
    )
    .unwrap_or_else(|| panic!("{src:?}: range formatting declined"))
}

#[test]
fn test_format_parsed_range_keeps_every_byte_of_a_broken_directive() {
    for (label, src) in CASES {
        let (snap, out) = format_all(src);
        let snapped = &src[usize::from(snap.start())..usize::from(snap.end())];
        assert_eq!(
            non_whitespace(&out),
            non_whitespace(snapped),
            "{label}: range formatting changed non-whitespace text\n  out: {out:?}"
        );
    }
}

#[test]
fn test_format_parsed_range_still_formats_the_directives_around_a_broken_one() {
    for (label, src) in CASES {
        let (_, out) = format_all(src);
        assert!(
            out.contains("2024-01-01 open Assets:A\n"),
            "{label}: the directive before was not formatted: {out:?}"
        );
        if src.contains("Assets:C") {
            assert!(
                out.contains("2024-01-03 open Assets:C\n"),
                "{label}: the directive after was not formatted: {out:?}"
            );
        }
    }
}

#[test]
fn test_format_parsed_range_is_idempotent_on_broken_input() {
    for (label, src) in CASES {
        let (snap, out) = format_all(src);
        let once = format!(
            "{}{out}{}",
            &src[..usize::from(snap.start())],
            &src[usize::from(snap.end())..]
        );
        let (snap2, out2) = format_all(&once);
        let twice = format!(
            "{}{out2}{}",
            &once[..usize::from(snap2.start())],
            &once[usize::from(snap2.end())..]
        );
        assert_eq!(twice, once, "{label}: not idempotent");
    }
}

/// Drift guard: over the whole file, range formatting and the whole-file
/// error-tolerant formatter agree byte for byte on these inputs, so they
/// cannot disagree on which directives are copied verbatim. (They still
/// differ on a top-level `ERROR_NODE` line: `format_source` copies it, range
/// formatting declines the request rather than touch it.)
#[test]
fn test_format_parsed_range_matches_format_source_over_the_whole_file() {
    // Plus an indented first directive after a leading comment: its
    // indentation is a top-level token before it, which both walks must
    // keep (#2786). Dropping it would also remove the indentation's parse
    // error, so the second shape would reformat on the next pass.
    let indented: &[(&str, &str)] = &[
        (
            "indented broken directive after a comment",
            "; c\n  2024-01-01 open   Assets:A junk\n2024-01-02 open   Assets:B\n",
        ),
        (
            "indented directive after a comment, broken one after",
            "; c\n  2024-01-01 open   Assets:A\n2024-01-02 open   Assets:B junk\n",
        ),
    ];
    for (label, src) in CASES.iter().chain(indented) {
        let (snap, out) = format_all(src);
        assert_eq!(
            usize::from(snap.start()),
            0,
            "{label}: snap does not start at the file start"
        );
        assert_eq!(out, format_source(src), "{label}");
    }
}

/// A selection that covers only the broken directive copies it as written
/// and leaves its neighbors alone.
#[test]
fn test_format_parsed_range_on_only_the_broken_directive_returns_it_verbatim() {
    let src =
        "2024-01-01 open   Assets:A\n2024-01-02 open   Assets:B junk\n2024-01-03 open   Assets:C\n";
    let parsed = parse(src);
    let start = src.find("2024-01-02").expect("line 2");
    let (snap, out) = format_parsed_range(
        &parsed,
        TextRange::new(ts(start), ts(start + 5)),
        GroupingStyle::default(),
    )
    .expect("the selection hits a directive");
    assert_eq!(
        &src[usize::from(snap.start())..usize::from(snap.end())],
        "2024-01-02 open   Assets:B junk\n"
    );
    assert_eq!(out, "2024-01-02 open   Assets:B junk\n");
}

/// The error-tolerant formatter keeps a bare `\r` (classic-Mac) line ending
/// after a stray quote: the lexer does not end a line there, so the whole
/// line is one broken directive, copied verbatim with its error. Folding the
/// `\r` into a line break used to turn the file into a different, valid one.
#[test]
fn test_format_source_keeps_a_bare_cr_after_a_stray_quote() {
    let src = "2024-01-01 open Assets:A \"\r2024-01-02 open   Assets:B\r";
    let out = format_source(src);
    // Copied as written, the stray `\r` at the end of the file included.
    assert_eq!(out, src);
    assert_eq!(parse(&out).errors.len(), parse(src).errors.len());
}

fn crlf() -> FormatOptions<'static> {
    FormatOptions {
        line_ending: LineEnding::Crlf,
        ..FormatOptions::default()
    }
}

/// Writing CRLF follows the tree's line structure: a quote the lexer does not
/// read as a string (none closes it, or a `\` comes before the line break)
/// ends at its own line (#2788), so the lines after it are not inside a
/// string and get CRLF; a string that does close keeps its own line endings.
#[test]
fn test_crlf_option_ends_an_unterminated_quote_at_its_line() {
    for (label, lf) in [
        (
            "stray quote",
            "2024-01-01 open Assets:A\n2024-01-02 open Assets:B \"\n2024-01-03 open Assets:C\n2024-01-04 open Assets:D\n",
        ),
        (
            "unterminated string",
            "2024-01-01 note Assets:A \"unterminated\n2024-01-02 open Assets:C\n",
        ),
        (
            "backslash before the line break",
            "2024-01-01 note Assets:A \"a\\\n2024-01-02 open Assets:C\n",
        ),
        (
            "backslash before the line break, later quote",
            "2024-01-01 note Assets:A \"a\\\n2024-01-02 note Assets:C \"x\"\n2024-01-03 open Assets:D\n",
        ),
    ] {
        let source = lf.replace('\n', "\r\n");
        let out = format_source_with_options(&source, crlf());
        assert!(
            !out.replace("\r\n", "").contains('\n'),
            "{label}: a bare LF: {out:?}"
        );
    }
    // A string that does close keeps its own line endings.
    let multi = "2024-01-01 note Assets:A \"a\nb\"\r\n2024-01-02 open Assets:C\r\n";
    assert_eq!(format_source_with_options(multi, crlf()), multi);
}

/// The same over a range edit on a CRLF file with a copied stray quote, as
/// the LSP formats it: every line ending in the edit is CRLF.
#[test]
fn test_format_parsed_range_on_crlf_keeps_crlf_after_a_stray_quote() {
    for src in [
        "2024-01-01 open   Assets:A\r\n2024-01-02 open   Assets:B \"\r\n2024-01-03 open   Assets:C\r\n2024-01-04 open   Assets:D\r\n",
        "2024-01-01 note Assets:A \"unterminated\r\n2024-01-02 open   Assets:C\r\n",
        // A `\` before `\r\n` escapes the `\r` (the lexer's `.` matches
        // it), so this string runs on to the later quote in the lexer too;
        // the edit still has CRLF throughout.
        "2024-01-01 note Assets:A \"a\\\r\n2024-01-02 note Assets:B \"x\"\r\n2024-01-03 open   Assets:C\r\n",
    ] {
        let parsed = parse(src);
        let (_, edit) =
            format_parsed_range_with_options(&parsed, TextRange::new(ts(0), ts(src.len())), crlf())
                .unwrap_or_else(|| panic!("{src:?}: range formatting declined"));
        assert!(
            !edit.replace("\r\n", "").contains('\n'),
            "{src:?}: a bare LF in the CRLF edit: {edit:?}"
        );
        assert!(edit.contains("open Assets:C\r\n"), "{src:?}: {edit:?}");
    }
}
