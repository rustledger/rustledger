//! Range formatting must keep the text a parse error sits in (#2803).
//!
//! The LSP formats a selection in a file with parse errors through
//! `format_parsed_range`. It rebuilds each directive from its typed values,
//! so text the parser could not read into one (`junk` after a header or a
//! posting, a stray character in a cost) used to vanish from the edit,
//! taking the parse error with it. A directive that holds a parse error is
//! now copied verbatim, by the same rule and the same error ranges as the
//! whole-file error-tolerant formatter (`format_source`, #2794).

use rustledger_parser::format::{GroupingStyle, format_parsed_range, format_source};
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
    for (label, src) in CASES {
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
