//! The error-tolerant formatter must keep unparsable lines verbatim, so
//! they stay errors (#2786).
//!
//! `format_source` formats a file despite parse errors (it backs the FFI
//! component's best-effort `format.source`). It copies an unparsable line
//! verbatim, but before the first node of the file it used to drop the
//! line's indentation, because only there does the parser leave that
//! whitespace outside the error node. An indented `*` line is a reported
//! error; moved to column 0 it becomes a silenced org-mode heading, so
//! formatting erased the error and changed what the file means.
//!
//! Unparsable text inside a directive (`2024-01-01 open Assets:A junk`) was
//! deleted, because the directive was rebuilt from its typed values; it is now
//! copied verbatim (#2794). A property test below checks that no text of a
//! broken file is lost.
//!
//! An indented directive is a reported error too (`top-level directive must
//! start at column 0`), so it is now copied verbatim as well and keeps its
//! error, where it used to be dedented, which silently repaired it (#2795).

use proptest::prelude::*;
use rustledger_parser::format::format_source;
use rustledger_parser::parse;

/// The text of each line that holds a parse error, in order.
fn error_lines(src: &str) -> Vec<String> {
    parse(src)
        .errors
        .iter()
        .map(|e| {
            let start = src[..e.span.start].rfind('\n').map_or(0, |i| i + 1);
            let end = src[start..].find('\n').map_or(src.len(), |i| start + i);
            src[start..end].trim_end().to_string()
        })
        .collect()
}

fn assert_errors_kept(label: &str, src: &str) {
    let before = error_lines(src);
    assert!(
        !before.is_empty(),
        "{label}: the input must have parse errors"
    );
    let out = format_source(src);
    assert_eq!(
        error_lines(&out),
        before,
        "{label}: formatting changed the error lines\n  in:  {src:?}\n  out: {out:?}"
    );
    assert_eq!(
        format_source(&out),
        out,
        "{label}: formatting is not idempotent"
    );
}

/// `src` is already canonical: formatting must keep its error lines and
/// return it unchanged.
fn assert_unchanged(label: &str, src: &str) {
    assert_errors_kept(label, src);
    assert_eq!(
        format_source(src),
        src,
        "{label}: formatting changed the file"
    );
}

#[test]
fn test_format_source_keeps_an_indented_first_line_star_an_error() {
    assert_unchanged("first line", "  * h\n2024-01-02 open Assets:B\n");
    assert_unchanged(
        "after a leading blank line",
        "\n  * h\n2024-01-02 open Assets:B\n",
    );
    assert_errors_kept(
        "after a leading comment",
        "; c\n  * h\n2024-01-02 open Assets:B\n",
    );
    assert_errors_kept(
        "after a whitespace-only line",
        "  \n  * h\n2024-01-02 open Assets:B\n",
    );
    assert_unchanged("tab indent", "\t* h\n2024-01-02 open Assets:B\n");
    assert_unchanged(
        "issue reproducer",
        "  * h \"x\n2024-01-02 open Assets:B\n2024-01-03 open Assets:C\n",
    );
}

/// A leading BOM is dropped and CRLF is normalized to LF (the formatter's
/// documented output), but the indentation of the first error line is kept.
#[test]
fn test_format_source_keeps_an_indented_first_line_star_with_bom_or_crlf() {
    let expected = "  * h\n2024-01-02 open Assets:B\n";
    for (label, src) in [
        ("BOM", "\u{FEFF}  * h\n2024-01-02 open Assets:B\n"),
        ("CRLF", "  * h\r\n2024-01-02 open Assets:B\r\n"),
        (
            "BOM and CRLF",
            "\u{FEFF}  * h\r\n2024-01-02 open Assets:B\r\n",
        ),
    ] {
        assert_eq!(format_source(src), expected, "{label}");
    }
}

#[test]
fn test_format_source_keeps_an_indented_first_error_line_verbatim() {
    assert_unchanged("junk", "  junk here\n2024-01-02 open Assets:B\n");
}

/// Mid-file the indentation was already inside the error node and kept.
#[test]
fn test_format_source_keeps_a_mid_file_indented_star_an_error() {
    assert_errors_kept(
        "mid-file",
        "2024-01-01 open Assets:A\n  * h\n2024-01-02 open Assets:B\n",
    );
}

/// A whitespace-only first line is not an error line and stays blank.
#[test]
fn test_format_source_drops_whitespace_of_a_blank_first_line() {
    assert_eq!(
        format_source("   \n2024-01-02 open Assets:B\n"),
        "\n2024-01-02 open Assets:B\n"
    );
}

// ---- Unparsable text inside a directive (#2794) ----------------------------
//
// Text the parser cannot read on a directive's own lines is part of no typed
// value, so rebuilding the directive from its values deleted it, and the parse
// error with it. A directive holding a parse error is now copied verbatim.

#[test]
fn test_format_source_keeps_junk_after_a_directive() {
    assert_unchanged(
        "word",
        "2024-01-01 open Assets:A junk\n2024-01-02 open Assets:B\n",
    );
    assert_unchanged("star", "2024-01-01 open Assets:A* h\n");
}

/// The file's missing final newline is still added; the `"` stays.
#[test]
fn test_format_source_keeps_a_stray_quote_after_a_directive() {
    let src = "2024-01-01 open Assets:A\"";
    assert_errors_kept("quote", src);
    assert_eq!(format_source(src), "2024-01-01 open Assets:A\"\n");
}

#[test]
fn test_format_source_keeps_junk_after_a_transaction_header() {
    assert_unchanged(
        "header",
        "2024-01-01 * \"p\" junk\n  Assets:A  1 USD\n  Assets:B\n",
    );
}

#[test]
fn test_format_source_keeps_junk_after_a_posting() {
    assert_unchanged(
        "posting",
        "2024-01-01 *\n  Assets:A  1 USD junk\n  Assets:B\n",
    );
}

#[test]
fn test_format_source_keeps_junk_after_a_metadata_value() {
    assert_unchanged(
        "transaction metadata",
        "2024-01-01 *\n  k: \"v\" junk\n  Assets:A  1 USD\n  Assets:B\n",
    );
    assert_unchanged(
        "posting metadata",
        "2024-01-01 *\n  Assets:A  1 USD\n    k: \"v\" junk\n  Assets:B\n",
    );
    assert_unchanged(
        "open metadata",
        "2024-01-01 open Assets:A\n  k: \"v\" junk\n",
    );
}

#[test]
fn test_format_source_keeps_an_error_token_mid_line() {
    assert_unchanged("open", "2024-01-01 open Assets:A $ USD\n");
    assert_unchanged("price", "2024-01-01 price HOOL $ 10 USD\n");
    assert_unchanged("posting", "2024-01-01 *\n  Assets:A  1 $ USD\n  Assets:B\n");
    assert_unchanged("pushtag", "pushtag! #t\n");
}

/// The broken directive is copied as written, unaligned spacing included; the
/// directives around it are still formatted.
#[test]
fn test_format_source_formats_the_directives_around_a_broken_one() {
    let src = "2024-01-01 *\n  Assets:A    1 USD junk\n  Assets:B\n\
               2024-01-02 *\n  Assets:A    1 USD\n  Assets:B\n";
    assert_errors_kept("neighbors", src);
    assert_eq!(
        format_source(src),
        "2024-01-01 *\n  Assets:A    1 USD junk\n  Assets:B\n\
         2024-01-02 *\n  Assets:A  1 USD\n  Assets:B\n"
    );
}

/// An indented directive keeps its indentation and its error; the directive
/// beside it is still formatted (#2795).
#[test]
fn test_format_source_keeps_an_indented_directive_an_error() {
    for (label, src, expected) in [
        (
            "first line",
            "  2024-01-01 open Assets:A   USD\n2024-01-02 open Assets:B   USD\n",
            "  2024-01-01 open Assets:A   USD\n2024-01-02 open Assets:B USD\n",
        ),
        (
            "mid-file",
            "2024-01-01 open Assets:A   USD\n  2024-01-02 open Assets:B   USD\n",
            "2024-01-01 open Assets:A USD\n  2024-01-02 open Assets:B   USD\n",
        ),
    ] {
        assert_errors_kept(label, src);
        assert_eq!(format_source(src), expected, "{label}");
    }
}

/// A broken directive is copied verbatim, but trailing whitespace is trimmed
/// only outside strings: inside a multi-line string the spaces are part of
/// its value and are kept.
#[test]
fn test_format_source_keeps_whitespace_inside_a_broken_directive_string() {
    assert_unchanged("query", "2024-01-01 query \"q\" \"SELECT\n  1  \n\" junk\n");
    assert_unchanged("note", "2024-01-01 note Assets:A \"a  \n  b\" junk\n");
    // Trailing spaces outside the string are still trimmed.
    assert_eq!(
        format_source("2024-01-01 note Assets:A \"a  \n  b\" junk   \n"),
        "2024-01-01 note Assets:A \"a  \n  b\" junk\n"
    );
}

/// CRLF is normalized to LF outside strings only, so a `\r\n` inside a broken
/// directive's string survives, as it does in a clean one.
#[test]
fn test_format_source_keeps_a_crlf_inside_a_broken_directive_string() {
    let src = "2024-01-01 * \"multi  \r\nline\" junk\r\n  Assets:A  1 USD\r\n  Assets:B\r\n";
    assert_errors_kept("CRLF", src);
    assert_eq!(
        format_source(src),
        "2024-01-01 * \"multi  \r\nline\" junk\n  Assets:A  1 USD\n  Assets:B\n"
    );
    // The clean version keeps the same string bytes.
    let clean = "2024-01-01 * \"multi  \r\nline\"\r\n  Assets:A  1 USD\r\n  Assets:B\r\n";
    assert!(format_source(clean).starts_with("2024-01-01 * \"multi  \r\nline\"\n"));
}

// ---- Property: a broken file loses no text (#2794) -------------------------

/// The text with every whitespace character removed, in order.
///
/// The formatter only moves whitespace: it realigns columns, trims trailing
/// spaces, and normalizes blank lines and line endings. Every other character
/// is the author's text. The snippet corpus below is already canonical, so the
/// non-whitespace sequence must survive formatting exactly: no character
/// dropped, added, or reordered. That is stricter than a multiset check, which
/// would accept a reordering.
fn non_whitespace(s: &str) -> String {
    s.chars().filter(|c| !c.is_whitespace()).collect()
}

/// The 0-based numbers of the lines that hold a parse error.
fn error_line_numbers(src: &str) -> Vec<usize> {
    parse(src)
        .errors
        .iter()
        .map(|e| src[..e.span.start.min(src.len())].matches('\n').count())
        .collect()
}

/// Canonical, error-free snippets covering every directive kind, and the
/// transaction shapes (header strings, tags and links, metadata, postings with
/// cost and price) whose typed rebuild could drop a token it does not model.
const SNIPPETS: &[&str] = &[
    "2024-01-01 open Assets:A USD\n",
    "2024-01-01 close Assets:A\n",
    "2024-01-01 commodity USD\n",
    "2024-01-01 note Assets:A \"n\"\n",
    "2024-01-01 event \"loc\" \"Paris\"\n",
    "2024-01-01 query \"q\" \"SELECT 1\"\n",
    "2024-01-01 pad Assets:A Equity:B\n",
    "2024-01-01 document Assets:A \"/f.pdf\"\n",
    "2024-01-01 price HOOL 10 USD\n",
    "2024-01-01 balance Assets:A 1 USD\n",
    "2024-01-01 custom \"budget\" Assets:A \"monthly\" 10 USD\n",
    "option \"title\" \"T\"\n",
    "include \"other.beancount\"\n",
    "plugin \"beancount.plugins.auto\"\n",
    "pushtag #t\n",
    "poptag #t\n",
    "pushmeta k: \"v\"\n",
    "popmeta k:\n",
    "2024-01-01 open Assets:A\n  k: \"v\"\n",
    "2024-01-01 * \"payee\" \"narration\" #tag ^link\n  k: \"v\"\n  Assets:A  1 USD\n  Assets:B\n",
    "2024-01-01 * \"n\"\n  Assets:A  1 HOOL {10 USD}\n  Assets:B\n",
    "2024-01-01 ! \"n\"\n  Assets:A  1 HOOL @ 10 USD\n    pk: 2\n  Assets:B\n",
    "; a comment\n",
];

/// Text inserted into a snippet: a word, the characters that end or start
/// another construct (`"`, `*`, `{`, `@`), and stray punctuation.
const JUNK: &[&str] = &[
    "junk", "\"", "*", "* h", "!", "@", "{", "}", "~", "#", "^", "x", "?", "$", ",", "|", "&",
];

/// A concatenation of snippets with junk inserted at random byte offsets,
/// and the offset where each insertion now sits.
fn broken_source() -> impl Strategy<Value = (String, Vec<usize>)> {
    (
        prop::collection::vec(prop::sample::select(SNIPPETS), 1..4),
        prop::collection::vec(
            (
                any::<prop::sample::Index>(),
                prop::sample::select(JUNK),
                any::<bool>(),
            ),
            1..3,
        ),
    )
        .prop_map(|(snippets, edits)| {
            let mut src = snippets.concat();
            let mut at: Vec<usize> = Vec::new();
            for (index, junk, spaced) in edits {
                // Every snippet and junk string is ASCII, so any byte offset
                // is a char boundary.
                let i = index.index(src.len() + 1);
                let ins = if spaced {
                    format!(" {junk}")
                } else {
                    junk.to_string()
                };
                for a in &mut at {
                    if *a >= i {
                        *a += ins.len();
                    }
                }
                at.push(i);
                src.insert_str(i, &ins);
            }
            (src, at)
        })
}

proptest! {
    // A fixed seed and no failure file: the same inputs run everywhere, in
    // well under a second.
    #![proptest_config(ProptestConfig {
        cases: 512,
        max_global_rejects: 8192,
        rng_seed: proptest::test_runner::RngSeed::Fixed(2794),
        failure_persistence: None,
        ..ProptestConfig::default()
    })]

    /// For a file with parse errors, `format_source` keeps every non-whitespace
    /// character in order, its output has the same error lines, and it is a
    /// fixed point.
    ///
    /// Only inputs whose every insertion sits on a line holding a parse error
    /// are checked. The parser silently accepts some stray characters inside
    /// an otherwise valid directive (`open! Assets:A`), and the formatter's
    /// rebuild drops them with no error to say so. That is a parser leniency,
    /// not the loss of unparsable text this property is about.
    #[test]
    fn test_format_source_keeps_every_byte_of_a_broken_file((src, at) in broken_source()) {
        let lines = error_line_numbers(&src);
        prop_assume!(
            !lines.is_empty()
                && at.iter().all(|&i| lines.contains(&src[..i].matches('\n').count()))
        );
        let before = error_lines(&src);
        let out = format_source(&src);
        prop_assert_eq!(
            non_whitespace(&out),
            non_whitespace(&src),
            "formatting lost text\n  in:  {:?}\n  out: {:?}",
            &src,
            &out
        );
        prop_assert_eq!(
            error_lines(&out),
            before,
            "formatting changed the error lines\n  in:  {:?}\n  out: {:?}",
            &src,
            &out
        );
        prop_assert_eq!(format_source(&out), out, "not idempotent\n  in: {:?}", &src);
    }
}

/// A whitespace-only line next to an error node is one blank line, not two:
/// its whitespace is trimmed before the node's leading and trailing blank
/// lines are counted, so it is not emitted both as a gap and as an empty line
/// of the node (#2796).
#[test]
fn test_format_source_keeps_one_blank_line_for_a_whitespace_only_line_by_an_error_node() {
    for (label, src, expected) in [
        (
            "issue reproducer",
            "2024-01-01 open Assets:A\n   \n  * h\n",
            "2024-01-01 open Assets:A\n\n  * h\n",
        ),
        (
            "before an indented star",
            "2024-01-01 open Assets:A\n  \n  * h\n2024-01-02 open Assets:B\n",
            "2024-01-01 open Assets:A\n\n  * h\n2024-01-02 open Assets:B\n",
        ),
        (
            "among blank lines",
            "2024-01-01 open Assets:A\n\n  \n\n  * h\n  \n\n2024-01-02 open Assets:B\n",
            "2024-01-01 open Assets:A\n\n\n\n  * h\n\n\n2024-01-02 open Assets:B\n",
        ),
        (
            "before a broken directive",
            "2024-01-01 open Assets:A\n  \n2024-01-02 open Assets:B junk\n",
            "2024-01-01 open Assets:A\n\n2024-01-02 open Assets:B junk\n",
        ),
    ] {
        assert_errors_kept(label, src);
        assert_eq!(format_source(src), expected, "{label}");
    }
}
