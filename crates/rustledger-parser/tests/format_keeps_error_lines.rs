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
//! An indented directive is a different case and is still moved to column 0.
//! It is a reported error too (`top-level directive must start at column 0`),
//! but `format_source` currently dedents it, which repairs the error. That
//! pre-existing behavior is tracked as a separate follow-up.

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
