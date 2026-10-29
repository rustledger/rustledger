//! A column-0 `#` comment on a CRLF line must not break the next directive
//! (#2769).
//!
//! The comment token ran to the `\n`, so it included the `\r` that the
//! `\r?\n` newline token also starts at. The two tokens overlapped by one
//! byte: the CST text and the lossless token stream came out one byte longer
//! than the source, and the directive after the comment was reported as
//! "top-level directive must start at column 0". `bean-check` accepts the
//! same file. `;` comments were never affected (their regex stops before
//! `\r`), so they are checked here as the control.

use rustledger_parser::format::try_format_source;
use rustledger_parser::logos_lexer::tokenize_lossless;
use rustledger_parser::{parse, parse_structured};

const ENDINGS: [(&str, &str); 4] = [
    ("LF", "\n"),
    ("CRLF", "\r\n"),
    ("CR CR LF", "\r\r\n"),
    ("CR CR CR LF", "\r\r\r\n"),
];

/// The comment line ends in `eol`; the directive lines use the plain form of
/// the same convention (`\n` or `\r\n`), so only the comment line carries the
/// extra `\r` bytes.
fn ledger(comment: &str, eol: &str) -> String {
    let plain = if eol.contains('\r') { "\r\n" } else { "\n" };
    format!("2024-01-01 open Assets:Cash{plain}{comment}{eol}2024-01-02 open Assets:Bank{plain}")
}

fn lossless_text(src: &str) -> String {
    tokenize_lossless(src)
        .iter()
        .map(|(_, span)| &src[span.start..span.end])
        .collect()
}

#[test]
fn test_parse_structured_hash_comment_round_trips_every_line_ending() {
    for comment in ["# a comment", "; a comment"] {
        for (label, eol) in ENDINGS {
            let src = ledger(comment, eol);
            assert_eq!(
                parse_structured(&src).text().to_string(),
                src,
                "CST text differs from source: {comment:?} + {label}"
            );
            assert_eq!(
                lossless_text(&src),
                src,
                "lossless tokens differ from source: {comment:?} + {label}"
            );
        }
    }
}

/// The `;` control covers every ending too: a stray `\r` before the line
/// ending after a `;` comment was reported as "unexpected input" until #2774.
#[test]
fn test_parse_hash_comment_keeps_the_next_directive() {
    let cases = ["# a comment", "; a comment"]
        .into_iter()
        .flat_map(|comment| {
            ENDINGS
                .iter()
                .map(move |&(label, eol)| (comment, label, eol))
        });
    for (comment, label, eol) in cases {
        let src = ledger(comment, eol);
        let result = parse(&src);
        assert!(
            result.errors.is_empty(),
            "{comment:?} + {label}: {:?}",
            result.errors
        );
        assert_eq!(
            result.directives.len(),
            2,
            "{comment:?} + {label}: both opens must parse"
        );
    }
}

/// A `#` comment as the last line, with and without its line ending, and a
/// lone trailing `\r` at EOF (no `\n` follows, so no newline token claims it;
/// it is trailing whitespace, #2774).
#[test]
fn test_parse_structured_hash_comment_at_eof_round_trips() {
    for src in [
        "2024-01-01 open Assets:Cash\r\n# last\r\n",
        "2024-01-01 open Assets:Cash\r\n# last",
        "2024-01-01 open Assets:Cash\r\n# last\r",
        "# only\r\n",
    ] {
        assert_eq!(parse_structured(src).text().to_string(), src, "{src:?}");
        assert_eq!(lossless_text(src), src, "{src:?}");
        assert!(parse(src).errors.is_empty(), "{src:?}");
    }
}

/// A file ending in a CRLF `#` comment parsed clean before the fix, so the
/// CLI cached it, with its last directive's span one byte past the end of the
/// source (the reason for loader cache v44). The span now stops at the end,
/// and the comment's value no longer carries the `\r`.
#[test]
fn test_parse_hash_comment_crlf_at_eof_keeps_spans_in_bounds() {
    let src = "2024-01-01 open Assets:Cash\r\n# last\r\n";
    let result = parse(src);
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    assert_eq!(result.directives.len(), 1);
    assert_eq!(result.directives[0].span.end, src.len());
    assert_eq!(result.comments.len(), 1);
    assert_eq!(result.comments[0].value, "# last");
}

/// The comment as the first line after a byte-order mark, and right after a
/// `pushtag` line: both reported P0012 on the next directive before the fix.
#[test]
fn test_parse_hash_comment_crlf_after_bom_and_pushtag() {
    for src in [
        "\u{feff}# a comment\r\n2024-01-01 open Assets:Cash\r\n",
        "pushtag #trip\r\n# a comment\r\n2024-01-01 open Assets:Cash\r\npoptag #trip\r\n",
    ] {
        let result = parse(src);
        assert!(result.errors.is_empty(), "{src:?}: {:?}", result.errors);
        assert_eq!(result.directives.len(), 1, "{src:?}");
    }
}

/// `rledger format` goes through `try_format_source`, which refused a CRLF
/// file with a `#` comment because of the parse error. It now formats, to
/// the same output as the LF file.
#[test]
fn test_try_format_source_hash_comment_crlf_formats_like_lf() {
    let crlf = ledger("# a comment", "\r\n");
    let lf = ledger("# a comment", "\n");
    let expected = try_format_source(&lf).expect("the LF file formats");
    assert_eq!(try_format_source(&crlf), Ok(expected));
}
