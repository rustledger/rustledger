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
fn test_hash_comment_round_trips_for_every_line_ending() {
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

/// The `;` control covers `\n` and `\r\n` only: a stray `\r` before the line
/// ending outside a `#` comment is a separate divergence from beancount (it
/// is reported as "unexpected input", which `bean-check` accepts) and is not
/// what #2769 fixes.
#[test]
fn test_hash_comment_does_not_break_the_next_directive() {
    let cases = ENDINGS
        .iter()
        .map(|&(label, eol)| ("# a comment", label, eol))
        .chain([("; a comment", "LF", "\n"), ("; a comment", "CRLF", "\r\n")]);
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
/// lone trailing `\r` at EOF (no `\n` follows, so no newline token claims it
/// and it stays in the comment).
#[test]
fn test_hash_comment_at_eof_round_trips() {
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
