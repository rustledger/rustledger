//! A `"` in an org-mode `*` heading must not swallow what follows (#2778).
//!
//! A column-0 `*` line is an org-mode heading. Beancount ignores the whole
//! line (`^\*/.` enters its IGNORE state); rledger wraps it in a silenced
//! `ERROR_NODE`. But the lexer tokenized the heading's text, so a `"` there
//! opened an unterminated string that ran to the end of the file: every
//! directive after the heading vanished, with no error. The lexer now emits
//! the rest of a heading line as one token without lexing it, and the
//! formatter's line-ending state machine treats the line as a comment.

use rustledger_core::Directive;
use rustledger_parser::format::{
    cr_outside_strings_present, crlf_to_lf_outside_strings, format_source,
    lf_to_crlf_outside_strings, try_format_source,
};
use rustledger_parser::logos_lexer::{Token, tokenize_lossless};
use rustledger_parser::{parse, parse_structured};

/// Every byte of `src` covered exactly once, in order, by the lossless
/// token stream, and the CST text equal to the source.
fn assert_lossless(src: &str) {
    let mut at = 0;
    for (token, span) in tokenize_lossless(src) {
        assert_eq!(
            span.start, at,
            "{src:?}: gap or overlap before {token:?} at {}..{}",
            span.start, span.end
        );
        at = span.end;
    }
    assert_eq!(at, src.len(), "{src:?}: the token stream stops short");
    assert_eq!(parse_structured(src).text().to_string(), src, "{src:?}");
}

/// The parsed directives, as `date account [note]` lines.
fn summary(src: &str) -> Vec<String> {
    parse(src)
        .directives
        .iter()
        .map(|d| match &d.value {
            Directive::Open(o) => format!("{} {}", o.date, o.account),
            Directive::Note(n) => format!("{} {} {:?}", n.date, n.account, n.comment),
            other => panic!("unexpected directive {other:?}"),
        })
        .collect()
}

#[test]
fn test_parse_org_heading_with_quote_keeps_the_following_directives() {
    for eol in ["\n", "\r\n"] {
        let heading = format!("* Heading with 27\" monitor{eol}");
        let src = format!("{heading}2024-01-02 open Assets:B{eol}2024-01-03 open Assets:C{eol}");
        let result = parse(&src);
        assert!(result.errors.is_empty(), "{src:?}: {:?}", result.errors);
        assert_eq!(
            summary(&src),
            ["2024-01-02 Assets:B", "2024-01-03 Assets:C"],
            "{src:?}"
        );
        // The heading is still the one empty section-marker comment it
        // always was, spanning exactly its own line (it spanned to the end
        // of the file while the string swallowed the rest).
        let comments: Vec<(&str, usize, usize)> = result
            .comments
            .iter()
            .map(|c| (c.value.as_str(), c.span.start, c.span.end))
            .collect();
        assert_eq!(comments, [("", 0, heading.len())], "{src:?}");
        assert_lossless(&src);
    }
}

/// Deeper headings, a quote right after the star, and a quote followed by a
/// string on a later line.
#[test]
fn test_parse_org_heading_with_quote_variants() {
    let src = "** Sub \"heading\n\
               2024-01-02 open Assets:B\n\
               *\"x\n\
               2024-01-03 note Assets:B \"two\nlines\"\n\
               2024-01-04 open Assets:C\n";
    let result = parse(src);
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    assert_eq!(
        summary(src),
        [
            "2024-01-02 Assets:B",
            "2024-01-03 Assets:B \"two\\nlines\"",
            "2024-01-04 Assets:C",
        ]
    );
    assert_lossless(src);
}

/// The rest of the heading line is one token after the `Star`, ending
/// before the line's `\r\n`; nothing on the line is lexed.
#[test]
fn test_tokenize_lossless_org_heading_is_one_token_after_the_star() {
    let tokens = tokenize_lossless("* a \"b\r\n");
    let shapes: Vec<(&Token<'_>, usize, usize)> =
        tokens.iter().map(|(t, s)| (t, s.start, s.end)).collect();
    assert!(
        matches!(
            shapes.as_slice(),
            [
                (Token::Star, 0, 1),
                (Token::Error(" a \"b"), 1, 6),
                (Token::Newline, 6, 8)
            ]
        ),
        "{shapes:?}"
    );
    // A bare `*` line has nothing after the star to hold.
    let tokens = tokenize_lossless("*\n");
    assert!(
        matches!(tokens.as_slice(), [(Token::Star, _), (Token::Newline, _)]),
        "{tokens:?}"
    );
    for src in [
        "* \"",
        "* \"\n",
        "\u{feff}* 27\" x\n2024-01-02 open Assets:B\n",
        "2024-01-01 open Assets:A\n* x \"y\r\r\n2024-01-02 open Assets:B\r\n",
    ] {
        assert_lossless(src);
    }
}

/// A `*` that is not at line start is still a flag, not a heading.
#[test]
fn test_parse_star_flag_is_unchanged() {
    let src = "2024-01-02 * \"payee\" \"narration\"\n  Assets:A  1 USD\n  Assets:B\n";
    let result = parse(src);
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    assert_eq!(result.directives.len(), 1);
    assert!(result.comments.is_empty(), "{:?}", result.comments);
    assert_lossless(src);
}

/// The line-ending helpers treat the heading as a comment: its line ending
/// folds, and a later string's interior stays verbatim, on the first line and
/// on a later CRLF line.
#[test]
fn test_crlf_to_lf_outside_strings_org_heading_with_quote() {
    let src = "2024-01-01 open Assets:A\r\n\
               * 27\" monitor\r\n\
               2024-01-02 note Assets:B \"a\r\nb\"\r\n";
    assert_eq!(
        crlf_to_lf_outside_strings(src),
        "2024-01-01 open Assets:A\n\
         * 27\" monitor\n\
         2024-01-02 note Assets:B \"a\r\nb\"\n"
    );
    assert!(cr_outside_strings_present("* 27\" monitor\r\n"));
    assert_eq!(
        lf_to_crlf_outside_strings("* 27\" monitor\n2024-01-02 note Assets:B \"a\nb\"\n"),
        "* 27\" monitor\r\n2024-01-02 note Assets:B \"a\nb\"\r\n"
    );
    assert_eq!(
        format_source(src),
        try_format_source(src).expect("the file formats")
    );
}

/// `rledger format` keeps the heading and the directives; the file is
/// already canonical, so the output is the input.
#[test]
fn test_try_format_source_org_heading_with_quote_keeps_directives() {
    let src = "* 27\" monitor\n2024-01-02 open Assets:B\n2024-01-03 open Assets:C\n";
    assert_eq!(try_format_source(src).expect("the file formats"), src);
}
