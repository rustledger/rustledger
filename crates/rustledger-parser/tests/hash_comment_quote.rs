//! A `"` inside a column-0 `#` comment must not swallow what follows
//! (#2775).
//!
//! The lexer computed the comment's end from the line, then advanced token
//! by token until a `Newline`. A `"` in the comment opened a String token,
//! which may span lines, so that loop ate every line up to the next `"` (or
//! the end of the file): the directives there vanished, no error was
//! reported, and `rledger format` deleted them. Beancount skips the rest of
//! a `#` line without tokenizing it. The formatter's line-ending state
//! machine had the matching gap: it did not treat a column-0 `#` as a
//! comment, so the `"` flipped it into string state.

use rustledger_core::Directive;
use rustledger_parser::format::{
    cr_outside_strings_present, crlf_to_lf_outside_strings, format_source,
    lf_to_crlf_outside_strings, try_format_source,
};
use rustledger_parser::logos_lexer::{Token, tokenize_lossless};
use rustledger_parser::{parse, parse_structured};

/// Every byte of `src` covered exactly once, in order, by the lossless
/// token stream.
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

/// The parsed directives, as `date account [note]` lines, so a test pins
/// exactly which ones survive rather than how many.
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
fn test_parse_hash_comment_with_quote_keeps_the_following_directives() {
    for eol in ["\n", "\r\n"] {
        let src = format!(
            "# 27\" monitor{eol}2024-01-02 open Assets:B{eol}2024-01-03 open Assets:C{eol}"
        );
        let result = parse(&src);
        assert!(result.errors.is_empty(), "{src:?}: {:?}", result.errors);
        assert_eq!(
            summary(&src),
            ["2024-01-02 Assets:B", "2024-01-03 Assets:C"],
            "{src:?}"
        );
        assert_eq!(result.comments.len(), 1, "{src:?}");
        assert_eq!(result.comments[0].value, "# 27\" monitor", "{src:?}");
        assert_lossless(&src);
    }
}

/// A quote in the comment and a string on a later line: the old loop closed
/// the "string" on that line's opening quote, jumping over everything in
/// between, and misread the rest.
#[test]
fn test_parse_hash_comment_with_quote_before_a_multiline_string() {
    let src = "# say \"hi\n\
               2024-01-02 open Assets:B\n\
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

/// The quote shapes the review turned up, plus an unterminated quote at the
/// end of the file and a comment that is only a quote.
#[test]
fn test_tokenize_lossless_hash_comment_with_quote_is_contiguous() {
    for src in [
        "# \"a\r\r\n2024-01-02 open Assets:B\r\n",
        "2024-01-01 open Assets:A\n# \"",
        "2024-01-01 open Assets:A\n# \"\n",
        "#\"\n2024-01-02 open Assets:B\n",
        "# \"x\" and \"y\n2024-01-02 open Assets:B \"\n",
        "\u{feff}# 27\" monitor\n2024-01-02 open Assets:B\n",
    ] {
        assert_lossless(src);
    }
}

/// The line-ending helpers keep a string's interior verbatim and fold
/// everything else. With the old state machine, the `"` in the comment
/// opened a "string" that closed on the note's opening quote: the comment's
/// CRLF was kept and the real string's interior CRLF was folded.
#[test]
fn test_crlf_to_lf_outside_strings_hash_comment_with_quote() {
    let src = "# 27\" monitor\r\n2024-01-02 note Assets:B \"a\r\nb\"\r\n";
    assert_eq!(
        crlf_to_lf_outside_strings(src),
        "# 27\" monitor\n2024-01-02 note Assets:B \"a\r\nb\"\n"
    );
    assert!(cr_outside_strings_present("# 27\" monitor\r\n"));
    assert_eq!(
        lf_to_crlf_outside_strings("# 27\" monitor\n2024-01-02 note Assets:B \"a\nb\"\n"),
        "# 27\" monitor\r\n2024-01-02 note Assets:B \"a\nb\"\r\n"
    );
}

/// The same on a CRLF line after the first. The fold consumes a CRLF pair
/// whole, so the `\n` never passed through the line-start bookkeeping: a
/// `#` comment on line 2 or later was not recognized, its `"` opened a
/// string, and a real string's interior CRLF further down was folded. On
/// this clean file `format_source` (which folds first) then disagreed with
/// `try_format_source`.
#[test]
fn test_crlf_to_lf_outside_strings_hash_comment_with_quote_on_a_later_line() {
    let src = "2024-01-01 open Assets:A\r\n\
               # 27\" monitor\r\n\
               2024-01-02 note Assets:B \"a\r\nb\"\r\n";
    assert_eq!(
        crlf_to_lf_outside_strings(src),
        "2024-01-01 open Assets:A\n\
         # 27\" monitor\n\
         2024-01-02 note Assets:B \"a\r\nb\"\n"
    );
    assert_eq!(
        format_source(src),
        try_format_source(src).expect("the file formats")
    );
}

/// `rledger format` keeps the directives after the comment (it deleted
/// them). The file is already canonical, so the output is the input.
#[test]
fn test_try_format_source_hash_comment_with_quote_keeps_directives() {
    let src = "# 27\" monitor\n2024-01-02 open Assets:B\n2024-01-03 open Assets:C\n";
    assert_eq!(try_format_source(src).expect("the file formats"), src);
}

/// A `#` followed by a tag character is a tag even at column 0, and a
/// mid-line `#` is not a comment: neither may start skipping a line.
#[test]
fn test_parse_hash_that_is_not_a_comment_is_unchanged() {
    let src = "2024-01-02 * \"x\" #trip\n  Assets:A  1 USD\n  Assets:B\n";
    let result = parse(src);
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    assert_eq!(result.directives.len(), 1);
    assert!(result.comments.is_empty(), "{:?}", result.comments);
    assert_lossless(src);

    // The column-0 tag lexes as a TAG, and its string stays a STRING; a
    // lossless check alone would also pass if the line were one comment.
    let tag_line = "#tag \"x\"\n";
    let tokens = tokenize_lossless(tag_line);
    assert!(matches!(tokens[0].0, Token::Tag("#tag")), "{tokens:?}");
    assert!(
        tokens.iter().any(|(t, _)| matches!(t, Token::String(_))),
        "{tokens:?}"
    );
    assert!(parse(tag_line).comments.is_empty());
    assert_lossless("#tag \"x\n2024-01-02 open Assets:B\n");
}
