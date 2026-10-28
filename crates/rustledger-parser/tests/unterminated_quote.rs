//! An unterminated `"` must not hide everything after it (#2784).
//!
//! The lexer has one `String` regex. When a `"` has no closing quote before
//! the end of the file, logos reports everything it scanned as ONE error
//! token, so a single typo (`2024-01-01 * "Lunch`) took every later directive
//! with it behind one error that ran to the end of the file. Beancount
//! reports the stray quote and carries on with the next line. The error now
//! ends at its own line and lexing resumes there. A terminated string may
//! still span lines.

use rustledger_core::Directive;
use rustledger_parser::cst::parse_red_only;
use rustledger_parser::logos_lexer::{Token, tokenize_lossless};
use rustledger_parser::{ParseResult, parse, parse_structured};

/// `(kind, start, end)` for each error.
fn errors(result: &ParseResult) -> Vec<(String, usize, usize)> {
    result
        .errors
        .iter()
        .map(|e| (e.kind.to_string(), e.span.start, e.span.end))
        .collect()
}

/// The parsed directives as `date kind account` lines.
fn summary(result: &ParseResult) -> Vec<String> {
    result
        .directives
        .iter()
        .map(|d| match &d.value {
            Directive::Open(o) => format!("{} open {}", o.date, o.account),
            Directive::Note(n) => format!("{} note {} {:?}", n.date, n.account, n.comment),
            Directive::Transaction(t) => format!("{} txn {} postings", t.date, t.postings.len()),
            other => panic!("unexpected directive {other:?}"),
        })
        .collect()
}

/// Lossless, and the green-wired `parse` agrees with the pure-red path.
fn assert_invariants(src: &str) {
    let mut at = 0;
    for (token, span) in tokenize_lossless(src) {
        assert_eq!(span.start, at, "{src:?}: gap or overlap before {token:?}");
        at = span.end;
    }
    assert_eq!(at, src.len(), "{src:?}");
    assert_eq!(parse_structured(src).text().to_string(), src, "{src:?}");
    let (green, red) = (parse(src), parse_red_only(src));
    assert_eq!(
        format!("{:?}", green.directives),
        format!("{:?}", red.directives),
        "{src:?}"
    );
    assert_eq!(
        format!("{:?}", green.errors),
        format!("{:?}", red.errors),
        "{src:?}"
    );
}

const UNEXPECTED: &str = "parse error: unexpected input";

#[test]
fn test_parse_unterminated_quote_keeps_the_following_directives() {
    let cases: [(&str, &[(usize, usize)], &[&str]); 4] = [
        (
            "\"\n2024-01-02 open Assets:B\n2024-01-03 open Assets:C\n",
            &[(0, 2)],
            &["2024-01-02 open Assets:B", "2024-01-03 open Assets:C"],
        ),
        (
            "2024-01-01 open Assets:A\n\"x\r\n2024-01-02 open Assets:B\r\n",
            &[(25, 29)],
            &["2024-01-01 open Assets:A", "2024-01-02 open Assets:B"],
        ),
        // An escaped quote cannot close the string either.
        (
            "2024-01-01 open Assets:A\n\"a\\\"b\n2024-01-02 open Assets:B\n",
            &[(25, 31)],
            &["2024-01-01 open Assets:A", "2024-01-02 open Assets:B"],
        ),
        // The last line: nothing follows, nothing changes.
        (
            "2024-01-01 open Assets:A\n\"tail",
            &[(25, 30)],
            &["2024-01-01 open Assets:A"],
        ),
    ];
    for (src, spans, expected) in cases {
        let result = parse(src);
        let expected_errors: Vec<(String, usize, usize)> = spans
            .iter()
            .map(|&(s, e)| (UNEXPECTED.to_string(), s, e))
            .collect();
        assert_eq!(errors(&result), expected_errors, "{src:?}");
        assert_eq!(summary(&result), expected, "{src:?}");
        assert_invariants(src);
    }
}

/// The reported shape: a narration typo. Everything after it is kept, as in
/// beancount. The transaction itself is kept too, with its header error
/// reported; beancount drops it. Keeping it is a deliberate divergence
/// (Python Compatibility Policy): its postings still get checked, and the
/// error already marks it.
#[test]
fn test_parse_unterminated_narration_keeps_the_rest_of_the_ledger() {
    let src = "2024-01-01 * \"Lunch\n  Assets:A  1 USD\n  Assets:B\n2024-01-02 open Assets:B\n";
    let result = parse(src);
    assert_eq!(
        errors(&result),
        [
            (
                "parse error: unexpected \"\\\"Lunch\" in transaction header".to_string(),
                13,
                19
            ),
            (UNEXPECTED.to_string(), 13, 19),
        ]
    );
    assert_eq!(
        summary(&result),
        ["2024-01-01 txn 2 postings", "2024-01-02 open Assets:B"]
    );
    assert_invariants(src);
}

/// The other way a string scan fails: a `\` right before a line break
/// (`\\.` does not match a newline) inside an otherwise closed multi-line
/// string. The scan stops there, not at the end of the file, and the cut
/// re-lexes from the first line's end: every quote in the scanned region
/// was escaped, so re-lexing meets the same stop and the quotes pair up as
/// before. Pinned here because the cut's comment reasons about this case.
#[test]
fn test_parse_backslash_before_newline_in_a_string_keeps_its_pairing() {
    let src = "2024-01-01 note Assets:A \"ab\ncd\\\nef\"\n\
               2024-01-02 open Assets:B\n\
               2024-01-03 note Assets:A \"z\"\n\
               2024-01-04 open Assets:C\n";
    let result = parse(src);
    assert_eq!(
        errors(&result),
        [
            (UNEXPECTED.to_string(), 0, 29),
            (UNEXPECTED.to_string(), 25, 28),
            (UNEXPECTED.to_string(), 29, 33),
            (UNEXPECTED.to_string(), 33, 91),
        ]
    );
    assert_eq!(summary(&result), ["2024-01-04 open Assets:C"]);
    assert_invariants(src);
}

/// The error token is the quote and the rest of its line, ending before the
/// line's `\r\n`; lexing resumes with the `Newline`.
#[test]
fn test_tokenize_lossless_unterminated_quote_ends_at_its_line() {
    let tokens = tokenize_lossless("\"ab\r\nx");
    let shapes: Vec<(&Token<'_>, usize, usize)> =
        tokens.iter().map(|(t, s)| (t, s.start, s.end)).collect();
    assert!(
        matches!(
            shapes.as_slice(),
            [(Token::Error("\"ab"), 0, 3), (Token::Newline, 3, 5), ..]
        ),
        "{shapes:?}"
    );
}

/// A terminated string still spans lines, and a later string still closes a
/// quote that only LOOKED unterminated on its own line.
#[test]
fn test_parse_terminated_multiline_strings_are_unchanged() {
    for (src, expected) in [
        (
            "2024-01-01 note Assets:A \"two\nlines\"\n2024-01-02 open Assets:B\n",
            &[
                "2024-01-01 note Assets:A \"two\\nlines\"",
                "2024-01-02 open Assets:B",
            ][..],
        ),
        (
            "2024-01-01 note Assets:A \"a\r\nb\"\r\n",
            &["2024-01-01 note Assets:A \"a\\r\\nb\""][..],
        ),
    ] {
        let result = parse(src);
        assert!(result.errors.is_empty(), "{src:?}: {:?}", result.errors);
        assert_eq!(summary(&result), expected, "{src:?}");
        assert_invariants(src);
    }
}
