//! An indented top-level `*` line is an error, not an org-mode heading
//! (#2783).
//!
//! Only a `*` at column 0 is a heading, which beancount ignores and rledger
//! keeps as a silenced section-marker line. The silencing checks matched the
//! line's first NON-TRIVIA token, so an indented `  * h` was silenced too,
//! where beancount reports `syntax error, unexpected INDENT`. With a `"` on
//! such a line the string swallowed the following directives inside the
//! silenced node, and `rledger check` reported nothing. The line is now an
//! ordinary error line, on both conversion paths, so the loss is reported.
//! (Keeping the swallowed directives is #2784: a stray `"` should not run
//! past its line.)

use rustledger_core::Directive;
use rustledger_parser::cst::parse_red_only;
use rustledger_parser::{ParseResult, parse};

/// `(kind, start, end)` for each error.
fn errors(result: &ParseResult) -> Vec<(String, usize, usize)> {
    result
        .errors
        .iter()
        .map(|e| (e.kind.to_string(), e.span.start, e.span.end))
        .collect()
}

/// The parsed directives as `date account` lines.
fn summary(result: &ParseResult) -> Vec<String> {
    result
        .directives
        .iter()
        .map(|d| match &d.value {
            Directive::Open(o) => format!("{} {}", o.date, o.account),
            other => panic!("unexpected directive {other:?}"),
        })
        .collect()
}

/// The green-wired `parse` and the pure-red path agree on the result.
fn assert_green_eq_red(src: &str) {
    let green = parse(src);
    let red = parse_red_only(src);
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
    assert_eq!(
        format!("{:?}", green.comments),
        format!("{:?}", red.comments),
        "{src:?}"
    );
}

const UNEXPECTED: &str = "parse error: unexpected input";

#[test]
fn test_parse_indented_star_line_is_reported() {
    let cases: [(&str, &[&str], (usize, usize)); 4] = [
        // At the start of the file the indentation sits before the error
        // node, so the error span starts at the `*`.
        (
            "  * h x\n2024-01-02 open Assets:B\n",
            &["2024-01-02 Assets:B"],
            (2, 8),
        ),
        (
            "\t* h x\n2024-01-02 open Assets:B\n",
            &["2024-01-02 Assets:B"],
            (1, 7),
        ),
        (
            "2024-01-01 open Assets:A\n  * h x\n2024-01-02 open Assets:B\n",
            &["2024-01-01 Assets:A", "2024-01-02 Assets:B"],
            (25, 33),
        ),
        (
            "2024-01-01 open Assets:A\n  ** h x\n2024-01-02 open Assets:B\n",
            &["2024-01-01 Assets:A", "2024-01-02 Assets:B"],
            (25, 34),
        ),
    ];
    for (src, expected, span) in cases {
        let result = parse(src);
        assert_eq!(
            errors(&result),
            [(UNEXPECTED.to_string(), span.0, span.1)],
            "{src:?}"
        );
        assert_eq!(summary(&result), expected, "{src:?}");
        assert!(result.comments.is_empty(), "{src:?}: {:?}", result.comments);
        assert_green_eq_red(src);
    }
}

/// The reported case: a `"` on the indented line still opens a string that
/// runs on (that is #2784), but the line is now an error instead of a
/// silenced heading, so the loss is visible.
#[test]
fn test_parse_indented_star_line_with_quote_is_not_silent() {
    for src in [
        "  * h \"x\n2024-01-02 open Assets:B\n2024-01-03 open Assets:C\n",
        "2024-01-01 open Assets:A\n  * h \"x\n2024-01-02 open Assets:B\n",
    ] {
        let result = parse(src);
        let star = src.find('*').expect("the line has a star");
        let errs = errors(&result);
        assert_eq!(errs.len(), 1, "{src:?}: {errs:?}");
        assert_eq!(errs[0].0, UNEXPECTED, "{src:?}");
        // The error starts on the indented line (at its indentation, or at
        // the `*` when the indentation precedes the error node).
        let line_start = src[..star].rfind('\n').map_or(0, |i| i + 1);
        assert!(
            errs[0].1 == line_start || errs[0].1 == star,
            "{src:?}: {errs:?}"
        );
        assert!(result.comments.is_empty(), "{src:?}: {:?}", result.comments);
        assert_green_eq_red(src);
    }
}

/// A column-0 heading is unchanged: no error, one section-marker comment
/// spanning its line, the directive after it kept.
#[test]
fn test_parse_column0_heading_is_still_silenced() {
    for src in [
        "* h \"x\n2024-01-02 open Assets:B\n",
        "2024-01-01 open Assets:A\n** h x\n2024-01-02 open Assets:B\n",
    ] {
        let result = parse(src);
        assert!(result.errors.is_empty(), "{src:?}: {:?}", result.errors);
        let heading_start = src.find('*').expect("the line has a star");
        let heading_end = heading_start + src[heading_start..].find('\n').unwrap() + 1;
        let comments: Vec<(&str, usize, usize)> = result
            .comments
            .iter()
            .map(|c| (c.value.as_str(), c.span.start, c.span.end))
            .collect();
        assert_eq!(comments, [("", heading_start, heading_end)], "{src:?}");
        assert!(
            summary(&result).contains(&"2024-01-02 Assets:B".to_string()),
            "{src:?}"
        );
        assert_green_eq_red(src);
    }
}

/// An indented `*` inside a transaction is a posting flag, as before.
#[test]
fn test_parse_star_posting_flag_is_unchanged() {
    let src = "2024-01-01 * \"x\"\n  * Assets:A  1 USD\n  Assets:B\n";
    let result = parse(src);
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    assert_eq!(result.directives.len(), 1);
    assert!(result.comments.is_empty(), "{:?}", result.comments);
    assert_green_eq_red(src);
}
