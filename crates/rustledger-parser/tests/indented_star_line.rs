//! An indented top-level `*` line is an error, not an org-mode heading
//! (#2783).
//!
//! Only a `*` at column 0 is a heading, which beancount ignores and rledger
//! keeps as a silenced section-marker line. The silencing checks matched the
//! line's first NON-TRIVIA token, so an indented `  * h` was silenced too,
//! where beancount reports a syntax error (`unexpected INDENT`, or
//! `unexpected ASTERISK` after a directive). With a `"` on such a line the
//! string swallowed the following directives inside the silenced node, and
//! `rledger check` reported nothing. The line is now an ordinary error line,
//! on both conversion paths, so the loss is reported. (Keeping the swallowed
//! directives is #2784: a stray `"` should not run past its line.)

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

/// `(value, start, end)` for each comment.
fn comments(result: &ParseResult) -> Vec<(String, usize, usize)> {
    result
        .comments
        .iter()
        .map(|c| (c.value.clone(), c.span.start, c.span.end))
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

/// One input: its exact errors (as spans of `unexpected input`), exact
/// section-marker comments (as spans), and the opens that survive.
struct Case {
    src: &'static str,
    errors: &'static [(usize, usize)],
    comments: &'static [(usize, usize)],
    opens: &'static [&'static str],
}

fn check(case: &Case) {
    let result = parse(case.src);
    let expected_errors: Vec<(String, usize, usize)> = case
        .errors
        .iter()
        .map(|&(s, e)| (UNEXPECTED.to_string(), s, e))
        .collect();
    assert_eq!(errors(&result), expected_errors, "{:?}", case.src);
    let expected_comments: Vec<(String, usize, usize)> = case
        .comments
        .iter()
        .map(|&(s, e)| (String::new(), s, e))
        .collect();
    assert_eq!(comments(&result), expected_comments, "{:?}", case.src);
    assert_eq!(summary(&result), case.opens, "{:?}", case.src);
    assert_green_eq_red(case.src);
}

const A: &str = "2024-01-01 Assets:A";
const B: &str = "2024-01-02 Assets:B";

#[test]
fn test_parse_indented_star_line_is_reported() {
    for case in [
        // At the start of the file the indentation sits before the error
        // node, so the error span starts at the `*`; mid-file it starts at
        // the line start, as for any indented junk line (`  @@ x`).
        Case {
            src: "  * h x\n2024-01-02 open Assets:B\n",
            errors: &[(2, 8)],
            comments: &[],
            opens: &[B],
        },
        Case {
            src: "\t* h x\n2024-01-02 open Assets:B\n",
            errors: &[(1, 7)],
            comments: &[],
            opens: &[B],
        },
        Case {
            src: "2024-01-01 open Assets:A\n  * h x\n2024-01-02 open Assets:B\n",
            errors: &[(25, 33)],
            comments: &[],
            opens: &[A, B],
        },
        Case {
            src: "2024-01-01 open Assets:A\n  ** h x\n2024-01-02 open Assets:B\n",
            errors: &[(25, 34)],
            comments: &[],
            opens: &[A, B],
        },
        // A bare indented `*`, a CRLF line, the last line without a newline
        // (the walkers' end-of-file flush), and after an indented comment.
        Case {
            src: "2024-01-01 open Assets:A\n  *\n2024-01-02 open Assets:B\n",
            errors: &[(25, 29)],
            comments: &[],
            opens: &[A, B],
        },
        Case {
            src: "2024-01-01 open Assets:A\n  * h x\r\n2024-01-02 open Assets:B\r\n",
            errors: &[(25, 34)],
            comments: &[],
            opens: &[A, B],
        },
        Case {
            src: "2024-01-01 open Assets:A\n  * h x",
            errors: &[(25, 32)],
            comments: &[],
            opens: &[A],
        },
        Case {
            src: "2024-01-01 open Assets:A\n  ; c\n  * h x\n2024-01-02 open Assets:B\n",
            errors: &[(31, 39)],
            comments: &[],
            opens: &[A, B],
        },
    ] {
        check(&case);
    }
}

/// The reported case: a `"` on the indented line still opens a string that
/// runs to the end of the file (that is #2784, which will change these
/// rows), but the line is now an error instead of a silenced heading, so
/// the loss is visible.
#[test]
fn test_parse_indented_star_line_with_quote_is_not_silent() {
    for case in [
        Case {
            src: "  * h \"x\n2024-01-02 open Assets:B\n2024-01-03 open Assets:C\n",
            errors: &[(2, 59)],
            comments: &[],
            opens: &[],
        },
        Case {
            src: "2024-01-01 open Assets:A\n  * h \"x\n2024-01-02 open Assets:B\n",
            errors: &[(25, 59)],
            comments: &[],
            opens: &[A],
        },
    ] {
        check(&case);
    }
}

/// A `*` after a BOM is not at column 0 either. `parse` strips one leading
/// BOM, so it takes a second one, or a BOM then indentation, to get here;
/// beancount rejects the BOM (`Invalid token`), as rledger does before a
/// directive.
#[test]
fn test_parse_star_after_bom_is_reported() {
    for case in [
        Case {
            src: "\u{feff}\u{feff}* h x\n2024-01-02 open Assets:B\n",
            errors: &[(6, 12)],
            comments: &[],
            opens: &[B],
        },
        Case {
            src: "\u{feff}  * h x\n2024-01-02 open Assets:B\n",
            errors: &[(5, 11)],
            comments: &[],
            opens: &[B],
        },
    ] {
        check(&case);
    }
}

/// Column-0 headings are unchanged: no error, one section-marker comment
/// spanning exactly the heading line, the directives around it kept. In a
/// multi-line error node the column-0 heading stays silenced while an
/// indented `*` line in the same node is reported.
#[test]
fn test_parse_column0_heading_is_still_silenced() {
    for case in [
        Case {
            src: "* h \"x\n2024-01-02 open Assets:B\n",
            errors: &[],
            comments: &[(0, 7)],
            opens: &[B],
        },
        Case {
            src: "2024-01-01 open Assets:A\n** h x\n2024-01-02 open Assets:B\n",
            errors: &[],
            comments: &[(25, 32)],
            opens: &[A, B],
        },
        Case {
            src: "2024-01-01 open Assets:A\n@@ junk\n* heading\n  * ind\n2024-01-02 open Assets:B\n",
            errors: &[(25, 33), (43, 51)],
            comments: &[(33, 43)],
            opens: &[A, B],
        },
    ] {
        check(&case);
    }
}

/// An indented `*` inside a transaction is a posting flag, as before.
#[test]
fn test_parse_star_posting_flag_is_unchanged() {
    let src = "2024-01-01 * \"x\"\n  * Assets:A  1 USD\n  Assets:B\n";
    let result = parse(src);
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    assert!(result.comments.is_empty(), "{:?}", result.comments);
    let [d] = result.directives.as_slice() else {
        panic!("{:?}", result.directives)
    };
    let Directive::Transaction(t) = &d.value else {
        panic!("{d:?}")
    };
    let flags: Vec<Option<char>> = t.postings.iter().map(|p| p.flag).collect();
    assert_eq!(flags, [Some('*'), None]);
    assert_green_eq_red(src);
}
