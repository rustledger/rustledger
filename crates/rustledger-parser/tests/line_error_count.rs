//! The leniencies of #2787, each checked against bean-check 3.2.3.
//!
//! - A line beancount cannot read gets as many errors as beancount reports
//!   for it: one `Invalid token` for each token its lexer cannot read, plus a
//!   syntax error when its grammar fails at a readable token first. `  * h`
//!   after a transaction's postings gave two overlapping errors here; it is
//!   one there (the `*` is a posting flag, then `h` is unreadable), while
//!   `  ** h` and `  @ x` are two.
//! - A lone `*` line, a trailing `*` after a directive and a one-character
//!   metadata key are errors, as there. Those were fixed earlier (#2779,
//!   #2802, #1955) and are pinned here with the rest of the issue.

use rustledger_parser::parse;

/// The 1-based line of each parse error, in order.
fn error_lines(src: &str) -> Vec<usize> {
    let mut lines: Vec<usize> = parse(src)
        .errors
        .iter()
        .map(|e| src[..e.span.start].matches('\n').count() + 1)
        .collect();
    lines.sort_unstable();
    lines
}

#[test]
fn test_parse_reports_a_broken_body_line_as_often_as_beancount() {
    let head = "2024-01-01 open Assets:A\n2024-01-01 open Assets:B\n\
                2024-01-02 *\n  Assets:A  1 USD\n  Assets:B\n";
    let tail = "2024-01-03 open Assets:C\n";
    for (line, count) in [
        ("  * h", 1),
        ("  ! h", 1),
        ("  * \"h", 1),
        ("  *h", 1),
        ("  h", 1),
        ("  h: 1", 1),
        ("  k: 1", 1),
        ("  * h x", 2),
        ("  k: 1 h", 2),
        ("  ** h", 2),
        ("  @ x", 2),
        ("  kk: 1 h", 1),
        ("  Assets:A 1 USD h", 1),
        ("  Assets:A h", 1),
        ("  Assets:A  -39.65 oops USD", 1),
        ("  Assets:A  1 USD oops", 1),
        ("  ! Assets:A  1 h USD", 1),
        ("  ofxid*: \"x\"", 1),
        // The grammar fails at the `*` after the account, before `f855c`.
        ("  Assets:A****7f855c 1 USD", 2),
    ] {
        let src = format!("{head}{line}\n{tail}");
        assert_eq!(error_lines(&src), vec![6; count], "{src:?}");
    }
    // Under a posting, too.
    let src = "2024-01-01 *\n  k: 1\n  Assets:A  1 USD\n    p: 2\n  Assets:B\n";
    assert_eq!(error_lines(src), [2, 4], "{src:?}");
}

#[test]
fn test_parse_reports_the_other_leniencies_of_2787() {
    // A lone `*` line.
    assert_eq!(error_lines("*\n2024-01-02 open Assets:B\n"), [1]);
    // A trailing `*` after each directive kind.
    for directive in [
        "2024-01-01 open Assets:A",
        "2024-01-01 close Assets:A",
        "2024-01-01 commodity USD",
        "2024-01-01 balance Assets:A 1 USD",
        "2024-01-01 price USD 1 EUR",
        "2024-01-01 note Assets:A \"x\"",
        "2024-01-01 event \"a\" \"b\"",
        "2024-01-01 pad Assets:A Assets:B",
        "2024-01-01 document Assets:A \"p\"",
        "2024-01-01 query \"a\" \"b\"",
        "option \"title\" \"x\"",
        "plugin \"p\"",
    ] {
        let src = format!("{directive} *\n");
        assert_eq!(error_lines(&src), [1], "{src:?}");
    }
    // A one-character metadata key.
    assert_eq!(error_lines("2024-01-01 open Assets:A\n  k: 1\n"), [2]);
    assert_eq!(
        error_lines("2024-01-01 open Assets:A\n  kk: 1\n"),
        Vec::<usize>::new()
    );
}
