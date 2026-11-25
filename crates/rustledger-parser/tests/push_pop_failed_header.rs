//! A `pushtag`, `poptag`, `pushmeta` or `popmeta` whose line has an error
//! changes no tag or metadata state, and a pop error is reported on the
//! pop's own line (#2995).
//!
//! beancount's grammar never reduces a statement whose line fails, and an
//! invalid date fails it too (the lexer raises it, so the parser never sees
//! the token). So a failed push pushes nothing: the matching pop reports the
//! absent tag, and a later transaction is not tagged. A failed pop pops
//! nothing: the push stays unbalanced and still tags later transactions, and
//! a failed pop of nothing pushed reports no absent tag. The parser used to
//! skip the state change only for an invalid token (`ERROR_TOKEN`).
//!
//! A directive node starts at the blank and comment lines before it, so the
//! pop errors, which took the node's span, were reported on a comment line.
//! They, and the unclosed-push errors, now start at the directive itself.
//!
//! Every count below was checked against beancount 3.2.3
//! (`beancount.parser.parser.parse_string`, the parity harness's ground
//! truth). An unclosed push is beancount's line 0 (end of file); rledger
//! reports it at the push, and `per_line` maps it to 0 as the harness does.

use rustledger_core::Directive;
use rustledger_parser::cst::parse_red_only;
use rustledger_parser::{ParseErrorKind, parse};

/// The errors of `src` per line (1-based, counting `\n` only, as
/// `rledger check` does; an unclosed push is line 0): `(line, count)`, in line
/// order. The green and the red converter agree on them.
fn per_line(src: &str) -> Vec<(usize, usize)> {
    let count = |errors: &[rustledger_parser::ParseError]| {
        let mut counts: Vec<(usize, usize)> = Vec::new();
        for e in errors {
            let line = if matches!(
                e.kind,
                ParseErrorKind::UnclosedPushtag(_) | ParseErrorKind::UnclosedPushmeta(_)
            ) {
                0
            } else {
                1 + src[..e.span.start].matches('\n').count()
            };
            match counts.iter_mut().find(|(l, _)| *l == line) {
                Some((_, n)) => *n += 1,
                None => counts.push((line, 1)),
            }
        }
        counts.sort_unstable();
        counts
    };
    let green = count(&parse(src).errors);
    assert_eq!(green, count(&parse_red_only(src).errors), "{src:?}");
    green
}

/// Each transaction's tags and its `kk` metadata value (as text), in source
/// order. The green and the red converter agree on them.
fn tag_state(src: &str) -> Vec<(Vec<String>, Option<String>)> {
    let state = |directives: &[rustledger_parser::Spanned<Directive>]| {
        directives
            .iter()
            .filter_map(|d| match &d.value {
                Directive::Transaction(t) => Some((
                    t.tags.iter().map(ToString::to_string).collect(),
                    t.meta.get("kk").map(ToString::to_string),
                )),
                _ => None,
            })
            .collect::<Vec<_>>()
    };
    let green = state(&parse(src).directives);
    assert_eq!(green, state(&parse_red_only(src).directives), "{src:?}");
    green
}

fn assert_counts(cases: &[(String, Vec<(usize, usize)>)]) {
    for (src, expected) in cases {
        assert_eq!(&per_line(src), expected, "{src:?}");
    }
}

/// The issue's prefix: one open.
const P: &str = "2024-01-01 open Assets:A\n";
/// A balanced transaction.
const T: &str = "2024-01-02 * \"n\"\n  Assets:A 1 USD\n  Assets:A -1 USD\n";

fn tagged(tags: &[&str], kk: Option<&str>) -> (Vec<String>, Option<String>) {
    (
        tags.iter().map(ToString::to_string).collect(),
        kk.map(ToString::to_string),
    )
}

/// The issue's rows.
#[test]
fn test_parse_push_pop_failed_header_issue_rows() {
    assert_counts(&[
        // A pop with a date error does not pop. bean-check: 0 3.
        (
            format!("{P}pushtag #a\npoptag #a 2024-02-30\n"),
            vec![(0, 1), (3, 1)],
        ),
        (
            format!("{P}pushmeta kk: \"v\"\npopmeta kk: 2024-02-30\n"),
            vec![(0, 1), (3, 1)],
        ),
        // A push with a date error does not push. bean-check: 2 3.
        (
            format!("{P}pushtag #a 2024-02-30\npoptag #a\n"),
            vec![(2, 1), (3, 1)],
        ),
        // bean-check: 2 (no unbalanced push).
        (format!("{P}pushtag #a 2024-02-30\n{T}"), vec![(2, 1)]),
        // bean-check: 1 3.
        (
            "pushtag #a 2024-02-30\n  ; c\npoptag #a\n".to_string(),
            vec![(1, 1), (3, 1)],
        ),
        // The pop error on the pop's line, not the comment's. bean-check: 1 3.
        (
            "pushmeta kk: \"v\" $\n  ; c\npopmeta kk:\n".to_string(),
            vec![(1, 1), (3, 1)],
        ),
        (
            "pushtag #a $\n  ; c\npoptag #a\n".to_string(),
            vec![(1, 1), (3, 1)],
        ),
        // A one-letter key makes the popmeta an invalid token. bean-check: 1x2 3.
        (
            "pushmeta k: \"v\" $\n  ; c\npopmeta k:\n".to_string(),
            vec![(1, 2), (3, 1)],
        ),
    ]);
}

/// The tags and metadata the issue's pushes and pops leave on a transaction
/// after them, as beancount's parser leaves them.
#[test]
fn test_parse_push_pop_failed_header_tag_state() {
    // A failed push tags nothing.
    assert_eq!(
        tag_state(&format!("{P}pushtag #a 2024-02-30\n{T}")),
        [tagged(&[], None)]
    );
    // A failed pop leaves the tag on.
    let src = format!("{P}pushtag #a\npoptag #a 2024-02-30\n{T}");
    assert_eq!(tag_state(&src), [tagged(&["a"], None)]);
    assert_eq!(per_line(&src), [(0, 1), (3, 1)]);
    // A failed popmeta leaves the key on.
    let src = format!("{P}pushmeta kk: \"v\"\npopmeta kk: 2024-02-30\n{T}");
    assert_eq!(tag_state(&src), [tagged(&[], Some("\"v\""))]);
    assert_eq!(per_line(&src), [(0, 1), (3, 1)]);
    // Nested: the inner push failed, so the first pop takes the outer one.
    let src = format!("{P}pushtag #a\npushtag #a 2024-02-30\n{T}poptag #a\n{T}poptag #a\n{T}");
    assert_eq!(
        tag_state(&src),
        [tagged(&["a"], None), tagged(&[], None), tagged(&[], None)]
    );
    // bean-check: 3 (the date), 11 (the second pop finds nothing).
    assert_eq!(per_line(&src), [(3, 1), (11, 1)]);
    // Nested: the first pop failed, so the second pops, and the tag holds
    // in between.
    let src = format!("{P}pushtag #a\npoptag #a #b\n{T}poptag #a\n{T}");
    assert_eq!(tag_state(&src), [tagged(&["a"], None), tagged(&[], None)]);
    assert_eq!(per_line(&src), [(3, 1)]);
}

/// Any error on the line fails it, not only an invalid date or token: a
/// token the statement does not take (a second tag, a valid date, a value on
/// a `popmeta`) pops nothing either, and a failed pop of nothing pushed
/// reports only its own error.
#[test]
fn test_parse_push_pop_any_header_error_changes_no_state() {
    assert_counts(&[
        // bean-check: 0 3 each.
        (
            format!("{P}pushtag #a\npoptag #a 2024-01-01\n"),
            vec![(0, 1), (3, 1)],
        ),
        (
            format!("{P}pushtag #a\npoptag #a #b\n"),
            vec![(0, 1), (3, 1)],
        ),
        (
            format!("{P}pushtag #a\npoptag #a $\n"),
            vec![(0, 1), (3, 1)],
        ),
        (
            format!("{P}pushmeta kk: \"v\"\npopmeta kk: \"v\"\n"),
            vec![(0, 1), (3, 1)],
        ),
        (
            format!("{P}pushmeta kk: \"v\"\npopmeta kk: 2024-01-01\n"),
            vec![(0, 1), (3, 1)],
        ),
        // A failed pop of nothing pushed: its error alone. bean-check: 2.
        (format!("{P}popmeta kk: 2024-02-30\n"), vec![(2, 1)]),
        (format!("{P}poptag #a 2024-02-30\n"), vec![(2, 1)]),
        (format!("{P}popmeta kk: Assets:A\n"), vec![(2, 1)]),
        // A failed push is a later pop's absent tag. bean-check: 2 3.
        (
            format!("{P}pushtag #a 2024-01-01\npoptag #a\n"),
            vec![(2, 1), (3, 1)],
        ),
        (
            format!("{P}pushtag #a #b\npoptag #a\n"),
            vec![(2, 1), (3, 1)],
        ),
        (
            format!("{P}pushmeta kk: \"v\" 2024-02-30\npopmeta kk:\n"),
            vec![(2, 1), (3, 1)],
        ),
        (
            format!("{P}pushmeta kk: 2024-02-30\npopmeta kk:\n"),
            vec![(2, 1), (3, 1)],
        ),
        // Two errors on the failed pop, one each. bean-check: 0 3x2.
        (
            format!("{P}pushtag #a\npoptag #a 2024-02-30 $\n"),
            vec![(0, 1), (3, 2)],
        ),
    ]);
}

/// The pop errors and unclosed pushes start at the directive, past the blank
/// and comment lines before it.
#[test]
fn test_parse_push_pop_errors_skip_leading_trivia() {
    assert_counts(&[
        // bean-check: 0 4 each: the pop of a tag never pushed is on line 4.
        (
            format!("{P}pushtag #a\n; c\npoptag #b\n"),
            vec![(0, 1), (4, 1)],
        ),
        (
            format!("{P}pushtag #a\n\npoptag #b\n"),
            vec![(0, 1), (4, 1)],
        ),
        // An indented comment after a push that succeeded is `unexpected
        // INDENT`, as the push takes no metadata. bean-check: 0 3 4.
        (
            format!("{P}pushtag #a\n  ; c\npopmeta kk:\n"),
            vec![(0, 1), (3, 1), (4, 1)],
        ),
        // bean-check: 1 4.
        (
            "pushtag #a $\n; c\n\npoptag #a\n".to_string(),
            vec![(1, 1), (4, 1)],
        ),
    ]);
    // The spans themselves: the pop error and the unclosed push start at
    // their keyword.
    let src = "; c\n\npushtag #a\n; d\npoptag #b\n";
    let result = parse(src);
    for e in &result.errors {
        let at = &src[e.span.start..];
        assert!(
            at.starts_with("pushtag #a") || at.starts_with("poptag #b"),
            "{e:?} starts at {at:?}"
        );
    }
    assert_eq!(result.errors.len(), 2, "{:?}", result.errors);
}

/// A key pushed twice and never popped is one error, as in beancount; each
/// leftover pushed tag is its own.
#[test]
fn test_parse_unclosed_pushmeta_is_one_error_per_key() {
    assert_counts(&[
        // bean-check: 0 (`leftover metadata 'v, w'`).
        (
            "pushmeta kk: \"v\"\npushmeta kk: \"w\"\n".to_string(),
            vec![(0, 1)],
        ),
        // bean-check: 0x2.
        ("pushtag #a\npushtag #a\n".to_string(), vec![(0, 2)]),
        // bean-check: 0x2, one per key.
        (
            "pushmeta kk: \"v\"\npushmeta jj: \"w\"\npushmeta kk: \"x\"\n".to_string(),
            vec![(0, 2)],
        ),
        // One push of the key left. bean-check: 0.
        (
            "pushmeta kk: \"v\"\npushmeta kk: \"w\"\npopmeta kk:\n".to_string(),
            vec![(0, 1)],
        ),
    ]);
}

/// CRLF line ends and a leading BOM change nothing.
#[test]
fn test_parse_push_pop_failed_header_crlf_and_bom() {
    for (src, expected) in [
        (
            format!("{P}pushtag #a\npoptag #a 2024-02-30\n"),
            vec![(0, 1), (3, 1)],
        ),
        (
            "pushtag #a 2024-02-30\n  ; c\npoptag #a\n".to_string(),
            vec![(1, 1), (3, 1)],
        ),
        (
            "pushtag #a $\n  ; c\npoptag #a\n".to_string(),
            vec![(1, 1), (3, 1)],
        ),
    ] {
        let crlf = src.replace('\n', "\r\n");
        assert_eq!(per_line(&crlf), expected, "{crlf:?}");
        let bom = format!("\u{feff}{src}");
        assert_eq!(per_line(&bom), expected, "{bom:?}");
    }
    let src = format!("\u{feff}{P}pushtag #a\npoptag #a 2024-02-30\n{T}").replace('\n', "\r\n");
    assert_eq!(tag_state(&src), [tagged(&["a"], None)]);
}

/// The other error that took a directive's whole node span: the deprecated
/// `|` on a transaction header is on the header's line, not on a comment
/// above it. bean-check: 3.
#[test]
fn test_parse_deprecated_pipe_skips_leading_trivia() {
    assert_counts(&[
        (
            format!("{P}; c\n2024-01-02 * \"a\" | \"b\"\n  Assets:A 1 USD\n  Assets:A -1 USD\n"),
            vec![(3, 1)],
        ),
        (
            format!("{P}\n2024-01-02 * \"a\" | \"b\"\n  Assets:A 1 USD\n  Assets:A -1 USD\n"),
            vec![(3, 1)],
        ),
    ]);
}
