//! An indented tag or link line in a transaction, then an invalid token, is
//! one error, as in beancount (#2997).
//!
//! beancount's grammar reads a line of tags and links in a transaction's body
//! (`posting_or_kv_list INDENT tags_links EOL`), so on `  #tag h` its first
//! error is the lexer's `Invalid token: 'h'`, and its recovery discards the
//! rest of the line. The line error here stands for that token. Under any
//! other directive such a line is a syntax error at the tag first, and both
//! errors stay.
//!
//! Where a lone capital glued to what follows it (`Z\r`, `Z` at the end of
//! the input) comes later on the line, beancount reports it as one more
//! invalid token, which nothing here reports yet (`  h1 Z\r\n` is one error
//! here, two there): such a line keeps both its errors, as before #2997.
//!
//! Every expected count below was checked against `bean-check` 3.2.3
//! (`beancount.parser.parser.parse_string`, the parity harness's ground
//! truth).

use rustledger_parser::cst::parse_red_only;
use rustledger_parser::parse;

/// The errors of `src` per line (1-based, counting `\n` only, as
/// `rledger check` does): `(line, count)`, in line order. The green and the
/// red converter agree on them.
fn per_line(src: &str) -> Vec<(usize, usize)> {
    let count = |errors: &[rustledger_parser::ParseError]| {
        let mut counts: Vec<(usize, usize)> = Vec::new();
        for e in errors {
            let line = 1 + src[..e.span.start].matches('\n').count();
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

fn assert_counts(cases: &[(String, Vec<(usize, usize)>)]) {
    for (src, expected) in cases {
        assert_eq!(&per_line(src), expected, "{src:?}");
    }
}

/// The issue's prefix: one open.
const P: &str = "2024-01-01 open Assets:A\n";
/// The issue's transaction header.
const T: &str = "2024-01-02 * \"n\"\n";
/// Two postings that balance.
const POSTINGS: &str = "  Assets:A 1 USD\n  Assets:A -1 USD\n";

/// The issue's rows.
#[test]
fn test_parse_tag_line_then_invalid_token_in_transaction_is_one_error() {
    assert_counts(&[
        (format!("{P}{T}  #tag h\n"), vec![(3, 1)]),
        (format!("{P}{T}  ^link h\n"), vec![(3, 1)]),
        (format!("{P}{T}  #tag $\n"), vec![(3, 1)]),
        (format!("{P}{T}  #tag hh\n"), vec![(3, 1)]),
    ]);
}

/// The issue's controls, unchanged.
#[test]
fn test_parse_tag_line_controls_keep_their_counts() {
    assert_counts(&[
        // Under `open` the tag is a syntax error first.
        (format!("{P}  #tag h\n"), vec![(2, 2)]),
        (format!("{P}{T}  h\n"), vec![(3, 1)]),
        (format!("{P}{T}  Assets:A 1 USD h\n"), vec![(3, 1)]),
        (format!("{P}{T}  #tag\n{POSTINGS}"), vec![]),
    ]);
}

/// More tag-and-link prefixes, indentations, line endings and places in the
/// body.
#[test]
fn test_parse_tag_line_then_invalid_token_variants() {
    assert_counts(&[
        (format!("{P}{T}  #a ^l h\n"), vec![(3, 1)]),
        (format!("{P}{T}\t^l h\n"), vec![(3, 1)]),
        (format!("{P}{T}      #a h\n"), vec![(3, 1)]),
        (format!("{P}{T}  #a$\n"), vec![(3, 1)]),
        (format!("{P}{T}  #a h #b\n"), vec![(3, 1)]),
        (format!("{P}{T}  #a h ;c\n"), vec![(3, 1)]),
        (format!("{P}{T}  #a h\r\n"), vec![(3, 1)]),
        (format!("{P}{T}  #a h"), vec![(3, 1)]),
        (format!("{P}{T}  #a h\n{POSTINGS}"), vec![(3, 1)]),
        (format!("{P}2024-01-02 txn\n  #a $\n"), vec![(3, 1)]),
        // After a posting: beancount's grammar reads the line there too.
        (format!("{P}{T}  Assets:A 1 USD\n  #a h\n"), vec![(4, 1)]),
        (format!("{P}{T}  Assets:A 1 USD\n    #a h\n"), vec![(4, 1)]),
        // Each later invalid token is one more.
        (format!("{P}{T}  #a h x\n"), vec![(3, 2)]),
    ]);
}

/// A token beancount's grammar does not take after tags fails first, so the
/// line keeps both its errors.
#[test]
fn test_parse_tag_line_then_unreadable_start_keeps_both_errors() {
    assert_counts(&[
        (format!("{P}{T}  #a 1 h\n"), vec![(3, 2)]),
        (format!("{P}{T}  #a 2024-01-03 h\n"), vec![(3, 2)]),
        (format!("{P}{T}  #a Assets:B h\n"), vec![(3, 2)]),
    ]);
}

/// Under a directive other than a transaction a tag line is a syntax error
/// at the tag, then the invalid token.
#[test]
fn test_parse_tag_line_under_other_directives_keeps_both_errors() {
    assert_counts(&[
        (
            format!("{P}2024-01-02 balance Assets:A 1 USD\n  #a h\n"),
            vec![(3, 2)],
        ),
        (
            format!("{P}2024-01-02 event \"e\" \"v\"\n  #a h\n"),
            vec![(3, 2)],
        ),
        (
            format!("{P}2024-01-02 custom \"b\" 1\n  #a h\n"),
            vec![(3, 2)],
        ),
        (
            format!("{P}2024-01-02 note Assets:A \"x\"\n  ^l h\n"),
            vec![(3, 2)],
        ),
    ]);
}

/// A lone capital glued to a `\r` or to the end of the input later on the
/// line is one more invalid token in beancount, which nothing here reports
/// yet: the line keeps both its errors, as before #2997.
#[test]
fn test_parse_tag_line_with_glued_lone_capital_keeps_both_errors() {
    assert_counts(&[
        (format!("{P}{T}  #a h1 Z"), vec![(3, 2)]),
        (format!("{P}{T}  #a h1 Z\r\n"), vec![(3, 2)]),
    ]);
}
