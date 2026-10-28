//! A transaction converts the same whatever precedes it (#2628), and string
//! escapes decode as beancount decodes them (#2672).
//!
//! Blank lines and comment lines before a transaction attach INSIDE its CST
//! node (the Directive-Terminator Rule), so the node can open with a NEWLINE.
//! Walks that took the first NEWLINE as the end of the header line put the
//! header-line comment into the first posting's `comments` and missed a
//! deprecated `|`, but only when something preceded the transaction.
//!
//! Every assertion runs on both converters: `parse` (green, falling back to
//! red) and `parse_red_only`.

use rustledger_core::format::{FormatConfig, format_directives};
use rustledger_core::{Directive, MetaValue, Transaction};
use rustledger_parser::cst::parse_red_only;
use rustledger_parser::{ParseErrorKind, ParseResult, parse};

/// The directive that precedes the transaction. Without one, leading trivia
/// attaches to the file node instead of the transaction, and the bug hides.
const OPEN: &str = "2024-01-01 open Assets:Cash\n";

/// What can sit between the preceding directive and the transaction.
const PREFIXES: &[&str] = &[
    "",
    "\n",
    "\n\n\n",
    "   \n",
    "; a comment line\n",
    "\n; a comment line\n\n",
    "% a ledger-style comment\n",
    "#+ an org-mode line\n",
];

fn both(source: &str) -> [(&'static str, ParseResult); 2] {
    [
        ("parse", parse(source)),
        ("parse_red_only", parse_red_only(source)),
    ]
}

/// The transaction, with every span dropped (the prefix shifts them).
fn txn_without_spans(result: &ParseResult) -> String {
    let txns: Vec<&Transaction> = result
        .directives
        .iter()
        .filter_map(|d| match &d.value {
            Directive::Transaction(t) => Some(t),
            _ => None,
        })
        .collect();
    assert_eq!(txns.len(), 1, "expected one transaction");
    let t = txns[0];
    let postings: Vec<_> = t.postings.iter().map(|p| &p.value).collect();
    format!(
        "{:?} {:?} {:?} {:?} {:?} {:?} {:?} {postings:?} {:?}",
        t.date, t.flag, t.payee, t.narration, t.tags, t.links, t.meta, t.trailing_comments
    )
}

#[test]
fn leading_trivia_does_not_change_a_transaction() {
    let txn = "2024-01-02 * \"Shop\" \"Groceries\" #food ; header comment\n  \
               ; before the first posting\n  \
               Expenses:Food  10.00 USD\n  \
               ; before the second posting\n  \
               Assets:Cash\n  \
               ; after the last posting\n";
    let mut expected: Option<String> = None;
    for prefix in PREFIXES {
        let source = format!("{OPEN}{prefix}{txn}");
        for (name, result) in both(&source) {
            assert!(
                result.errors.is_empty(),
                "{name} {prefix:?}: {:?}",
                result.errors
            );
            let got = txn_without_spans(&result);
            match &expected {
                None => expected = Some(got),
                Some(e) => assert_eq!(&got, e, "{name} with prefix {prefix:?}"),
            }
            let Directive::Transaction(t) = &result.directives[1].value else {
                panic!("{name}: second directive is not the transaction");
            };
            // The header-line comment belongs to no posting.
            assert_eq!(
                t.postings[0].value.comments,
                vec!["; before the first posting".to_string()].into(),
                "{name} with prefix {prefix:?}"
            );
            assert_eq!(
                t.postings[1].value.comments,
                vec!["; before the second posting".to_string()].into(),
                "{name} with prefix {prefix:?}"
            );
            assert_eq!(
                t.trailing_comments,
                vec!["; after the last posting".to_string()].into(),
                "{name} with prefix {prefix:?}"
            );
        }
    }
}

#[test]
fn header_comment_reaches_no_posting_after_leading_trivia() {
    // The shape #2614's split/merge check tripped on: no body comments at all.
    for prefix in PREFIXES {
        let source = format!(
            "{OPEN}{prefix}2024-01-02 * \"x\" ; header comment\n  Assets:Cash  1 USD\n  Assets:Cash\n"
        );
        for (name, result) in both(&source) {
            let Directive::Transaction(t) = &result.directives[1].value else {
                panic!("{name}: second directive is not the transaction");
            };
            for p in &t.postings {
                assert!(
                    p.value.comments.is_empty(),
                    "{name} {prefix:?}: {:?}",
                    p.value.comments
                );
            }
            assert!(t.trailing_comments.is_empty(), "{name} {prefix:?}");
        }
    }
}

#[test]
fn deprecated_pipe_is_reported_after_leading_trivia() {
    for prefix in PREFIXES {
        let source = format!(
            "{OPEN}{prefix}2024-01-02 * \"Shop\" | \"Groceries\"\n  Assets:Cash  1 USD\n  Assets:Cash\n"
        );
        for (name, result) in both(&source) {
            let pipes = result
                .errors
                .iter()
                .filter(|e| matches!(e.kind, ParseErrorKind::DeprecatedPipeSymbol))
                .count();
            assert_eq!(
                pipes, 1,
                "{name} with prefix {prefix:?}: {:?}",
                result.errors
            );
        }
    }
}

#[test]
fn backspace_and_form_feed_escapes_decode_like_beancount() {
    // beancount 3.2.3 loads this as payee 'p\x08q', narration
    // 'x\x08y\x0czaz' and key 'm\x0cn': `\b` and `\f` decode, `\a` drops the
    // backslash as every other unknown escape does.
    let source = "2024-01-02 * \"p\\bq\" \"x\\by\\fz\\az\"\n  \
                  key: \"m\\fn\"\n  \
                  Assets:Cash  0 USD\n\
                  2024-01-03 note Assets:Cash \"n\\bo\\fte\"\n\
                  plugin \"some.plugin\" \"{'k\\f': 1}\"\n";
    for (name, result) in both(source) {
        assert!(result.errors.is_empty(), "{name}: {:?}", result.errors);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("{name}: first directive is not the transaction");
        };
        assert_eq!(t.payee.as_deref(), Some("p\u{8}q"), "{name}");
        assert_eq!(t.narration.as_str(), "x\u{8}y\u{c}zaz", "{name}");
        assert_eq!(
            t.meta.get("key"),
            Some(&MetaValue::String("m\u{c}n".into())),
            "{name}"
        );
        let Directive::Note(n) = &result.directives[1].value else {
            panic!("{name}: second directive is not the note");
        };
        assert_eq!(n.comment, "n\u{8}o\u{c}te", "{name}");
        assert_eq!(
            result.plugins[0].1.as_deref(),
            Some("{'k\u{c}': 1}"),
            "{name}"
        );
    }
}

#[test]
fn printed_backspace_and_form_feed_parse_back_to_the_same_value() {
    // Printing keeps U+0008 / U+000C raw (#2538 decides output escaping); a
    // raw control character inside quotes parses back as itself, so the
    // printed ledger re-reads to the same strings, and printing that is a
    // fixed point.
    let source = "2024-01-02 * \"p\\bq\" \"x\\by\\fz\"\n  key: \"m\\fn\"\n  Assets:Cash  0 USD\n";
    let first = parse(source);
    let printed = format_directives(
        first.directives.iter().map(|d| &d.value),
        &FormatConfig::default(),
    );
    let second = parse(&printed);
    assert!(second.errors.is_empty(), "{:?}", second.errors);
    // Spans move (printing re-aligns), so compare everything but them.
    assert_eq!(txn_without_spans(&first), txn_without_spans(&second));
    let reprinted = format_directives(
        second.directives.iter().map(|d| &d.value),
        &FormatConfig::default(),
    );
    assert_eq!(printed, reprinted);
}

#[test]
fn format_source_keeps_backspace_and_form_feed_escapes_as_written() {
    let source = "2024-01-02 * \"x\\by\\fz\"\n  Assets:Cash  0 USD\n  Assets:Cash\n";
    let formatted = rustledger_parser::format::format_source(source);
    assert!(formatted.contains("\"x\\by\\fz\""), "{formatted:?}");
}
