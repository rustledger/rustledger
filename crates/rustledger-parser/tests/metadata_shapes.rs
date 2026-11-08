//! Metadata shapes beancount 3.2.3 rejects (#2813), each checked against
//! bean-check.
//!
//! - An indented line right after a directive that takes no metadata
//!   (`option`, `include`, `plugin`, `pushtag`, `poptag`, `pushmeta`,
//!   `popmeta`) is `syntax error, unexpected INDENT` there, once per indented
//!   block. rledger absorbed `  kk: 1` into the directive and dropped it.
//! - A posting's `filename:` or `lineno:` is `Duplicate posting metadata
//!   field` there, at the transaction's line.
//! - `True` / `true` / `False` / `false` are not booleans (see
//!   `parser_integration_test.rs`), and an account value with an invalid root
//!   is the validator's `E1005` (see `rustledger-validate`).

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
fn test_parse_reports_an_indented_line_after_a_directive_without_metadata() {
    for (header, closer) in [
        ("option \"title\" \"x\"", ""),
        ("plugin \"p\" \"c\"", ""),
        ("include \"x.beancount\"", ""),
        // Closed, so the pushed value is not also reported (bean-check
        // 3.2.3 crashes on a `pushmeta` number never popped).
        ("pushtag #a", "poptag #a\n"),
        ("pushmeta kk: \"v\"", "popmeta kk:\n"),
        ("poptag #a", ""),
        ("popmeta kk:", ""),
    ] {
        for (body, lines) in [
            ("  jj: 1\n", vec![2]),
            ("  ; c\n", vec![2]),
            ("\t; c\n", vec![2]),
            ("  #tag\n", vec![2]),
            // One error per indented block, as beancount's recovery
            // swallows the rest of it.
            ("  jj: 1\n  ii: 2\n", vec![2]),
            ("  ; c\n  jj: 1\n", vec![2]),
            // A blank (whitespace-only) line is not indented content.
            ("  \n", vec![]),
            ("\n2024-01-01 open Assets:A\n  jj: 1\n", vec![]),
        ] {
            let src = format!("{header}\n{body}{closer}");
            let mut expected = lines.clone();
            // `poptag` / `popmeta` of nothing pushed is its own error, on
            // line 1, as in beancount.
            if header.starts_with("pop") {
                expected.insert(0, 1);
            }
            assert_eq!(error_lines(&src), expected, "{src:?}");
        }
    }
    // The header ends at its line break, not at one inside a string.
    assert_eq!(error_lines("option \"title\" \"a\nb\"\n  kk: 1\n"), [3]);
    // A header that is already a syntax error: beancount's recovery
    // swallows the indented line, so it is not reported again.
    assert_eq!(error_lines("option \"a\" \"b\" \"c\"\n  kk: 1\n"), [1]);
}

#[test]
fn test_parse_reports_posting_filename_and_lineno_metadata() {
    let head = "2024-01-01 open Assets:A\n2024-01-01 open Assets:B\n2024-01-02 *\n";
    for meta in ["filename: \"x\"", "lineno: 3"] {
        let src = format!("{head}  Assets:A  1 USD\n    {meta}\n  Assets:B\n");
        assert_eq!(error_lines(&src), [3], "{src:?}");
    }
    // On the transaction itself, or on any other directive, beancount
    // accepts them.
    for src in [
        format!("{head}  filename: \"x\"\n  Assets:A  1 USD\n  Assets:B\n"),
        "2024-01-01 open Assets:A\n  filename: \"x\"\n  lineno: 3\n".to_string(),
    ] {
        assert_eq!(error_lines(&src), Vec::<usize>::new(), "{src:?}");
    }
}

/// The rule for what swallows the indented line after a directive that
/// takes no metadata is one predicate, shared by the indented-line report and
/// the bad-date gap rule (#2813 review). A `poptag` / `popmeta` of nothing
/// pushed is the builder's error, not the grammar's, so the indented line is
/// still `unexpected INDENT`; a syntax error or an invalid date on the header
/// swallows it. Each expectation is bean-check 3.2.3's.
#[test]
fn test_parse_no_metadata_header_errors_swallow_the_next_line_as_beancount() {
    for (src, lines) in [
        // Absent tag, INDENT, then the date.
        ("poptag #zz\n  2024-02-30 open Assets:A\n", vec![1, 2, 2]),
        ("poptag #zz\n  kk: 1\n", vec![1, 2]),
        ("popmeta zz:\n  2024-02-30 5\n", vec![1, 2, 2]),
        // An invalid date on the header swallows the indented line.
        (
            "pushmeta kk: 2024-02-30\n  jj: 1\npopmeta kk:\n",
            vec![1, 3],
        ),
        // A syntax error on the header too; the date is still named.
        ("option \"title\" \"a\" \"b\"\n  2024-02-30 5\n", vec![1, 2]),
        (
            "pushtag #a\npushtag #a\n  kk: 1\npoptag #a\npoptag #a\n",
            vec![3],
        ),
    ] {
        assert_eq!(error_lines(src), lines, "{src:?}");
    }
}

/// A misspelled boolean is named (#2813, maintainer's decision: match
/// beancount, with a kind error).
#[test]
fn test_parse_names_a_misspelled_boolean() {
    for word in ["true", "false", "True", "False"] {
        for src in [
            format!("2024-01-01 open Assets:A\n  kk: {word}\n"),
            format!("2024-01-01 custom \"a\" {word}\n"),
            format!("pushmeta kk: {word}\npopmeta kk:\n"),
        ] {
            let messages: Vec<String> =
                parse(&src).errors.iter().map(ToString::to_string).collect();
            let want = format!("invalid token '{word}' (booleans are written TRUE or FALSE)");
            assert!(
                messages.iter().any(|m| m.contains(&want)),
                "{src:?}: {messages:?}"
            );
        }
    }
    // At the end of the source, and before a comment.
    for src in [
        "2024-01-01 open Assets:A\n  kk: true",
        "2024-01-01 open Assets:A\n  kk: true ; c\n",
        "2024-01-01 open Assets:A\n  kk: true;c\n",
    ] {
        let messages: Vec<String> = parse(src).errors.iter().map(ToString::to_string).collect();
        assert!(
            messages.iter().any(|m| m.contains("invalid token 'true'")),
            "{src:?}: {messages:?}"
        );
    }
    // Part of a longer token, which beancount names whole: not taken for one.
    for value in [
        "Truex",
        "Assets:true",
        "trueé",
        "true.",
        "True'",
        "😀true",
        "xfalse",
        "falsee",
    ] {
        let src = format!("2024-01-01 open Assets:A\n  kk: {value}\n");
        let messages: Vec<String> = parse(&src).errors.iter().map(ToString::to_string).collect();
        assert!(
            !messages.iter().any(|m| m.contains("booleans")),
            "{src:?}: {messages:?}"
        );
    }
    let src = "2024-01-01 open Assets:true\n";
    let messages: Vec<String> = parse(src).errors.iter().map(ToString::to_string).collect();
    assert!(
        !messages.iter().any(|m| m.contains("booleans")),
        "{src:?}: {messages:?}"
    );
}

/// A repeated metadata key on a transaction or a posting is reported as
/// beancount reports it, at the transaction's line, and the FIRST value
/// stands; on any other directive the last value stands with no error, as
/// there. A `pushmeta` key the transaction writes twice is one repeat, and
/// the first written value wins over the pushed one (bean-check 3.2.3, #2893).
#[test]
fn test_parse_reports_a_repeated_metadata_key_as_beancount() {
    use rustledger_core::{Directive, MetaValue};
    let src = "2024-01-01 open Assets:A\n2024-01-02 * \"x\"\n  kk: \"first\"\n  kk: \"second\"\n\
               \x20 Assets:A  1 USD\n    pk: 1\n    pk: 2\n  Assets:A  -1 USD\n";
    let result = parse(src);
    let messages: Vec<String> = result.errors.iter().map(ToString::to_string).collect();
    assert_eq!(error_lines(src), [2, 2], "{messages:?}");
    assert!(
        messages[0].contains("duplicate metadata field on entry: `kk`"),
        "{messages:?}"
    );
    assert!(
        messages[1].contains("duplicate posting metadata field: `pk`"),
        "{messages:?}"
    );
    let Directive::Transaction(txn) = &result.directives[1].value else {
        panic!("not a transaction");
    };
    assert_eq!(txn.meta.get("kk"), Some(&MetaValue::String("first".into())));
    assert_eq!(txn.meta.len(), 1);
    assert_eq!(txn.postings[0].meta.get("pk"), Some(&MetaValue::Int(1)));
    // The green and red conversions agree.
    assert_eq!(
        format!("{:?}", result.directives),
        format!(
            "{:?}",
            rustledger_parser::cst::parse_red_only(src).directives
        )
    );

    // Any other directive: the last value, no error.
    let src = "2024-01-01 open Assets:A\n  kk: 1\n  jj: 2\n  kk: 3\n  kk: 4\n";
    let result = parse(src);
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let Directive::Open(open) = &result.directives[0].value else {
        panic!("not an open");
    };
    assert_eq!(open.meta.get("kk"), Some(&MetaValue::Int(4)));

    // A pushed key the transaction writes twice.
    let src = "2024-01-01 open Assets:A\npushmeta kk: \"p\"\n2024-01-02 * \"x\"\n  kk: \"a\"\n  kk: \"b\"\n\
               \x20 Assets:A  1 USD\n  Assets:A  -1 USD\npopmeta kk:\n";
    let result = parse(src);
    assert_eq!(error_lines(src), [3], "{:?}", result.errors);
    let Directive::Transaction(txn) = &result.directives[1].value else {
        panic!("not a transaction");
    };
    assert_eq!(txn.meta.get("kk"), Some(&MetaValue::String("a".into())));

    // A key on the transaction and on a posting is no repeat.
    let src = "2024-01-01 open Assets:A\n2024-01-02 * \"x\"\n  kk: \"a\"\n  Assets:A  1 USD\n    kk: \"b\"\n\
               \x20 Assets:A  -1 USD\n";
    assert_eq!(error_lines(src), Vec::<usize>::new());
}
