//! A BOM (U+FEFF) inside a string literal is string content (#2910).
//!
//! The mid-file BOM rule (`BomInDirectiveBody`) searched every token's text
//! for U+FEFF, so a BOM the lexer had already placed inside a `STRING` (or a
//! comment) was reported as a stray one. Beancount 3.2.3 accepts it and keeps
//! it byte-for-byte in the string's value; only a BOM the lexer cannot place
//! in a token, e.g. right before an opening quote, is an error there.

use rustledger_core::{Directive, MetaValue};
use rustledger_parser::cst::parse_red_only;
use rustledger_parser::format::format_source;
use rustledger_parser::{__baseline_canonical_payload, ParseErrorKind, ParseResult, parse};

const BOM: &str = "\u{FEFF}";

const HEAD: &str = "2024-01-01 open Assets:A\n2024-01-01 open Expenses:B\n";
const LEGS: &str = "\n  Assets:A  1 USD\n  Expenses:B  -1 USD\n";

/// Parse `src` with the green (default) and the red path, require them to
/// agree, and return the green result.
fn parse_both(src: &str) -> ParseResult {
    let green = parse(src);
    let red = parse_red_only(src);
    assert_eq!(
        __baseline_canonical_payload(&green),
        __baseline_canonical_payload(&red),
        "green vs red diverged for {src:?}"
    );
    green
}

fn bom_errors(result: &ParseResult) -> usize {
    result
        .errors
        .iter()
        .filter(|e| matches!(e.kind, ParseErrorKind::BomInDirectiveBody))
        .count()
}

/// The transaction of `src`, which must be its only one.
fn transaction(result: &ParseResult) -> &rustledger_core::Transaction {
    let mut txns = result.directives.iter().filter_map(|d| match &d.value {
        Directive::Transaction(t) => Some(t),
        _ => None,
    });
    let txn = txns.next().expect("a transaction");
    assert!(txns.next().is_none(), "more than one transaction");
    txn
}

#[test]
fn test_parse_bom_in_narration_is_string_content() {
    // Inside, at the start, at the end, next to escaped quotes, and on the
    // second line of a multi-line string: each one is content.
    for (literal, value) in [
        (format!("\"a{BOM}b\""), format!("a{BOM}b")),
        (format!("\"{BOM}ab\""), format!("{BOM}ab")),
        (format!("\"ab{BOM}\""), format!("ab{BOM}")),
        (format!("\"{BOM}\""), BOM.to_string()),
        (format!("\"a\\\"{BOM}\\\"b\""), format!("a\"{BOM}\"b")),
        (
            format!("\"line1\nli{BOM}ne2\""),
            format!("line1\nli{BOM}ne2"),
        ),
    ] {
        let src = format!("{HEAD}2024-01-02 * {literal}{LEGS}");
        let result = parse_both(&src);
        assert!(result.errors.is_empty(), "{src:?}: {:?}", result.errors);
        assert_eq!(transaction(&result).narration.as_str(), value, "{src:?}");
    }
}

#[test]
fn test_parse_bom_in_payee_is_string_content() {
    let src = format!("{HEAD}2024-01-02 * \"p{BOM}q\" \"n\"{LEGS}");
    let result = parse_both(&src);
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let txn = transaction(&result);
    assert_eq!(
        txn.payee.as_ref().map(rustledger_core::InternedStr::as_str),
        Some(&*format!("p{BOM}q"))
    );
    assert_eq!(txn.narration.as_str(), "n");
}

#[test]
fn test_parse_bom_in_metadata_string_is_string_content() {
    let src = format!("{HEAD}2024-01-02 * \"n\"\n  kk: \"v{BOM}w\"{LEGS}");
    let result = parse_both(&src);
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    assert_eq!(
        transaction(&result).meta.get("kk"),
        Some(&MetaValue::String(format!("v{BOM}w")))
    );
}

#[test]
fn test_parse_bom_in_option_and_include_is_string_content() {
    let src = format!("option \"title\" \"T{BOM}X\"\ninclude \"x{BOM}y.beancount\"\n{HEAD}");
    let result = parse_both(&src);
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    assert_eq!(result.options.len(), 1);
    assert_eq!(result.options[0].0, "title");
    assert_eq!(result.options[0].1, format!("T{BOM}X"));
    assert_eq!(result.includes.len(), 1);
    assert_eq!(result.includes[0].0, format!("x{BOM}y.beancount"));
}

#[test]
fn test_parse_bom_in_note_and_document_is_string_content() {
    let src = format!(
        "{HEAD}2024-01-03 note Assets:A \"n{BOM}o\"\n\
         2024-01-03 document Assets:A \"/tmp/d{BOM}x.pdf\"\n"
    );
    let result = parse_both(&src);
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let mut seen = 0;
    for d in &result.directives {
        match &d.value {
            Directive::Note(n) => {
                assert_eq!(n.comment.as_str(), format!("n{BOM}o"));
                seen += 1;
            }
            Directive::Document(doc) => {
                assert_eq!(doc.path.as_str(), format!("/tmp/d{BOM}x.pdf"));
                seen += 1;
            }
            _ => {}
        }
    }
    assert_eq!(seen, 2);
}

#[test]
fn test_parse_bom_in_comment_is_not_an_error() {
    // A trailing comment is skipped whole, as in beancount.
    let src = format!("{HEAD}2024-01-02 * \"ab\" ; c{BOM}d{LEGS}");
    let result = parse_both(&src);
    assert!(result.errors.is_empty(), "{:?}", result.errors);
}

#[test]
fn test_parse_bom_glued_into_account_is_part_of_the_account() {
    // The account token takes any non-ASCII character after its first, so
    // beancount lexes the BOM into the account: `open Assets:Ca\u{feff}sh` loads
    // in bean-check with no error. It is no stray BOM here either.
    let src = format!("2024-01-01 open Assets:Ca{BOM}sh\n");
    let result = parse_both(&src);
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    match &result.directives[0].value {
        Directive::Open(o) => assert_eq!(o.account.as_str(), format!("Assets:Ca{BOM}sh")),
        other => panic!("expected an open, got {other:?}"),
    }
}

#[test]
fn test_parse_bom_outside_string_stays_an_error() {
    // Right before the opening quote, and right after the closing one: the
    // lexer places it in no token. bean-check: `Invalid token: '\u{feff}"ab"'`
    // and `Invalid token: '\u{feff}'`.
    for src in [
        format!("{HEAD}2024-01-02 * {BOM}\"ab\"{LEGS}"),
        format!("{HEAD}2024-01-02 * \"ab\"{BOM} {LEGS}"),
    ] {
        let result = parse_both(&src);
        assert!(bom_errors(&result) >= 1, "{src:?}: {:?}", result.errors);
    }
}

#[test]
fn test_parse_bom_in_string_on_a_broken_line_is_not_reported_as_bom() {
    // The line is a syntax error for its own reason (an account after the
    // narration); the BOM in its string is not a second problem. bean-check
    // reports only the syntax error.
    let src = format!("{HEAD}2024-01-02 * \"a{BOM}b\" Assets:A{LEGS}");
    let result = parse_both(&src);
    assert!(!result.errors.is_empty(), "expected the syntax error");
    assert_eq!(bom_errors(&result), 0, "{:?}", result.errors);

    // With a stray BOM on the same line as well, that one is still reported.
    let src = format!("{HEAD}2024-01-02 * \"a{BOM}b\" Assets:A {BOM}x{LEGS}");
    let result = parse_both(&src);
    assert!(bom_errors(&result) >= 1, "{:?}", result.errors);
}

#[test]
fn test_is_stray_bom_at_tells_string_content_from_stray_bom() {
    let line = format!("2024-01-02 * \"a{BOM}b\" {BOM}\"c\"");
    for lead in ["", BOM] {
        let src = format!("{lead}{HEAD}{line}{LEGS}");
        let result = parse(&src);
        let in_string = src.find(&format!("a{BOM}b")).expect("string") + 1;
        let stray = src.rfind(&format!("{BOM}\"c\"")).expect("stray");
        assert!(!result.is_stray_bom_at(in_string), "{src:?}");
        assert!(result.is_stray_bom_at(stray), "{src:?}");
        // Not a BOM at all, and the stripped leading BOM.
        assert!(!result.is_stray_bom_at(stray + 1), "{src:?}");
        assert!(!result.is_stray_bom_at(0) || lead.is_empty(), "{src:?}");
        assert!(!result.is_stray_bom_at(src.len()), "{src:?}");
    }
}

#[test]
fn test_format_source_keeps_bom_in_string() {
    let payee = format!("\"p{BOM}q\"");
    let narration = format!("\"{BOM}a\\\"{BOM}\\\"b{BOM}\"");
    let meta = format!("\"v{BOM}w\"");
    let multi = format!("\"line1\nli{BOM}ne2\"");
    let option = format!("\"T{BOM}X\"");
    for (src, literals) in [
        (
            format!("{HEAD}\n2024-01-02 * {payee} {narration}\n  kk: {meta}{LEGS}"),
            vec![&payee, &narration, &meta],
        ),
        (
            format!("{HEAD}2024-01-03 note Assets:A {multi}\n"),
            vec![&multi],
        ),
        (format!("option \"title\" {option}\n"), vec![&option]),
    ] {
        let result = parse(&src);
        assert!(result.errors.is_empty(), "{src:?}: {:?}", result.errors);
        let once = format_source(&src);
        // Each literal comes out byte-for-byte, no BOM is added or lost, and
        // formatting is stable.
        for literal in literals {
            assert!(
                once.contains(literal.as_str()),
                "{literal:?} not in {once:?}"
            );
        }
        assert_eq!(
            once.matches(BOM).count(),
            src.matches(BOM).count(),
            "{once:?}"
        );
        assert!(parse(&once).errors.is_empty(), "{once:?}");
        assert_eq!(format_source(&once), once, "{src:?}");
    }
}
