//! A BOM-led invalid run in the middle of a line runs to the next blank, as
//! beancount's does (#2928).
//!
//! beancount's lexer reads an invalid token as `[^ \t\n\r]+`: from the first
//! character no rule takes, everything up to the next space, tab or line
//! ending. A BOM-led error used to keep its own extent wherever it stood, so
//! a `"` right after a mid-line BOM opened a string, and a `#!` or `#+` lexed
//! as a token of its own. Now only a BOM that starts its line keeps its own
//! extent (layout transparency for concatenated files). Each count below is
//! bean-check 3.2.3's for the same input.

use rustledger_core::Directive;
use rustledger_parser::cst::parse_red_only;
use rustledger_parser::{__baseline_canonical_payload, ParseErrorKind, ParseResult, parse};

const BOM: &str = "\u{FEFF}";

const HEAD: &str = "2024-01-01 open Assets:A\n2024-01-01 open Assets:B\n";
const LEGS: &str = "\n  Assets:A  1 USD\n  Assets:B\n";

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

/// `<BOM>"x"`, `<BOM>#!d`, `<BOM>#+x`, `x<BOM>"y"` and two BOMs in a row on
/// a transaction's header line: one invalid token each, so one error, as in
/// bean-check. The `#!` and `#+` were a second error, and the quote after a
/// BOM opened the narration of a transaction that was kept.
#[test]
fn test_parse_mid_line_bom_run_is_one_error() {
    for header in [
        format!("2024-01-02 * {BOM}\"x\""),
        format!("2024-01-02 * {BOM}{BOM}\"x\""),
        format!("2024-01-02 * \"x\" {BOM}#!d"),
        format!("2024-01-02 * \"x\" {BOM}#+x"),
        format!("2024-01-02 * \"x\" x{BOM}\"y\""),
        format!("2024-01-02 * \"x\" {BOM}abc"),
    ] {
        let src = format!("{HEAD}{header}{LEGS}");
        let result = parse_both(&src);
        assert_eq!(result.errors.len(), 1, "{src:?}: {:?}", result.errors);
        assert_eq!(bom_errors(&result), 1, "{src:?}: {:?}", result.errors);
    }
}

/// The quote after a mid-line BOM opens no string: `"x"` is part of the
/// invalid token, never the narration. (The transaction itself is kept
/// under rledger's error-recovery policy, with no narration.)
#[test]
fn test_parse_mid_line_bom_before_quote_opens_no_string() {
    let src = format!("{HEAD}2024-01-02 * {BOM}\"x\"{LEGS}");
    let result = parse_both(&src);
    for d in &result.directives {
        if let Directive::Transaction(t) = &d.value {
            assert_eq!(t.narration.as_str(), "", "{:?}", result.directives);
        }
    }
}

/// A BOM that starts its line keeps its own extent, one BOM or two: the
/// line is one `BomInDirectiveBody` error, as it was, where a BOM-led run
/// would also report the date glued to it.
#[test]
fn test_parse_line_start_bom_is_one_error() {
    for lead in [BOM.to_string(), format!("{BOM}{BOM}")] {
        let src = format!("{HEAD}{lead}2024-01-02 open Assets:C\n");
        let result = parse_both(&src);
        assert_eq!(result.errors.len(), 1, "{src:?}: {:?}", result.errors);
        assert_eq!(bom_errors(&result), 1, "{src:?}");
    }
}

/// A BOM inside a string stays string content (#2926): no error at all.
#[test]
fn test_parse_bom_in_string_stays_content() {
    let src = format!("{HEAD}2024-01-02 * \"a{BOM}b\"{LEGS}");
    let result = parse_both(&src);
    assert!(result.errors.is_empty(), "{:?}", result.errors);
}

/// On an unreadable line, a mid-line BOM-led run is one more invalid token,
/// reported like any other: `313<BOM>x` is beancount's `unexpected NUMBER`
/// and `Invalid token: '<BOM>x'`, and `foo <BOM>"x"` two invalid tokens.
/// Its BOM is still named by the line's `BomInDirectiveBody`.
#[test]
fn test_parse_bom_led_token_on_error_line_is_reported() {
    for (line, errors) in [
        (format!("313{BOM}x"), 2),
        (format!("GOO{BOM}OO"), 2),
        (format!("foo {BOM}\"x\""), 2),
        (format!("313 {BOM} a"), 3),
    ] {
        let src = format!("{line}\n");
        let result = parse_both(&src);
        assert_eq!(result.errors.len(), errors, "{src:?}: {:?}", result.errors);
        assert_eq!(bom_errors(&result), 1, "{src:?}: {:?}", result.errors);
    }
}

/// When the line's error is another one (an invalid account), the BOM
/// diagnostic after it stands for the line's BOM-led token, so that token is
/// not counted twice: `Ü:A <BOM>x` is two errors, as in bean-check.
#[test]
fn test_parse_bom_led_token_after_invalid_account_counts_once() {
    let src = format!("Ü:A {BOM}x\n");
    let result = parse_both(&src);
    assert_eq!(result.errors.len(), 2, "{:?}", result.errors);
    assert_eq!(bom_errors(&result), 1, "{:?}", result.errors);
}

/// A mid-line BOM-led run in an `open` is an invalid token there, so the
/// directive's booking method is not checked (beancount never builds a
/// directive with an invalid token in it): the token's error is the only one.
#[test]
fn test_parse_open_with_mid_line_bom_run_reports_only_the_token() {
    let src = format!("2024-01-01 open Assets:A USD \"BAD\" {BOM}x\n");
    let result = parse_both(&src);
    assert_eq!(result.errors.len(), 1, "{:?}", result.errors);
    assert_eq!(bom_errors(&result), 1, "{:?}", result.errors);
}

/// The "Remove BOM" quick fix asks `is_stray_bom_at` for each BOM in a
/// diagnostic's span. A BOM inside a longer invalid token (at its start,
/// after another BOM, or after other characters) is still a stray one; the
/// string's BOM next to it is not.
#[test]
fn test_is_stray_bom_at_finds_bom_inside_longer_error_token() {
    for (header, strays) in [
        (format!("2024-01-02 * {BOM}\"x\""), 1),
        (format!("2024-01-02 * {BOM}{BOM}\"x\""), 2),
        (format!("2024-01-02 * \"x\" {BOM}#!d"), 1),
        (format!("2024-01-02 * \"x\" x{BOM}\"y\""), 1),
        (format!("2024-01-02 * \"a{BOM}b\" {BOM}#+x"), 1),
    ] {
        let src = format!("{HEAD}{header}{LEGS}");
        let result = parse(&src);
        let found: Vec<usize> = src
            .match_indices(BOM)
            .map(|(i, _)| i)
            .filter(|&i| result.is_stray_bom_at(i))
            .collect();
        assert_eq!(found.len(), strays, "{src:?}: {found:?}");
        if let Some(string_bom) = src.find(&format!("a{BOM}b")) {
            assert!(!result.is_stray_bom_at(string_bom + 1), "{src:?}");
        }
    }
}
