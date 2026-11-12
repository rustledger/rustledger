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
use rustledger_parser::format::format_source;
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

/// A BOM-led invalid token where a directive's argument belongs is that
/// directive's one error, as bean-check's one `Invalid token` (a BOM-led
/// account keeps the account; see
/// `test_parse_bom_glued_to_account_keeps_the_account`). The
/// directive's own line error stands for the token, under the BOM diagnostic,
/// and is not reported twice.
#[test]
fn test_parse_bom_led_argument_of_directive_is_one_error() {
    for line in [
        format!("2024-01-02 balance Assets:A 0 {BOM}USD"),
        format!("2024-01-02 balance Assets:A {BOM}0 USD"),
        format!("2024-01-02 price USD 1 {BOM}EUR"),
        format!("2024-01-02 price {BOM}USD 1 EUR"),
        format!("2024-01-02 commodity {BOM}EUR"),
        format!("2024-01-02 note Assets:A {BOM}\"x\""),
        format!("2024-01-02 event {BOM}\"t\" \"v\""),
        format!("2024-01-02 event \"t\" {BOM}\"v\""),
        format!("2024-01-02 document Assets:A {BOM}\"f.pdf\""),
        format!("2024-01-02 custom {BOM}\"budget\" 1"),
        format!("2024-01-02 query {BOM}\"q\" \"select\""),
        format!("2024-01-02 query \"q\" {BOM}\"select\""),
    ] {
        let src = format!("{HEAD}{line}\n");
        let result = parse_both(&src);
        assert_eq!(result.errors.len(), 1, "{src:?}: {:?}", result.errors);
        assert_eq!(bom_errors(&result), 1, "{src:?}: {:?}", result.errors);
        // The two `open`s are kept; the broken directive is not.
        assert_eq!(
            result.directives.len(),
            2,
            "{src:?}: {:?}",
            result.directives
        );
        // The quick fix still finds the BOM, inside the line's error span.
        let at = src.find(BOM).expect("a BOM");
        assert!(result.is_stray_bom_at(at), "{src:?}");
    }
}

/// A BOM glued to an account shape (`<BOM>Assets:A`) keeps its own extent in
/// the middle of a line, as a line-start BOM does: it is reported as the
/// stray BOM it is (`P0026`, whose quick fix removes it), and the account
/// lexes as the account it names, so the directive keeps it. beancount reads
/// the BOM into the account and rejects the name when it loads; on a line
/// with another error the BOM adds no invalid token, as there.
#[test]
fn test_parse_bom_glued_to_account_keeps_the_account() {
    for (line, account) in [
        (format!("2024-01-02 open {BOM}Assets:C"), "Assets:C"),
        (format!("2024-01-02 open\t{BOM}{BOM}Assets:C"), "Assets:C"),
        (format!("2024-01-02 close {BOM}Assets:A"), "Assets:A"),
        (
            format!("2024-01-02 balance {BOM}Assets:A 0 USD"),
            "Assets:A",
        ),
        (format!("2024-01-02 note {BOM}Ü:A \"x\""), "Ü:A"),
    ] {
        let src = format!("{HEAD}{line}\n");
        let result = parse_both(&src);
        assert_eq!(result.errors.len(), 1, "{src:?}: {:?}", result.errors);
        assert_eq!(bom_errors(&result), 1, "{src:?}: {:?}", result.errors);
        assert_eq!(result.directives.len(), 3, "{src:?}");
        let got = match &result.directives[2].value {
            Directive::Open(d) => d.account.to_string(),
            Directive::Close(d) => d.account.to_string(),
            Directive::Balance(d) => d.account.to_string(),
            Directive::Note(d) => d.account.to_string(),
            other => panic!("{src:?}: {other:?}"),
        };
        assert_eq!(got, account, "{src:?}");
        for (at, _) in src.match_indices(BOM) {
            assert!(result.is_stray_bom_at(at), "{src:?}");
        }
    }
    // On an error line, the BOM is no invalid token of its own: `$x
    // <BOM>Assets:A` is one error, as in bean-check.
    for line in [format!("$x {BOM}Assets:A"), format!("{BOM}\t{BOM}Assets:A")] {
        let src = format!("{HEAD}{line}\n");
        let result = parse_both(&src);
        assert_eq!(result.errors.len(), 1, "{src:?}: {:?}", result.errors);
    }
    // Not an account shape: an invalid run to the next blank.
    for line in [
        format!("2024-01-02 note Assets:A \"x\" {BOM}A"),
        format!("2024-01-02 note Assets:A \"x\" {BOM}USD"),
        format!("2024-01-02 note Assets:A \"x\" {BOM}Assets:"),
    ] {
        let src = format!("{HEAD}{line}\n");
        let result = parse_both(&src);
        assert_eq!(bom_errors(&result), 1, "{src:?}: {:?}", result.errors);
    }
}

/// A lone capital glued to a BOM (`A<BOM>b`) is one invalid token from the
/// capital on, here and in beancount, and it is counted like a BOM-led one:
/// `$x A<BOM>b` is two errors and `@ ! A<BOM>b %x` three, as in bean-check.
#[test]
fn test_parse_lone_capital_glued_to_bom_is_counted() {
    for (line, errors) in [(format!("$x A{BOM}b"), 2), (format!("@ ! A{BOM}b %x"), 3)] {
        let src = format!("{HEAD}{line}\n");
        let result = parse_both(&src);
        assert_eq!(result.errors.len(), errors, "{src:?}: {:?}", result.errors);
    }
}

/// After a `<BOM>*` heading start, beancount's invalid token runs to the
/// first blank, and the rest of the line lexes as usual: each invalid token
/// in it is one more error, and a tag or a string is none.
#[test]
fn test_parse_line_start_bom_heading_counts_the_rest() {
    for (line, errors) in [
        (format!("{BOM}*7{BOM}* #tag"), 1),
        (format!("{BOM}**{BOM}*\t\"s{BOM}t\""), 1),
        (format!("{BOM}* Heading with words"), 4),
        (format!("{BOM}*7 Z#"), 2),
    ] {
        let src = format!("{HEAD}{line}\n");
        let result = parse_both(&src);
        assert_eq!(result.errors.len(), errors, "{src:?}: {:?}", result.errors);
    }
}

/// The secondary BOM error after an invalid account stands for the line's
/// first token with a stray BOM in it, whether the BOM leads that token or
/// not, so a later BOM-led token keeps its own error: `Ü:A x<BOM>y <BOM>z`
/// is three errors, as in bean-check.
#[test]
fn test_parse_secondary_bom_error_stands_for_first_bom_token_of_either_kind() {
    let src = format!("Ü:A x{BOM}y {BOM}z\n");
    let result = parse_both(&src);
    assert_eq!(result.errors.len(), 3, "{:?}", result.errors);
    assert_eq!(bom_errors(&result), 1, "{:?}", result.errors);
}

/// The run stops at the next blank, as beancount's does: in
/// `query "q" <BOM>"select 1"` it is `<BOM>"select`, and the `"` after the
/// `1` is one more invalid token (an unterminated string here). Two errors,
/// as in bean-check.
#[test]
fn test_parse_bom_led_run_stops_at_blank_inside_quotes() {
    let src = format!("{HEAD}2024-01-02 query \"q\" {BOM}\"select 1\"\n");
    let result = parse_both(&src);
    assert_eq!(result.errors.len(), 2, "{:?}", result.errors);
    assert_eq!(bom_errors(&result), 1, "{:?}", result.errors);
}

/// The 1-based line and column (in characters) of byte `at` of `src`.
fn line_col(src: &str, at: usize) -> (usize, usize) {
    let before = &src[..at];
    let line = before.matches('\n').count() + 1;
    let line_start = before.rfind('\n').map_or(0, |i| i + 1);
    (line, src[line_start..at].chars().count() + 1)
}

/// The one error of a directive whose argument is a BOM-led invalid token is
/// reported at that token, BOM to the next blank, as main reported its BOM
/// (`rledger check` prints its line and column, the LSP squiggles it), not
/// over the whole directive. Also for a directive with a metadata line after
/// it, whose own error spanned both lines.
#[test]
fn test_parse_bom_led_argument_error_is_at_the_token() {
    for (line, token) in [
        (
            format!("2024-01-02 price USD 1 {BOM}EUR"),
            format!("{BOM}EUR"),
        ),
        (
            format!("2024-01-02 commodity {BOM}EUR"),
            format!("{BOM}EUR"),
        ),
        (
            format!("2024-01-02 balance Assets:A {BOM}0 USD"),
            format!("{BOM}0"),
        ),
        (
            format!("2024-01-02 note Assets:A {BOM}\"x\""),
            format!("{BOM}\"x\""),
        ),
        (
            format!("2024-01-02 price USD 1 {BOM}EUR\n  source: \"x\""),
            format!("{BOM}EUR"),
        ),
        (
            format!("2024-01-02 event \"t\" {BOM}\"v\"\n  kk: \"x\"\n  jj: 1"),
            format!("{BOM}\"v\""),
        ),
    ] {
        let src = format!("{HEAD}{line}\n");
        let result = parse_both(&src);
        assert_eq!(result.errors.len(), 1, "{src:?}: {:?}", result.errors);
        let error = &result.errors[0];
        assert_eq!(bom_errors(&result), 1, "{src:?}");
        let start = src.find(&token).expect("the token");
        assert_eq!(
            (error.span.start, error.span.end),
            (start, start + token.len()),
            "{src:?}"
        );
        // Line 3, after the two `open`s, at the BOM's column.
        let column = line.find(BOM).expect("a BOM");
        assert_eq!(
            line_col(&src, error.span.start),
            (3, line[..column].chars().count() + 1),
            "{src:?}"
        );
    }
}

/// The formatter copies such a directive verbatim, metadata included, though
/// its error now covers only the token: the token lies inside the directive.
#[test]
fn test_format_source_keeps_directive_with_bom_led_argument() {
    let broken = format!("2024-01-02 price USD 1 {BOM}EUR\n  source: \"x\"\n");
    let src = format!("{HEAD}{broken}");
    let formatted = format_source(&src);
    assert!(formatted.contains(&broken), "{formatted:?}");
}

/// After an invalid account, the secondary BOM error stands for one token
/// with a stray BOM in it and every other such token has its own error,
/// whatever their order and kinds: each line is bean-check's count.
#[test]
fn test_parse_secondary_bom_error_with_several_bom_tokens() {
    for (line, errors) in [
        (format!("Ü:A {BOM}z x{BOM}y"), 3),
        (format!("Ü:A x{BOM}y {BOM}z"), 3),
        (format!("Ü:A {BOM}a x{BOM}y {BOM}z"), 4),
        (format!("Ü:A x{BOM}y z{BOM}w"), 3),
        (format!("Ü:A x{BOM}y {BOM}a z{BOM}w"), 4),
        (format!("Ü:A {BOM}a {BOM}b"), 3),
    ] {
        let src = format!("{line}\n");
        let result = parse_both(&src);
        assert_eq!(result.errors.len(), errors, "{src:?}: {:?}", result.errors);
        assert_eq!(bom_errors(&result), 1, "{src:?}: {:?}", result.errors);
    }
}

/// A BOM that starts its line, glued to an invalid run, is beancount's one
/// invalid token there (`<BOM>tApo`), so the line's error stands for it and
/// the run is not reported a second time.
#[test]
fn test_parse_line_start_bom_glued_to_invalid_run_is_one_error() {
    let src = format!("{HEAD}{BOM}tApo\tcd\n");
    let result = parse_both(&src);
    assert_eq!(result.errors.len(), 2, "{:?}", result.errors);
    assert_eq!(bom_errors(&result), 1, "{:?}", result.errors);
}

/// A BOM that starts its line, glued to an invalid run, is beancount's first
/// invalid token there, and the line's BOM diagnostic stands for it. So a
/// later run with a BOM inside it is one more invalid token, with its own
/// error. Each count is bean-check's.
#[test]
fn test_parse_line_start_glued_bom_then_inner_bom_token_counts_both() {
    for (line, errors) in [
        (format!("{BOM}foo x{BOM}y"), 2),
        (format!("{BOM}tApo x{BOM}y"), 2),
        (format!("{BOM}$x x{BOM}y"), 2),
        (format!("{BOM}foo {BOM}a x{BOM}y"), 3),
    ] {
        let src = format!("{HEAD}{line}\n");
        let result = parse_both(&src);
        assert_eq!(result.errors.len(), errors, "{src:?}: {:?}", result.errors);
        assert_eq!(bom_errors(&result), 1, "{src:?}: {:?}", result.errors);
    }
}

/// A BOM before the indentation of a metadata line is beancount's first
/// invalid token on the line (it is followed by a blank, so nothing is glued
/// to it), and the invalid key after it is one more: both are counted, with
/// the rest of the line, as in bean-check.
#[test]
fn test_parse_bom_before_metadata_indentation_counts_the_key() {
    for (line, errors) in [
        (format!("{BOM}  k: Ü:A {BOM}a0 x{BOM}y1"), 4),
        (format!("{BOM}  k: Ü:A x{BOM}y0"), 3),
    ] {
        let src = format!("{HEAD}2024-01-02 *\n{line}\n");
        let result = parse_both(&src);
        let on_line = result
            .errors
            .iter()
            .filter(|e| src[..e.span.start].matches('\n').count() == 3)
            .count();
        assert_eq!(on_line, errors, "{src:?}: {:?}", result.errors);
    }
}

/// A BOM-led first token after a date, or after an indentation, is the one
/// the line's error stands for, and that error is the BOM diagnostic: a later
/// run with a BOM inside it then has its own error. Each count is
/// bean-check's (the lines are numbered after the two `open`s).
#[test]
fn test_parse_bom_led_first_token_spends_the_bom_diagnostic() {
    for (lines, line, errors) in [
        (format!("2024-01-02 {BOM}a x{BOM}y"), 3, 2),
        (format!("2024-01-02\t{BOM}a x{BOM}y"), 3, 2),
        (format!("2024-01-02  {BOM}a x{BOM}y x{BOM}z"), 3, 3),
        (format!("2024-01-02 *\n  {BOM}a x{BOM}y"), 4, 2),
        (format!("2024-01-02 *\n  {BOM}a"), 4, 1),
        (format!("2024-01-02 *\n  {BOM}; c"), 4, 2),
    ] {
        let src = format!("{HEAD}{lines}\n");
        let result = parse_both(&src);
        let on_line = result
            .errors
            .iter()
            .filter(|e| src[..e.span.start].matches('\n').count() + 1 == line)
            .count();
        assert_eq!(on_line, errors, "{src:?}: {:?}", result.errors);
    }
}

/// A BOM that starts its line, glued to tokens that lex here and then to an
/// invalid one, is one beancount token, the whole blank-free run: the
/// invalid part of it is not counted again.
#[test]
fn test_parse_line_start_bom_run_through_valid_tokens_is_one_token() {
    for (line, errors) in [
        (format!("{BOM}12$ x{BOM}y"), 2),
        (format!("{BOM}2024-01-02$x x{BOM}y"), 2),
        (format!("{BOM}USD$ x{BOM}y"), 2),
        (format!("{BOM}#t$ x{BOM}y"), 2),
        (format!("{BOM}\"s\"$ x{BOM}y"), 2),
        (format!("{BOM}12{BOM}z"), 1),
        (format!("{BOM}2024-01-02{BOM}a"), 1),
    ] {
        let src = format!("{HEAD}{line}\n");
        let result = parse_both(&src);
        assert_eq!(result.errors.len(), errors, "{src:?}: {:?}", result.errors);
    }
}

/// The unread rest of a `<BOM>*` heading line holds more than the BOM's run:
/// it is still reported, so `<BOM>*7 Z#` is two errors, as in bean-check.
#[test]
fn test_parse_line_start_bom_heading_rest_is_not_glued() {
    let src = format!("{HEAD}{BOM}*7 Z#\n");
    let result = parse_both(&src);
    assert_eq!(result.errors.len(), 2, "{:?}", result.errors);
}

/// beancount lets a BOM be an account's first character, so a BOM-led word
/// its account rule reads is one account there (its name rejected on load),
/// whether or not an account of rledger's follows the BOM: `<BOM>assets:A`,
/// `<BOM>1:A`, `<BOM>:A` and `<BOM>-:A` add no parse error after `$x`. It
/// ends where that account does, so a tail glued to it is one more invalid
/// token; and a line-start run before one is the line's first token. Each
/// count is bean-check's.
#[test]
fn test_parse_bom_led_account_shapes_count_as_beancount() {
    for (line, errors) in [
        (format!("$x {BOM}assets:A"), 1),
        (format!("$x {BOM}1:A"), 1),
        (format!("$x {BOM}:A"), 1),
        (format!("$x {BOM}-:A"), 1),
        (format!("{BOM}* {BOM}Assets:A"), 1),
        (format!("{BOM}* x\t{BOM}Assets:A"), 2),
        (format!("{BOM}{BOM}Assets:A$x"), 2),
        (format!("{BOM}Assets:A x{BOM}y"), 2),
        (format!("{BOM}{BOM}Assets:A x{BOM}y"), 2),
    ] {
        let src = format!("{HEAD}{line}\n");
        let result = parse_both(&src);
        assert_eq!(result.errors.len(), errors, "{src:?}: {:?}", result.errors);
        assert!(bom_errors(&result) >= 1, "{src:?}: {:?}", result.errors);
    }
}

/// BOMs beancount reads into an account are no invalid token on a metadata
/// line either, so the `open` above it still has its booking method checked,
/// as in beancount (`Invalid booking method: BAD`): the BOM is reported as
/// the stray BOM it is, and the booking method as invalid.
#[test]
fn test_parse_bom_account_in_metadata_keeps_booking_method_check() {
    for value in [format!("{BOM}Assets:D"), format!("{BOM}assets:D")] {
        let src = format!("2024-01-02 open Assets:C USD \"BAD\"\n  kk: {value}\n");
        let result = parse_both(&src);
        assert!(
            result
                .errors
                .iter()
                .any(|e| matches!(e.kind, ParseErrorKind::InvalidBookingMethod(_))),
            "{src:?}: {:?}",
            result.errors
        );
        assert_eq!(bom_errors(&result), 1, "{src:?}: {:?}", result.errors);
    }
}

/// Round-9 shapes, each count bean-check's: a tail glued to a BOM-led
/// account (`<BOM>"s"`, `~<BOM>1:A`, `<BOM>x`) is no second error; an
/// account inside a heading's invalid token (`Heading,Ü:A`) is that token,
/// not one more error; an invalid token after a heading's first word is
/// one; and a comment after a BOM-led key ends the line. Round 10: a
/// comment right after a later BOM-led account of the tail ends the line
/// too, a token after it included (`~<BOM>1:A;c $x`); and after a `<BOM>*`
/// heading, `{#t` is a brace and a tag, as beancount lexes it, while a `$x`
/// glued after a `{#` is still one invalid token.
#[test]
fn test_parse_bom_led_line_tails_count_as_beancount() {
    for (line, errors) in [
        (format!("{BOM}assets:A{BOM}\"s\""), 1),
        (format!("{BOM}assets:A~{BOM}1:A"), 1),
        (format!("{BOM}assets:A{BOM}x"), 1),
        (format!("{BOM}* Heading,\u{DC}:A"), 2),
        (format!("{BOM}* Heading{BOM}a-b:C{{  1{BOM}2"), 2),
        (format!("{BOM}{BOM}kk:{BOM};c\t{BOM}1.5"), 1),
        (format!("{BOM}assets:A~{BOM}1:A;c $x"), 1),
        (format!("{BOM}assets:A,{BOM}a-b:C;c $x $y"), 1),
        (
            format!("{BOM}{BOM}{BOM}assets:A\"x\"{BOM}a-b:C;c\t{BOM}1.5"),
            1,
        ),
        (format!("{BOM}* H {{#t"), 1),
        (format!("{BOM}* H {{#t{{#$x {{#\"a b\""), 2),
    ] {
        let src = format!("{HEAD}{line}\n");
        let result = parse_both(&src);
        assert_eq!(result.errors.len(), errors, "{src:?}: {:?}", result.errors);
    }
}

/// An account glued to a line-start BOM is not taken for an account of its
/// own when the line is recovered after an error line: the BOM's diagnostic
/// stands for the word, as it did before the BOM's run was split.
#[test]
fn test_parse_bom_glued_unicode_account_after_error_line_is_not_counted_twice() {
    let src = format!("{HEAD}x\n{BOM}F\u{77E}:\u{DC}\n");
    let result = parse_both(&src);
    assert!(
        !result
            .errors
            .iter()
            .any(|e| matches!(e.kind, ParseErrorKind::InvalidAccount(_))),
        "{:?}",
        result.errors
    );
    assert_eq!(bom_errors(&result), 1, "{:?}", result.errors);
}

/// An account word only partly inside an invalid token keeps main's message,
/// the whole word as written (`G:\u{3A8}@3O+.1`), not the text masked for
/// the account search. This pins main's message, not beancount's behavior:
/// beancount's account there is `G:\u{3A8}`, and the rest another token.
#[test]
fn test_parse_partly_invalid_account_word_keeps_mains_message() {
    let src = format!("{HEAD}{BOM}\tG:\u{3A8}@3O+.1\n");
    let result = parse_both(&src);
    assert!(
        result
            .errors
            .iter()
            .any(|e| e.kind == ParseErrorKind::InvalidAccount("G:\u{3A8}@3O+.1".to_string())),
        "{:?}",
        result.errors
    );
}

/// The account search skips invalid tokens only on a line that starts with
/// a BOM: on any other line an account inside one is still main's `P0006`
/// (`Heading,Ü:A` alone is one error, an invalid account), so masking stays
/// limited to the lines it was made for. Masking every line regressed 63
/// fuzz inputs of the parse-error parity harness.
#[test]
fn test_parse_invalid_account_on_bom_free_line_keeps_its_p0006() {
    let src = format!("{HEAD}Heading,\u{DC}:A\n");
    let result = parse_both(&src);
    assert_eq!(result.errors.len(), 1, "{:?}", result.errors);
    assert_eq!(
        result.errors[0].kind,
        ParseErrorKind::InvalidAccount("Heading,\u{DC}:A".to_string()),
        "{:?}",
        result.errors
    );
}

/// The invalid token reported after a `<BOM>*` heading, or in the tail of a
/// BOM-led account, is the one bean-check names: it starts past the valid
/// tokens before it (`{#t{#$x` is `$x`, `"s"$x` is `$x`), and at a lone
/// capital glued to what follows (`1A$x` is `A$x`, `A{#t` is `A{#t`, and
/// `A{#`, where the lexer reads the capital and the `{#` apart, is `A{#`).
#[test]
fn test_parse_bom_line_reports_beancounts_invalid_token_text() {
    for (line, token) in [
        (format!("{BOM}* H {{#t{{#$x"), "$x"),
        (format!("{BOM}* H 1A$x"), "A$x"),
        (format!("{BOM}* H \"s\"$x"), "$x"),
        (format!("{BOM}* H A{{#t"), "A{#t"),
        (format!("{BOM}* H A{{#"), "A{#"),
        (format!("{BOM}assets:A\"s\"$x"), "$x"),
        (format!("{BOM}assets:A1A$x"), "$x"),
    ] {
        let src = format!("{HEAD}{line}\n");
        let result = parse_both(&src);
        let want = format!("unexpected input: invalid token '{token}'");
        let texts: Vec<&str> = result
            .errors
            .iter()
            .filter_map(|e| match &e.kind {
                ParseErrorKind::SyntaxError(m) => Some(m.as_str()),
                _ => None,
            })
            .collect();
        assert_eq!(texts, [want.as_str()], "{src:?}: {:?}", result.errors);
        assert_eq!(result.errors.len(), 2, "{src:?}: {:?}", result.errors);
    }
}

/// After a `{#` in a `<BOM>*` heading rest the lexer resumes mid-line: a
/// `#` there is beancount's `HASH`, not a line-start `#` comment, so the
/// `$x` after `{# ` is still an invalid token (two errors, as bean-check).
#[test]
fn test_parse_heading_rest_hash_after_brace_is_not_a_comment() {
    let src = format!("{HEAD}{BOM}* H {{# $x\n");
    let result = parse_both(&src);
    assert_eq!(result.errors.len(), 2, "{:?}", result.errors);
}

/// KNOWN GAP, pinned on purpose (issue #2954): a BOM right before a
/// posting's price or cost is the line's one `P0026`, as in bean-check, but
/// recovery keeps the posting without its price or cost. The transaction
/// then no longer balances, so `rledger check` adds two `E3001` where
/// bean-check reports one error. `main` already drops the cost after any
/// other invalid character (`\x11{2 USD}`), so this is the same recovery gap,
/// newly reached by a mid-line BOM since its run takes the `@` or `{`.
/// Fixing #2954 must update this test on purpose.
#[test]
fn test_parse_bom_before_price_or_cost_drops_it_issue_2954() {
    for (tail, invalid) in [
        (format!("{BOM}@ 2 USD"), BOM),
        (format!("{BOM}@@ 2 USD"), BOM),
        (format!("{BOM}{{2 USD}}"), BOM),
        ("\x11{2 USD}".to_string(), "\x11"),
    ] {
        let src =
            format!("{HEAD}\n2024-01-02 * \"x\"\n  Assets:A  1 HOOL {tail}\n  Assets:B  -2 USD\n");
        let result = parse_both(&src);
        assert_eq!(result.errors.len(), 1, "{src:?}: {:?}", result.errors);
        if invalid == BOM {
            assert_eq!(bom_errors(&result), 1, "{src:?}: {:?}", result.errors);
        }
        assert_eq!(result.directives.len(), 3, "{src:?}");
        let Directive::Transaction(t) = &result.directives[2].value else {
            panic!("{src:?}: {:?}", result.directives[2].value);
        };
        assert_eq!(t.postings.len(), 2, "{src:?}");
        let leg = &t.postings[0];
        assert_eq!(leg.account.as_str(), "Assets:A", "{src:?}");
        assert_eq!(
            leg.units.as_ref().map(ToString::to_string).as_deref(),
            Some("1 HOOL"),
            "{src:?}"
        );
        // The gap itself: the price and the cost are gone.
        assert!(leg.price.is_none(), "{src:?}: {:?}", leg.price);
        assert!(leg.cost.is_none(), "{src:?}: {:?}", leg.cost);
    }
}

/// A token of BOMs alone that ends the file is still an invalid token: no
/// account follows it, so the directive holds an invalid token, and its
/// `BomInDirectiveBody` is the line's one error, with the `open` kept. bean-
/// check 3.2.3 reports one error for this file, which has no final newline.
/// Pins the end-of-walk rule of `holds_an_invalid_token`: treating the held
/// BOMs as no token drops the `open` and adds a second error.
#[test]
fn test_parse_bom_alone_at_eof_after_directive_is_one_error() {
    let src = format!("{HEAD}2024-01-03 open Assets:C USD \"BAD\" {BOM}");
    let result = parse_both(&src);
    assert_eq!(result.errors.len(), 1, "{src:?}: {:?}", result.errors);
    assert_eq!(bom_errors(&result), 1, "{src:?}: {:?}", result.errors);
    assert_eq!(result.directives.len(), 3, "{src:?}");
    let Directive::Open(open) = &result.directives[2].value else {
        panic!("{src:?}: {:?}", result.directives[2].value);
    };
    assert_eq!(open.account.as_str(), "Assets:C", "{src:?}");
}

/// A BOM glued to a posting's currency right before its price or cost, or
/// to a balance's number right before its tolerance, starts the line's one
/// invalid token there (`<BOM>@`, `<BOM>{2`, `<BOM>~`), with or without a
/// blank before it and with LF or CRLF line endings: one error, as in
/// bean-check 3.2.3. A posting's trailing-tokens check, whose error starts
/// where the amount ends, right at the glued token, and a balance's
/// malformed-amount check reported a second one. The price or cost after
/// the token is dropped (issue #2954), as it is with the blank.
#[test]
fn test_parse_bom_glued_before_price_cost_or_tolerance_is_one_error() {
    for end in ["\n", "\r\n"] {
        for gap in ["", " "] {
            for tail in [
                "@ 2 USD",
                "@@ 2 USD",
                "{2 USD}",
                "{{2 USD}}",
                "{{4 USD}} @@ 5 USD",
                "~ 2 USD",
            ] {
                let src = format!(
                    "{HEAD}2024-01-02 * \"x\"{end}  Assets:A  1 HOOL{gap}{BOM}{tail}{end}  \
                     Assets:B  -2 USD{end}"
                );
                let result = parse_both(&src);
                assert_eq!(result.errors.len(), 1, "{src:?}: {:?}", result.errors);
                assert_eq!(bom_errors(&result), 1, "{src:?}: {:?}", result.errors);
                let posting = result
                    .directives
                    .iter()
                    .find_map(|d| match &d.value {
                        Directive::Transaction(t) => t.postings.first().cloned(),
                        _ => None,
                    })
                    .expect("the transaction is kept");
                assert!(
                    posting.value.price.is_none() && posting.value.cost.is_none(),
                    "{src:?}: {posting:?}"
                );
            }
            let src = format!("{HEAD}2024-01-02 balance Assets:A 1.00{gap}{BOM}~ 0.01 USD{end}");
            let result = parse_both(&src);
            assert_eq!(result.errors.len(), 1, "{src:?}: {:?}", result.errors);
            assert_eq!(bom_errors(&result), 1, "{src:?}: {:?}", result.errors);
        }
    }
}
