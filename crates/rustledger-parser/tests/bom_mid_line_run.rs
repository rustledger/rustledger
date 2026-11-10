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
/// account is an account; see `test_parse_bom_led_account_is_an_account`). The
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

/// A BOM glued to an account shape is an account in beancount, whose account
/// type admits a non-ASCII first character, a BOM included: `<BOM>Assets:A`
/// is one ACCOUNT there, and the BOM only makes its name invalid when the
/// file loads. So it is here: no parse error, the directive is kept with the
/// BOM in its account, and the account-name check reports it on load.
#[test]
fn test_parse_bom_led_account_is_an_account() {
    for (line, account) in [
        (
            format!("2024-01-02 open {BOM}Assets:C"),
            format!("{BOM}Assets:C"),
        ),
        (
            format!("2024-01-02 open\t{BOM}Assets:C"),
            format!("{BOM}Assets:C"),
        ),
        (
            format!("2024-01-02 close {BOM}Assets:A"),
            format!("{BOM}Assets:A"),
        ),
        (
            format!("2024-01-02 pad {BOM}Assets:A Assets:B"),
            format!("{BOM}Assets:A"),
        ),
        (
            format!("2024-01-02 balance {BOM}Assets:A 0 USD"),
            format!("{BOM}Assets:A"),
        ),
        (
            format!("2024-01-02 note {BOM}Ü:A \"x\""),
            format!("{BOM}Ü:A"),
        ),
        (format!("2024-01-02 close {BOM}1:A"), format!("{BOM}1:A")),
    ] {
        let src = format!("{HEAD}{line}\n");
        let result = parse_both(&src);
        assert!(result.errors.is_empty(), "{src:?}: {:?}", result.errors);
        assert_eq!(result.directives.len(), 3, "{src:?}");
        let got = match &result.directives[2].value {
            Directive::Open(d) => d.account.to_string(),
            Directive::Close(d) => d.account.to_string(),
            Directive::Pad(d) => d.account.to_string(),
            Directive::Balance(d) => d.account.to_string(),
            Directive::Note(d) => d.account.to_string(),
            other => panic!("{src:?}: {other:?}"),
        };
        assert_eq!(got, account, "{src:?}");
    }
    // Not an account shape: still an invalid token.
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
