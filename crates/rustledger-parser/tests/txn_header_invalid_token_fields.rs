//! An invalid token in a transaction header moves no string to a different
//! field (#2932).
//!
//! beancount drops a transaction whose header holds an invalid token; rledger
//! keeps it under error recovery, so that editor surfaces (LSP, WASM, FFI) do
//! not lose the entry on a typo. Counting only the surviving strings then
//! moved them: `* "p" <bad>` loaded with no payee and the narration `p`. The
//! rule now in `txn_header::header_payee_narration` lets an invalid token
//! hold the string slot it sits in, so `p` stays the payee and the narration
//! is empty. The invalid token is still reported, once, at the same span.
//!
//! Every case runs on `parse` (green, falling back to red) and on
//! `parse_red_only`, and the two must agree on directives and errors.

use rustledger_core::{Directive, InternedStr, Link, Tag, Transaction};
use rustledger_parser::cst::parse_red_only;
use rustledger_parser::{ParseResult, parse};

/// The invalid character: a control character, which no lexer rule takes.
const BAD: &str = "\u{11}";

struct Case {
    header: String,
    payee: Option<&'static str>,
    narration: &'static str,
    tags: &'static [&'static str],
    links: &'static [&'static str],
}

fn case(
    header: &str,
    payee: Option<&'static str>,
    narration: &'static str,
    tags: &'static [&'static str],
    links: &'static [&'static str],
) -> Case {
    Case {
        header: header.replace("<bad>", BAD),
        payee,
        narration,
        tags,
        links,
    }
}

fn only_transaction<'a>(result: &'a ParseResult, src: &str) -> &'a Transaction {
    let txns: Vec<&Transaction> = result
        .directives
        .iter()
        .filter_map(|d| match &d.value {
            Directive::Transaction(t) => Some(t),
            _ => None,
        })
        .collect();
    assert_eq!(txns.len(), 1, "{src:?}: the transaction is kept");
    txns[0]
}

fn check(c: &Case) {
    let src = format!(
        "2024-01-01 open Assets:A\n2024-01-01 open Assets:B\n\
         2024-01-02 {}\n  Assets:A 1 USD\n  Assets:B\n",
        c.header
    );
    let green = parse(&src);
    let red = parse_red_only(&src);
    for (name, result) in [("parse", &green), ("parse_red_only", &red)] {
        let t = only_transaction(result, &src);
        assert_eq!(
            t.payee.as_ref().map(InternedStr::as_str),
            c.payee,
            "{name} payee {src:?}"
        );
        assert_eq!(
            t.narration.as_str(),
            c.narration,
            "{name} narration {src:?}"
        );
        let tags: Vec<&str> = t.tags.iter().map(Tag::as_str).collect();
        let links: Vec<&str> = t.links.iter().map(Link::as_str).collect();
        assert_eq!(tags, c.tags, "{name} tags {src:?}");
        assert_eq!(links, c.links, "{name} links {src:?}");
        assert_eq!(t.postings.len(), 2, "{name} postings {src:?}");
        // One error, the invalid token itself, reported where it is.
        assert_eq!(
            result.errors.len(),
            1,
            "{name} {src:?}: {:?}",
            result.errors
        );
        let at = src.find(BAD).expect("fixture has an invalid token");
        assert_eq!(result.errors[0].span.start, at, "{name} {src:?}");
    }
    assert_eq!(
        format!("{:?}", green.directives),
        format!("{:?}", red.directives),
        "green/red directives {src:?}"
    );
    assert_eq!(
        format!("{:?}", green.errors),
        format!("{:?}", red.errors),
        "green/red errors {src:?}"
    );
}

#[test]
fn test_parse_invalid_token_glued_to_the_only_string_leaves_no_field() {
    // The string glued to the invalid token is part of it, as in beancount.
    check(&case("* <bad>\"x\"", None, "", &[], &[]));
    check(&case("txn <bad>\"x\"", None, "", &[], &[]));
}

#[test]
fn test_parse_invalid_token_after_the_payee_keeps_the_payee() {
    // The issue's case: `p` was the narration.
    check(&case("* \"p\" <bad>\"y\"", Some("p"), "", &[], &[]));
    check(&case("* \"p\" <bad>", Some("p"), "", &[], &[]));
    check(&case("txn \"p\" <bad>", Some("p"), "", &[], &[]));
    check(&case("! \"p\" <bad>\"y\"", Some("p"), "", &[], &[]));
}

#[test]
fn test_parse_invalid_token_before_the_strings_moves_neither() {
    check(&case("* <bad> \"p\" \"n\"", Some("p"), "n", &[], &[]));
    check(&case("txn <bad> \"p\" \"n\"", Some("p"), "n", &[], &[]));
    check(&case("* <bad> \"n\"", None, "n", &[], &[]));
    check(&case("*<bad> \"n\"", None, "n", &[], &[]));
}

#[test]
fn test_parse_invalid_token_between_two_strings_moves_neither() {
    check(&case("* \"p\" <bad> \"n\"", Some("p"), "n", &[], &[]));
    check(&case("* \"p\" \"n\" <bad>", Some("p"), "n", &[], &[]));
}

#[test]
fn test_parse_invalid_token_with_tags_and_links_keeps_every_field() {
    check(&case("* \"p\" <bad> #t ^l", Some("p"), "", &["t"], &["l"]));
    check(&case(
        "txn \"p\" <bad> #t ^l",
        Some("p"),
        "",
        &["t"],
        &["l"],
    ));
    check(&case(
        "* \"p\" \"n\" <bad> #t ^l",
        Some("p"),
        "n",
        &["t"],
        &["l"],
    ));
    check(&case("* <bad>\"x\" #t ^l", None, "", &["t"], &["l"]));
    // After a tag the invalid token is in the tag position, not a string
    // slot: the lone string is still the narration.
    check(&case("* \"n\" #t <bad>", None, "n", &["t"], &[]));
    check(&case("* \"n\" #t ^l <bad>", None, "n", &["t"], &["l"]));
}
