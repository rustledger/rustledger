//! An unexpected token in a transaction header moves no string to a
//! different field (#2932).
//!
//! beancount drops a transaction whose header holds an invalid token, or a
//! token its header grammar has no place for (a number, a currency, an
//! account, `~`, `@`, ...); rledger keeps it under error recovery, so that
//! editor surfaces (LSP, WASM, FFI) do not lose the entry on a typo. Counting
//! only the strings then moved them: `* "p" <bad>` and `* "p" 123` loaded
//! with no payee and the narration `p`. The rule now in
//! `txn_header::header_strings` lets an unexpected token hold the string
//! slot it sits in, so `p` stays the payee and the narration is empty. The
//! token is still reported, at the same span, as many times as before.
//!
//! Every case runs on `parse` (green, falling back to red) and on
//! `parse_red_only`, and the two must agree on directives and errors.

use rustledger_core::{Directive, InternedStr, Link, Tag, Transaction};
use rustledger_parser::cst::ast;
use rustledger_parser::cst::parse_red_only;
use rustledger_parser::{ParseResult, parse};

/// The invalid character: a control character, which no lexer rule takes.
const BAD: &str = "\u{11}";

/// The date the transaction under test starts with.
const TXN_DATE: &str = "2024-01-02 ";

struct Case {
    header: String,
    payee: Option<&'static str>,
    narration: &'static str,
    tags: &'static [&'static str],
    links: &'static [&'static str],
    /// The number of errors: one per invalid token, or one for the first
    /// other unexpected token.
    errors: usize,
}

fn case(
    header: &str,
    payee: Option<&'static str>,
    narration: &'static str,
    tags: &'static [&'static str],
    links: &'static [&'static str],
) -> Case {
    Case {
        errors: header.matches("<bad>").count().max(1),
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

/// `junk` is the first unexpected token's text, which the first error is
/// reported at.
fn check(c: &Case, junk: &str) {
    let src = format!(
        "2024-01-01 open Assets:A\n2024-01-01 open Assets:B\n\
         {TXN_DATE}{}\n  Assets:A 1 USD\n  Assets:B\n",
        c.header
    );
    let header_at = src.find(TXN_DATE).expect("fixture has the transaction") + TXN_DATE.len();
    // Searched after the flag, so a junk `*` or `txn` is not the flag itself.
    let after_flag = if c.header.starts_with("txn") { 3 } else { 1 };
    let junk_at = header_at
        + after_flag
        + c.header[after_flag..]
            .find(junk)
            .expect("header has the token");
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
        assert_eq!(
            result.errors.len(),
            c.errors,
            "{name} {src:?}: {:?}",
            result.errors
        );
        assert_eq!(result.errors[0].span.start, junk_at, "{name} {src:?}");
    }
    // The typed accessors (which the formatter reads) use the same rule.
    let file = ast::SourceFile::parse(&src);
    let txn = file
        .directives()
        .find_map(|d| match d {
            ast::Directive::Transaction(t) => Some(t),
            _ => None,
        })
        .expect("the CST has the transaction");
    let text = |s: Option<ast::StringLit>| s.and_then(|s| s.text_unquoted().map(str::to_string));
    assert_eq!(text(txn.payee()).as_deref(), c.payee, "ast payee {src:?}");
    assert_eq!(
        text(txn.narration()).unwrap_or_default(),
        c.narration,
        "ast narration {src:?}"
    );
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

fn check_bad(c: &Case) {
    check(c, BAD);
}

#[test]
fn test_parse_invalid_token_glued_to_the_only_string_leaves_no_field() {
    // The string glued to the invalid token is part of it, as in beancount.
    check_bad(&case("* <bad>\"x\"", None, "", &[], &[]));
    check_bad(&case("txn <bad>\"x\"", None, "", &[], &[]));
}

#[test]
fn test_parse_invalid_token_after_the_payee_keeps_the_payee() {
    // The issue's case: `p` was the narration.
    check_bad(&case("* \"p\" <bad>\"y\"", Some("p"), "", &[], &[]));
    check_bad(&case("* \"p\" <bad>", Some("p"), "", &[], &[]));
    check_bad(&case("txn \"p\" <bad>", Some("p"), "", &[], &[]));
    check_bad(&case("! \"p\" <bad>\"y\"", Some("p"), "", &[], &[]));
}

#[test]
fn test_parse_invalid_token_before_the_strings_moves_neither() {
    check_bad(&case("* <bad> \"p\" \"n\"", Some("p"), "n", &[], &[]));
    check_bad(&case("txn <bad> \"p\" \"n\"", Some("p"), "n", &[], &[]));
    check_bad(&case("* <bad> \"n\"", None, "n", &[], &[]));
    check_bad(&case("*<bad> \"n\"", None, "n", &[], &[]));
}

/// A token written after the string does not move it: `* <bad> "n"` is the
/// narration, and stays so with a second invalid token after it.
#[test]
fn test_parse_invalid_token_before_and_after_the_string_keeps_the_narration() {
    check_bad(&case("* <bad> \"n\" <bad>", None, "n", &[], &[]));
    check_bad(&case(
        "txn <bad> \"n\" <bad> #t ^l",
        None,
        "n",
        &["t"],
        &["l"],
    ));
}

#[test]
fn test_parse_invalid_token_between_two_strings_moves_neither() {
    check_bad(&case("* \"p\" <bad> \"n\"", Some("p"), "n", &[], &[]));
    check_bad(&case("* \"p\" \"n\" <bad>", Some("p"), "n", &[], &[]));
}

#[test]
fn test_parse_invalid_token_with_tags_and_links_keeps_every_field() {
    check_bad(&case("* \"p\" <bad> #t ^l", Some("p"), "", &["t"], &["l"]));
    check_bad(&case(
        "txn \"p\" <bad> #t ^l",
        Some("p"),
        "",
        &["t"],
        &["l"],
    ));
    check_bad(&case(
        "* \"p\" \"n\" <bad> #t ^l",
        Some("p"),
        "n",
        &["t"],
        &["l"],
    ));
    check_bad(&case("* <bad>\"x\" #t ^l", None, "", &["t"], &["l"]));
    // After a tag the invalid token is in the tag position, not a string
    // slot: the lone string is still the narration.
    check_bad(&case("* \"n\" #t <bad>", None, "n", &["t"], &[]));
    check_bad(&case("* \"n\" #t ^l <bad>", None, "n", &["t"], &["l"]));
}

/// Every other token the header grammar has no place for holds its slot the
/// same way: a number, a currency (one letter too), an account, `~`, `@`,
/// a brace, a parenthesis, a comma, a date, a boolean, a metadata key, a
/// keyword, a second flag and a mid-line `#!`.
const JUNK: &[&str] = &[
    "123", "USD", "A", "Assets:A", "~", "@", "{", "(1+2)", ",", "TRUE", "key:", "open", "txn", "*",
    "!", "#!x",
];

#[test]
fn test_parse_unexpected_token_after_the_payee_keeps_the_payee() {
    for junk in JUNK {
        for (flag, tags, links, tail) in [
            ("*", &[][..], &[][..], ""),
            ("txn", &[][..], &[][..], ""),
            ("*", &["t"][..], &["l"][..], " #t ^l"),
        ] {
            // A mid-line `#!` runs to the end of the line (#2802), so it
            // takes any tag after it with it.
            if *junk == "#!x" && !tail.is_empty() {
                continue;
            }
            let c = Case {
                header: format!("{flag} \"p\" {junk}{tail}"),
                payee: Some("p"),
                narration: "",
                tags,
                links,
                errors: 1,
            };
            check(&c, junk);
        }
    }
}

#[test]
fn test_parse_unexpected_token_before_the_string_keeps_the_narration() {
    for junk in JUNK {
        // A mid-line `#!` runs to the end of the line (#2802), so no string
        // after it survives.
        if *junk == "#!x" {
            continue;
        }
        for header in [format!("* {junk} \"n\""), format!("* {junk} \"n\" {junk}")] {
            let c = Case {
                header,
                payee: None,
                narration: "n",
                tags: &[],
                links: &[],
                errors: 1,
            };
            check(&c, junk);
        }
        let c = Case {
            header: format!("* {junk} \"p\" \"n\""),
            payee: Some("p"),
            narration: "n",
            tags: &[],
            links: &[],
            errors: 1,
        };
        check(&c, junk);
    }
}

#[test]
fn test_parse_unexpected_token_after_a_tag_is_in_no_string_slot() {
    for junk in JUNK {
        let c = Case {
            header: format!("* \"n\" #t {junk}"),
            payee: None,
            narration: "n",
            tags: &["t"],
            links: &[],
            errors: 1,
        };
        check(&c, junk);
    }
}
