//! Two error counts after a line's grammar has failed, from #2968.
//!
//! A BOM that beancount reads into an account (`<BOM>Assets:A`,
//! `<BOM>xAssets:A`) is no invalid token there: that `ACCOUNT` is an error
//! only when the grammar fails right at it, which our `BomInDirectiveBody`
//! stands for. After an earlier error on its line (an invalid token, or a
//! defect the grammar fails at first), beancount reports nothing for it, so
//! neither do we.
//!
//! A tag or link on a directive that does not take one is reported in its
//! own words (`reject_tags_and_links`), but a defect before it on the line
//! (`close Assets:A TRUE #t`) is where beancount's grammar fails, so that is
//! reported in the tag's place. With an invalid token between the two
//! (`TRUE $x #t`) the line used to keep the token's error alone.
//!
//! Every count below was checked against `bean-check` 3.2.3.

use rustledger_parser::cst::parse_red_only;
use rustledger_parser::{ParseResult, parse};

const OPENS: &str = "2024-01-01 open Assets:A\n2024-01-01 open Assets:B\n";
const BOM: char = '\u{feff}';

/// `(line, errors on it)`, 1-based, in line order.
fn line_counts(src: &str, result: &ParseResult) -> Vec<(usize, usize)> {
    let mut out: Vec<(usize, usize)> = Vec::new();
    for e in &result.errors {
        let line = src[..e.span.start].matches('\n').count() + 1;
        match out.iter_mut().find(|(l, _)| *l == line) {
            Some((_, n)) => *n += 1,
            None => out.push((line, 1)),
        }
    }
    out.sort_unstable();
    out
}

/// The per-line counts of `src`, the same on the green and the red path.
fn counts(src: &str) -> Vec<(usize, usize)> {
    let green = line_counts(src, &parse(src));
    assert_eq!(green, line_counts(src, &parse_red_only(src)), "{src:?}");
    green
}

fn messages(src: &str) -> Vec<String> {
    parse(src)
        .errors
        .iter()
        .map(|e| e.kind.to_string())
        .collect()
}

fn txn(posting: &str) -> String {
    format!("{OPENS}2024-01-02 *\n{posting}\n  Assets:B\n")
}

#[test]
fn test_parse_bom_account_after_an_invalid_token_is_no_error() {
    // The issue's first row, and its update's two.
    let cases = [
        (
            txn(&format!("  Assets:A $@ {BOM}xAssets:A.00")),
            vec![(4, 2)],
        ),
        (txn(&format!("  Assets:A $@ {BOM}Assets:A")), vec![(4, 1)]),
        (
            txn(&format!("  Assets:A $@ {BOM}Assets:A.00")),
            vec![(4, 2)],
        ),
        // The same with CRLF, and at the end of the file.
        (
            txn(&format!("  Assets:A $@ {BOM}Assets:A")).replace('\n', "\r\n"),
            vec![(4, 1)],
        ),
        (
            format!("{OPENS}2024-01-02 *\n  Assets:A $@ {BOM}Assets:A"),
            vec![(4, 1)],
        ),
        // A `~$` after it: beancount's `$`, our second invalid token.
        (
            txn(&format!("  Assets:A $@ {BOM}Assets:A ~$")),
            vec![(4, 2)],
        ),
    ];
    for (src, want) in cases {
        assert_eq!(counts(&src), want, "{src:?}");
        assert!(
            !messages(&src).iter().any(|m| m.contains("BOM")),
            "{src:?}: {:?}",
            messages(&src)
        );
    }
}

#[test]
fn test_parse_bom_account_after_a_grammar_defect_is_no_error() {
    let cases = [
        // Two BOM-led accounts after a posting's account: the grammar fails
        // at the first, and only there.
        (
            txn(&format!("  Assets:A {BOM}Assets:B {BOM}Assets:A")),
            vec![(4, 1)],
        ),
        (
            txn(&format!("  Assets:A 1 USD ! {BOM}Assets:A")),
            vec![(4, 1)],
        ),
        (
            format!("{OPENS}2024-01-02 commodity HOOL TRUE {BOM}Assets:A\n"),
            vec![(3, 1)],
        ),
        (
            format!("{OPENS}2024-01-02 commodity HOOL TRUE {BOM}Assets:A #t\n"),
            vec![(3, 1)],
        ),
        // A grammar defect, the BOM-led account, an invalid token, a tag.
        (
            format!("{OPENS}2024-01-02 commodity HOOL  TRUE\t{BOM}Assets:A.00  #t\n"),
            vec![(3, 2)],
        ),
        (
            format!("{OPENS}2024-01-02 open Assets:C USD  ( {BOM}Assets:A.00 #t\n"),
            vec![(3, 2)],
        ),
        (
            format!("{OPENS}2024-01-02 event \"a\" \"b\" %\t{BOM}Assets:A.00  #t2\n"),
            vec![(3, 2)],
        ),
    ];
    for (src, want) in cases {
        assert_eq!(counts(&src), want, "{src:?}");
    }
}

#[test]
fn test_parse_bom_account_where_the_grammar_fails_is_still_reported() {
    // Nothing on the line before it: the grammar fails at that account, and
    // its `BomInDirectiveBody` stands for that.
    let src = txn(&format!("  Assets:A {BOM}Assets:A"));
    assert_eq!(counts(&src), vec![(4, 1)]);
    assert!(messages(&src)[0].contains("BOM"), "{:?}", messages(&src));
    // And with an invalid token after it, both.
    let src = txn(&format!("  Assets:A {BOM}Assets:A $@"));
    assert_eq!(counts(&src), vec![(4, 2)]);
    assert!(messages(&src)[0].contains("BOM"), "{:?}", messages(&src));
}

#[test]
fn test_parse_header_defect_before_a_tag_is_reported_in_its_place() {
    let cases = [
        // The issue's second row, its BOM-free form, and its update's rows.
        (
            format!("{OPENS}2024-01-02 close Assets:A TRUE {BOM}x  (k: #t Assets:A{BOM}~\n"),
            vec![(3, 3)],
        ),
        (
            format!("{OPENS}2024-01-02 close Assets:A TRUE $x  (k: #t Assets:A$~\n"),
            vec![(3, 4)],
        ),
        (
            format!("{OPENS}2024-01-02 close Assets:A TRUE $x #t\n"),
            vec![(3, 2)],
        ),
        (
            format!("{OPENS}2024-01-02 close Assets:A TRUE {BOM}x\n"),
            vec![(3, 2)],
        ),
        // Other directives that take no tag or link.
        (
            format!("{OPENS}2024-01-02 open Assets:C USD TRUE $x #t\n"),
            vec![(3, 2)],
        ),
        (
            format!("{OPENS}2024-01-02 event \"a\" \"b\" TRUE $x #t\n"),
            vec![(3, 2)],
        ),
        (
            format!("{OPENS}2024-01-02 pad Assets:A Assets:B 1 $x ^l\n"),
            vec![(3, 2)],
        ),
        (
            format!("{OPENS}2024-01-02 balance Assets:A 1 USD TRUE $x #t\n"),
            vec![(3, 2)],
        ),
        // No invalid token: one error either way, and two tags after the
        // defect are still one.
        (
            format!("{OPENS}2024-01-02 close Assets:A TRUE #t\n"),
            vec![(3, 1)],
        ),
        (
            format!("{OPENS}2024-01-02 close Assets:A TRUE #t ^l\n"),
            vec![(3, 1)],
        ),
    ];
    for (src, want) in cases {
        assert_eq!(counts(&src), want, "{src:?}");
    }
    // The defect is named, where beancount's grammar fails.
    let src = format!("{OPENS}2024-01-02 close Assets:A TRUE $x #t\n");
    assert!(
        messages(&src)[0].contains("unexpected \"TRUE\" in the close directive"),
        "{:?}",
        messages(&src)
    );
}

#[test]
fn test_parse_tag_before_a_header_defect_keeps_its_own_error() {
    // The tag is where the grammar fails: its own message, once.
    for src in [
        format!("{OPENS}2024-01-02 close Assets:A #t TRUE\n"),
        format!("{OPENS}2024-01-02 open Assets:C #t\n"),
        format!("{OPENS}2024-01-02 event \"a\" \"b\" #t\n"),
    ] {
        assert_eq!(counts(&src), vec![(3, 1)], "{src:?}");
        assert!(
            messages(&src)[0].contains("does not take a tag"),
            "{src:?}: {:?}",
            messages(&src)
        );
    }
}

/// Known, documented in the PR: where our lexer already reads the line with
/// one error fewer than beancount (`~$`, beancount's `TILDE` and `$`; `% $x`,
/// its `FLAG` and `$x`), a BOM-led account's error made the count match by
/// chance. It is gone now, and the line counts what it counts with a plain
/// account in the BOM-led one's place.
#[test]
fn test_parse_bom_account_no_longer_stands_in_for_a_missed_error() {
    let cases = [
        (
            txn(&format!("  Assets:A  ~$ {BOM}{BOM}Assets:B  -$")),
            txn("  Assets:A  ~$ Assets:Z  -$"),
            vec![(4, 2)], // beancount: 3
        ),
        (
            txn(&format!("  Assets:A  % $x  {BOM}Assets:A,  ^a-b")),
            txn("  Assets:A  % $x  Assets:Z,  ^a-b"),
            vec![(4, 1)], // beancount: 2
        ),
    ];
    for (src, plain, want) in cases {
        assert_eq!(counts(&src), want, "{src:?}");
        assert_eq!(counts(&plain), want, "{plain:?}");
    }
}
