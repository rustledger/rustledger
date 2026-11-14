//! A mid-file BOM at the start of a line is counted as beancount counts it
//! (#2956).
//!
//! beancount's lexer reads a line-start BOM (U+FEFF, not the file's first
//! byte) as the start of an invalid token, which runs to the next blank. So
//! the statement it starts, or breaks into, fails right there, and bison's
//! recovery stays quiet about the lines after it until its grammar has read
//! three tokens again (`quiet_after_line_start_bom_lines`): a transaction's
//! postings after its BOM-led header, or the rest of a block a BOM line
//! breaks into, are no errors there. Each was an orphan `unexpected input`
//! here, where the BOM line ended the block.
//!
//! And a BOM glued to a `;` (or a line start beancount skips: `%`, `#`, `!`,
//! `&`, `?`, `:`) is that same invalid token there, so the rest of the line is
//! lexed and its words reported. Here the BOM kept its own extent and the `;`
//! hid the rest of the line as a comment.
//!
//! Every expected count below was checked against `bean-check` 3.2.3.

use rustledger_parser::cst::parse_red_only;
use rustledger_parser::{parse, transaction_holds_invalid_token};

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

/// Two opens, the start of every source below.
const OPENS: &str = "2024-01-01 open Assets:A\n2024-01-01 open Assets:B\n";

const BOM: &str = "\u{feff}";

/// The issue's rows, item 1: a line a BOM starts, in a transaction or at its
/// header, is the one error; the postings after it are none.
#[test]
fn test_parse_line_start_bom_quiets_the_rest_of_its_block() {
    let cases = [
        // The header the BOM starts, and its postings.
        (
            format!("{OPENS}{BOM}2024-01-02 * \"x\"\n  Assets:A 1 USD\n  Assets:B  -1 USD\n"),
            vec![(3, 1)],
        ),
        // The first posting.
        (
            format!("{OPENS}2024-01-02 * \"x\"\n{BOM}  Assets:A 1 USD\n  Assets:B  -1 USD\n"),
            vec![(4, 1)],
        ),
        // A posting glued to the BOM: beancount reads the BOM into the
        // account, and its grammar fails at that account.
        (
            format!("{OPENS}2024-01-02 * \"x\"\n{BOM}Assets:A 1 USD\n  Assets:B  -1 USD\n"),
            vec![(4, 1)],
        ),
        // A metadata line between postings.
        (
            format!(
                "{OPENS}2024-01-02 * \"x\"\n  Assets:A 1 USD\n{BOM}  key: \"v\"\n  Assets:B  -1 USD\n"
            ),
            vec![(5, 1)],
        ),
        // A comment line between postings: three invalid tokens (item 2).
        (
            format!(
                "{OPENS}2024-01-02 * \"x\"\n  Assets:A 1 USD\n{BOM}; c x\n  Assets:B  -1 USD\n"
            ),
            vec![(5, 3)],
        ),
        // A one-letter key is an invalid token of beancount's, quiet or not.
        (
            format!(
                "{OPENS}{BOM}2024-01-02 * \"x\"\n  k: \"v\"\n  Assets:A 1 USD\n  Assets:B  -1 USD\n"
            ),
            vec![(3, 1), (4, 1)],
        ),
        // An open's metadata after the BOM line.
        (
            format!(
                "{OPENS}2024-01-02 open Assets:C\n  kk: \"v\"\n{BOM}  jj: \"w\"\n  ll: \"z\"\n"
            ),
            vec![(5, 1)],
        ),
        // Two BOM lines, each with a posting after it.
        (
            format!("{OPENS}{BOM}x\n  Assets:A 1 USD\n{BOM}y\n  Assets:A 1 USD\n"),
            vec![(3, 1), (5, 1)],
        ),
    ];
    for (src, expected) in cases {
        assert_eq!(per_line(&src), expected, "{src:?}");
        let crlf = src.replace('\n', "\r\n");
        assert_eq!(per_line(&crlf), expected, "{crlf:?}");
        let tabs = src.replace("  ", "\t");
        assert_eq!(per_line(&tabs), expected, "{tabs:?}");
    }
}

/// How long the quiet lasts: bison reports again once it has shifted three
/// tokens. The BOM line's ending is one, each blank or skipped line one
/// more; an indented line, or a column-0 line no declaration starts, fails
/// again and starts the count over; a directive's date and keyword end it.
#[test]
fn test_parse_line_start_bom_quiet_lasts_three_tokens() {
    let posting = "  Assets:A 1 USD\n";
    let cases = [
        // One blank line: still quiet.
        (format!("{OPENS}{BOM}x\n\n{posting}"), vec![(3, 1)]),
        // Two: the orphan posting is reported (`unexpected INDENT`).
        (
            format!("{OPENS}{BOM}x\n\n\n{posting}"),
            vec![(3, 1), (6, 1)],
        ),
        // Comment lines count as blank ones.
        (format!("{OPENS}{BOM}x\n; c\n{posting}"), vec![(3, 1)]),
        (
            format!("{OPENS}{BOM}x\n; c\n; d\n{posting}"),
            vec![(3, 1), (6, 1)],
        ),
        // An indented comment starts the count over.
        (format!("{OPENS}{BOM}x\n  ; c\n\n{posting}"), vec![(3, 1)]),
        // A line no declaration starts fails again, quietly.
        (format!("{OPENS}{BOM}x\n5\n{posting}"), vec![(3, 1)]),
        // A directive ends the quiet: the posting after it is reported.
        (
            format!("{OPENS}{BOM}x\n2024-01-03 open Assets:D\n{posting}"),
            vec![(3, 1), (5, 1)],
        ),
        (
            format!("{OPENS}{BOM}x\noption \"title\" \"t\"\n{posting}"),
            vec![(3, 1), (5, 1)],
        ),
        // So does an error past its third token.
        (
            format!("{OPENS}{BOM}x\n2024-01-03 * \"y\" 5\n{posting}"),
            vec![(3, 1), (4, 1)],
        ),
        // A directive with metadata after the BOM line is fine.
        (
            format!("{OPENS}{BOM}x\n2024-01-03 open Assets:D\n  kk: 1\n"),
            vec![(3, 1)],
        ),
        // The last line, with no line ending.
        (format!("{OPENS}{BOM}x"), vec![(3, 1)]),
    ];
    for (src, expected) in cases {
        assert_eq!(per_line(&src), expected, "{src:?}");
    }
}

/// The issue's rows, item 2: a BOM glued to a comment start, or to a line
/// start beancount skips, is one invalid token with it, and the words after
/// it are invalid tokens too, where the comment hid them.
#[test]
fn test_parse_line_start_bom_glued_to_a_comment_start_reads_the_rest_of_the_line() {
    for start in [";", "%", "!", "*", ":", "&", "?", "#", "#t", "#!", "#+"] {
        let src = format!("{OPENS}{BOM}{start} c x\n");
        assert_eq!(per_line(&src), vec![(3, 3)], "{src:?}");
    }
}

/// Where the BOM starts an account in beancount (`<BOM>:A`, `<BOM>Assets:A`),
/// the account is its token there: its grammar fails at it, and what follows
/// it is lexed on, an unclosed `"` included. A `"` in a run beancount reads
/// as one invalid token opens no string.
#[test]
fn test_parse_line_start_bom_account_and_quote() {
    let cases = [
        (format!("{OPENS}{BOM}:A c\n"), vec![(3, 2)]),
        (format!("{OPENS}{BOM}{BOM}:A c\n"), vec![(3, 2)]),
        (format!("{OPENS}{BOM}:A\"\n"), vec![(3, 2)]),
        (
            format!("{OPENS}{BOM}:A\"\n2024-01-03 open Assets:D\n"),
            vec![(3, 2)],
        ),
        (format!("{OPENS}{BOM}Assets:A\"\n"), vec![(3, 2)]),
        // One invalid token, then a string: no swallowed directive.
        (
            format!("{OPENS}{BOM}~\"x\n2024-01-03 open Assets:D\n2024-01-04 open \"y\n"),
            vec![(3, 1), (5, 1)],
        ),
        (format!("{OPENS}{BOM}\"x y\" z\n"), vec![(3, 3)]),
        (format!("{OPENS}{BOM}12;c x\n"), vec![(3, 2)]),
    ];
    for (src, expected) in cases {
        assert_eq!(per_line(&src), expected, "{src:?}");
    }
}

/// A line a BOM starts right where a transaction's block goes on discards the
/// transaction in beancount, so the validator reports no residual for it
/// (`transaction_holds_invalid_token`, asked of the transaction's span, which
/// runs to the next directive). After a blank line the transaction is
/// complete there and keeps its findings.
#[test]
fn test_transaction_holds_invalid_token_counts_a_bom_line_after_it() {
    let broken = format!(
        "2024-01-02 * \"x\"\n  Assets:A 1 USD\n  Assets:B -2 USD\n{BOM}  k: \"v\"\n  Assets:A 1 USD\n"
    );
    assert!(transaction_holds_invalid_token(&broken), "{broken:?}");
    let header = format!("2024-01-02 * \"x\"\n{BOM}  Assets:A 1 USD\n  Assets:B -1 USD\n");
    assert!(transaction_holds_invalid_token(&header), "{header:?}");
    for complete in [
        format!("2024-01-02 * \"x\"\n  Assets:A 1 USD\n\n{BOM}  k: \"v\"\n"),
        format!("2024-01-02 * \"x\"\n  Assets:A 1 USD\n; c\n{BOM}  k: \"v\"\n"),
    ] {
        assert!(!transaction_holds_invalid_token(&complete), "{complete:?}");
    }
}

/// Documented: the same recovery follows a line beancount cannot read for a
/// reason other than a BOM (`5`, `$x`, a failed metadata line), which is not
/// modeled here (#2872). A BOM-led account line inside that window counts
/// what the same line with a plain account counts.
#[test]
fn test_parse_bom_account_after_another_unreadable_line_counts_as_a_plain_account() {
    let bom = per_line(&format!("{OPENS}5\n{BOM}:A\"\n; c\n"));
    let plain = per_line(&format!("{OPENS}5\nAssets:A\"\n; c\n"));
    assert_eq!(bom, plain);
    // beancount counts one on line 4 there.
    assert_eq!(bom, vec![(3, 1), (4, 2)]);
}
