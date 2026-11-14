//! A construct check that ends right where its line's first invalid token
//! starts is that token's error alone, as in beancount (#2967).
//!
//! beancount's lexer reports each token it cannot read, and its grammar never
//! sees one: when the line's grammar has read up to the invalid token, the
//! token is the line's first and only grammar-level error there. A posting's
//! sign check (`-$x`: a `-` that must be followed by a number) covers the
//! sign and the blanks after it, so it ends exactly where the token starts.
//! `quiet_after_invalid_tokens` dropped such a check only when it ran past the
//! token's start, so this one was kept, one error more than beancount.
//!
//! Every expected count below was checked against `bean-check` 3.2.3.

use rustledger_parser::parse;

/// The errors of `src` per line (1-based, counting `\n` only, as
/// `rledger check` does): `(line, count)`, in line order.
fn per_line(src: &str) -> Vec<(usize, usize)> {
    let mut counts: Vec<(usize, usize)> = Vec::new();
    for e in &parse(src).errors {
        let line = 1 + src[..e.span.start].matches('\n').count();
        match counts.iter_mut().find(|(l, _)| *l == line) {
            Some((_, n)) => *n += 1,
            None => counts.push((line, 1)),
        }
    }
    counts.sort_unstable();
    counts
}

/// Two opens, the start of every source below.
const OPENS: &str = "2024-01-01 open Assets:A\n2024-01-01 open Assets:B\n";

const BOM: &str = "\u{feff}";

/// Every posting row of the issue, with bean-check's count for its line:
/// `(posting line, errors on it)`. Main counted one more on each.
fn issue_postings() -> Vec<(String, usize)> {
    vec![
        ("  Assets:A  -$x".to_string(), 1),
        ("  Assets:A  +$".to_string(), 1),
        ("  Assets:A  -$~ 2 USD".to_string(), 1),
        ("  Assets:A -$  {".to_string(), 1),
        ("  Assets:A  -$~@@".to_string(), 1),
        ("  Assets:A  -$~ \"s\"".to_string(), 1),
        ("  Assets:A  -$~ 1,000".to_string(), 1),
        (format!("  Assets:A -{BOM}  {{"), 1),
        // The control character is an invalid token of its own.
        (format!("  Assets:A +{BOM}x EUR  \x11"), 2),
    ]
}

#[test]
fn test_parse_sign_check_ending_at_an_invalid_token_is_that_token_alone() {
    for (posting, n) in issue_postings() {
        // The posting first, then a second one.
        let src = format!("{OPENS}2024-01-02 *\n{posting}\n  Assets:B\n");
        assert_eq!(per_line(&src), vec![(4, n)], "{src:?}");
        // CRLF line endings.
        let crlf = src.replace('\n', "\r\n");
        assert_eq!(per_line(&crlf), vec![(4, n)], "{crlf:?}");
        // Tab indentation (and a tab before the amount).
        let tabs = src.replace("  ", "\t");
        assert_eq!(per_line(&tabs), vec![(4, n)], "{tabs:?}");
        // The last line of the file, with no final newline.
        let last = format!("{OPENS}2024-01-02 *\n  Assets:B  1 USD\n{posting}");
        assert_eq!(per_line(&last), vec![(5, n)], "{last:?}");
        // After a metadata line, which beancount reads as an invalid token
        // (`k:`) under a transaction header with no posting yet.
        let meta = format!("{OPENS}2024-01-02 * \"x\"\n  k: \"v\"\n{posting}\n  Assets:B\n");
        assert_eq!(per_line(&meta), vec![(4, 1), (5, n)], "{meta:?}");
    }
}

/// A header's amount check that ends where an invalid token starts (`1 +`
/// glued to `2x`, which beancount reads as one invalid token) is that token's
/// error alone too. Main counted one more on each.
#[test]
fn test_parse_header_amount_check_ending_at_an_invalid_token_is_that_token_alone() {
    for (line, n) in [
        ("2024-01-02 balance Assets:A 1 +2x EUR  \x11", 2),
        ("2024-01-02 balance Assets:A 1 +2x EUR", 1),
        ("2024-01-02 price HOOL 1 +\t2x EUR  \x11", 2),
        ("2024-01-02 price HOOL 1 +2x EUR", 1),
    ] {
        let src = format!("{OPENS}{line}\n");
        assert_eq!(per_line(&src), vec![(3, n)], "{src:?}");
    }
}

/// A known mismatch, unchanged from main for the same line without its sign:
/// a sign glued to an invalid token (`-.5`: beancount's NUMBER needs a digit
/// first) and, later on the line, a capital-led word with a character our
/// lexer reads as a token of its own (`U~SD`, `US?D`), which beancount reads
/// as one more invalid token and we do not. Main's sign check stood in for
/// that missing error; with it dropped the line counts what main counts for
/// `.5 U~SD`. Pinned so a fix of the lexer gap shows up here.
#[test]
fn test_parse_sign_check_dropped_before_a_token_we_do_not_read_as_invalid() {
    for word in ["U~SD", "U?SD", "U%SD", "US~D"] {
        let signed = format!("{OPENS}2024-01-02 *\n  Assets:A  1 USD\n  Assets:B  -.5 {word}\n");
        let unsigned = signed.replace("-.5", ".5");
        // beancount: 2 on line 5, for each.
        assert_eq!(per_line(&signed), vec![(5, 1)], "{signed:?}");
        assert_eq!(per_line(&unsigned), vec![(5, 1)], "{unsigned:?}");
    }
}

/// The issue's fuzz input: a sign check inside an orphan indented line that
/// follows an invalid date line.
#[test]
fn test_parse_sign_check_at_an_invalid_token_fuzz_input() {
    assert_eq!(per_line("2615-2-3#\n\tG:\u{3a8}+t+{\n"), vec![(2, 1)]);
}
