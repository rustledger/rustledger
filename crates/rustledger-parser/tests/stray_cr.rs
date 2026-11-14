//! A stray `\r` right before the line ending is trivia, as in beancount
//! (#2774).
//!
//! Beancount's lexer skips `\r` as whitespace (`[ \t\r]+`), so a line ending
//! in `\r\r\n` (some editors and converters write it) or a file ending in a
//! lone `\r` is accepted by `bean-check` 3.2.3. Ours has no rule for a lone
//! `\r`: the `Newline` token (`\r?\n`) claims only the one right before the
//! `\n`, so every other `\r` came out as an error token. A run of `\r` (mixed
//! with spaces or tabs) that reaches the line ending or the end of the file
//! is now one `Whitespace` token, so its bytes stay in the CST.
//!
//! A `\r` with more of the line after it is still an error. Beancount takes
//! it as a token separator; we deliberately do not, because the formatter
//! folds such a bare `\r` into a line break (that is what keeps classic-Mac
//! files formattable), so accepting it would let `rledger format` split a
//! line `rledger check` accepted. See `TokenIter::stray_cr_trivia_end`.
//!
//! Except before an invalid token (#2966): there the line has that token's
//! error in any case, so nothing is accepted, and the `\r` is a blank, as in
//! beancount, rather than one error more. A lone capital glued to such a
//! `\r` is an invalid token, as beancount's `CAPITAL` needs a space, tab or
//! `\n` after it.
//!
//! Every expected outcome below was checked against `bean-check` 3.2.3.

use rustledger_core::{Directive, InternedStr};
use rustledger_parser::cst::parse_red_only;
use rustledger_parser::format::try_format_source;
use rustledger_parser::logos_lexer::{Token, tokenize_lossless};
use rustledger_parser::{ParseResult, parse, parse_structured};

/// `(kind, start, end)` for each error.
fn errors(result: &ParseResult) -> Vec<(String, usize, usize)> {
    result
        .errors
        .iter()
        .map(|e| (e.kind.to_string(), e.span.start, e.span.end))
        .collect()
}

/// The parsed directives, one line each.
fn summary(result: &ParseResult) -> Vec<String> {
    result
        .directives
        .iter()
        .map(|d| match &d.value {
            Directive::Open(o) => {
                let keys: Vec<&str> = o.meta.keys().map(InternedStr::as_str).collect();
                format!("{} open {} {keys:?}", o.date, o.account)
            }
            Directive::Transaction(t) => {
                let postings: Vec<String> = t
                    .postings
                    .iter()
                    .map(|p| {
                        let keys: Vec<&str> = p.meta.keys().map(InternedStr::as_str).collect();
                        format!("{} {keys:?}", p.account)
                    })
                    .collect();
                format!("{} txn {:?} {postings:?}", t.date, t.narration.as_str())
            }
            other => panic!("unexpected directive {other:?}"),
        })
        .collect()
}

/// Lossless (no gap or overlap, every byte kept), the CST reproduces the
/// source, and the green-wired `parse` agrees with the pure-red path.
fn assert_invariants(src: &str) {
    let mut at = 0;
    for (token, span) in tokenize_lossless(src) {
        assert_eq!(span.start, at, "{src:?}: gap or overlap before {token:?}");
        at = span.end;
    }
    assert_eq!(at, src.len(), "{src:?}");
    assert_eq!(parse_structured(src).text().to_string(), src, "{src:?}");
    let (green, red) = (parse(src), parse_red_only(src));
    assert_eq!(
        format!("{:?}", green.directives),
        format!("{:?}", red.directives),
        "{src:?}"
    );
    assert_eq!(
        format!("{:?}", green.errors),
        format!("{:?}", red.errors),
        "{src:?}"
    );
}

/// Parses with no errors, to exactly `expected`, with the invariants.
fn assert_clean(src: &str, expected: &[&str]) {
    assert_invariants(src);
    let result = parse(src);
    assert_eq!(errors(&result), [], "{src:?}");
    assert_eq!(summary(&result), expected, "{src:?}");
}

const CASH: &str = "2024-01-01 open Assets:Cash []";
const OPENING: &str = "2024-01-01 open Equity:Opening []";
const TXN: &str = r#"2024-01-02 txn "x" ["Assets:Cash []", "Equity:Opening []"]"#;

/// Two opens and a transaction, CRLF throughout, except for the endings of
/// the first open line (`a`), the transaction header and its two postings.
fn ledger(a: &str, header: &str, p1: &str, p2: &str) -> String {
    format!(
        "2024-01-01 open Assets:Cash{a}2024-01-01 open Equity:Opening\r\n\
         2024-01-02 * \"x\"{header}  Assets:Cash  1 USD{p1}  Equity:Opening  -1 USD{p2}"
    )
}

/// The rows of the issue's table: one stray `\r` before the CRLF of an open
/// line, a `;` comment line, a posting line, a transaction header (which
/// gave two errors) and a metadata line. All error on `main`; `bean-check`
/// accepts every one. The last row is the control (`" \r\n"`), clean in
/// both before and after.
#[test]
fn test_parse_stray_cr_before_crlf_issue_rows() {
    let crlf = "\r\n";
    let stray = "\r\r\n";
    assert_clean(&ledger(stray, crlf, crlf, crlf), &[CASH, OPENING, TXN]);
    assert_clean(
        &format!("; note{stray}{}", ledger(crlf, crlf, crlf, crlf)),
        &[CASH, OPENING, TXN],
    );
    assert_clean(&ledger(crlf, crlf, stray, crlf), &[CASH, OPENING, TXN]);
    assert_clean(&ledger(crlf, crlf, crlf, stray), &[CASH, OPENING, TXN]);
    assert_clean(&ledger(crlf, stray, crlf, crlf), &[CASH, OPENING, TXN]);
    assert_clean(
        "2024-01-01 open Assets:Cash\r\n  key: \"v\"\r\r\n2024-01-01 open Equity:Opening\r\n",
        &["2024-01-01 open Assets:Cash [\"key\"]", OPENING],
    );
    assert_clean(&ledger(" \r\n", crlf, crlf, crlf), &[CASH, OPENING, TXN]);
}

/// Further shapes `bean-check` accepts: several stray `\r`, mixed with
/// spaces or tabs, on a posting's metadata line, on a line of its own, in a
/// file that otherwise uses LF, and at the end of the file with no `\n`.
#[test]
fn test_parse_stray_cr_run_before_line_ending_or_eof() {
    for eol in ["\r\r\r\n", " \r\r\n", "\r \r\n", "\r\t\r\n"] {
        assert_clean(&ledger(eol, eol, eol, eol), &[CASH, OPENING, TXN]);
    }
    assert_clean(
        "2024-01-01 open Assets:Cash\r\r\n2024-01-01 open Equity:Opening\n",
        &[CASH, OPENING],
    );
    assert_clean(
        "2024-01-01 open Assets:Cash\n2024-01-01 open Equity:Opening\n\
         2024-01-02 * \"x\"\r\r\n  Assets:Cash  1 USD\n  Equity:Opening  -1 USD\n",
        &[CASH, OPENING, TXN],
    );
    assert_clean(
        "2024-01-01 open Assets:Cash\r\n2024-01-01 open Equity:Opening\r\n\
         2024-01-02 * \"x\"\r\n  Assets:Cash  1 USD\r\n    key: \"v\"\r\r\n\
         \x20 Equity:Opening  -1 USD\r\n",
        &[
            CASH,
            OPENING,
            r#"2024-01-02 txn "x" ["Assets:Cash [\"key\"]", "Equity:Opening []"]"#,
        ],
    );
    assert_clean("2024-01-01 open Assets:Cash\r\n\r\r\n\r\n", &[CASH]);
    assert_clean("\r\r\r\n\r\n2024-01-01 open Assets:Cash\r\n", &[CASH]);
    assert_clean("2024-01-01 open Assets:Cash\r", &[CASH]);
    assert_clean("2024-01-01 open Assets:Cash\r\r", &[CASH]);
    assert_clean("2024-01-01 open Assets:Cash \r", &[CASH]);
    assert_clean("2024-01-01 open Assets:Cash\r\n\r", &[CASH]);
    assert_clean("\r", &[]);
}

/// After every comment form and an org-mode heading. `#` and `*` lines were
/// already accepted (#2769, #2778); `;`, `%`, `#!` and `#+` were not.
#[test]
fn test_parse_stray_cr_after_comments_and_headings() {
    for line in [
        "; c",
        "% c",
        "#! c",
        "#+ c",
        "# c",
        "* c",
        "2024-01-01 open Assets:Cash ; c",
    ] {
        for eol in ["\r\r\n", "\r\r\r\n"] {
            let src = format!("{line}{eol}2024-01-01 open Equity:Opening\r\n");
            let mut expected = vec![OPENING];
            if line.starts_with("2024") {
                expected.insert(0, CASH);
            }
            assert_clean(&src, &expected);
        }
        // As the last line, with no `\n` after the `\r`.
        assert_clean(&format!("2024-01-01 open Equity:Opening\r\n{line}\r"), &{
            let mut expected = vec![OPENING];
            if line.starts_with("2024") {
                expected.push(CASH);
            }
            expected
        });
    }
}

/// The stray bytes are trivia: one `Whitespace` token holding the whole run,
/// then the `Newline` (`\r\n`, as on every other CRLF line). A comment's
/// text no longer carries them.
#[test]
fn test_tokenize_lossless_stray_cr_run_is_one_whitespace_token() {
    let src = "2024-01-01 open Assets:Cash \r\t\r\r\n";
    let tokens = tokenize_lossless(src);
    let tail: Vec<(&Token<'_>, (usize, usize))> = tokens[tokens.len() - 2..]
        .iter()
        .map(|(t, s)| (t, (s.start, s.end)))
        .collect();
    assert_eq!(
        tail,
        [
            (&Token::Whitespace(" \r\t\r"), (27, 31)),
            (&Token::Newline, (31, 33))
        ]
    );

    let tokens = tokenize_lossless("; note\r\r\n");
    let all: Vec<(&Token<'_>, (usize, usize))> =
        tokens.iter().map(|(t, s)| (t, (s.start, s.end))).collect();
    assert_eq!(
        all,
        [
            (&Token::Comment("; note"), (0, 6)),
            (&Token::Whitespace("\r"), (6, 7)),
            (&Token::Newline, (7, 9))
        ]
    );
    let result = parse("; note\r\r\n");
    assert_eq!(result.comments.len(), 1);
    assert_eq!(result.comments[0].value, "; note");

    let tokens = tokenize_lossless("\r\r");
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0].0, Token::Whitespace("\r\r"));
}

/// A `\r` inside a string was already data, and still is.
#[test]
fn test_parse_cr_inside_string_is_unchanged() {
    let src = "2024-01-02 * \"a\rb\"\r\r\n  Assets:Cash  1 USD\r\n  Equity:Opening\r\n";
    assert_invariants(src);
    let result = parse(src);
    assert_eq!(errors(&result), []);
    let Directive::Transaction(t) = &result.directives[0].value else {
        panic!("{:?}", result.directives);
    };
    assert_eq!(t.narration.as_str(), "a\rb");
}

/// Shapes `bean-check` rejects stay errors: classic-Mac `\r`-only line
/// endings (it reports `unexpected DATE`), a whitespace-only line with a
/// stray `\r` inside a transaction (a blank line, which ends it, exactly as
/// `"  \r\n"` does; it reports `unexpected INDENT`), and a `\r` inside a
/// posting's indentation (it reports `unexpected ACCOUNT`).
#[test]
fn test_parse_shapes_beancount_rejects_stay_errors() {
    let src = "2024-01-01 open Assets:Cash\r2024-01-01 open Equity:Opening\r";
    assert_invariants(src);
    assert_eq!(
        errors(&parse(src)),
        [("parse error: unexpected input".to_string(), 27, 28)]
    );

    for blank in ["  \r\n", "  \r\r\n"] {
        let src =
            format!("2024-01-02 * \"x\"\r\n  Assets:Cash  1 USD\r\n{blank}  Equity:Opening\r\n");
        assert_invariants(&src);
        let start = 40 + blank.len();
        assert_eq!(
            errors(&parse(&src)),
            [(
                "parse error: unexpected input".to_string(),
                start,
                start + 18
            )],
            "{blank:?}"
        );
    }

    for posting in ["  \rAssets:Cash  1 USD\r\n", "\r  Assets:Cash  1 USD\r\n"] {
        let src = format!("2024-01-02 * \"x\"\r\n{posting}  Equity:Opening\r\n");
        assert_invariants(&src);
        assert!(!parse(&src).errors.is_empty(), "{posting:?}");
    }
}

/// Stricter than beancount, deliberately (see the module docs): a `\r` with
/// more of the line after it is still an error, where `bean-check` accepts
/// it as a token separator. Exact errors, so a change here is a decision.
#[test]
fn test_parse_cr_with_more_of_the_line_after_it_stays_an_error() {
    let unexpected = |start: usize| {
        (
            "parse error: unexpected input".to_string(),
            start,
            start + 1,
        )
    };
    let cases: [(&str, Vec<(String, usize, usize)>); 4] = [
        ("2024-01-01 open\rAssets:Cash\r\n", vec![unexpected(15)]),
        ("2024-01-01 open Assets:Cash\rUSD\r\n", vec![unexpected(27)]),
        ("2024-01-01 open Assets:Cash\r; c\r\n", vec![unexpected(27)]),
        (
            "2024-01-01 open Assets:Cash\r \r; c\r\n",
            vec![unexpected(27), unexpected(29)],
        ),
    ];
    for (src, expected) in cases {
        assert_invariants(src);
        assert_eq!(errors(&parse(src)), expected, "{src:?}");
    }
    let src = "2024-01-01 open Assets:Cash\r\n\r2024-01-01 open Equity:Opening\r\n";
    assert_invariants(src);
    assert_eq!(
        errors(&parse(src)),
        [("parse error: unexpected input".to_string(), 29, 62)]
    );
}

/// `rledger format` goes through `try_format_source`, which refused these
/// files because of the parse error. Each now formats to the same output as
/// the file without the stray bytes.
#[test]
fn test_try_format_source_stray_cr_formats_like_crlf() {
    let crlf = "\r\n";
    let expected =
        try_format_source(&ledger(crlf, crlf, crlf, crlf)).expect("the CRLF file formats");
    for eol in ["\r\r\n", "\r\r\r\n", " \r\r\n", "\r \r\n"] {
        for src in [
            ledger(eol, crlf, crlf, crlf),
            ledger(crlf, eol, crlf, crlf),
            ledger(crlf, crlf, eol, crlf),
            ledger(crlf, crlf, crlf, eol),
            ledger(crlf, crlf, crlf, "\r"),
        ] {
            assert_eq!(try_format_source(&src).as_ref(), Ok(&expected), "{src:?}");
        }
    }
}

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

/// A stray `\r` before an invalid token is a blank, as in beancount, not an
/// error of its own (#2966): every row of the issue, per context. Each count
/// is bean-check 3.2.3's, per line; main counted one more on each.
#[test]
fn test_parse_cr_before_an_invalid_token_is_a_blank() {
    const BOM: &str = "\u{feff}";
    let cases: Vec<(String, Vec<(usize, usize)>)> = vec![
        // A directive header.
        (
            format!("{OPENS}2024-01-02 open Assets:C\r$\n"),
            vec![(3, 1)],
        ),
        // A transaction header.
        (
            format!("{OPENS}2024-01-02 * \"x\"\r$\n  Assets:A  1 USD\n  Assets:B  -1 USD\n"),
            vec![(3, 1)],
        ),
        // A posting.
        (
            format!("{OPENS}2024-01-02 * \"x\"\n  Assets:A  1 USD\rx\n  Assets:B  -1 USD\n"),
            vec![(4, 1)],
        ),
        // A metadata line.
        (
            format!("{OPENS}2024-01-02 note Assets:A \"n\"\n  kk: \"v\"\r$\n"),
            vec![(4, 1)],
        ),
    ];
    for (src, expected) in cases {
        assert_invariants(&src);
        assert_eq!(per_line(&src), expected, "{src:?}");
    }

    // A line that is `\r<BOM>` (or `\r$`), after any directive, with CRLF, or
    // with no final newline, and as a whole file: one error, the BOM's.
    for before in [
        "2024-01-02 close Assets:A\n",
        "2024-01-02 open Assets:C\n",
        "2024-01-02 commodity HOOL\n",
        "pushtag #t\n",
        "2024-01-02 * \"x\"\n  Assets:A  1 USD\n  Assets:B  -1 USD\n",
        "",
    ] {
        let line = 3 + before.matches('\n').count();
        for tail in [
            format!("\r{BOM}\n"),
            "\r$\n".to_string(),
            format!("\r{BOM}"),
        ] {
            // The `poptag` goes on a line of its own, after a final newline.
            let pop = match (before.starts_with("pushtag"), tail.ends_with('\n')) {
                (true, true) => "poptag #t\n",
                (true, false) => "\npoptag #t\n",
                (false, _) => "",
            };
            let src = format!("{OPENS}{before}{tail}{pop}");
            assert_invariants(&src);
            assert_eq!(per_line(&src), [(line, 1)], "{src:?}");
        }
    }
    let crlf = format!(
        "{}2024-01-02 close Assets:A\r\n\r{BOM}\r\n",
        OPENS.replace('\n', "\r\n")
    );
    assert_invariants(&crlf);
    assert_eq!(per_line(&crlf), [(4, 1)], "{crlf:?}");
    let whole = format!("\r{BOM}");
    assert_invariants(&whole);
    assert_eq!(per_line(&whole), [(1, 1)]);

    // `\r<BOM>~`, `\r<BOM>@` and `\r <BOM>~` after a header, and a `\r`, a
    // blank, then a token: one error. After a metadata line: two, the
    // grammar's at the key's line and the invalid token's.
    for tail in [
        format!("\r{BOM}~"),
        format!("\r{BOM}@"),
        format!("\r {BOM}~"),
        "\r $~".to_string(),
        "\r $".to_string(),
    ] {
        for header in [
            "2024-01-02 close Assets:A",
            "2024-01-02 balance Assets:A 1.00 USD",
            "2024-01-02 price HOOL 2 USD",
        ] {
            let src = format!("{OPENS}{header}{tail}\n");
            assert_invariants(&src);
            assert_eq!(per_line(&src), [(3, 1)], "{src:?}");
        }
    }
    for tail in [
        format!("\r{BOM}~"),
        format!("\r{BOM}@"),
        format!("\r {BOM}~"),
        "\r$~".to_string(),
        "\r $~".to_string(),
    ] {
        for eol in ["\n", "\r\n"] {
            let src = format!(
                "{}2024-01-02 close Assets:A{eol}  k: \"v\"{tail}{eol}",
                OPENS.replace('\n', eol)
            );
            assert_invariants(&src);
            assert_eq!(per_line(&src), [(4, 2)], "{src:?}");
        }
    }
}

/// A lone capital glued to a stray `\r` is beancount's invalid token, which
/// ends at the `\r` (#2966): `CAPITAL` needs a space, tab or `\n` after it.
/// It counts once, and the `\r` is then a blank. Each count is bean-check
/// 3.2.3's; a `\r` before a token that lexes stays an error of its own and
/// stands for the capital's (`1N\rAssets:B`).
#[test]
fn test_parse_lone_capital_glued_to_a_stray_cr_is_an_invalid_token() {
    let cases: [(String, Vec<(usize, usize)>); 11] = [
        (
            format!("{OPENS}2024-01-02 close Assets:A B\r$\n"),
            vec![(3, 2)],
        ),
        (
            format!("{OPENS}2024-01-02 close Assets:A AB\r$\n"),
            vec![(3, 2)],
        ),
        (
            format!("{OPENS}2024-01-02 close Assets:A B \r$\n"),
            vec![(3, 2)],
        ),
        // Glued to a date, the capital is the transaction's flag, which the
        // header's glued-flag rule reports, after an invalid date too: in
        // beancount it is an invalid token, which the date does not swallow.
        ("2024-02-07B\r\u{0}\u{0}\n".to_string(), vec![(1, 2)]),
        ("2229-2-37B\r\u{0}\u{0}\n".to_string(), vec![(1, 3)]),
        ("2229-2-37B\r\r\n".to_string(), vec![(1, 2)]),
        (format!("{OPENS}2024-01-02 P\r$\n"), vec![(3, 2)]),
        (format!("{OPENS}2024-01-02 * \"x\"\n  P\r$\n"), vec![(4, 2)]),
        (format!("{OPENS}  k: B\r\r\n"), vec![(3, 2)]),
        (
            format!("{OPENS}2024-01-02 close Assets:A 1N\rAssets:B\n"),
            vec![(3, 2)],
        ),
        // A chain: each capital is glued to a `\r` run that is trivia,
        // because the run after the next capital is (`1\rD\r` at its end).
        ("1\rD\r".to_string(), vec![(1, 2)]),
    ];
    for (src, expected) in cases {
        assert_invariants(&src);
        assert_eq!(per_line(&src), expected, "{src:?}");
    }
}

/// A one-letter transaction flag glued to a stray `\r` keeps main's reading
/// (#2966 review): the parser's glued-flag rule reports it, as the flag of a
/// transaction it keeps, so its postings and metadata stay quiet. Turning it
/// into an invalid token dropped the header and reported every indented line
/// under it. Where an invalid token follows the `\r`, the `\r` is a blank,
/// so the line has the flag's error and the token's, as in beancount. Each
/// count is bean-check 3.2.3's.
#[test]
fn test_parse_flag_glued_to_a_stray_cr_keeps_the_transaction() {
    let body = "  k: \"v\"\n  Assets:A  1 USD\n    pk: \"w\"\n  Assets:B  -1 USD\n";
    let postings = "  Assets:A  1 USD\n  Assets:B  -1 USD\n";
    for flag in ["P", "S"] {
        // With metadata right under the header, beancount also reports that
        // line (its header failed); with postings only, the header alone.
        for (tail, header_errors) in [
            ("\r\r\n", 1),
            ("\r\t\n", 1),
            ("\r$\n", 2),
            ("\r $\n", 2),
            ("\r\r$\n", 2),
        ] {
            let src = format!("{OPENS}2024-01-02 {flag}{tail}{body}");
            assert_invariants(&src);
            assert_eq!(per_line(&src), [(3, header_errors), (4, 1)], "{src:?}");
            let src = format!("{OPENS}2024-01-02 {flag}{tail}{postings}");
            assert_invariants(&src);
            assert_eq!(per_line(&src), [(3, header_errors)], "{src:?}");
        }
        let src = format!("{OPENS}2024-01-02 {flag}\r");
        assert_invariants(&src);
        assert_eq!(per_line(&src), [(3, 1)], "{src:?}");
        // A capital after the narration is no flag: it is the invalid token.
        let src = format!("{OPENS}2024-01-02 * \"x\" {flag}\r$\n{body}");
        assert_invariants(&src);
        assert_eq!(per_line(&src), [(3, 2), (4, 1)], "{src:?}");
    }
}

/// An indented date with a one-letter flag glued to a stray `\r` (#2966
/// review). At the top level it is still a transaction, as on main: the
/// indented-directive error and the flag's invalid token, its postings
/// quiet. Under a transaction it is a body line beancount cannot read: the
/// line's error and the invalid token. Each count is bean-check 3.2.3's.
#[test]
fn test_parse_indented_date_with_a_flag_glued_to_a_stray_cr() {
    let postings = "  Assets:A  1 USD\n  Assets:B\n";
    for indent in ["  ", "\t"] {
        for (tail, after) in [
            ("\r\r\n", postings),
            ("\r\t\n", postings),
            ("\r\r\n", ""),
            ("\r", ""),
        ] {
            let src = format!("{OPENS}{indent}2024-01-02 P{tail}{after}");
            assert_invariants(&src);
            assert_eq!(per_line(&src), [(3, 2)], "{src:?}");
        }
        // An invalid token after the `\r`: one more, the `\r` a blank.
        let src = format!("{OPENS}{indent}2024-01-02 P\r$\n{postings}");
        assert_invariants(&src);
        assert_eq!(per_line(&src), [(3, 3)], "{src:?}");
    }
    let crlf = format!(
        "{}  2024-01-02 P\r\r\n{}",
        OPENS.replace('\n', "\r\n"),
        postings.replace('\n', "\r\n")
    );
    assert_invariants(&crlf);
    assert_eq!(per_line(&crlf), [(3, 2)], "{crlf:?}");

    let txn = "2024-01-02 * \"x\"\n  Assets:A  1 USD\n";
    for (tail, expected) in [("\r\r\n", 2), ("\r$\n", 3)] {
        let src = format!("{OPENS}{txn}  2024-01-02 P{tail}  Assets:B  -1 USD\n");
        assert_invariants(&src);
        assert_eq!(per_line(&src), [(5, expected)], "{src:?}");
    }
    let src = format!("{OPENS}{txn}  2024-01-02 P\r");
    assert_invariants(&src);
    assert_eq!(per_line(&src), [(5, 2)], "{src:?}");
}

/// An indented date with a stray `\r` between it and a one-letter capital,
/// after a line that already failed (#2966 round-3 review). beancount is in
/// error recovery there and reports the line's invalid tokens only, so it is
/// no transaction: the capital is a transaction's flag only after spaces or
/// tabs, as the `CURRENCY` flag is. Each count is bean-check 3.2.3's.
#[test]
fn test_parse_indented_date_cr_capital_after_a_failed_line() {
    // (the context, the line its error is on)
    let contexts = [
        ("2024-01-01 open Assets:A $\n", 1),
        ("2024-01-01 open Assets:A\n$\n", 2),
        ("2024-01-01 open Assets:A\n  kk: \"v\" $\n", 2),
        ("2024-01-01 open Assets:A\n  k: \"v\"\n", 2),
        (
            "2024-01-01 open Assets:A\n2024-01-01 close Assets:A\n  k: \"v\"\n",
            3,
        ),
    ];
    for (context, failed) in contexts {
        let line = failed + 1;
        for before in ["\r", "\r ", " \r"] {
            for (tail, expected) in [("\r", 1), ("\r\r\n", 1), ("\rB\r\r\n", 2)] {
                let src = format!("{context}  2024-01-02{before}P{tail}");
                assert_invariants(&src);
                assert_eq!(per_line(&src), [(failed, 1), (line, expected)], "{src:?}");
            }
        }
    }
    let src = "2024-01-01 open Assets:A\n  k: 1\n  2024-01-02\rP\r$\n";
    assert_invariants(src);
    assert_eq!(per_line(src), [(2, 1), (3, 2)], "{src:?}");
}

/// A run of capitals and punctuation that ends in a capital glued to a
/// stray `\r` is ONE invalid token, as beancount's `P@T` and `B,B` are, not
/// a token run and then the last capital's own error (#2966 round-4
/// review). In a flag position the header's glued-flag rule reports the run,
/// as on main. Each count is bean-check 3.2.3's.
#[test]
fn test_parse_capital_run_ending_at_a_stray_cr_is_one_invalid_token() {
    let cases: [(String, Vec<(usize, usize)>); 10] = [
        ("P@T\r\r\n".to_string(), vec![(1, 1)]),
        (
            format!("{OPENS}2024-01-02 commodity B,B\r\r\n"),
            vec![(3, 1)],
        ),
        (format!("{OPENS}2024-01-02 P@T\r"), vec![(3, 1)]),
        (
            format!("{OPENS}2024-01-02 txn \"x\" P@T\r\r\n"),
            vec![(3, 1)],
        ),
        (
            format!("{OPENS}2024-01-02 open Assets:C USD,P@T\r\r\n"),
            vec![(3, 1)],
        ),
        (
            format!("{OPENS}2024-01-02 price HOOL 2 B,B\r\r\n"),
            vec![(3, 1)],
        ),
        (format!("{OPENS}2024-01-02 P,P\r\r\n"), vec![(3, 1)]),
        (format!("{OPENS}  P@P\r\r\r\n"), vec![(3, 1)]),
        (format!("{OPENS}  2024-01-02 P@Z\r\r\n"), vec![(3, 2)]),
        (
            format!("{OPENS}  2024-01-02 P@Z\r\r\n  Assets:A  1 USD\n  Assets:B\n"),
            vec![(3, 2)],
        ),
    ];
    for (src, expected) in cases {
        assert_invariants(&src);
        assert_eq!(per_line(&src), expected, "{src:?}");
    }
}

/// A one-letter capital glued straight to a date that starts its line
/// (indented or not) and to a stray `\r` stays that line's transaction
/// flag, as on main: the transaction keeps its postings quiet (#2966
/// round-4 review). Each count is bean-check 3.2.3's.
#[test]
fn test_parse_capital_glued_to_a_date_and_a_stray_cr_keeps_the_transaction() {
    let postings = "  Assets:A  1 USD\n  Assets:B\n";
    let cases: [(String, Vec<(usize, usize)>); 5] = [
        (format!("{OPENS}2024-01-02P\r\r\n{postings}"), vec![(3, 1)]),
        (format!("{OPENS}2024-01-02P\r$\n{postings}"), vec![(3, 2)]),
        (format!("2024/01/02T\r\r\r\n{postings}"), vec![(1, 1)]),
        (format!("  2024-1-2Z\r\r\r\n{postings}"), vec![(1, 2)]),
        // An invalid date: its error, the glued flag's and the `$`.
        (format!("2229-2-37B\r$\n{postings}"), vec![(1, 3)]),
    ];
    for (src, expected) in cases {
        assert_invariants(&src);
        assert_eq!(per_line(&src), expected, "{src:?}");
    }
}
