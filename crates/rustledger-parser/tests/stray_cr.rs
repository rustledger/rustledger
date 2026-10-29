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
//! Every expected outcome below was checked against `bean-check` 3.2.3.

use rustledger_core::Directive;
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
                let keys: Vec<&str> = o.meta.keys().map(String::as_str).collect();
                format!("{} open {} {keys:?}", o.date, o.account)
            }
            Directive::Transaction(t) => {
                let postings: Vec<String> = t
                    .postings
                    .iter()
                    .map(|p| {
                        let keys: Vec<&str> = p.meta.keys().map(String::as_str).collect();
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
