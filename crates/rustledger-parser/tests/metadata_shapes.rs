//! Metadata shapes beancount 3.2.3 rejects (#2813), each checked against
//! bean-check.
//!
//! - An indented line right after a directive that takes no metadata
//!   (`option`, `include`, `plugin`, `pushtag`, `poptag`, `pushmeta`,
//!   `popmeta`) is `syntax error, unexpected INDENT` there, once per indented
//!   block. rledger absorbed `  kk: 1` into the directive and dropped it.
//! - A posting's `filename:` or `lineno:` is `Duplicate posting metadata
//!   field` there, at the transaction's line.
//! - `True` / `true` / `False` / `false` are not booleans (see
//!   `parser_integration_test.rs`), and an account value with an invalid root
//!   is the validator's `E1005` (see `rustledger-validate`).

use rustledger_parser::parse;

/// The 1-based line of each parse error, in order.
fn error_lines(src: &str) -> Vec<usize> {
    let mut lines: Vec<usize> = parse(src)
        .errors
        .iter()
        .map(|e| src[..e.span.start].matches('\n').count() + 1)
        .collect();
    lines.sort_unstable();
    lines
}

#[test]
fn test_parse_reports_an_indented_line_after_a_directive_without_metadata() {
    for (header, closer) in [
        ("option \"title\" \"x\"", ""),
        ("plugin \"p\" \"c\"", ""),
        ("include \"x.beancount\"", ""),
        // Closed, so the pushed value is not also reported (bean-check
        // 3.2.3 crashes on a `pushmeta` number never popped).
        ("pushtag #a", "poptag #a\n"),
        ("pushmeta kk: \"v\"", "popmeta kk:\n"),
        ("poptag #a", ""),
        ("popmeta kk:", ""),
    ] {
        for (body, lines) in [
            ("  jj: 1\n", vec![2]),
            ("  ; c\n", vec![2]),
            ("\t; c\n", vec![2]),
            ("  #tag\n", vec![2]),
            // One error per indented block, as beancount's recovery
            // swallows the rest of it.
            ("  jj: 1\n  ii: 2\n", vec![2]),
            ("  ; c\n  jj: 1\n", vec![2]),
            // A blank (whitespace-only) line is not indented content.
            ("  \n", vec![]),
            ("\n2024-01-01 open Assets:A\n  jj: 1\n", vec![]),
        ] {
            let src = format!("{header}\n{body}{closer}");
            let mut expected = lines.clone();
            // `poptag` / `popmeta` of nothing pushed is its own error, on
            // line 1, as in beancount.
            if header.starts_with("pop") {
                expected.insert(0, 1);
            }
            assert_eq!(error_lines(&src), expected, "{src:?}");
        }
    }
    // The header ends at its line break, not at one inside a string.
    assert_eq!(error_lines("option \"title\" \"a\nb\"\n  kk: 1\n"), [3]);
    // A header that is already a syntax error: beancount's recovery
    // swallows the indented line, so it is not reported again.
    assert_eq!(error_lines("option \"a\" \"b\" \"c\"\n  kk: 1\n"), [1]);
}

#[test]
fn test_parse_reports_posting_filename_and_lineno_metadata() {
    let head = "2024-01-01 open Assets:A\n2024-01-01 open Assets:B\n2024-01-02 *\n";
    for meta in ["filename: \"x\"", "lineno: 3"] {
        let src = format!("{head}  Assets:A  1 USD\n    {meta}\n  Assets:B\n");
        assert_eq!(error_lines(&src), [3], "{src:?}");
    }
    // On the transaction itself, or on any other directive, beancount
    // accepts them.
    for src in [
        format!("{head}  filename: \"x\"\n  Assets:A  1 USD\n  Assets:B\n"),
        "2024-01-01 open Assets:A\n  filename: \"x\"\n  lineno: 3\n".to_string(),
    ] {
        assert_eq!(error_lines(&src), Vec::<usize>::new(), "{src:?}");
    }
}
