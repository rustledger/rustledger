//! The LSP and `rledger check` put a syntax error at a multi-line string on
//! the line the string ends, as beancount does (#2994).
//!
//! The parser moves the error's span to the string's last line; every surface
//! maps that one span to a line. This pins two of them to agree with each
//! other and with bean-check 3.2.3 on the issue's rows: the LSP diagnostic's
//! start line (`parse_errors_to_diagnostics`, 0-based) and the line
//! `rledger check` prints (`rustledger_loader::LineIndex`, 1-based, the same
//! lookup `check --format json` and the WASM and FFI error fields use).

use rustledger_lsp::handlers::diagnostics::parse_errors_to_diagnostics;
use rustledger_lsp::handlers::utils::PositionEncoding;

const P: &str = "2024-01-01 open Assets:A\n";
const S: &str = "  2024-02-30 5\n";

#[test]
fn test_parse_errors_to_diagnostics_multi_line_string_line_matches_check() {
    // (source, bean-check 3.2.3's error lines)
    let cases: [(String, &[usize]); 6] = [
        (format!("{P}\"a\nb\"\n{S}"), &[3, 4]),
        (format!("{P}\"a\nb\"\n"), &[3]),
        (format!("{P}\"a\nb\nc\"\n{S}"), &[4, 5]),
        (
            format!("{P}option \"title\" \"a\nb\" \"c\nd\"\n{S}"),
            &[4, 5],
        ),
        // CRLF, and a multi-byte character before the string's last line.
        (
            "2024-01-01 open Assets:A\r\n\"é\r\nb\"\r\n".to_string(),
            &[3],
        ),
        // Too many strings: beancount's builder reports the first line.
        ("2024-01-01 * \"a\nb\" \"c\" \"d\"\n".to_string(), &[1]),
    ];
    for (src, expected) in &cases {
        let result = rustledger_parser::parse(src);
        let index = rustledger_loader::LineIndex::new(src);
        let check: Vec<usize> = result
            .errors
            .iter()
            .map(|e| index.line_col(e.span.start).0)
            .collect();
        for encoding in [PositionEncoding::Utf8, PositionEncoding::Utf16] {
            let lsp: Vec<usize> = parse_errors_to_diagnostics(&result, src, encoding)
                .iter()
                .map(|d| d.range.start.line as usize + 1)
                .collect();
            assert_eq!(lsp, check, "LSP and check disagree on {src:?}");
        }
        assert_eq!(&check[..], *expected, "{src:?}");
    }
}
