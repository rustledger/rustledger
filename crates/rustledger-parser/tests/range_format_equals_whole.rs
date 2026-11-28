//! Range formatting is whole-file formatting restricted to the range (ADR
//! 0009, promise 5): it runs the same certified driver, with every item
//! outside the range copied as written. Formatting a clean ledger one
//! directive (or top-level comment) at a time, each through a range edit the
//! way the LSP applies it, ends where formatting the whole file does.

use std::fs;
use std::path::PathBuf;

use rustledger_parser::format::{GroupingStyle, format_parsed_range, format_source};
use rustledger_parser::{SyntaxKind, TextRange, parse};

/// The ranges (in the tree's frame) of the top-level children range
/// formatting snaps to: directives and comments.
fn formattable(src: &str) -> Vec<TextRange> {
    let parsed = parse(src);
    parsed
        .syntax_node()
        .children_with_tokens()
        .filter(|el| match el {
            rustledger_parser::NodeOrToken::Node(n) => n.kind() != SyntaxKind::ERROR_NODE,
            rustledger_parser::NodeOrToken::Token(t) => matches!(
                t.kind(),
                SyntaxKind::COMMENT
                    | SyntaxKind::PERCENT_COMMENT
                    | SyntaxKind::SHEBANG
                    | SyntaxKind::EMACS_DIRECTIVE
            ),
        })
        .map(|el| el.text_range())
        .collect()
}

/// `src` formatted one child at a time, each by a cursor-only range edit at
/// the child's start, applied as an editor applies it.
fn format_by_ranges(src: &str) -> String {
    let mut text = src.to_string();
    let mut k = 0;
    loop {
        let children = formattable(&text);
        let Some(child) = children.get(k) else {
            return text;
        };
        let parsed = parse(&text);
        let bom = if parsed.has_leading_bom { 3 } else { 0 };
        let cursor = TextRange::empty(child.start());
        if let Some((snap, replacement)) =
            format_parsed_range(&parsed, cursor, GroupingStyle::default())
        {
            let start = usize::from(snap.start()) + bom;
            let end = usize::from(snap.end()) + bom;
            text.replace_range(start..end, &replacement);
        }
        k += 1;
    }
}

fn check(label: &str, src: &str) {
    if !parse(src).errors.is_empty() {
        return;
    }
    // The leading BOM is outside every range (the parser strips it before the
    // tree starts), so only whole-file formatting drops it.
    let by_ranges = format_by_ranges(src);
    assert_eq!(
        by_ranges.strip_prefix('\u{FEFF}').unwrap_or(&by_ranges),
        format_source(src),
        "{label}: formatting one range at a time differs from the whole file"
    );
}

#[test]
fn test_range_formatting_equals_whole_file_on_format_compat_cases() {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/format_compat/cases");
    let mut checked = 0;
    for case in fs::read_dir(&dir).expect("format_compat cases").flatten() {
        let input = case.path().join("input.bean");
        let Ok(src) = fs::read_to_string(&input) else {
            continue;
        };
        check(&input.display().to_string(), &src);
        checked += 1;
    }
    assert!(checked >= 30, "only {checked} cases checked");
}

#[test]
fn test_range_formatting_equals_whole_file_on_edge_shapes() {
    for (label, src) in [
        (
            "blank lines and comments",
            "; head\n\n2024-01-01 open   Assets:A\n\n\n; between\n2024-01-02 open   Assets:B\n; tail\n",
        ),
        (
            "aligned postings",
            "2024-01-01 *   \"x\"\n  Assets:A    1.50 USD\n  Expenses:Long:Account  -1.50 USD\n2024-01-02 * \"y\"\n  Assets:A  2 USD\n  Assets:B\n",
        ),
        ("no final newline", "2024-01-01 open   Assets:A"),
        (
            "CRLF",
            "2024-01-01 open   Assets:A\r\n2024-01-02 open   Assets:B\r\n",
        ),
        ("BOM", "\u{FEFF}2024-01-01 open   Assets:A\n"),
    ] {
        check(label, src);
    }
}

#[path = "format_roundtrip_common/ledger_gen.rs"]
mod ledger_gen;

/// The same on generated realistic ledgers (with comments, metadata and
/// aligned postings). On a CRLF ledger a blank line outside every directive
/// and comment (before the first one, say) is in no range, so range edits
/// leave its `\r\n` where the whole-file formatter writes `\n`; there the
/// range edits must still be a step toward the whole-file form.
#[test]
fn test_range_formatting_equals_whole_file_on_generated_ledgers() {
    ledger_gen::run_property(64, ledger_gen::ledger, |src| {
        let by_ranges = format_by_ranges(&src);
        let by_ranges = by_ranges.strip_prefix('\u{FEFF}').unwrap_or(&by_ranges);
        if src.contains('\r') {
            proptest::prop_assert_eq!(format_source(by_ranges), format_source(&src), "{:?}", src);
        } else {
            proptest::prop_assert_eq!(by_ranges, format_source(&src), "{:?}", src);
        }
        Ok(())
    });
}
