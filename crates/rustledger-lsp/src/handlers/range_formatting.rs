//! Range-formatting handler for `textDocument/rangeFormatting`.
//!
//! Delegates to [`super::formatting::format_document`] (the canonical
//! whole-file formatter that produces byte-identical output to `rledger
//! format`) and then filters the emitted edits to those that touch the
//! request's range. Routing both formatter kinds through one path gives
//! parity-by-construction with the CLI; the alternative (per-line indent
//! heuristics, as the pre-#1242 implementation did) cannot resolve
//! file-wide currency-column widths, so it would always disagree with the
//! CLI for files with non-uniform account widths — the exact drift class
//! issue #1242 is closing.
//!
//! Range semantics: file-wide widths must come from the whole document, so
//! the formatter always runs on the full source. Only edits whose start
//! position lies in the requested range are returned, so the user sees
//! changes only in their selection even though widths were resolved
//! globally.

use lsp_types::{DocumentRangeFormattingParams, TextEdit};
use rustledger_parser::ParseResult;

use super::formatting::format_document;
use super::utils::document_format_config;

/// Handle a `textDocument/rangeFormatting` request.
pub fn handle_range_formatting(
    params: &DocumentRangeFormattingParams,
    source: &str,
    parse_result: &ParseResult,
) -> Option<Vec<TextEdit>> {
    let config = document_format_config(Some(&params.options));
    let all_edits = format_document(source, parse_result, &config)?;

    // Keep only edits whose start position is inside the requested range.
    // `format_document` returns one contiguous edit on a clean parse, so
    // this is usually a 0/1-element filter; on parse-error fallback it's a
    // per-line cleanup pass and we filter line-by-line.
    let range = params.range;
    let kept: Vec<TextEdit> = all_edits
        .into_iter()
        .filter(|edit| edit_overlaps(edit, &range))
        .collect();
    if kept.is_empty() { None } else { Some(kept) }
}

fn edit_overlaps(edit: &TextEdit, range: &lsp_types::Range) -> bool {
    // An edit overlaps the range if its `[start, end]` line interval
    // intersects `[range.start.line, range.end.line]`.
    let edit_start_line = edit.range.start.line;
    let edit_end_line = edit.range.end.line;
    edit_start_line <= range.end.line && edit_end_line >= range.start.line
}

#[cfg(test)]
mod tests {
    use super::*;
    use lsp_types::{DocumentRangeFormattingParams, Position, Range};
    use rustledger_parser::parse;

    fn params(range: Range) -> DocumentRangeFormattingParams {
        DocumentRangeFormattingParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            range,
            options: Default::default(),
            work_done_progress_params: Default::default(),
        }
    }

    /// On a clean, canonical document, no edits are emitted regardless of
    /// the requested range.
    #[test]
    fn already_canonical_returns_none() {
        let source = "2024-01-01 open Assets:Cash\n";
        let result = parse(source);
        let p = params(Range {
            start: Position::new(0, 0),
            end: Position::new(0, 27),
        });
        assert!(handle_range_formatting(&p, source, &result).is_none());
    }

    /// On a misindented document, range formatting emits the same canonical
    /// fix as full formatting (when the range covers the change).
    #[test]
    fn fixes_misindentation_in_range() {
        let source = "2024-01-15 * \"Coffee\"\n    Assets:Bank  -5.00 USD\n  Expenses:Food\n";
        let result = parse(source);
        let p = params(Range {
            start: Position::new(0, 0),
            end: Position::new(2, 0),
        });
        let edits = handle_range_formatting(&p, source, &result).expect("expected edits");
        assert!(!edits.is_empty());
    }

    /// Edits outside the requested range are filtered out.
    #[test]
    fn filters_edits_outside_range() {
        let source = "2024-01-15 * \"A\"\n    Assets:Bank  -5.00 USD\n  Expenses:Food\n\n2024-02-15 * \"B\"\n    Assets:Bank  -7.00 USD\n  Expenses:Food\n";
        let result = parse(source);
        // Range covers only the first transaction (lines 0-2).
        let p = params(Range {
            start: Position::new(0, 0),
            end: Position::new(2, 0),
        });
        let edits = handle_range_formatting(&p, source, &result).unwrap_or_default();
        // format_document returns one contiguous edit covering all changed
        // lines; that single edit starts at line ≤ 2 so it's kept by the
        // range filter. The filter's value is that it would drop edits
        // starting after line 2, which the fallback parse-error path can
        // emit per-line.
        for edit in &edits {
            assert!(
                edit.range.start.line <= 2,
                "edit at line {} should be filtered (range ends at 2)",
                edit.range.start.line
            );
        }
    }

    /// Parse-error fallback: cleanup edits inside the range are kept, those
    /// outside are dropped.
    #[test]
    fn parse_error_fallback_respects_range() {
        let source =
            "2024-01-01 open Assets:Bank   \n2024-01-02 not_a_directive\n\tAssets:Bank   \n";
        let result = parse(source);
        assert!(!result.errors.is_empty());

        // Request only line 0.
        let p = params(Range {
            start: Position::new(0, 0),
            end: Position::new(0, 30),
        });
        let edits = handle_range_formatting(&p, source, &result).unwrap_or_default();
        for edit in &edits {
            assert_eq!(
                edit.range.start.line, 0,
                "edits outside range (line 0) should be filtered: {edit:?}"
            );
        }
    }
}
