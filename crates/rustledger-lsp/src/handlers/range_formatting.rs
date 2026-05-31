//! Range-formatting handler for `textDocument/rangeFormatting`.
//!
//! Always uses the canonical whole-file formatter ([`format_document`]) so
//! the column widths it resolves agree with what `rledger format` writes
//! on disk. Per LSP semantics the request specifies a half-open
//! `[range.start, range.end)` selection; this handler clips the canonical
//! edits to the actual selected byte range so changes never spill outside
//! the user's selection.
//!
//! On parse errors the handler returns `None` rather than degrading to a
//! surface-cleanup pass: the CLI bails on parse errors and parity-by-
//! construction requires this path to do the same. The
//! `textDocument/formatting` (whole-document) path opts into surface
//! cleanup separately; range formatting deliberately does not.

use lsp_types::{DocumentRangeFormattingParams, TextEdit};
use rustledger_parser::ParseResult;

use super::formatting::format_document;
use super::utils::{document_format_config, rope_lsp_position_to_byte};

/// Handle a `textDocument/rangeFormatting` request.
///
/// Returns only those canonical edits that lie entirely inside the user's
/// selection. Edits that straddle either range boundary are dropped — re-
/// flowed bytes outside the selection are NOT a "best-effort clip"
/// rewrite, because the canonical formatter changes column positions and
/// slicing its output by source byte counts produces semantically wrong
/// content. Matching the standard LSP convention for rangeFormatting:
/// "format only edits fully inside the selection."
pub fn handle_range_formatting(
    params: &DocumentRangeFormattingParams,
    source: &str,
    parse_result: &ParseResult,
) -> Option<Vec<TextEdit>> {
    let config = document_format_config(Some(&params.options));
    let all_edits = format_document(source, parse_result, &config)?;

    let rope = ropey::Rope::from_str(source);
    let range_start_byte = rope_lsp_position_to_byte(&rope, params.range.start);
    let range_end_byte = rope_lsp_position_to_byte(&rope, params.range.end);
    // Defensive: a malformed client request with end < start.
    if range_end_byte < range_start_byte {
        return None;
    }

    let kept: Vec<TextEdit> = all_edits
        .into_iter()
        .filter(|edit| edit_inside_range(&rope, edit, range_start_byte, range_end_byte))
        .collect();
    if kept.is_empty() { None } else { Some(kept) }
}

/// `true` when the edit's `[start, end]` byte range lies entirely inside
/// `[range_start, range_end]` (inclusive of zero-width edits at the
/// boundaries, since a pure insertion at the selection start is
/// semantically inside the selection).
fn edit_inside_range(
    rope: &ropey::Rope,
    edit: &TextEdit,
    range_start: usize,
    range_end: usize,
) -> bool {
    let edit_start = rope_lsp_position_to_byte(rope, edit.range.start);
    let edit_end = rope_lsp_position_to_byte(rope, edit.range.end);
    edit_start >= range_start && edit_end <= range_end
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

    #[test]
    fn fixes_misindentation_in_range() {
        let source = "2024-01-15 * \"Coffee\"\n    Assets:Bank  -5.00 USD\n  Expenses:Food\n";
        let result = parse(source);
        let p = params(Range {
            start: Position::new(0, 0),
            end: Position::new(3, 0),
        });
        let edits = handle_range_formatting(&p, source, &result).expect("expected edits");
        assert!(!edits.is_empty());
    }

    /// Edits whose start is at `range.end` (half-open semantics) must be
    /// excluded — the user did not select that boundary line.
    #[test]
    fn half_open_range_excludes_end_line() {
        let source = "2024-01-15 * \"A\"\n    Assets:Bank  -5.00 USD\n  Expenses:Food\n\n2024-02-15 * \"B\"\n    Assets:Bank  -7.00 USD\n  Expenses:Food\n";
        let result = parse(source);
        // Range covers lines 4-7 (the second transaction); line 4 starts
        // at byte position of '2024-02-15...'. Editor sends end on
        // line 7, char 0 (i.e. one past the last selected line).
        let p = params(Range {
            start: Position::new(4, 0),
            end: Position::new(7, 0),
        });
        let edits = handle_range_formatting(&p, source, &result).expect("expected edits");
        for edit in &edits {
            // Inclusive lower bound, exclusive upper bound.
            assert!(
                edit.range.start.line >= 4 && edit.range.end.line <= 7,
                "edit {edit:?} escapes the half-open range [4, 7)"
            );
        }
    }

    /// Returned edits' byte ranges fall entirely inside the user's
    /// selection. Canonical edits straddling the range boundary are
    /// dropped rather than sliced (slicing the reformatter's output by
    /// source byte counts would produce semantically wrong content).
    #[test]
    fn edits_lie_entirely_inside_range() {
        let source = "2024-01-15 * \"A\"\n    Assets:Bank  -5.00 USD\n  Expenses:Food\n\n2024-02-15 * \"B\"\n    Assets:Bank  -7.00 USD\n  Expenses:Food\n";
        let result = parse(source);
        let p = params(Range {
            start: Position::new(0, 0),
            end: Position::new(3, 0),
        });
        let edits = handle_range_formatting(&p, source, &result).unwrap_or_default();
        let rope = ropey::Rope::from_str(source);
        let range_start = rope_lsp_position_to_byte(&rope, p.range.start);
        let range_end = rope_lsp_position_to_byte(&rope, p.range.end);
        for edit in &edits {
            let s = rope_lsp_position_to_byte(&rope, edit.range.start);
            let e = rope_lsp_position_to_byte(&rope, edit.range.end);
            assert!(
                s >= range_start && e <= range_end,
                "edit {edit:?} (bytes {s}..{e}) escapes byte range {range_start}..{range_end}"
            );
        }
    }

    /// Zero-width edits (pure insertions) at the selection boundary are
    /// considered inside the range: position at byte = range_start is
    /// semantically inside `[start, end]`.
    #[test]
    fn zero_width_edit_at_range_start_is_kept() {
        // Source missing trailing newline; format_source adds one →
        // pure insertion edit at the end of the document.
        let source = "2024-01-01 open Assets:Bank";
        let result = parse(source);
        let p = params(Range {
            start: Position::new(0, 0),
            end: Position::new(0, source.encode_utf16().count() as u32),
        });
        let edits = handle_range_formatting(&p, source, &result).expect("expected edits");
        assert!(
            !edits.is_empty(),
            "the trailing-newline insertion must be kept"
        );
    }

    /// Parse-error files: rangeFormatting bails like the CLI (returns
    /// None) instead of degrading to surface cleanup. handle_formatting
    /// remains the only surface-cleanup path.
    #[test]
    fn parse_errors_return_none() {
        let source = "2024-01-01 open Assets:Bank   \n2024-01-02 not_a_directive\n";
        let result = parse(source);
        assert!(!result.errors.is_empty());
        let p = params(Range {
            start: Position::new(0, 0),
            end: Position::new(2, 0),
        });
        assert!(handle_range_formatting(&p, source, &result).is_none());
    }
}
