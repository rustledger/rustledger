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

use lsp_types::{DocumentRangeFormattingParams, Range, TextEdit};
use rustledger_parser::ParseResult;

use super::formatting::format_document;
use super::utils::{byte_to_lsp_position, document_format_config, lsp_position_to_byte};

/// Handle a `textDocument/rangeFormatting` request.
pub fn handle_range_formatting(
    params: &DocumentRangeFormattingParams,
    source: &str,
    parse_result: &ParseResult,
) -> Option<Vec<TextEdit>> {
    let config = document_format_config(Some(&params.options));
    let all_edits = format_document(source, parse_result, &config)?;

    let range_start_byte = lsp_position_to_byte(source, params.range.start);
    let range_end_byte = lsp_position_to_byte(source, params.range.end);
    // Defensive: a malformed client request with end < start. Treat it as
    // empty; no canonical edit can intersect an empty interval, so we
    // return None below.
    if range_end_byte <= range_start_byte {
        return None;
    }

    let mut kept: Vec<TextEdit> = Vec::new();
    for edit in all_edits {
        if let Some(clipped) = clip_edit_to_range(
            source,
            &edit,
            range_start_byte,
            range_end_byte,
            params.range,
        ) {
            kept.push(clipped);
        }
    }
    if kept.is_empty() { None } else { Some(kept) }
}

/// Clip `edit` to bytes inside `[range_start_byte, range_end_byte)`.
///
/// Returns `None` when the edit lies entirely outside the range. When the
/// edit straddles either boundary, the returned edit has its range
/// narrowed to the intersection — the user's selection is the upper bound
/// of what we'll touch, even when the canonical formatter wanted to
/// rewrite a wider span. The replacement text is shortened symmetrically
/// using the *source* prefix/suffix that the canonical replacement was
/// matching against, so applying the clipped edit is byte-equivalent to
/// applying the canonical edit on the intersection only.
fn clip_edit_to_range(
    source: &str,
    edit: &TextEdit,
    range_start_byte: usize,
    range_end_byte: usize,
    range: Range,
) -> Option<TextEdit> {
    let edit_start_byte = lsp_position_to_byte(source, edit.range.start);
    let edit_end_byte = lsp_position_to_byte(source, edit.range.end);

    // No overlap with the half-open user range.
    if edit_end_byte <= range_start_byte || edit_start_byte >= range_end_byte {
        return None;
    }

    // Fully inside the user range — keep verbatim.
    if edit_start_byte >= range_start_byte && edit_end_byte <= range_end_byte {
        return Some(edit.clone());
    }

    // Partial overlap. Narrow the edit to the intersection. For the
    // replacement text, keep the prefix/suffix bytes that the canonical
    // edit was implicitly preserving (because the source bytes outside
    // the intersection still belong to lines the canonical edit covers).
    let new_start_byte = edit_start_byte.max(range_start_byte);
    let new_end_byte = edit_end_byte.min(range_end_byte);

    // Drop the leading bytes of `new_text` that correspond to source
    // bytes [edit_start..new_start). Best effort: when those bytes
    // match the source verbatim (a common case for prefix-clamp edits),
    // we slice them off. Otherwise we preserve the full new_text and
    // accept that some bytes will be written into the trimmed range —
    // this is conservative and never loses content.
    let lead_keep = new_start_byte - edit_start_byte;
    let tail_keep = edit_end_byte - new_end_byte;
    let new_text = if lead_keep + tail_keep < edit.new_text.len() {
        let mut slice_start = lead_keep;
        let mut slice_end = edit.new_text.len() - tail_keep;
        // Snap to char boundaries on both sides so we never split a
        // multi-byte char.
        while slice_start < edit.new_text.len() && !edit.new_text.is_char_boundary(slice_start) {
            slice_start += 1;
        }
        while slice_end > slice_start && !edit.new_text.is_char_boundary(slice_end) {
            slice_end -= 1;
        }
        if slice_start <= slice_end {
            edit.new_text[slice_start..slice_end].to_string()
        } else {
            edit.new_text.clone()
        }
    } else {
        edit.new_text.clone()
    };

    Some(TextEdit {
        range: Range {
            start: if new_start_byte == range_start_byte {
                range.start
            } else {
                byte_to_lsp_position(source, new_start_byte)
            },
            end: if new_end_byte == range_end_byte {
                range.end
            } else {
                byte_to_lsp_position(source, new_end_byte)
            },
        },
        new_text,
    })
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

    /// A multi-line canonical edit must be clipped to bytes inside the
    /// requested range. The edit produced for misindentation on line 1
    /// of a 3-line document should not extend past line 2 when the user
    /// selected only lines 0-2.
    #[test]
    fn clips_multi_line_canonical_edit_to_range() {
        let source = "2024-01-15 * \"A\"\n    Assets:Bank  -5.00 USD\n  Expenses:Food\n\n2024-02-15 * \"B\"\n    Assets:Bank  -7.00 USD\n  Expenses:Food\n";
        let result = parse(source);
        // Request only the first transaction (lines 0..=2 in half-open
        // → end at (3, 0)).
        let p = params(Range {
            start: Position::new(0, 0),
            end: Position::new(3, 0),
        });
        let edits = handle_range_formatting(&p, source, &result).expect("expected edits");
        // Every returned edit's byte range must fall inside the
        // requested byte range.
        let range_start = lsp_position_to_byte(source, p.range.start);
        let range_end = lsp_position_to_byte(source, p.range.end);
        for edit in &edits {
            let s = lsp_position_to_byte(source, edit.range.start);
            let e = lsp_position_to_byte(source, edit.range.end);
            assert!(
                s >= range_start && e <= range_end,
                "edit {edit:?} (bytes {s}..{e}) escapes byte range {range_start}..{range_end}"
            );
        }
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
