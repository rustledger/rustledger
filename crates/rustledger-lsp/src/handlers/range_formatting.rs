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
use super::utils::{LineIndex, PositionEncoding};

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
    encoding: PositionEncoding,
) -> Option<Vec<TextEdit>> {
    let all_edits = format_document(source, parse_result, encoding)?;

    let line_index = LineIndex::new(source, encoding);
    // Both the request range AND the returned edit ranges are in the
    // negotiated encoding; resolve them through the same index.
    // Client-supplied positions that overshoot a line return None;
    // a malformed range short-circuits to a no-op rather than risking
    // misaligned clip boundaries.
    let range_start_byte =
        line_index.position_to_offset(params.range.start.line, params.range.start.character)?;
    let mut range_end_byte =
        line_index.position_to_offset(params.range.end.line, params.range.end.character)?;
    // Reject empty / inverted ranges FIRST, before any snap. A
    // zero-width range (start == end) is a cursor position, not a
    // selection; widening it via the EOL snap below would convert a
    // pure cursor-on-empty-line into a 1-byte selection of '\n',
    // bypassing this guard's purpose.
    if range_end_byte <= range_start_byte {
        return None;
    }
    // Snap range_end past the trailing line terminator when the user
    // selected to the visual end of a line. Editors that click+shift-
    // end produce Position(N, eol_char) which maps to the byte BEFORE
    // the terminator; canonical line-replacement edits end at the byte
    // AFTER the terminator (start of line N+1). Handle both LF and
    // CRLF line endings so the snap fires uniformly on Windows-
    // authored ledgers too.
    let bytes = source.as_bytes();
    if range_end_byte < bytes.len() {
        match bytes[range_end_byte] {
            b'\n' => range_end_byte += 1,
            b'\r' if range_end_byte + 1 < bytes.len() && bytes[range_end_byte + 1] == b'\n' => {
                range_end_byte += 2;
            }
            _ => {}
        }
    }

    let kept: Vec<TextEdit> = all_edits
        .into_iter()
        .filter(|edit| edit_inside_range(&line_index, edit, range_start_byte, range_end_byte))
        .collect();
    if kept.is_empty() { None } else { Some(kept) }
}

/// `true` when the edit's `[start, end]` byte range lies entirely inside
/// `[range_start, range_end]` (inclusive of zero-width edits at the
/// boundaries, since a pure insertion at the selection start is
/// semantically inside the selection).
fn edit_inside_range(
    line_index: &LineIndex,
    edit: &TextEdit,
    range_start: usize,
    range_end: usize,
) -> bool {
    let Some(edit_start) =
        line_index.position_to_offset(edit.range.start.line, edit.range.start.character)
    else {
        return false;
    };
    let Some(edit_end) =
        line_index.position_to_offset(edit.range.end.line, edit.range.end.character)
    else {
        return false;
    };
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
        assert!(handle_range_formatting(&p, source, &result, PositionEncoding::Utf16).is_none());
    }

    #[test]
    fn fixes_misindentation_in_range() {
        let source = "2024-01-15 * \"Coffee\"\n    Assets:Bank  -5.00 USD\n  Expenses:Food\n";
        let result = parse(source);
        let p = params(Range {
            start: Position::new(0, 0),
            end: Position::new(3, 0),
        });
        let edits = handle_range_formatting(&p, source, &result, PositionEncoding::Utf16)
            .expect("expected edits");
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
        let edits = handle_range_formatting(&p, source, &result, PositionEncoding::Utf16)
            .expect("expected edits");
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
        let edits = handle_range_formatting(&p, source, &result, PositionEncoding::Utf16)
            .unwrap_or_default();
        let line_index = LineIndex::new(source, PositionEncoding::Utf16);
        let range_start = line_index
            .position_to_offset(p.range.start.line, p.range.start.character)
            .expect("range start in bounds");
        let range_end = line_index
            .position_to_offset(p.range.end.line, p.range.end.character)
            .expect("range end in bounds");
        for edit in &edits {
            let s = line_index
                .position_to_offset(edit.range.start.line, edit.range.start.character)
                .expect("edit start in bounds");
            let e = line_index
                .position_to_offset(edit.range.end.line, edit.range.end.character)
                .expect("edit end in bounds");
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
        let edits = handle_range_formatting(&p, source, &result, PositionEncoding::Utf16)
            .expect("expected edits");
        assert!(
            !edits.is_empty(),
            "the trailing-newline insertion must be kept"
        );
    }

    /// Regression for the deep-review finding: when the user
    /// click+shift-end-selects a line, the IDE sends
    /// `range.end = Position(N, eol_char)` (byte BEFORE the '\n').
    /// Canonical line-replacement edits end at the byte AFTER the
    /// '\n' (start of line N+1). The snap inside handle_range_formatting
    /// extends range_end past the '\n' so those edits are kept.
    #[test]
    fn end_of_line_selection_keeps_line_replace_edit() {
        let source = "2024-01-15 * \"Coffee\"\n    Assets:Bank  -5.00 USD\n";
        let result = parse(source);
        // Select the misindented posting line in full: range ends at
        // visual EOL (the char BEFORE '\n'). The byte at that position
        // is '\n', so the snap extends range_end by one.
        let line1 = "    Assets:Bank  -5.00 USD";
        let p = params(Range {
            start: Position::new(1, 0),
            end: Position::new(1, line1.encode_utf16().count() as u32),
        });
        let edits = handle_range_formatting(&p, source, &result, PositionEncoding::Utf16)
            .expect("EOL selection should preserve the line-replace edit");
        assert!(!edits.is_empty(), "got {edits:?}");
    }

    /// A pure cursor-position request (start == end) is a no-op, not
    /// an opportunity to inject a pure-insertion edit.
    #[test]
    fn empty_range_is_a_noop() {
        let source = "2024-01-01 open Assets:Bank\n";
        let result = parse(source);
        let p = params(Range {
            start: Position::new(0, 5),
            end: Position::new(0, 5),
        });
        assert!(handle_range_formatting(&p, source, &result, PositionEncoding::Utf16).is_none());
    }

    /// Cursor on an empty line: the EOL snap MUST run after the
    /// empty-range guard, otherwise the cursor's zero-width range is
    /// widened to a 1-byte selection of '\n' and rangeFormatting
    /// silently runs on it.
    #[test]
    fn cursor_on_empty_line_does_not_get_widened() {
        let source = "2024-01-01 open Assets:Bank\n\n2024-01-02 open Assets:Cash\n";
        let result = parse(source);
        // Position(1, 0): start of the empty middle line. The byte at
        // that position is '\n' — the snap would widen it without the
        // guard ordering fix.
        let p = params(Range {
            start: Position::new(1, 0),
            end: Position::new(1, 0),
        });
        assert!(
            handle_range_formatting(&p, source, &result, PositionEncoding::Utf16).is_none(),
            "empty range on '\\n' byte must NOT be widened by the snap"
        );
    }

    /// CRLF EOL snap + format_document's CRLF preservation: Windows-
    /// authored files send Position(N, eol_char) that maps to the
    /// `\r` byte (not `\n`) on a CRLF line. The snap must extend
    /// past both bytes, and format_document must NOT include
    /// `\r`→`` edits in the per-line diff (otherwise every emitted
    /// edit on a CRLF file would be multi-line and get filtered out
    /// by the inside-range guard).
    #[test]
    fn crlf_end_of_line_selection_keeps_line_replace_edit() {
        // CRLF source with a misindented posting on line 1.
        let source = "2024-01-15 * \"Coffee\"\r\n    Assets:Bank  -5.00 USD\r\n";
        let result = parse(source);
        let line1 = "    Assets:Bank  -5.00 USD";
        let p = params(Range {
            start: Position::new(1, 0),
            end: Position::new(1, line1.encode_utf16().count() as u32),
        });
        let edits = handle_range_formatting(&p, source, &result, PositionEncoding::Utf16)
            .expect("CRLF EOL selection should preserve the line-replace edit");
        assert!(!edits.is_empty(), "got {edits:?}");
    }

    /// Whole-document selection on a CRLF file also produces edits
    /// (the canonical reformat still fires; CRLF stays CRLF in the
    /// emitted text per the LSP-side preservation).
    #[test]
    fn crlf_whole_document_selection_produces_edits() {
        let source = "2024-01-15 * \"Coffee\"\r\n    Assets:Bank  -5.00 USD\r\n";
        let result = parse(source);
        let p = params(Range {
            start: Position::new(0, 0),
            end: Position::new(2, 0),
        });
        let edits = handle_range_formatting(&p, source, &result, PositionEncoding::Utf16)
            .expect("whole-document CRLF selection should produce edits");
        assert!(!edits.is_empty(), "got {edits:?}");
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
        assert!(handle_range_formatting(&p, source, &result, PositionEncoding::Utf16).is_none());
    }
}
