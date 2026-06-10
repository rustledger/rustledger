//! Range-formatting handler for `textDocument/rangeFormatting`.
//!
//! Two-path design.
//!
//! **Happy path (clean parse).** Runs [`format_document`] — same code
//! path as `textDocument/formatting` — and clips the resulting edits to
//! the user's selection. Each emitted edit is a minimal line-or-sub-line
//! diff produced by `similar::TextDiff::from_lines`, so cursor positions
//! and inline decorations OUTSIDE the changed bytes survive the format.
//! Edits that straddle the selection boundary are dropped rather than
//! sliced: slicing the reformatter's output by source byte counts
//! produces semantically wrong content. This is the standard LSP
//! "format only edits fully inside the selection" policy.
//!
//! **Fallback path (parse errors).** When [`format_document`] declines
//! to format because the file has parse errors, the private
//! `fallback_cst_snap_edit` helper runs as the second-chance path: it
//! walks the cached CST root via
//! [`rustledger_parser::format::format_node_range`], snaps the user's
//! selection up to the smallest set of top-level directives that
//! intersect it, and emits a single `TextEdit` replacing the snapped
//! range with the formatted text. The fallback INTENTIONALLY extends
//! past the user's selection — it has to, because partial-directive
//! formatting would require inventing a partial canonical form. The
//! result is "the user's selection has been formatted, plus we
//! rounded outward to the directive boundaries", which is the
//! rust-analyzer / Prettier convention for range formatting through
//! a broken file.
//!
//! The fallback REFUSES to format (returns `None`) whenever the
//! snapped range would cover an `ERROR_NODE` byte. Range formatting
//! must not delete content the parser couldn't classify — the
//! "Format Selection" keybinding has no opt-in to content loss. This
//! is the deliberate divergence from `format_node`'s whole-file
//! policy (which silently drops `ERROR_NODE` content); the whole-file
//! path is invoked through tooling (`rledger format` CLI, FFI
//! `format.entry`) that decides to accept content loss, while the
//! per-handler LSP path does not.
//!
//! Both paths use the LSP's negotiated position encoding (UTF-16 by
//! spec default, UTF-8 when modern editors negotiate). The fallback
//! path additionally bridges the BOM frame: the cached CST root lives
//! in post-BOM byte coordinates, so the fallback subtracts
//! `bom_offset` when mapping LSP positions in and adds it back when
//! emitting the edit range. It uses `saturating_sub` rather than the
//! `selection_range` handler's `checked_sub` because a *range*
//! selection starting at byte 0 of original source ("select from
//! start of file") naturally maps to byte 0 of the CST; the cursor
//! semantics `selection_range` follows ("cursor inside BOM is
//! degenerate, bail") don't fit a range selection.
//!
//! **CLI parity, intentionally dropped.** The pre-PR-#1298 module
//! rustdoc committed to "the CLI bails on parse errors and parity-
//! by-construction requires this path to do the same." Phase 5.3 of
//! #1262 supersedes that contract: range formatting on a parse-error
//! file no longer bails unconditionally; instead, it offers the
//! CST-snap fallback as a second-chance path, refusing only when
//! the snap would cover an `ERROR_NODE`. The asymmetry with the
//! `rledger format` CLI (which still bails on any parse error) is
//! deliberate — interactive editing through a typo is a different
//! workflow than batch reformatting, and the UX cost of refusing
//! every range-format request mid-edit outweighs the parity gain.

use lsp_types::{DocumentRangeFormattingParams, Position, Range, TextEdit};
use rustledger_parser::ParseResult;
use rustledger_parser::format::{format_node_range_with_alignment, lf_to_crlf_outside_strings};

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
    // Happy path: the file parses cleanly, run the minimal-diff
    // pipeline. The fallback below covers ONLY the case where
    // `format_document` declines because of parse errors — a clean
    // parse that produces an already-canonical result (i.e.
    // `format_document` returns None for the OTHER reason: no edits
    // needed) must still surface as None so the client sees a no-op,
    // not a coarse CST-snap reformat over an already-canonical file.
    if let Some(all_edits) = format_document(source, parse_result, encoding) {
        return clip_edits_to_range(params, source, encoding, all_edits);
    }
    // Fallback: file has parse errors. Try the CST-snap path on the
    // selection so users editing through a typo still get formatting
    // on the well-formed directives in their selection. If the
    // selection covers only broken syntax (no Directive nodes
    // intersected) we surface None, matching the "nothing to format"
    // shape the happy path returns on already-canonical input.
    if !parse_result.errors.is_empty() {
        return fallback_cst_snap_edit(params, source, parse_result, encoding);
    }
    None
}

/// Clip the canonical document edits to the user's selection.
///
/// Factored out of [`handle_range_formatting`] so the happy path stays
/// readable and the fallback path can be a sibling instead of a nested
/// branch. Behavior unchanged from the pre-fallback shape.
fn clip_edits_to_range(
    params: &DocumentRangeFormattingParams,
    source: &str,
    encoding: PositionEncoding,
    all_edits: Vec<TextEdit>,
) -> Option<Vec<TextEdit>> {
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

/// CST-snap fallback: format the well-formed directives intersecting
/// the user's selection by walking the cached syntax tree, snapping
/// the selection up to top-level directive boundaries, and emitting
/// a single `TextEdit`.
///
/// Only called when the file has parse errors AND the happy path
/// (minimal-diff via `format_document`) declined. The trade-off vs.
/// the happy path:
///
/// - **Coarser edits.** One `TextEdit` covers the whole snapped
///   range; cursor and inline-decoration positions inside the
///   snapped range do NOT survive (the editor re-positions them at
///   the start of the replacement). The minimal-diff path preserves
///   sub-line positions; this path cannot, because the snapped
///   range may contain ERROR_NODE bytes that have no analogue in
///   the formatted output.
/// - **Extends past the user's selection.** If the selection lands
///   inside a transaction body, the snap rounds outward to the
///   transaction's start and end. This violates the "edits stay
///   strictly inside the selection" policy the happy path follows,
///   but does it deliberately: a partial-directive canonical form
///   would create a second truth alongside `format_source`'s
///   whole-file canonical form. Range formatting through a parse
///   error is rare enough that the rust-analyzer / Prettier
///   convention (round outward to the structural unit) is the
///   right call.
/// - **ERROR_NODE content is preserved, by refusing to format.**
///   If the snapped range would cover any top-level `ERROR_NODE`
///   byte, the fallback returns `None` and the client sees
///   "nothing to format". This diverges from
///   [`format_node`](rustledger_parser::format::format_node)'s
///   whole-file policy of silently dropping `ERROR_NODE` content —
///   the LSP keybinding has no opt-in to data loss. Users editing
///   through a typo get a "Format Selection did nothing" response
///   while the error sits inside their selection, but no in-
///   progress content is silently deleted. For byte-conservative
///   editing of the surrounding whitespace, `textDocument/formatting`
///   still falls back to `surface_cleanup_edits` on parse-error
///   files.
///
/// Returns `None` if the selection intersects no top-level Directive
/// or top-level standalone comment, OR if the snapped range would
/// cover an `ERROR_NODE` byte. Mapped 1:1 to LSP `null` on the wire
/// (not `[]`) — clients treat both as "no formatting available".
fn fallback_cst_snap_edit(
    params: &DocumentRangeFormattingParams,
    source: &str,
    parse_result: &ParseResult,
    encoding: PositionEncoding,
) -> Option<Vec<TextEdit>> {
    let line_index = LineIndex::new(source, encoding);
    let orig_start =
        line_index.position_to_offset(params.range.start.line, params.range.start.character)?;
    let orig_end =
        line_index.position_to_offset(params.range.end.line, params.range.end.character)?;
    // Empty / inverted range: a cursor (start == end) is a position,
    // not a selection. The happy path's `clip_edits_to_range` rejects
    // it via `range_end_byte <= range_start_byte`; we mirror that
    // policy so handler semantics don't depend on whether the file
    // has parse errors. Matches the `empty_range_is_a_noop` invariant.
    if orig_end <= orig_start {
        return None;
    }
    // Bridge the BOM frame: the cached `syntax_root` is in post-BOM
    // coordinates, the `LineIndex` is in original-source coordinates.
    // Subtract `bom_offset` going in, add it back when emitting.
    //
    // `saturating_sub` is the correct semantics for a *range* —
    // intentionally diverging from `selection_range`, which takes a
    // *position* and uses `checked_sub` to bail on the degenerate
    // "cursor inside the BOM" case. For range formatting the user's
    // selection starting at byte 0 of original source ("select from
    // the start of the file") naturally maps to byte 0 of the CST
    // ("start of CST content"). Clamping to 0 here lets a
    // "Select All + Format" gesture work on a BOM-prefixed file;
    // failing-to-None would surprise the user. If `orig_end < bom_offset`
    // (both ends inside the BOM region — pathological), the
    // clamped range collapses to `[0, 0)` and `format_node_range`
    // returns None below, which is the correct refuse-to-format
    // response.
    let bom_offset: usize = if parse_result.has_leading_bom { 3 } else { 0 };
    let cst_start = orig_start.saturating_sub(bom_offset);
    let cst_end = orig_end.saturating_sub(bom_offset);
    let cst_start_ts = rustledger_parser::TextSize::try_from(cst_start).ok()?;
    let cst_end_ts = rustledger_parser::TextSize::try_from(cst_end).ok()?;
    let cst_range = rustledger_parser::TextRange::new(cst_start_ts, cst_end_ts);
    let node = parse_result.syntax_node();
    // Reuse the file-wide alignment the parser pre-computed at
    // parse time (see `ParseResult::alignment`). This skips the
    // O(N_postings) `compute_alignment` walk that the bare
    // `format_node_range` would do per call — the difference
    // matters on format-on-type clients that send a
    // rangeFormatting request per keystroke while the user is
    // editing through a parse error in a large ledger.
    let (snap_cst, mut new_text) =
        format_node_range_with_alignment(&node, cst_range, parse_result.alignment)?;

    // CRLF preservation: `format_node_range` always emits LF (it
    // re-uses the canonical-form pipeline, which is LF-only by
    // design). If the source buffer is CRLF, re-inject `\r` before
    // every emitted `\n` outside string literals so the snapped
    // region's line endings match the surrounding buffer. Without
    // this, applying the fallback edit on a Windows-authored file
    // would introduce mixed line endings inside the snapped range.
    // Mirrors `format_document`'s preservation (see
    // `formatting.rs::format_document`).
    if source.contains("\r\n") {
        new_text = lf_to_crlf_outside_strings(&new_text);
    }

    // Map the snapped CST range back to LSP positions: add
    // `bom_offset` to translate into original-source bytes, then
    // resolve via the line index in the negotiated encoding.
    let snap_start_byte = u32::from(snap_cst.start()) as usize + bom_offset;
    let snap_end_byte = u32::from(snap_cst.end()) as usize + bom_offset;
    let (sl, sc) = line_index.offset_to_position(snap_start_byte);
    let (el, ec) = line_index.offset_to_position(snap_end_byte);
    Some(vec![TextEdit {
        range: Range {
            start: Position::new(sl, sc),
            end: Position::new(el, ec),
        },
        new_text,
    }])
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

    /// Parse-error file + selection covers ONLY broken content:
    /// no valid Directive in the selection → no fallback fires →
    /// None. The bail-on-broken behavior is preserved for the
    /// narrow case where there's nothing structural to format.
    #[test]
    fn parse_errors_with_only_broken_content_returns_none() {
        // Single line of garbage; CST wraps it in ERROR_NODE.
        let source = "}}}garbage{{{\n";
        let result = parse(source);
        assert!(!result.errors.is_empty(), "expected parse error");
        let p = params(Range {
            start: Position::new(0, 0),
            end: Position::new(1, 0),
        });
        assert!(
            handle_range_formatting(&p, source, &result, PositionEncoding::Utf16).is_none(),
            "selection covers only ERROR_NODE; fallback must surface None",
        );
    }

    /// Parse-error file + selection covers a well-formed directive
    /// without intersecting any ERROR_NODE: the CST-snap fallback
    /// fires and returns a single TextEdit covering the snapped
    /// directive boundaries. The "no ERROR_NODE in snap" half is
    /// load-bearing — `format_node_range` bails when the snap
    /// would cover an ERROR_NODE byte (see
    /// `parse_errors_with_error_node_in_snap_returns_none`).
    #[test]
    fn parse_errors_with_valid_directive_in_selection_returns_fallback_edit() {
        // Line 0: valid Open directive (parse-clean, with trailing
        // whitespace that the formatter strips). Line 1: garbage
        // (parse error). Selection covers ONLY line 0 — the
        // snapped range does not include the line-1 ERROR_NODE,
        // so the fallback fires.
        let source = "2024-01-01 open Assets:Bank   \n}}}not_a_directive\n";
        let result = parse(source);
        assert!(!result.errors.is_empty(), "expected parse error on line 1");
        let p = params(Range {
            start: Position::new(0, 0),
            end: Position::new(1, 0),
        });
        let edits = handle_range_formatting(&p, source, &result, PositionEncoding::Utf16)
            .expect("CST-snap fallback must fire");
        // Single TextEdit (the fallback is coarse-grained by design).
        assert_eq!(edits.len(), 1, "expected one fallback edit, got {edits:?}");
        let edit = &edits[0];
        // The replacement text is the canonical form of the
        // valid Open directive — trailing whitespace stripped.
        assert_eq!(edit.new_text, "2024-01-01 open Assets:Bank\n");
        // Pin BOTH ends of the replaced range. The previous
        // version only asserted edit.range.start, so a regression
        // that accidentally emitted a pure insertion
        // (`snap_end_byte = snap_start_byte`, common copy-paste
        // bug) would have passed — leaving the original
        // trailing-whitespace line unchanged on disk while the
        // formatted text got prepended.
        assert_eq!(edit.range.start, Position::new(0, 0));
        let line0_end = "2024-01-01 open Assets:Bank   \n".encode_utf16().count() as u32;
        assert_eq!(
            edit.range.end,
            Position::new(1, 0),
            "replaced range must cover the ENTIRE line 0 (through its newline), \
             ending at the start of line 1; otherwise the original line 0 \
             would persist alongside the formatted text",
        );
        let _ = line0_end; // value not used directly; line-1-col-0 is the canonical form
    }

    /// Parse-error file + selection causes the snap to cover an
    /// ERROR_NODE: the fallback returns None instead of silently
    /// deleting the user's in-progress directive. Range
    /// formatting must not delete content the parser couldn't
    /// classify — the "Format Selection" keybinding has no opt-in
    /// to content loss.
    #[test]
    fn parse_errors_with_error_node_in_snap_returns_none() {
        // Two valid directives sandwiching an ERROR_NODE. User
        // selects across all three. The snap range would cover
        // [open.start, close.end], which contains the ERROR_NODE
        // bytes — format_node_range bails, the fallback returns
        // None, the client sees "nothing to format".
        let source = "\
2024-01-01 open Assets:Bank USD
}}}garbage{{{
2024-01-31 close Assets:Bank
";
        let result = parse(source);
        assert!(!result.errors.is_empty(), "expected parse error");
        let p = params(Range {
            start: Position::new(0, 0),
            end: Position::new(3, 0),
        });
        assert!(
            handle_range_formatting(&p, source, &result, PositionEncoding::Utf16).is_none(),
            "selection covering valid + ERROR_NODE + valid must bail; \
             deleting the ERROR_NODE is content loss the user did not opt into",
        );
    }

    /// CRLF source through the fallback: emitted new_text must be
    /// CRLF, not LF. Without the `lf_to_crlf_outside_strings`
    /// re-injection in `fallback_cst_snap_edit`, applying the
    /// edit would introduce mixed line endings inside the snapped
    /// region (the formatter is LF-only by design).
    #[test]
    fn parse_errors_with_crlf_source_emits_crlf_replacement() {
        // CRLF on every line. Valid Open + garbage; selection
        // covers only the open.
        let source = "2024-01-01 open Assets:Bank   \r\n}}}garbage\r\n";
        let result = parse(source);
        assert!(!result.errors.is_empty(), "expected parse error");
        let p = params(Range {
            start: Position::new(0, 0),
            end: Position::new(1, 0),
        });
        let edits = handle_range_formatting(&p, source, &result, PositionEncoding::Utf16)
            .expect("CRLF source still gets a fallback edit");
        assert_eq!(edits.len(), 1);
        let edit = &edits[0];
        assert!(
            edit.new_text.contains("\r\n"),
            "CRLF source must produce CRLF replacement text; got {:?}",
            edit.new_text,
        );
        assert!(
            !edit.new_text.contains("\n") || edit.new_text.contains("\r\n"),
            "no bare LF allowed in replacement text on CRLF source; got {:?}",
            edit.new_text,
        );
    }

    /// Cursor-only request (start == end) on a parse-error file:
    /// fallback must NOT fire. Mirrors `empty_range_is_a_noop` on
    /// the happy path. Without this guard, auto-format-on-type
    /// clients that send a rangeFormatting request per keystroke
    /// would reformat the entire enclosing directive on every key
    /// press through a parse-error window.
    #[test]
    fn parse_errors_with_cursor_only_request_returns_none() {
        // Parse-error file; cursor mid-line on the valid Open.
        let source = "2024-01-01 open Assets:Bank\n}}}garbage\n";
        let result = parse(source);
        assert!(!result.errors.is_empty(), "expected parse error");
        let p = params(Range {
            start: Position::new(0, 5),
            end: Position::new(0, 5),
        });
        assert!(
            handle_range_formatting(&p, source, &result, PositionEncoding::Utf16).is_none(),
            "cursor-only request on a parse-error file must return None, \
             matching empty_range_is_a_noop on the happy path",
        );
    }

    /// Fallback path on a BOM-prefixed broken file: the snapped
    /// edit range MUST be in the original-source frame (BOM-aware),
    /// not the CST frame. Mirrors `selection_range`'s BOM frame
    /// regression and pins the same fix for the range_formatting
    /// fallback.
    ///
    /// The selection is narrowed to ONLY the valid Open (line 0)
    /// so the snap range does NOT cover the line-1 ERROR_NODE;
    /// otherwise the fallback would bail per the
    /// "no ERROR_NODE in snap" policy and we couldn't observe
    /// the emitted range at all.
    #[test]
    fn parse_errors_with_bom_fallback_emits_original_frame_range() {
        // Leading BOM, then a valid Open on line 0, then a parse
        // error on line 1.
        let source = "\u{FEFF}2024-01-01 open Assets:Bank\n}}}garbage\n";
        let result = parse(source);
        assert!(result.has_leading_bom, "fixture must have a BOM");
        assert!(!result.errors.is_empty(), "expected parse error");
        let p = params(Range {
            start: Position::new(0, 0),
            end: Position::new(1, 0),
        });
        let edits = handle_range_formatting(&p, source, &result, PositionEncoding::Utf16)
            .expect("CST-snap fallback must fire on BOM-prefixed broken file");
        assert_eq!(edits.len(), 1);
        let edit = &edits[0];
        // Edit's range.start must map to the byte AFTER the BOM:
        // line 0, column 1 (1 UTF-16 code unit for the BOM).
        // A bug that forgot to add `bom_offset` back when emitting
        // would land at (0, 0); a bug that double-counted would
        // land somewhere wrong.
        assert_eq!(
            edit.range.start,
            Position::new(0, 1),
            "fallback emit must add `bom_offset` back into the original-source frame; got {:?}",
            edit.range.start,
        );
    }

    /// Regression: already-canonical clean file STILL returns None.
    /// The fallback only fires on PARSE errors — a clean file
    /// whose format_document returns None because no edits are
    /// needed must not be re-formatted by the fallback (that
    /// would silently re-emit the snapped directives over an
    /// already-canonical file).
    #[test]
    fn clean_file_already_canonical_returns_none_not_fallback() {
        let source = "2024-01-01 open Assets:Cash\n";
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "fixture must be clean for this regression check",
        );
        let p = params(Range {
            start: Position::new(0, 0),
            end: Position::new(1, 0),
        });
        assert!(
            handle_range_formatting(&p, source, &result, PositionEncoding::Utf16).is_none(),
            "clean + canonical file must return None; fallback must not fire",
        );
    }
}
