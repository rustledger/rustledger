//! Document formatting handler for Beancount files.
//!
//! Two independent edit pipelines live here:
//!
//! * [`format_document`] returns *canonical* edits — the result of running
//!   [`rustledger_parser::format::format_source`] (the same path the `rledger
//!   format` CLI takes) and emitting the byte-level diff. It returns
//!   `None` when the parse has errors or when the document is already
//!   canonical. This is the path range-formatting, align-amounts, and the
//!   `textDocument/formatting` happy path all share.
//!
//! * [`surface_cleanup_edits`] returns *surface* edits — per-line
//!   trailing-whitespace strip (preserving CR, so CRLF files stay CRLF)
//!   and leading-tab → two-space-indent conversion. It is parser-
//!   independent and safe to apply on a broken file. Only
//!   [`handle_formatting`] opts into this fallback so that
//!   `format-on-save` still does *something* useful while the user is
//!   editing through a parse error. Alignment-named commands deliberately
//!   skip it.
//!
//! Edits are emitted in the LSP position encoding negotiated with the
//! client (UTF-16 by spec default; UTF-8 when modern editors negotiate).
//! The per-hunk algorithm in `minimal_diff_edits` emits one edit per
//! maximal run of differing lines (driven by
//! `similar::TextDiff::from_lines`), preserving the editor's cursor
//! and undo granularity across unchanged blocks.

use lsp_types::{DocumentFormattingParams, Position, Range, TextEdit};
use rustledger_parser::ParseResult;
use rustledger_parser::format::{format_source, lf_to_crlf_outside_strings};

use super::utils::{LineIndex, PositionEncoding};

/// Handle a `textDocument/formatting` request.
///
/// On a clean parse this returns the canonical reformat. On a parse error
/// it falls back to [`surface_cleanup_edits`] so the editor's
/// format-on-save still makes mechanical progress (tabs, trailing
/// whitespace) while the parse is broken.
pub fn handle_formatting(
    _params: &DocumentFormattingParams,
    source: &str,
    parse_result: &ParseResult,
    encoding: PositionEncoding,
) -> Option<Vec<TextEdit>> {
    if let Some(edits) = format_document(source, parse_result, encoding) {
        return Some(edits);
    }
    // Parse error or already canonical. The "already canonical" case
    // doesn't need cleanup either; surface_cleanup_edits is gated on
    // parse_result.errors so it only runs when canonical formatting
    // couldn't.
    if !parse_result.errors.is_empty() {
        return surface_cleanup_edits(source, encoding);
    }
    None
}

/// Compute the canonical document-format edits.
///
/// Returns `Some(edits)` when the parse is clean and the canonical
/// `format_source` would change the source; `None` when there are parse
/// errors or no canonical change is needed. The caller decides whether
/// to fall back to surface cleanup (the document-format request does,
/// alignment-named commands do not).
///
/// **CRLF preservation.** `format_source` always emits LF; when the
/// source uses CRLF, we re-inject `\r` before every emitted `\n` so
/// the diff only fires on ACTUAL canonical-form changes (alignment,
/// blank-line collapse, comment normalization). Without this, every
/// line on a CRLF file would diff (because of the `\r` removal),
/// which makes range-formatting on a single-line selection silently
/// no-op — every emitted edit would be multi-line by construction.
///
/// Whole-document formatting still produces LF output if the user
/// requests it explicitly via the CLI / FFI / WASM `format_source`
/// entry; this preservation is local to the LSP edits path.
pub fn format_document(
    source: &str,
    parse_result: &ParseResult,
    encoding: PositionEncoding,
) -> Option<Vec<TextEdit>> {
    if !parse_result.errors.is_empty() {
        return None;
    }
    let mut formatted = format_source(source);
    if source.contains("\r\n") {
        formatted = lf_to_crlf_outside_strings(&formatted);
    }
    if formatted == source {
        return None;
    }
    Some(minimal_diff_edits(source, &formatted, encoding))
}

/// Per-line cleanup pass: strip trailing space/tab from every line, and
/// convert the leading run of tabs on each line to two-space indent. CR
/// (`\r`) is preserved so CRLF-encoded files keep their line endings;
/// tabs inside string literals, comments, or anywhere past the leading
/// whitespace are preserved so we never silently mutate content.
///
/// `encoding` is the negotiated LSP wire encoding; the emitted line-end
/// column is computed accordingly (UTF-8 bytes vs. UTF-16 code units).
///
/// Returns `None` when no line needs changing.
#[must_use]
pub fn surface_cleanup_edits(source: &str, encoding: PositionEncoding) -> Option<Vec<TextEdit>> {
    let mut edits = Vec::new();
    for (line_num, line) in source.split('\n').enumerate() {
        let line_num = line_num as u32;
        let cleaned = clean_line(line);
        if cleaned == line {
            continue;
        }
        let line_end_col: u32 = match encoding {
            PositionEncoding::Utf8 => line.len() as u32,
            PositionEncoding::Utf16 => line.encode_utf16().count() as u32,
        };
        edits.push(TextEdit {
            range: Range {
                start: Position::new(line_num, 0),
                end: Position::new(line_num, line_end_col),
            },
            new_text: cleaned,
        });
    }
    if edits.is_empty() { None } else { Some(edits) }
}

/// Surface-cleanup transformation for one line. Used by
/// [`surface_cleanup_edits`]; isolated so the policy is testable on its
/// own.
fn clean_line(line: &str) -> String {
    // CRLF-encoded files split on '\n' yield segments terminated with
    // '\r'. Detect a single trailing '\r' and re-attach it after
    // trimming. We deliberately strip EXACTLY one CR (via
    // `strip_suffix`), preserving any preceding stray CRs in the body —
    // surface cleanup must be byte-conservative on parse-error files so
    // a paste-in-progress with `...\r\r\n` doesn't get silently
    // normalized while the user is still editing.
    let (body, cr) = match line.strip_suffix('\r') {
        Some(b) => (b, true),
        None => (line, false),
    };

    // Leading tabs → two-space indent. Walk only the leading run of
    // whitespace; once we hit any non-whitespace character we stop, so
    // tabs inside string literals or comments are preserved.
    let mut out = String::with_capacity(body.len());
    let mut leading = true;
    for c in body.chars() {
        if leading {
            if c == '\t' {
                out.push_str("  ");
                continue;
            }
            if c == ' ' {
                out.push(' ');
                continue;
            }
            leading = false;
        }
        out.push(c);
    }
    // Strip ONLY trailing ASCII space/tab — never CR, since the body's
    // own trailing CR (if any) was already lifted off into the `cr`
    // flag and a body-internal stray CR is part of the user's content.
    // `trim_end_matches` + `truncate` is O(n); the previous
    // `chars().next_back()` loop was O(n²) on long whitespace runs.
    let trimmed_len = out.trim_end_matches([' ', '\t']).len();
    out.truncate(trimmed_len);
    if cr {
        out.push('\r');
    }
    out
}

/// Produce a list of byte-correct `TextEdit`s that transform `source`
/// into `formatted` using a line-based diff.
///
/// Uses [`similar::TextDiff::from_lines`] and the structured `DiffOp`
/// API: every operation carries explicit `old_range` (source line index
/// range) and `new_range` (formatted line index range), so each
/// non-Equal op becomes one `TextEdit` with byte ranges resolved via
/// `Rope::line_to_byte`. No state machine, no implicit cursor — the
/// previous review confirmed a state-machine implementation corrupted
/// the buffer on pure insertions.
///
/// Two ropes are constructed up front (one each for source and
/// formatted) and threaded through the helpers, so the per-edit work is
/// O(1) lookups rather than O(N) rope construction per call.
fn minimal_diff_edits(source: &str, formatted: &str, encoding: PositionEncoding) -> Vec<TextEdit> {
    use similar::{DiffTag, TextDiff};

    let src_rope = ropey::Rope::from_str(source);
    let fmt_rope = ropey::Rope::from_str(formatted);
    let diff = TextDiff::from_lines(source, formatted);
    let mut edits: Vec<TextEdit> = Vec::new();
    // Source line index for emitting edits in the negotiated encoding.
    // The rope is kept only for `line_to_byte` lookups during diff
    // resolution; column math goes through LineIndex.
    let src_index = LineIndex::new(source, encoding);

    for op in diff.ops() {
        match op.tag() {
            DiffTag::Equal => {}
            DiffTag::Delete | DiffTag::Insert | DiffTag::Replace => {
                let old = op.old_range();
                let new = op.new_range();
                let src_start = line_idx_to_byte(&src_rope, old.start);
                let src_end = line_idx_to_byte(&src_rope, old.end);
                let fmt_start = line_idx_to_byte(&fmt_rope, new.start);
                let fmt_end = line_idx_to_byte(&fmt_rope, new.end);
                let src_slice = &source[src_start..src_end];
                let fmt_slice = &formatted[fmt_start..fmt_end];

                // Sub-line precision for single-line replacements:
                // strip the longest common UTF-8 prefix and suffix so
                // editor cursor and inline decoration positions outside
                // the actually-changed bytes are preserved. Only fires
                // when the operation is contained in a single source
                // and single formatted line — for multi-line ops the
                // full line-granular edit is correct.
                let (sub_start, sub_end, sub_new) =
                    narrow_single_line_replace(src_slice, fmt_slice);
                // Skip no-op edits (zero-width range + empty new_text).
                // similar's compact pass can emit a Replace whose
                // slices become byte-identical after the
                // common-prefix/suffix strip; pushing that as a
                // TextEdit pollutes clients that count any returned
                // edit as a dirty-document signal.
                if sub_start == sub_end && sub_new.is_empty() {
                    continue;
                }
                let edit_start = src_start + sub_start;
                let edit_end = src_start + sub_end;
                let (sl, sc) = src_index.offset_to_position(edit_start);
                let (el, ec) = src_index.offset_to_position(edit_end);
                edits.push(TextEdit {
                    range: Range {
                        start: Position::new(sl, sc),
                        end: Position::new(el, ec),
                    },
                    new_text: sub_new.to_string(),
                });
            }
        }
    }

    edits
}

/// Strip the longest common UTF-8 prefix and suffix between `src_slice`
/// (a source line region) and `fmt_slice` (the corresponding formatted
/// region), returning the byte offsets into `src_slice` that need
/// replacement and the replacement bytes from `fmt_slice`. Cursor and
/// inline-decoration positions outside the changed bytes survive the
/// format.
///
/// Skips the optimization when either slice spans multiple logical
/// lines (more than one `\n`); a single trailing `\n` (line terminator,
/// always present in `from_lines` output for non-tail ops) is peeled
/// off before computing prefix/suffix so it doesn't fool the
/// single-line check.
fn narrow_single_line_replace<'a>(src_slice: &str, fmt_slice: &'a str) -> (usize, usize, &'a str) {
    // Only narrow Replace ops on a single line. The sub-line
    // optimization needs BOTH slices to share the same terminator
    // shape: either both have a trailing '\n' (the common case
    // for line-replace) or both don't (a tail-of-file edit). Anything
    // else — including pure Insert (src_slice empty) and pure Delete
    // (fmt_slice empty) — falls through to the line-granular emit
    // because peeling an asymmetric terminator would either drop the
    // inserted line's '\n' or invent one on the source side.
    let src_terminated = src_slice.ends_with('\n');
    let fmt_terminated = fmt_slice.ends_with('\n');
    if src_slice.is_empty() || fmt_slice.is_empty() || src_terminated != fmt_terminated {
        return (0, src_slice.len(), fmt_slice);
    }
    let src_body = src_slice.strip_suffix('\n').unwrap_or(src_slice);
    let fmt_body = fmt_slice.strip_suffix('\n').unwrap_or(fmt_slice);
    // Multi-line after peeling: don't narrow.
    if src_body.contains('\n') || fmt_body.contains('\n') {
        return (0, src_slice.len(), fmt_slice);
    }
    let s = src_body.as_bytes();
    let f = fmt_body.as_bytes();
    let mut prefix = 0;
    let max_prefix = s.len().min(f.len());
    while prefix < max_prefix && s[prefix] == f[prefix] {
        prefix += 1;
    }
    while prefix > 0 && (!src_body.is_char_boundary(prefix) || !fmt_body.is_char_boundary(prefix)) {
        prefix -= 1;
    }
    let mut suffix = 0;
    let max_suffix = (s.len() - prefix).min(f.len() - prefix);
    while suffix < max_suffix && s[s.len() - 1 - suffix] == f[f.len() - 1 - suffix] {
        suffix += 1;
    }
    while suffix > 0
        && (!src_body.is_char_boundary(src_body.len() - suffix)
            || !fmt_body.is_char_boundary(fmt_body.len() - suffix))
    {
        suffix -= 1;
    }
    // No actual change after stripping common prefix/suffix? Return the
    // (zero-width, empty) shape — the caller's edit collection should
    // skip it. With Equal ops already filtered, this only fires when
    // similar emitted a Replace that turned out byte-identical (rare
    // but possible with whitespace normalization at the line ends).
    (
        prefix,
        s.len() - suffix,
        &fmt_body[prefix..f.len() - suffix],
    )
}

/// Map a line index (possibly == line_count, meaning "past last line")
/// to a byte offset. Saturates at `rope.len_bytes()`.
fn line_idx_to_byte(rope: &ropey::Rope, line: usize) -> usize {
    if line >= rope.len_lines() {
        rope.len_bytes()
    } else {
        rope.line_to_byte(line)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::handlers::utils::LineIndex;
    use rustledger_parser::parse;

    fn apply(source: &str, edits: &[TextEdit]) -> String {
        let mut sorted: Vec<&TextEdit> = edits.iter().collect();
        sorted.sort_by(|a, b| {
            b.range
                .start
                .line
                .cmp(&a.range.start.line)
                .then(b.range.start.character.cmp(&a.range.start.character))
        });
        let mut out = source.to_string();
        for edit in sorted {
            // Build a fresh LineIndex per edit because the buffer
            // mutates between edits; production handlers apply edits
            // client-side, so this O(edits * source.len()) cost is
            // test-only.
            let idx = LineIndex::new(&out, PositionEncoding::Utf16);
            let start = idx
                .position_to_offset(edit.range.start.line, edit.range.start.character)
                .expect("edit start in bounds");
            let end = idx
                .position_to_offset(edit.range.end.line, edit.range.end.character)
                .expect("edit end in bounds");
            out.replace_range(start..end, &edit.new_text);
        }
        out
    }

    fn params() -> DocumentFormattingParams {
        DocumentFormattingParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            options: Default::default(),
            work_done_progress_params: Default::default(),
        }
    }

    fn assert_well_formed(edits: &[TextEdit]) {
        for edit in edits {
            let s = edit.range.start;
            let e = edit.range.end;
            assert!(
                (e.line, e.character) >= (s.line, s.character),
                "malformed range: end {e:?} < start {s:?} for edit {edit:?}"
            );
        }
    }

    #[test]
    fn removes_trailing_whitespace() {
        let source = "2024-01-01 open Assets:Bank USD   \n";
        let result = parse(source);
        let edits = handle_formatting(&params(), source, &result, PositionEncoding::Utf16)
            .expect("expected edits");
        assert_well_formed(&edits);
        let after = apply(source, &edits);
        assert_eq!(after, "2024-01-01 open Assets:Bank USD\n");
    }

    #[test]
    fn converts_tabs_to_spaces() {
        let source = "2024-01-15 * \"Test\"\n\tAssets:Bank  -5.00 USD\n\tExpenses:Food\n";
        let result = parse(source);
        let edits = handle_formatting(&params(), source, &result, PositionEncoding::Utf16)
            .expect("expected edits");
        assert_well_formed(&edits);
        let after = apply(source, &edits);
        assert!(!after.contains('\t'), "got {after:?}");
    }

    #[test]
    fn preserves_interleaved_metadata_1142() {
        let source = "\
2024-01-15 * \"Test\"
  Assets:Bank  -50.00 USD
    effective_date: 2024-01-20
  Expenses:Food  50.00 USD
    effective_date: 2024-01-21
";
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "parse errors: {:?}",
            result.errors
        );

        let edits = handle_formatting(&params(), source, &result, PositionEncoding::Utf16)
            .expect("expected edits");
        assert_well_formed(&edits);
        let after = apply(source, &edits);

        let after_lines: Vec<&str> = after.lines().collect();
        assert_eq!(
            after_lines.get(2).copied(),
            Some("    effective_date: 2024-01-20"),
        );
        assert_eq!(
            after_lines.get(4).copied(),
            Some("    effective_date: 2024-01-21"),
        );

        let bank_line = after.lines().find(|l| l.contains("Assets:Bank")).unwrap();
        let food_line = after.lines().find(|l| l.contains("Expenses:Food")).unwrap();
        assert_eq!(
            bank_line.find("USD"),
            food_line.find("USD"),
            "amounts must align: {bank_line:?} / {food_line:?}"
        );
    }

    #[test]
    fn preserves_trailing_comment_on_posting() {
        let source = "\
2024-01-15 * \"Coffee\"
    Assets:Bank  -5.00 USD ; my comment
    Expenses:Food
";
        let result = parse(source);
        let edits = handle_formatting(&params(), source, &result, PositionEncoding::Utf16)
            .expect("expected edits");
        assert_well_formed(&edits);
        let after = apply(source, &edits);
        assert!(after.contains("; my comment"), "got {after:?}");
    }

    #[test]
    fn lsp_matches_format_source() {
        let source = "\
2024-01-01 open Assets:Bank
2024-01-15 * \"Coffee\"
    Assets:Bank  -5.00 USD
  Expenses:Food
";
        let result = parse(source);
        let edits = handle_formatting(&params(), source, &result, PositionEncoding::Utf16)
            .expect("expected edits");
        assert_well_formed(&edits);
        let after = apply(source, &edits);
        let cli = format_source(source);
        assert_eq!(after, cli);
    }

    #[test]
    fn source_without_trailing_newline_gets_one() {
        let source = "; comment";
        let result = parse(source);
        let edits = handle_formatting(&params(), source, &result, PositionEncoding::Utf16)
            .expect("expected edits");
        assert_well_formed(&edits);
        let after = apply(source, &edits);
        assert_eq!(after, "; comment\n");
    }

    #[test]
    fn blank_only_file_is_canonical() {
        // Canonical form for a no-directive file is a single newline,
        // not a run of blanks. handle_formatting returns edits to
        // collapse the trailing blanks into one '\n'.
        let source = "\n\n\n\n";
        let result = parse(source);
        assert_eq!(format_source(source), "\n");
        let edits = handle_formatting(&params(), source, &result, PositionEncoding::Utf16)
            .expect("blanks-only file should reflow to a single newline");
        assert_well_formed(&edits);
        let after = apply(source, &edits);
        assert_eq!(after, "\n");
    }

    #[test]
    fn non_ascii_payee_roundtrips() {
        let source = "2024-01-15 * \"Café\"\n    Assets:Bank  -1.00 USD\n  Expenses:Food\n";
        let result = parse(source);
        let edits = handle_formatting(&params(), source, &result, PositionEncoding::Utf16)
            .expect("expected edits");
        assert_well_formed(&edits);
        let after = apply(source, &edits);
        let cli = format_source(source);
        assert_eq!(after, cli);
    }

    #[test]
    fn emits_per_hunk_edits_for_far_apart_changes() {
        let source = "\
2024-01-15 * \"A\"
    Assets:Bank  -5.00 USD
  Expenses:Food

; unchanged separator block
; ----------------------------------
; (these lines must not appear in any edit's range)

2024-02-15 * \"B\"
    Assets:Bank  -7.00 USD
  Expenses:Coffee
";
        let result = parse(source);
        let edits = handle_formatting(&params(), source, &result, PositionEncoding::Utf16)
            .expect("expected edits");
        assert_well_formed(&edits);
        let after = apply(source, &edits);
        let cli = format_source(source);
        assert_eq!(after, cli);
        assert!(edits.len() >= 2, "per-hunk failed, got {edits:#?}");
        for edit in &edits {
            assert!(edit.range.end.line - edit.range.start.line < 8);
        }
    }

    /// Parse-error fallback via handle_formatting still emits surface
    /// cleanup so format-on-save makes mechanical progress.
    #[test]
    fn parse_errors_get_surface_cleanup_via_handle_formatting() {
        let source = "2024-01-01 open Assets:Bank   \n2024-01-02 not_a_directive\n\tAssets:Bank\n";
        let result = parse(source);
        assert!(!result.errors.is_empty());
        let edits = handle_formatting(&params(), source, &result, PositionEncoding::Utf16)
            .expect("expected cleanup edits");
        assert_well_formed(&edits);
        let after = apply(source, &edits);
        assert!(!after.contains('\t'));
        assert!(after.contains("not_a_directive"));
    }

    /// format_document itself is canonical-only: parse errors return None.
    #[test]
    fn format_document_returns_none_on_parse_errors() {
        let source = "2024-01-01 not_a_directive\n";
        let result = parse(source);
        assert!(!result.errors.is_empty());
        assert!(format_document(source, &result, PositionEncoding::Utf16).is_none());
    }

    // --- surface_cleanup_edits regression tests -----------------------

    /// CRLF line endings must survive surface cleanup verbatim — only
    /// trailing ASCII space/tab is stripped, never '\r'.
    #[test]
    fn surface_cleanup_preserves_crlf() {
        let source = "first\r\nsecond  \r\nthird\t\r\n";
        let edits = surface_cleanup_edits(source, PositionEncoding::Utf16)
            .expect("trailing whitespace requires edits");
        let after = apply(source, &edits);
        assert!(after.contains("first\r\n"), "first CRLF gone: {after:?}");
        assert!(after.contains("second\r\n"), "second CRLF gone: {after:?}");
        assert!(after.contains("third\r\n"), "third CRLF gone: {after:?}");
        assert!(!after.contains("  \r\n"));
        assert!(!after.contains("\t\r\n"));
    }

    /// Tabs inside string literals (i.e., NOT in the leading indent) must
    /// not be touched.
    #[test]
    fn surface_cleanup_only_replaces_leading_tabs() {
        let source = "\t2024-01-01 open Assets:Bank \"col1\tcol2\"\n";
        let edits = surface_cleanup_edits(source, PositionEncoding::Utf16)
            .expect("leading tab requires an edit");
        let after = apply(source, &edits);
        assert!(!after.starts_with('\t'));
        assert!(after.starts_with("  "));
        assert!(
            after.contains("col1\tcol2"),
            "tab inside string literal was clobbered: {after:?}"
        );
    }

    #[test]
    fn surface_cleanup_noop_on_canonical_input() {
        let source = "2024-01-01 open Assets:Bank USD\n";
        assert!(surface_cleanup_edits(source, PositionEncoding::Utf16).is_none());
    }

    /// Regression for the deep-review finding: the previous
    /// state-machine implementation of minimal_diff_edits anchored
    /// pure-insert hunks at a stale byte cursor, so a formatter that
    /// inserts a line between two unchanged lines (e.g., a blank
    /// separator, an appended directive, a trailing newline) corrupted
    /// the buffer. This test pins the byte-correctness of pure
    /// insertions via similar's DiffOp byte ranges.
    #[test]
    fn pure_insert_between_unchanged_lines_lands_at_correct_byte() {
        let source = "a\nb\n";
        let formatted = "a\nX\nb\n";
        let edits = minimal_diff_edits(source, formatted, PositionEncoding::Utf16);
        let after = apply(source, &edits);
        assert_eq!(
            after, formatted,
            "pure insert anchored at wrong byte: {edits:?}"
        );
    }

    #[test]
    fn pure_insert_at_eof_lands_at_correct_byte() {
        let source = "a\nb\n";
        let formatted = "a\nb\nc\n";
        let edits = minimal_diff_edits(source, formatted, PositionEncoding::Utf16);
        let after = apply(source, &edits);
        assert_eq!(
            after, formatted,
            "EOF insert anchored at wrong byte: {edits:?}"
        );
    }

    #[test]
    fn two_separate_inserts_each_at_correct_byte() {
        let source = "a\nb\nc\n";
        let formatted = "a\nX\nb\nY\nc\n";
        let edits = minimal_diff_edits(source, formatted, PositionEncoding::Utf16);
        let after = apply(source, &edits);
        assert_eq!(after, formatted, "multi-insert anchored wrong: {edits:?}");
    }

    /// Sub-line precision: when a single byte changes inside one line,
    /// the emitted edit is narrowed to that byte range only — cursors,
    /// inline diagnostics, and CodeLens positions outside the changed
    /// bytes survive the format.
    #[test]
    fn sub_line_precision_for_single_byte_change() {
        let source = "  Assets:Bank  -5.00 USD\n";
        let formatted = "  Assets:Bank  -6.00 USD\n";
        let edits = minimal_diff_edits(source, formatted, PositionEncoding::Utf16);
        assert_eq!(edits.len(), 1, "{edits:?}");
        let edit = &edits[0];
        assert_eq!(
            edit.new_text, "6",
            "should narrow to the changed digit, got new_text={:?}",
            edit.new_text
        );
        // The replaced range must be exactly the one byte at "5".
        assert_eq!(edit.range.start.line, 0);
        assert_eq!(edit.range.end.line, 0);
        assert_eq!(edit.range.end.character - edit.range.start.character, 1);
        let after = apply(source, &edits);
        assert_eq!(after, formatted);
    }

    /// Regression for the deep-review finding (#15): pin similar's
    /// granularity assumption. A line replacement should produce ONE
    /// edit, not Delete+Insert. If a future similar bump changes the
    /// compact pass, this test surfaces the regression so the consumer
    /// can adapt rather than silently double the per-hunk edit count.
    #[test]
    fn similar_compact_pass_keeps_replacements_atomic() {
        // Source and formatted differ only on one line out of three;
        // similar's compact pass should emit one DiffOp::Replace, not
        // a Delete+Insert pair.
        use similar::{DiffTag, TextDiff};
        let source = "alpha\nbeta\ngamma\n";
        let formatted = "alpha\nBETA\ngamma\n";
        let diff = TextDiff::from_lines(source, formatted);
        let non_equal: Vec<_> = diff
            .ops()
            .iter()
            .filter(|op| op.tag() != DiffTag::Equal)
            .collect();
        assert_eq!(
            non_equal.len(),
            1,
            "expected exactly one non-Equal op; similar's compact pass changed semantics: {non_equal:?}"
        );
        assert_eq!(non_equal[0].tag(), DiffTag::Replace);
    }
}
