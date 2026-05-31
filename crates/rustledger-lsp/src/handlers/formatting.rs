//! Document formatting handler for Beancount files.
//!
//! Two independent edit pipelines live here:
//!
//! * [`format_document`] returns *canonical* edits — the result of running
//!   [`rustledger_parser::format_source`] (the same path the `rledger
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
//! Edits use UTF-16 LSP positions (LSP 3.17 default). The per-hunk
//! algorithm in `minimal_diff_edits` emits one edit per maximal run of
//! differing lines (driven by `similar::TextDiff::from_lines`), preserving
//! the editor's cursor and undo granularity across unchanged blocks.

use lsp_types::{DocumentFormattingParams, Position, Range, TextEdit};
use rustledger_core::FormatConfig;
use rustledger_parser::{ParseResult, format_source};

use super::utils::{document_format_config, rope_byte_to_lsp_position};

/// Handle a `textDocument/formatting` request.
///
/// On a clean parse this returns the canonical reformat. On a parse error
/// it falls back to [`surface_cleanup_edits`] so the editor's
/// format-on-save still makes mechanical progress (tabs, trailing
/// whitespace) while the parse is broken.
pub fn handle_formatting(
    params: &DocumentFormattingParams,
    source: &str,
    parse_result: &ParseResult,
) -> Option<Vec<TextEdit>> {
    let config = document_format_config(Some(&params.options));
    if let Some(edits) = format_document(source, parse_result, &config) {
        return Some(edits);
    }
    // Parse error or already canonical. The "already canonical" case
    // doesn't need cleanup either; surface_cleanup_edits is gated on
    // parse_result.errors so it only runs when canonical formatting
    // couldn't.
    if !parse_result.errors.is_empty() {
        return surface_cleanup_edits(source);
    }
    None
}

/// Compute the canonical document-format edits.
///
/// Returns `Some(edits)` when the parse is clean and `format_source`
/// would change the source; `None` when there are parse errors or no
/// canonical change is needed. The caller decides whether to fall back to
/// surface cleanup (the document-format request does, alignment-named
/// commands do not).
pub fn format_document(
    source: &str,
    parse_result: &ParseResult,
    config: &FormatConfig,
) -> Option<Vec<TextEdit>> {
    if !parse_result.errors.is_empty() {
        return None;
    }
    let formatted = format_source(source, parse_result, config);
    if formatted == source {
        return None;
    }
    Some(minimal_diff_edits(source, &formatted))
}

/// Per-line cleanup pass: strip trailing space/tab from every line, and
/// convert the leading run of tabs on each line to two-space indent. CR
/// (`\r`) is preserved so CRLF-encoded files keep their line endings;
/// tabs inside string literals, comments, or anywhere past the leading
/// whitespace are preserved so we never silently mutate content.
///
/// Returns `None` when no line needs changing.
#[must_use]
pub fn surface_cleanup_edits(source: &str) -> Option<Vec<TextEdit>> {
    let mut edits = Vec::new();
    for (line_num, line) in source.split('\n').enumerate() {
        let line_num = line_num as u32;
        let cleaned = clean_line(line);
        if cleaned == line {
            continue;
        }
        let line_utf16_len = line.encode_utf16().count() as u32;
        edits.push(TextEdit {
            range: Range {
                start: Position::new(line_num, 0),
                end: Position::new(line_num, line_utf16_len),
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
    // trimming; pathological "...\r\r" (multiple CRs from buggy input)
    // is normalized to a single trailing CR so the line ending survives
    // round-trip.
    let cr = line.ends_with('\r');
    let body = line.trim_end_matches('\r');

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
    // Strip trailing ASCII space/tab + any stray CRs that ended up
    // inside the body. `trim_end_matches` walks bytes backwards in O(n);
    // truncate yields O(1) drop. Avoids the chars().next_back() loop's
    // O(n²) worst case on long whitespace runs.
    let trimmed_len = out.trim_end_matches([' ', '\t', '\r']).len();
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
fn minimal_diff_edits(source: &str, formatted: &str) -> Vec<TextEdit> {
    use similar::{DiffTag, TextDiff};

    let src_rope = ropey::Rope::from_str(source);
    let fmt_rope = ropey::Rope::from_str(formatted);
    let diff = TextDiff::from_lines(source, formatted);
    let mut edits: Vec<TextEdit> = Vec::new();

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
                edits.push(TextEdit {
                    range: Range {
                        start: rope_byte_to_lsp_position(&src_rope, src_start),
                        end: rope_byte_to_lsp_position(&src_rope, src_end),
                    },
                    new_text: formatted[fmt_start..fmt_end].to_string(),
                });
            }
        }
    }

    edits
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
    use crate::handlers::utils::lsp_position_to_byte;
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
            let start = lsp_position_to_byte(&out, edit.range.start);
            let end = lsp_position_to_byte(&out, edit.range.end);
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
        let edits = handle_formatting(&params(), source, &result).expect("expected edits");
        assert_well_formed(&edits);
        let after = apply(source, &edits);
        assert_eq!(after, "2024-01-01 open Assets:Bank USD\n");
    }

    #[test]
    fn converts_tabs_to_spaces() {
        let source = "2024-01-15 * \"Test\"\n\tAssets:Bank  -5.00 USD\n\tExpenses:Food\n";
        let result = parse(source);
        let edits = handle_formatting(&params(), source, &result).expect("expected edits");
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

        let edits = handle_formatting(&params(), source, &result).expect("expected edits");
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
        let edits = handle_formatting(&params(), source, &result).expect("expected edits");
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
        let edits = handle_formatting(&params(), source, &result).expect("expected edits");
        assert_well_formed(&edits);
        let after = apply(source, &edits);
        let cli = format_source(source, &result, &FormatConfig::default());
        assert_eq!(after, cli);
    }

    #[test]
    fn source_without_trailing_newline_gets_one() {
        let source = "; comment";
        let result = parse(source);
        let edits = handle_formatting(&params(), source, &result).expect("expected edits");
        assert_well_formed(&edits);
        let after = apply(source, &edits);
        assert_eq!(after, "; comment\n");
    }

    #[test]
    fn blank_only_file_is_canonical() {
        let source = "\n\n\n\n";
        let result = parse(source);
        assert_eq!(
            format_source(source, &result, &FormatConfig::default()),
            source
        );
        assert!(handle_formatting(&params(), source, &result).is_none());
    }

    #[test]
    fn non_ascii_payee_roundtrips() {
        let source = "2024-01-15 * \"Café\"\n    Assets:Bank  -1.00 USD\n  Expenses:Food\n";
        let result = parse(source);
        let edits = handle_formatting(&params(), source, &result).expect("expected edits");
        assert_well_formed(&edits);
        let after = apply(source, &edits);
        let cli = format_source(source, &result, &FormatConfig::default());
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
        let edits = handle_formatting(&params(), source, &result).expect("expected edits");
        assert_well_formed(&edits);
        let after = apply(source, &edits);
        let cli = format_source(source, &result, &FormatConfig::default());
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
        let edits = handle_formatting(&params(), source, &result).expect("expected cleanup edits");
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
        assert!(format_document(source, &result, &FormatConfig::default()).is_none());
    }

    // --- surface_cleanup_edits regression tests -----------------------

    /// CRLF line endings must survive surface cleanup verbatim — only
    /// trailing ASCII space/tab is stripped, never '\r'.
    #[test]
    fn surface_cleanup_preserves_crlf() {
        let source = "first\r\nsecond  \r\nthird\t\r\n";
        let edits = surface_cleanup_edits(source).expect("trailing whitespace requires edits");
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
        let edits = surface_cleanup_edits(source).expect("leading tab requires an edit");
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
        assert!(surface_cleanup_edits(source).is_none());
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
        let edits = minimal_diff_edits(source, formatted);
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
        let edits = minimal_diff_edits(source, formatted);
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
        let edits = minimal_diff_edits(source, formatted);
        let after = apply(source, &edits);
        assert_eq!(after, formatted, "multi-insert anchored wrong: {edits:?}");
    }
}
