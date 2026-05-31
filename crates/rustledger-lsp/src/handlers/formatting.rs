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

use super::utils::{byte_to_lsp_position, document_format_config};

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
    // '\r'; lift it off so the trim-trailing-whitespace logic doesn't
    // either treat '\r' as a wall (leaving spaces in front of it) or
    // strip it (silently converting CRLF→LF).
    let (body, cr) = match line.strip_suffix('\r') {
        Some(b) => (b, true),
        None => (line, false),
    };

    // Leading tabs → two-space indent. Walk only the leading run of
    // whitespace; once we hit any non-whitespace character we stop, so
    // tabs inside string literals or comments are preserved.
    let mut out = String::with_capacity(line.len());
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
    // Strip trailing ASCII space/tab from the body.
    while let Some(last) = out.chars().next_back() {
        if last == ' ' || last == '\t' {
            out.pop();
        } else {
            break;
        }
    }
    if cr {
        out.push('\r');
    }
    out
}

/// Produce a list of byte-correct `TextEdit`s that transform `source`
/// into `formatted` using a line-based diff.
///
/// Uses [`similar::TextDiff`] (Myers diff over lines) to compute the
/// minimal set of replacements. Consecutive non-equal operations are
/// merged into a single hunk so the editor receives one `TextEdit` per
/// contiguous changed region; unchanged regions between hunks are left
/// alone, preserving the editor's cursor and undo granularity. Line
/// endings (the `\n` between segments and the file's terminating
/// newline) are part of the source bytes the diff sees, so CRLF and
/// no-trailing-newline files round-trip correctly without bespoke
/// boundary handling.
fn minimal_diff_edits(source: &str, formatted: &str) -> Vec<TextEdit> {
    use similar::{ChangeTag, TextDiff};

    let diff = TextDiff::from_lines(source, formatted);
    let mut edits: Vec<TextEdit> = Vec::new();

    // `iter_all_changes()` walks line-by-line with byte offsets into
    // both strings. We group consecutive non-Equal changes into one
    // edit per hunk.
    let mut hunk_src_start: Option<usize> = None;
    let mut hunk_src_end: usize = 0;
    let mut hunk_new = String::new();

    let flush =
        |source: &str, edits: &mut Vec<TextEdit>, start: usize, end: usize, new_text: &str| {
            edits.push(TextEdit {
                range: Range {
                    start: byte_to_lsp_position(source, start),
                    end: byte_to_lsp_position(source, end),
                },
                new_text: new_text.to_string(),
            });
        };

    for change in diff.iter_all_changes() {
        match change.tag() {
            ChangeTag::Equal => {
                if let Some(start) = hunk_src_start.take() {
                    flush(source, &mut edits, start, hunk_src_end, &hunk_new);
                    hunk_new.clear();
                }
            }
            ChangeTag::Delete => {
                let old_idx = change.old_index().expect("Delete has old_index");
                // similar reports line indices, not byte offsets; resolve.
                let (start, end) = line_byte_range(source, old_idx);
                if hunk_src_start.is_none() {
                    hunk_src_start = Some(start);
                }
                hunk_src_end = end;
            }
            ChangeTag::Insert => {
                if hunk_src_start.is_none() {
                    // Pure insertion at the *current* source position
                    // (between the previous Equal block's last line and
                    // the next one). Anchor to the start of the line
                    // following the last Equal we saw. similar exposes
                    // this via change.old_index() == None and the value
                    // we should anchor at is the start of the line at
                    // new_index... which doesn't map to source. Easier:
                    // anchor to the previous hunk_src_end (default 0 if
                    // we haven't opened a hunk yet — fine, that means
                    // insertion at the start of the file).
                    let anchor = hunk_src_end;
                    hunk_src_start = Some(anchor);
                }
                hunk_new.push_str(change.value());
            }
        }
    }
    if let Some(start) = hunk_src_start {
        flush(source, &mut edits, start, hunk_src_end, &hunk_new);
    }

    edits
}

/// Return the `[start, end)` byte range of source line `line_idx` (0-indexed),
/// including its terminating '\n' when present.
fn line_byte_range(source: &str, line_idx: usize) -> (usize, usize) {
    let rope = ropey::Rope::from_str(source);
    let line_count = rope.len_lines();
    if line_idx >= line_count {
        return (rope.len_bytes(), rope.len_bytes());
    }
    let start = rope.line_to_byte(line_idx);
    let end = if line_idx + 1 < line_count {
        rope.line_to_byte(line_idx + 1)
    } else {
        rope.len_bytes()
    };
    (start, end)
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
}
