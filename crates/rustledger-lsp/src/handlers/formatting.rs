//! Document formatting handler for Beancount files.
//!
//! On a clean parse the handler delegates to [`rustledger_parser::format_source`],
//! the same whole-file formatter the `rledger format` CLI uses, so editor saves
//! and CLI output cannot drift. On a parse failure the formatter falls back to
//! a per-line cleanup pass that strips trailing whitespace and converts hard
//! tabs to two-space indent — operations that are safe to apply even when the
//! parser couldn't recognize the surrounding directive structure.
//!
//! Diffs against the original document are emitted as a single byte-correct
//! contiguous `TextEdit`. LSP positions use UTF-16 code units per the LSP 3.17
//! default; non-ASCII content is handled correctly.

use lsp_types::{DocumentFormattingParams, Position, Range, TextEdit};
use rustledger_core::FormatConfig;
use rustledger_parser::{ParseResult, format_source};

use super::utils::document_format_config;

/// Handle a `textDocument/formatting` request.
///
/// Thin LSP-shaped wrapper around [`format_document`].
pub fn handle_formatting(
    params: &DocumentFormattingParams,
    source: &str,
    parse_result: &ParseResult,
) -> Option<Vec<TextEdit>> {
    let config = document_format_config(Some(&params.options));
    format_document(source, parse_result, &config)
}

/// Compute the document-format edits for a parsed source with a resolved
/// [`FormatConfig`].
///
/// On a clean parse the function returns one minimal contiguous `TextEdit`
/// transforming `source` into [`format_source`]'s canonical output, or `None`
/// when the source already matches that output. On a parse failure it returns
/// the result of a per-line cleanup pass (trailing whitespace + hard-tab
/// removal), or `None` if there's nothing to clean.
pub fn format_document(
    source: &str,
    parse_result: &ParseResult,
    config: &FormatConfig,
) -> Option<Vec<TextEdit>> {
    if !parse_result.errors.is_empty() {
        // Parse-error fallback: tab→spaces and trailing-whitespace cleanup.
        // format_source would drop the unparsable bytes, so we don't call
        // it; per-line edits are mechanical and surface-only.
        return fallback_cleanup_edits(source);
    }

    let formatted = format_source(source, parse_result, config);
    if formatted == source {
        return None;
    }

    Some(minimal_diff_edits(source, &formatted))
}

/// Produce a list of byte-correct `TextEdit`s that transform `source` into
/// `formatted`.
///
/// Strategy: strip the longest common byte prefix and suffix (clamped to
/// char boundaries so multi-byte UTF-8 is never split) to get a "middle"
/// region that actually changed. When the middle has the same number of
/// lines on both sides — the common case for indent/whitespace/alignment
/// changes — emit one edit per maximal run of differing lines, preserving
/// the editor's cursor and undo granularity around unchanged regions. When
/// line counts differ (a structural change like a removed blank line),
/// fall back to one contiguous edit covering the whole middle.
///
/// LSP positions are computed in UTF-16 code units (the LSP 3.17 default)
/// so non-ASCII content is handled correctly.
fn minimal_diff_edits(source: &str, formatted: &str) -> Vec<TextEdit> {
    let (start_byte, end_byte, new_text) = byte_diff(source, formatted);

    // Try per-hunk edits when the changed region has the same number of
    // lines on both sides. This is the common case (re-aligning amounts,
    // normalizing indentation) and gives the editor per-hunk undo.
    let src_mid = &source[start_byte..end_byte];
    let fmt_mid = new_text;
    let src_lines: Vec<&str> = src_mid.split('\n').collect();
    let fmt_lines: Vec<&str> = fmt_mid.split('\n').collect();

    if src_lines.len() == fmt_lines.len() && src_lines.len() > 1 {
        let mut edits = Vec::new();
        let mut byte_cursor = start_byte;
        let mut i = 0;
        while i < src_lines.len() {
            // Byte length of source segment i, including the '\n' that
            // separates it from segment i+1. The final segment has no
            // separator because the middle ends there.
            let src_seg_bytes = src_lines[i].len() + usize::from(i + 1 < src_lines.len());

            if src_lines[i] == fmt_lines[i] {
                byte_cursor += src_seg_bytes;
                i += 1;
                continue;
            }

            // Open a hunk and extend it while lines keep differing.
            let hunk_start_byte = byte_cursor;
            let hunk_first = i;
            while i < src_lines.len() && src_lines[i] != fmt_lines[i] {
                let seg = src_lines[i].len() + usize::from(i + 1 < src_lines.len());
                byte_cursor += seg;
                i += 1;
            }
            let hunk_end_byte = byte_cursor;
            let hunk_end_exclusive = i;

            // new_text: join the matching fmt segments with '\n'. Append
            // the inter-segment '\n' only when the source hunk ended at an
            // internal boundary (some unchanged line follows). Hunks that
            // reach end-of-middle had no trailing '\n' in the source, so
            // emitting one would extend the edit one byte past the source
            // range we're replacing.
            let mut new_text = fmt_lines[hunk_first..hunk_end_exclusive].join("\n");
            if hunk_end_exclusive < src_lines.len() {
                new_text.push('\n');
            }

            edits.push(TextEdit {
                range: Range {
                    start: byte_to_lsp_position(source, hunk_start_byte),
                    end: byte_to_lsp_position(source, hunk_end_byte),
                },
                new_text,
            });
        }
        return edits;
    }

    // Fallback: one contiguous edit covering the whole middle.
    let start = byte_to_lsp_position(source, start_byte);
    let end = byte_to_lsp_position(source, end_byte);
    vec![TextEdit {
        range: Range { start, end },
        new_text: new_text.to_string(),
    }]
}

/// Find `(start, end, formatted[start..formatted.len() - suffix])` — the
/// byte-range in `source` that needs replacement, and the replacement text.
fn byte_diff<'a>(source: &str, formatted: &'a str) -> (usize, usize, &'a str) {
    let s = source.as_bytes();
    let f = formatted.as_bytes();

    let mut prefix = 0;
    let max_prefix = s.len().min(f.len());
    while prefix < max_prefix && s[prefix] == f[prefix] {
        prefix += 1;
    }
    // Back off to a UTF-8 char boundary that's valid in *both* strings.
    while prefix > 0 && (!source.is_char_boundary(prefix) || !formatted.is_char_boundary(prefix)) {
        prefix -= 1;
    }

    let mut suffix = 0;
    let max_suffix = (s.len() - prefix).min(f.len() - prefix);
    while suffix < max_suffix && s[s.len() - 1 - suffix] == f[f.len() - 1 - suffix] {
        suffix += 1;
    }
    while suffix > 0
        && (!source.is_char_boundary(source.len() - suffix)
            || !formatted.is_char_boundary(formatted.len() - suffix))
    {
        suffix -= 1;
    }

    (
        prefix,
        source.len() - suffix,
        &formatted[prefix..formatted.len() - suffix],
    )
}

/// Convert a byte offset in `source` to an LSP [`Position`] using UTF-16 code
/// units for the character field (per the LSP spec default).
fn byte_to_lsp_position(source: &str, byte: usize) -> Position {
    let mut line = 0u32;
    let mut line_start = 0usize;
    let bytes = source.as_bytes();
    let cap = byte.min(bytes.len());
    let mut i = 0;
    while i < cap {
        if bytes[i] == b'\n' {
            line += 1;
            line_start = i + 1;
        }
        i += 1;
    }
    let character = source[line_start..cap].encode_utf16().count() as u32;
    Position::new(line, character)
}

/// Per-line surface cleanup used when the parser couldn't validate the
/// document. Strips trailing whitespace and replaces hard tabs at the start
/// of a line with two-space indent; touches nothing else.
fn fallback_cleanup_edits(source: &str) -> Option<Vec<TextEdit>> {
    let mut edits = Vec::new();
    for (line_num, line) in source.split('\n').enumerate() {
        let line_num = line_num as u32;
        let line_utf16_len = line.encode_utf16().count() as u32;

        // Tabs anywhere on the line → replace with two spaces. Emit a
        // whole-line edit so we preserve column math under the line's new
        // width.
        if line.contains('\t') {
            let replaced = line.replace('\t', "  ");
            let trimmed = replaced.trim_end().to_string();
            edits.push(TextEdit {
                range: Range {
                    start: Position::new(line_num, 0),
                    end: Position::new(line_num, line_utf16_len),
                },
                new_text: trimmed,
            });
            continue;
        }

        // Trailing whitespace only.
        let trimmed = line.trim_end();
        if trimmed.len() < line.len() {
            let trim_start = trimmed.encode_utf16().count() as u32;
            edits.push(TextEdit {
                range: Range {
                    start: Position::new(line_num, trim_start),
                    end: Position::new(line_num, line_utf16_len),
                },
                new_text: String::new(),
            });
        }
    }
    if edits.is_empty() { None } else { Some(edits) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    /// Apply LSP `edits` to `source` using the same byte/UTF-16 math the
    /// production code uses. Sorts in reverse so trailing edits' byte ranges
    /// stay valid as earlier ones are applied.
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

    fn lsp_position_to_byte(source: &str, pos: Position) -> usize {
        let mut line = 0u32;
        let mut line_start = 0usize;
        let bytes = source.as_bytes();
        let mut i = 0;
        while i < bytes.len() && line < pos.line {
            if bytes[i] == b'\n' {
                line += 1;
                line_start = i + 1;
            }
            i += 1;
        }
        // Walk the line until we've consumed pos.character UTF-16 code units.
        let line_slice = &source[line_start..];
        let mut utf16_consumed = 0u32;
        let mut byte_off = 0usize;
        let mut buf = [0u16; 2];
        for c in line_slice.chars() {
            if utf16_consumed >= pos.character || c == '\n' {
                break;
            }
            utf16_consumed += c.encode_utf16(&mut buf).len() as u32;
            byte_off += c.len_utf8();
        }
        line_start + byte_off
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

    /// Every emitted edit must satisfy LSP's range invariant: end >= start
    /// componentwise (line then character).
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
        assert!(
            !after.contains('\t'),
            "tabs should be replaced with spaces, got {after:?}"
        );
    }

    /// Regression test for issue #1142.
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

        // Metadata lines survive byte-for-byte.
        let after_lines: Vec<&str> = after.lines().collect();
        assert_eq!(
            after_lines.get(2).copied(),
            Some("    effective_date: 2024-01-20"),
        );
        assert_eq!(
            after_lines.get(4).copied(),
            Some("    effective_date: 2024-01-21"),
        );

        // Positive guard against a degenerate "emit zero / no-op edit"
        // implementation: the misaligned 4-space posting indent (4 spaces)
        // must be normalized away.
        assert!(
            !after.contains("\n  Assets:Bank  -50.00"),
            "test fixture should still have 2-space-indented postings; check the assertion"
        );
        let bank_line = after
            .lines()
            .find(|l| l.contains("Assets:Bank"))
            .expect("bank posting survived");
        let food_line = after
            .lines()
            .find(|l| l.contains("Expenses:Food"))
            .expect("food posting survived");
        assert_eq!(
            bank_line.find("USD"),
            food_line.find("USD"),
            "amounts must align across postings; got {bank_line:?} / {food_line:?}"
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
        assert!(
            result.errors.is_empty(),
            "parse errors: {:?}",
            result.errors
        );

        let edits = handle_formatting(&params(), source, &result).expect("expected edits");
        assert_well_formed(&edits);
        let after = apply(source, &edits);
        assert!(
            after.contains("; my comment"),
            "trailing comment dropped after formatting; got {after:?}"
        );
    }

    /// Parity-by-construction: the LSP-applied buffer must equal what
    /// `format_source` (the CLI's path) writes.
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

    /// Regression for the deep-review finding: a source ending without a
    /// trailing newline must still receive `format_source`'s trailing
    /// newline, with a well-formed (end >= start) range.
    #[test]
    fn source_without_trailing_newline_gets_one() {
        let source = "; comment";
        let result = parse(source);
        let edits = handle_formatting(&params(), source, &result).expect("expected edits");
        assert_well_formed(&edits);
        let after = apply(source, &edits);
        assert_eq!(after, "; comment\n");
    }

    /// Regression: a blank-only file is now canonical (format_source
    /// preserves every trailing newline), so the LSP must emit no edits.
    /// Before the fix, format_source collapsed it to `"\n"` and the LSP
    /// emitted a malformed range trying to apply the delta.
    #[test]
    fn blank_only_file_is_canonical() {
        let source = "\n\n\n\n";
        let result = parse(source);
        assert_eq!(
            format_source(source, &result, &FormatConfig::default()),
            source,
            "format_source must preserve a blank-only file verbatim"
        );
        assert!(
            handle_formatting(&params(), source, &result).is_none(),
            "no edits should be emitted for an already-canonical file"
        );
    }

    /// Non-ASCII content must roundtrip correctly through UTF-16 positions.
    #[test]
    fn non_ascii_payee_roundtrips() {
        let source = "2024-01-15 * \"Café\"\n    Assets:Bank  -1.00 USD\n  Expenses:Food\n";
        let result = parse(source);
        let edits = handle_formatting(&params(), source, &result).expect("expected edits");
        assert_well_formed(&edits);
        let after = apply(source, &edits);
        let cli = format_source(source, &result, &FormatConfig::default());
        assert_eq!(after, cli, "non-ASCII payee diverged from CLI output");
    }

    /// Per-hunk edits: two far-apart misalignments in the same buffer
    /// should produce two separate edits, not one giant edit spanning the
    /// unchanged middle.
    #[test]
    fn emits_per_hunk_edits_for_far_apart_changes() {
        // Two transactions, each with its own misindented posting; many
        // unchanged lines between them. After `format_source` re-aligns
        // both, the diff should have two contiguous hunks separated by
        // unchanged content — and the LSP should emit two TextEdits, not
        // one spanning everything.
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

        // Applying the edits must still produce the canonical output.
        let after = apply(source, &edits);
        let cli = format_source(source, &result, &FormatConfig::default());
        assert_eq!(after, cli);

        // Per-hunk: at least two distinct edits, no single edit covers
        // both transactions.
        assert!(
            edits.len() >= 2,
            "expected per-hunk edits for two far-apart changes, got {} edit(s): {edits:#?}",
            edits.len()
        );
        for edit in &edits {
            let span = edit.range.end.line - edit.range.start.line;
            assert!(
                span < 8,
                "single edit spans {span} lines — likely covering the unchanged middle: {edit:?}"
            );
        }
    }

    /// Parse-error fallback: per-line tab/trim cleanup must still run on
    /// lines unaffected by the broken directive.
    #[test]
    fn parse_errors_get_cleanup_fallback() {
        let source = "2024-01-01 open Assets:Bank   \n2024-01-02 not_a_directive\n\tAssets:Bank\n";
        let result = parse(source);
        assert!(!result.errors.is_empty());
        let edits = handle_formatting(&params(), source, &result).expect("expected cleanup edits");
        assert_well_formed(&edits);
        let after = apply(source, &edits);
        // Trailing whitespace on line 0 is gone.
        assert!(after.lines().next().unwrap().trim_end() == after.lines().next().unwrap());
        // Tab on line 2 is gone.
        assert!(!after.contains('\t'));
        // The broken line is untouched.
        assert!(after.contains("not_a_directive"));
    }
}
