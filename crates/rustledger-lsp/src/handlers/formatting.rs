//! Document formatting handler for Beancount files.
//!
//! Defers all directive formatting to
//! [`rustledger_core::format::format_directive`] — the same code path
//! that powers `rledger format` on the CLI. This is the only place
//! the LSP should ever decide *how* a directive looks: any
//! "beancount-canonical formatting" logic lives in `rustledger-core`,
//! the LSP just emits text edits that replace each directive's source
//! span with the canonical rendering.
//!
//! This handler additionally cleans up non-directive lines:
//! - tabs → two spaces
//! - trailing whitespace stripped
//!
//! Closes #1142: previously the LSP shipped its own line-based
//! formatter that drifted out of sync with the AST-based core
//! formatter; with posting-level metadata it would overwrite
//! metadata lines with posting content (data loss). Delegating to
//! `format_directive` makes LSP and CLI output identical by
//! construction.
use lsp_types::{DocumentFormattingParams, Position, Range, TextEdit};
use rustledger_core::format::{FormatConfig, format_directive};
use rustledger_parser::ParseResult;

use super::utils::byte_offset_to_position;

/// Handle a document formatting request.
pub fn handle_formatting(
    _params: &DocumentFormattingParams,
    source: &str,
    parse_result: &ParseResult,
) -> Option<Vec<TextEdit>> {
    let mut edits = directive_format_edits(source, parse_result);
    edits.extend(non_directive_cleanup_edits(source));
    finalize_edits(edits)
}

/// One [`TextEdit`] per directive whose canonical rendering differs
/// from the source span. The edit replaces the directive's full
/// source span (start..end byte offsets from the parser) with the
/// output of [`format_directive`].
///
/// Per-posting line indexing is **deliberately avoided** — that was
/// the bug in #1142. Postings can have their own metadata lines, so
/// `start_line + 1 + i` doesn't reliably point at posting `i`'s
/// source line.
fn directive_format_edits(source: &str, parse_result: &ParseResult) -> Vec<TextEdit> {
    let config = FormatConfig::default();
    let mut edits = Vec::new();

    for spanned in &parse_result.directives {
        let start = spanned.span.start;
        let end = spanned.span.end;
        if start > source.len() || end > source.len() || start > end {
            // Malformed span — skip rather than panic.
            continue;
        }
        let original = &source[start..end];
        let formatted = format_directive(&spanned.value, &config);

        // The core formatter always appends a trailing newline; the
        // source span may or may not include the directive's own
        // newline depending on the parser. Compare trim_end'd forms
        // to avoid spurious edits for newline-only differences.
        if original.trim_end() == formatted.trim_end() {
            continue;
        }

        let (start_line, start_col) = byte_offset_to_position(source, start);
        let (end_line, end_col) = byte_offset_to_position(source, end);

        // Preserve whatever trailing newline the source had (or
        // didn't) so we don't churn line counts on files without a
        // final newline.
        let new_text = if original.ends_with('\n') {
            formatted
        } else {
            formatted.trim_end_matches('\n').to_string()
        };

        edits.push(TextEdit {
            range: Range {
                start: Position::new(start_line, start_col),
                end: Position::new(end_line, end_col),
            },
            new_text,
        });
    }

    edits
}

/// Whole-line tab→spaces and trailing-whitespace cleanup for lines
/// that aren't subsumed by a directive edit. Cheap, line-local, and
/// doesn't depend on the AST.
fn non_directive_cleanup_edits(source: &str) -> Vec<TextEdit> {
    let mut edits = Vec::new();
    for (line_num, line) in source.lines().enumerate() {
        if line.contains('\t') {
            let new_line = line.replace('\t', "  ");
            edits.push(TextEdit {
                range: Range {
                    start: Position::new(line_num as u32, 0),
                    end: Position::new(line_num as u32, line.len() as u32),
                },
                new_text: new_line,
            });
            continue;
        }
        let trimmed = line.trim_end();
        if trimmed.len() < line.len() {
            edits.push(TextEdit {
                range: Range {
                    start: Position::new(line_num as u32, trimmed.len() as u32),
                    end: Position::new(line_num as u32, line.len() as u32),
                },
                new_text: String::new(),
            });
        }
    }
    edits
}

/// Sort edits, drop edits subsumed by an earlier edit's range, return
/// `None` if empty. LSP requires non-overlapping edits.
///
/// Directive edits cover a multi-line range; the per-line cleanup
/// edits target specific positions on individual lines. When a
/// directive's span includes a line that also has trailing
/// whitespace, the directive edit's `new_text` (which is canonical
/// formatter output and therefore has no trailing whitespace) wins.
fn finalize_edits(mut edits: Vec<TextEdit>) -> Option<Vec<TextEdit>> {
    edits.sort_by(|a, b| {
        a.range
            .start
            .line
            .cmp(&b.range.start.line)
            .then(a.range.start.character.cmp(&b.range.start.character))
    });
    // After sorting by start, walk forward and keep an edit only if it
    // starts strictly after the previous kept edit's end. This drops
    // line-cleanup edits that fall inside a directive edit's span.
    let mut kept: Vec<TextEdit> = Vec::with_capacity(edits.len());
    for e in edits {
        if let Some(last) = kept.last()
            && !position_lt(last.range.end, e.range.start)
        {
            continue;
        }
        kept.push(e);
    }
    if kept.is_empty() { None } else { Some(kept) }
}

fn position_lt(a: Position, b: Position) -> bool {
    (a.line, a.character) < (b.line, b.character)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    fn format(source: &str) -> Option<Vec<TextEdit>> {
        let result = parse(source);
        let params = DocumentFormattingParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            options: Default::default(),
            work_done_progress_params: Default::default(),
        };
        handle_formatting(&params, source, &result)
    }

    /// Apply an LSP edit set to source for assertion purposes. Edits
    /// are non-overlapping after finalize_edits; we apply in reverse
    /// position order so earlier offsets stay valid as we splice.
    fn apply(source: &str, edits: &[TextEdit]) -> String {
        let line_starts: Vec<usize> = std::iter::once(0)
            .chain(
                source
                    .char_indices()
                    .filter(|(_, c)| *c == '\n')
                    .map(|(i, _)| i + 1),
            )
            .collect();
        let pos_to_offset = |p: Position| -> usize {
            let line = p.line as usize;
            let base = *line_starts.get(line).unwrap_or(&source.len());
            (base + p.character as usize).min(source.len())
        };
        let mut out = source.to_string();
        let mut applied: Vec<(usize, usize, String)> = edits
            .iter()
            .map(|e| {
                (
                    pos_to_offset(e.range.start),
                    pos_to_offset(e.range.end),
                    e.new_text.clone(),
                )
            })
            .collect();
        applied.sort_by_key(|(start, _, _)| std::cmp::Reverse(*start));
        for (start, end, text) in applied {
            out.replace_range(start..end, &text);
        }
        out
    }

    #[test]
    fn test_formatting_removes_trailing_whitespace() {
        let source = "2024-01-01 open Assets:Bank USD   \n";
        let edits = format(source).expect("expected edits");
        assert!(!edits.is_empty());
    }

    #[test]
    fn test_formatting_converts_tabs() {
        let source = "2024-01-01 * \"Test\"\n\tAssets:Bank\n";
        let edits = format(source).expect("expected edits");
        assert!(edits.iter().any(|e| e.new_text.contains("  ")));
    }

    /// Regression for #1142: posting-level metadata must be
    /// preserved. The previous line-based formatter used
    /// `posting_line = start_line + 1 + i` and clobbered metadata
    /// lines when postings had their own `meta:` entries.
    #[test]
    fn issue_1142_posting_metadata_is_preserved() {
        // Already canonically formatted (amount_column = 60).
        let source = "\
2024-07-20 * \"Purchase with multipart returns\"
  Assets:Joint:Revolut:EUR                           -26 EUR
  Assets:Ohad:Amazon-Gift-Card                      9.00 EUR
    effective_date: 2024-07-25
  Assets:Ohad:Amazon-Gift-Card                     17.00 EUR
    effective_date: 2024-07-27
";

        let edits = format(source);
        let result = match edits {
            None => source.to_string(),
            Some(ref edits) => apply(source, edits),
        };

        // Round-trip must preserve BOTH effective_date metadata lines.
        assert!(
            result.contains("effective_date: 2024-07-25"),
            "first posting metadata was clobbered; got:\n{result}",
        );
        assert!(
            result.contains("effective_date: 2024-07-27"),
            "second posting metadata was clobbered; got:\n{result}",
        );
        // And there must be exactly three posting lines, not the
        // four-line duplicated output the bug produced.
        let posting_line_count = result
            .lines()
            .filter(|l| l.starts_with("  Assets:"))
            .count();
        assert_eq!(
            posting_line_count, 3,
            "expected 3 posting lines, got {posting_line_count}:\n{result}",
        );
    }

    /// LSP and CLI must produce byte-identical output for the same
    /// directive — the whole point of #1142's "expected behavior".
    #[test]
    fn lsp_output_matches_rledger_format() {
        let source = "\
2024-07-20 * \"Purchase\"
  Assets:Bank             -26 EUR
  Expenses:Food            26 EUR
";
        let parse_result = parse(source);
        let txn = &parse_result.directives[0].value;
        let cli_output = format_directive(txn, &FormatConfig::default());

        let lsp_result = match format(source) {
            None => source.to_string(),
            Some(edits) => apply(source, &edits),
        };

        // Strip trailing newline differences (the CLI's format_directive
        // always appends one; the source span may or may not).
        assert_eq!(
            lsp_result.trim_end(),
            cli_output.trim_end(),
            "LSP and CLI output diverged"
        );
    }
}
