//! Range formatting handler for formatting selections.
//!
//! Delegates to [`rustledger_core::format::format_directive`] just
//! like the whole-document handler does (see `formatting.rs`); the
//! only difference is we restrict our emitted edits to directives
//! whose source span overlaps the user's selection. Non-directive
//! cleanup (tabs / trailing whitespace) is also scoped to the
//! selected lines.
//!
//! Same #1142 fix rationale as the document formatter — one code
//! path, the AST-based one.
use lsp_types::{DocumentRangeFormattingParams, Position, Range, TextEdit};
use rustledger_core::format::{FormatConfig, format_directive};
use rustledger_parser::ParseResult;

use super::utils::byte_offset_to_position;

/// Handle a range formatting request.
pub fn handle_range_formatting(
    params: &DocumentRangeFormattingParams,
    source: &str,
    parse_result: &ParseResult,
) -> Option<Vec<TextEdit>> {
    let range = params.range;
    let mut edits = directive_format_edits(source, parse_result, range);
    edits.extend(non_directive_cleanup_edits(source, range));
    finalize_edits(edits)
}

/// One [`TextEdit`] per directive whose source span overlaps the
/// requested range AND whose canonical rendering differs from the
/// source.
fn directive_format_edits(source: &str, parse_result: &ParseResult, range: Range) -> Vec<TextEdit> {
    let config = FormatConfig::default();
    let mut edits = Vec::new();

    for spanned in &parse_result.directives {
        let start = spanned.span.start;
        let end = spanned.span.end;
        if start > source.len() || end > source.len() || start > end {
            continue;
        }

        let (start_line, start_col) = byte_offset_to_position(source, start);
        let (end_line, end_col) = byte_offset_to_position(source, end);

        // Overlap check: directive ends before the range starts, OR
        // starts after the range ends → skip.
        let directive_start = Position::new(start_line, start_col);
        let directive_end = Position::new(end_line, end_col);
        if position_lt(directive_end, range.start) || position_lt(range.end, directive_start) {
            continue;
        }

        let original = &source[start..end];
        let formatted = format_directive(&spanned.value, &config);
        if original.trim_end() == formatted.trim_end() {
            continue;
        }

        let new_text = if original.ends_with('\n') {
            formatted
        } else {
            formatted.trim_end_matches('\n').to_string()
        };

        edits.push(TextEdit {
            range: Range {
                start: directive_start,
                end: directive_end,
            },
            new_text,
        });
    }

    edits
}

/// Whole-line tab→spaces and trailing-whitespace cleanup, restricted
/// to lines that fall within the requested range.
fn non_directive_cleanup_edits(source: &str, range: Range) -> Vec<TextEdit> {
    let mut edits = Vec::new();
    for (line_num, line) in source.lines().enumerate() {
        let line_num = line_num as u32;
        if line_num < range.start.line || line_num > range.end.line {
            continue;
        }
        if line.contains('\t') {
            let new_line = line.replace('\t', "  ");
            edits.push(TextEdit {
                range: Range {
                    start: Position::new(line_num, 0),
                    end: Position::new(line_num, line.len() as u32),
                },
                new_text: new_line,
            });
            continue;
        }
        let trimmed = line.trim_end();
        if trimmed.len() < line.len() {
            edits.push(TextEdit {
                range: Range {
                    start: Position::new(line_num, trimmed.len() as u32),
                    end: Position::new(line_num, line.len() as u32),
                },
                new_text: String::new(),
            });
        }
    }
    edits
}

fn finalize_edits(mut edits: Vec<TextEdit>) -> Option<Vec<TextEdit>> {
    edits.sort_by(|a, b| {
        a.range
            .start
            .line
            .cmp(&b.range.start.line)
            .then(a.range.start.character.cmp(&b.range.start.character))
    });
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

    #[test]
    fn test_range_formatting() {
        let source = "2024-01-01 open Assets:Bank USD   \n";
        let result = parse(source);
        let params = DocumentRangeFormattingParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            range: Range {
                start: Position::new(0, 0),
                end: Position::new(0, 35),
            },
            options: Default::default(),
            work_done_progress_params: Default::default(),
        };

        let edits = handle_range_formatting(&params, source, &result);
        assert!(edits.is_some());
    }

    /// Range formatter shares #1142's fix path. Pin it explicitly so
    /// a future divergence between the document and range handlers
    /// gets caught.
    #[test]
    fn issue_1142_posting_metadata_preserved_in_range_format() {
        let source = "\
2024-07-20 * \"Multipart\"
  Assets:Bank                                        -26 EUR
  Assets:Gift                                       9.00 EUR
    effective_date: 2024-07-25
  Assets:Gift                                      17.00 EUR
    effective_date: 2024-07-27
";
        let result = parse(source);
        let params = DocumentRangeFormattingParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            range: Range {
                start: Position::new(0, 0),
                end: Position::new(6, 0),
            },
            options: Default::default(),
            work_done_progress_params: Default::default(),
        };

        let edits = handle_range_formatting(&params, source, &result);
        // Either no edits (source already canonical) or any emitted
        // edit's `new_text` must contain both metadata lines —
        // never replacing a metadata line with a posting line.
        if let Some(edits) = edits {
            for e in &edits {
                // Per-line cleanup edits target a single line; skip those.
                if e.range.start.line == e.range.end.line {
                    continue;
                }
                assert!(
                    e.new_text.contains("effective_date: 2024-07-25"),
                    "directive edit dropped first metadata: {}",
                    e.new_text
                );
                assert!(
                    e.new_text.contains("effective_date: 2024-07-27"),
                    "directive edit dropped second metadata: {}",
                    e.new_text
                );
            }
        }
    }
}
