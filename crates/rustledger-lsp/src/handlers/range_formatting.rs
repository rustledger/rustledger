//! Range formatting handler for formatting selections.
//!
//! Formats only the selected range of the document.

use lsp_types::{DocumentRangeFormattingParams, Position, Range, TextEdit};
use rustledger_core::{Directive, SYNTHESIZED_FILE_ID};
use rustledger_parser::ParseResult;

use super::utils::LineIndex;

/// Handle a range formatting request.
pub fn handle_range_formatting(
    params: &DocumentRangeFormattingParams,
    source: &str,
    parse_result: &ParseResult,
) -> Option<Vec<TextEdit>> {
    let range = params.range;
    let mut edits = Vec::new();
    let lines: Vec<&str> = source.lines().collect();
    // Build the line index once so per-posting offset→line lookups are
    // O(log lines) instead of O(n). On a large file with many
    // transactions, the naive scanner would otherwise dominate.
    let line_index = LineIndex::new(source);

    // Process lines within the range
    for line_num in range.start.line..=range.end.line {
        if let Some(line) = lines.get(line_num as usize) {
            // Fix tabs to spaces
            if line.contains('\t') {
                let new_line = line.replace('\t', "  ");
                if new_line != *line {
                    edits.push(TextEdit {
                        range: Range {
                            start: Position::new(line_num, 0),
                            end: Position::new(line_num, line.len() as u32),
                        },
                        new_text: new_line,
                    });
                    continue; // Skip other edits for this line
                }
            }

            // Trim trailing whitespace
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
    }

    // Format postings within transactions in the range. Look up each
    // posting's line from its own source span, not via line arithmetic
    // off the transaction header — interleaved posting-level metadata
    // (e.g., `effective_date:`) breaks the `start_line + 1 + i`
    // assumption and caused #1142.
    for spanned in &parse_result.directives {
        if let Directive::Transaction(txn) = &spanned.value {
            let (start_line, _) = line_index.offset_to_position(spanned.span.start);

            // Check if transaction overlaps with range
            if start_line > range.end.line {
                continue;
            }

            for spanned_posting in &txn.postings {
                // Defensive: the LSP formats parser-derived directives,
                // which always carry real spans. Guard against
                // `Spanned::synthesized` entries in case a future
                // integration feeds loader/plugin output through here.
                if spanned_posting.file_id == SYNTHESIZED_FILE_ID {
                    continue;
                }
                let (posting_line, _) = line_index.offset_to_position(spanned_posting.span.start);

                // Check if posting is within range
                if posting_line >= range.start.line
                    && posting_line <= range.end.line
                    && let Some(line) = lines.get(posting_line as usize)
                    && let Some(edit) = format_posting_line(line, posting_line, spanned_posting)
                {
                    // Don't duplicate edits
                    if !edits.iter().any(|e| e.range.start.line == posting_line) {
                        edits.push(edit);
                    }
                }
            }
        }
    }

    // Sort and deduplicate
    edits.sort_by(|a, b| {
        a.range
            .start
            .line
            .cmp(&b.range.start.line)
            .then(a.range.start.character.cmp(&b.range.start.character))
    });
    edits.dedup_by(|a, b| a.range == b.range);

    if edits.is_empty() { None } else { Some(edits) }
}

/// Format a posting line for alignment.
fn format_posting_line(
    line: &str,
    line_num: u32,
    posting: &rustledger_core::Posting,
) -> Option<TextEdit> {
    let trimmed = line.trim();

    // Skip if empty or comment
    if trimmed.is_empty() || trimmed.starts_with(';') {
        return None;
    }

    let account = posting.account.to_string();
    let current_indent = line.len() - line.trim_start().len();
    let expected_indent = 2;

    // Only fix indentation issues
    if current_indent != expected_indent {
        let mut formatted = String::new();
        formatted.push_str(&" ".repeat(expected_indent));
        formatted.push_str(trimmed);

        return Some(TextEdit {
            range: Range {
                start: Position::new(line_num, 0),
                end: Position::new(line_num, line.len() as u32),
            },
            new_text: formatted,
        });
    }

    let _ = account; // suppress unused warning
    None
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

    /// Regression test for issue #1142 (range-formatting variant).
    ///
    /// Pre-fix, `posting_line = start_line + 1 + i` pointed at the
    /// metadata lines between postings, and the formatter emitted
    /// posting-shaped edits that overwrote them. See the matching test
    /// on `formatting.rs` for the full reasoning.
    #[test]
    fn test_range_formatting_preserves_interleaved_metadata_1142() {
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

        let params = DocumentRangeFormattingParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            // Cover the full transaction.
            range: Range {
                start: Position::new(0, 0),
                end: Position::new(5, 0),
            },
            options: Default::default(),
            work_done_progress_params: Default::default(),
        };

        let edits = handle_range_formatting(&params, source, &result).unwrap_or_default();

        let metadata_lines: Vec<u32> = source
            .lines()
            .enumerate()
            .filter_map(|(i, line)| {
                line.trim_start()
                    .starts_with("effective_date:")
                    .then_some(i as u32)
            })
            .collect();
        assert_eq!(metadata_lines, vec![2, 4], "test source layout assumption");

        for edit in &edits {
            assert!(
                !metadata_lines.contains(&edit.range.start.line),
                "edit targets a metadata line — issue #1142 regressed: {edit:?}"
            );
        }
        // No positive "must produce an edit" assertion here: range
        // formatting only emits edits when something actually needs
        // changing, and this source is already correctly formatted.
        // Emitting zero edits IS the right outcome — see the
        // `_misindented` variant below for the positive case.
    }

    /// Companion to the regression test above: with a *misindented*
    /// posting interleaved with metadata, range formatting should
    /// produce a fix for the posting and still leave the metadata
    /// alone. Catches a future regression that silently short-circuits
    /// the formatter (the all-correct test above can't tell those
    /// apart from a working fix).
    #[test]
    fn test_range_formatting_fixes_misindented_posting_without_touching_metadata() {
        // Note: posting 1 has 4-space indent (should be 2).
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

        let params = DocumentRangeFormattingParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            range: Range {
                start: Position::new(0, 0),
                end: Position::new(5, 0),
            },
            options: Default::default(),
            work_done_progress_params: Default::default(),
        };

        let edits = handle_range_formatting(&params, source, &result).unwrap_or_default();
        let metadata_lines = [2u32, 4u32];

        for edit in &edits {
            assert!(
                !metadata_lines.contains(&edit.range.start.line),
                "edit targets a metadata line — issue #1142 regressed: {edit:?}"
            );
        }
        assert!(
            edits.iter().any(|e| e.range.start.line == 3),
            "expected an edit at the misindented posting (line 3); got {edits:?}"
        );
    }
}
