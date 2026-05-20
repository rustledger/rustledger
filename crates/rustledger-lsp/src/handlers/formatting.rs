//! Document formatting handler for Beancount files.
//!
//! Provides formatting for:
//! - Consistent indentation (2 spaces for postings)
//! - Aligned amounts in transactions
//! - Consistent spacing around operators

use lsp_types::{DocumentFormattingParams, Position, Range, TextEdit};
use rustledger_core::{Directive, FormatConfig, SYNTHESIZED_FILE_ID, format_posting_line};
use rustledger_parser::ParseResult;

use super::utils::{LineIndex, document_format_config};

/// Handle a `textDocument/formatting` request.
///
/// Thin LSP-shaped wrapper around [`format_document`]. The protocol
/// passes client `FormattingOptions` here; this function feeds them
/// to [`document_format_config`] for the actual `FormatConfig`.
pub fn handle_formatting(
    params: &DocumentFormattingParams,
    source: &str,
    parse_result: &ParseResult,
) -> Option<Vec<TextEdit>> {
    let config = document_format_config(Some(&params.options));
    format_document(source, parse_result, &config)
}

/// Compute the document-format edits for a parsed source with a
/// resolved [`FormatConfig`].
///
/// Both `textDocument/formatting` (via [`handle_formatting`]) and
/// `rledger.alignAmounts` (via `handle_align_amounts`) call into
/// this — separated from the LSP-shaped wrapper so the executeCommand
/// path can express its config source explicitly (`None` → server
/// defaults) rather than synthesizing a fake `DocumentFormattingParams`
/// just to reach the formatter.
pub fn format_document(
    source: &str,
    parse_result: &ParseResult,
    config: &FormatConfig,
) -> Option<Vec<TextEdit>> {
    let mut edits = Vec::new();
    let lines: Vec<&str> = source.lines().collect();
    // Build the line index once: O(n) up front, O(log lines) per
    // offset lookup. Without it, calling the naive O(n) scanner per
    // posting per transaction is quadratic on large files.
    let line_index = LineIndex::new(source);

    for spanned in &parse_result.directives {
        if let Directive::Transaction(txn) = &spanned.value {
            // Format each posting using its own source span, not a
            // line-arithmetic guess from the directive's start_line.
            // Interleaved posting-level metadata (e.g., `effective_date:`)
            // makes `start_line + 1 + i` point at metadata lines, which
            // the formatter then overwrote with posting content — see
            // issue #1142.
            for spanned_posting in &txn.postings {
                // Defensive: the LSP formats parser-derived directives,
                // which always carry real spans. Guard against
                // `Spanned::synthesized` entries in case a future
                // integration feeds loader/plugin output through here.
                if spanned_posting.file_id == SYNTHESIZED_FILE_ID {
                    continue;
                }
                let (posting_line, _) = line_index.offset_to_position(spanned_posting.span.start);
                if let Some(line) = lines.get(posting_line as usize)
                    && let Some(edit) =
                        posting_text_edit(line, posting_line, spanned_posting, config)
                {
                    edits.push(edit);
                }
            }
        }
    }

    // Also format standalone lines (non-directive lines that might need cleanup)
    for (line_num, line) in lines.iter().enumerate() {
        // Fix tabs to spaces
        if line.contains('\t') {
            let new_line = line.replace('\t', "  ");
            if new_line != *line {
                edits.push(TextEdit {
                    range: Range {
                        start: Position::new(line_num as u32, 0),
                        end: Position::new(line_num as u32, line.len() as u32),
                    },
                    new_text: new_line,
                });
            }
        }

        // Trim trailing whitespace
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

    // Remove duplicate edits and sort
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

/// Compute a posting-line `TextEdit` by delegating to the canonical
/// core formatter ([`rustledger_core::format_posting_line`]). The
/// previous hand-rolled implementation here had two latent problems
/// fixed by the unification:
///
/// - It hardcoded `AMOUNT_COLUMN = 50`, so the LSP produced output one
///   column shy of `rledger format`'s default 60.
/// - It only formatted account + units, silently dropping cost specs
///   (`{...}`) and price annotations (`@`/`@@`).
///
/// `format_posting_line` is also the unit the on-disk formatter emits
/// (it's reused inside `format_transaction`), so any TextEdit we emit
/// matches exactly what `rledger format` would write to disk —
/// **including the first same-line trailing comment**. An earlier
/// draft delegated to the lower-level `format_posting`, which omitted
/// the comment and would have produced edits that silently dropped it.
fn posting_text_edit(
    line: &str,
    line_num: u32,
    posting: &rustledger_core::Posting,
    config: &FormatConfig,
) -> Option<TextEdit> {
    let trimmed = line.trim();

    // Skip if empty or comment
    if trimmed.is_empty() || trimmed.starts_with(';') {
        return None;
    }

    let formatted = format_posting_line(posting, config);

    // No edit needed when the source line already matches the canonical
    // form (ignoring trailing whitespace, which a separate pass strips).
    if formatted.trim_end() == line.trim_end() {
        return None;
    }

    Some(TextEdit {
        range: Range {
            start: Position::new(line_num, 0),
            end: Position::new(line_num, line.len() as u32),
        },
        new_text: formatted,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    #[test]
    fn test_formatting_removes_trailing_whitespace() {
        let source = "2024-01-01 open Assets:Bank USD   \n";
        let result = parse(source);
        let params = DocumentFormattingParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            options: Default::default(),
            work_done_progress_params: Default::default(),
        };

        let edits = handle_formatting(&params, source, &result);
        assert!(edits.is_some());
    }

    #[test]
    fn test_formatting_converts_tabs() {
        let source = "2024-01-01 * \"Test\"\n\tAssets:Bank\n";
        let result = parse(source);
        let params = DocumentFormattingParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            options: Default::default(),
            work_done_progress_params: Default::default(),
        };

        let edits = handle_formatting(&params, source, &result);
        assert!(edits.is_some());

        let edits = edits.unwrap();
        // Should have edit to replace tab
        assert!(edits.iter().any(|e| e.new_text.contains("  ")));
    }

    /// Regression test for issue #1142.
    ///
    /// When a transaction has posting-level metadata interleaved between
    /// postings (e.g., `effective_date:`), the previous formatter
    /// computed each posting's line as `txn_start_line + 1 + posting_idx`
    /// and so produced TextEdits targeting metadata lines instead of
    /// posting lines. Applying those edits overwrote the metadata. This
    /// test pins the post-fix behavior: emitted edits target only the
    /// posting lines and never the metadata lines between them.
    #[test]
    fn test_formatting_preserves_interleaved_metadata_1142() {
        // Note the two-space indentation on postings vs four-space on
        // metadata — this is the canonical effective_date format.
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

        let params = DocumentFormattingParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            options: Default::default(),
            work_done_progress_params: Default::default(),
        };

        let edits = handle_formatting(&params, source, &result).unwrap_or_default();

        // Identify the metadata-line indices in the source: lines whose
        // first non-whitespace content is the `effective_date:` key.
        // (The canonical form uses four-space indent, but the check
        // accepts any indentation so a future test fixture variation
        // doesn't silently start matching the wrong lines.)
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
        let posting_lines: [u32; 2] = [1, 3];

        // No emitted edit should touch a metadata line. Pre-fix, the
        // line-arithmetic bug produced a posting-shaped edit at line 2
        // (the first metadata line), overwriting it.
        for edit in &edits {
            assert!(
                !metadata_lines.contains(&edit.range.start.line),
                "edit targets a metadata line — issue #1142 regressed: {edit:?}"
            );
        }
        // Positive assertion: the formatter must still do its job on
        // the real posting lines (otherwise a degenerate "emit zero
        // edits" implementation would silently pass the test).
        assert!(
            edits
                .iter()
                .any(|e| posting_lines.contains(&e.range.start.line)),
            "formatter emitted no edits for posting lines — alignment broken"
        );
    }

    /// Regression test: the formatter must preserve a same-line
    /// trailing comment on a posting. An earlier draft of the
    /// unification (PR #1158, commit `e537755f`) delegated to
    /// `format_posting`, which omits trailing comments — so the
    /// formatter emitted edits that silently dropped them. The fix
    /// is to route through `format_posting_line` (the helper that
    /// `format_transaction` also uses on the on-disk path), which
    /// appends `posting.trailing_comments[0]` to the line.
    #[test]
    fn test_formatting_preserves_trailing_comment_on_posting() {
        // Indent is intentionally wrong (4-space) so the formatter
        // *must* emit an edit; otherwise we'd be testing nothing.
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

        let params = DocumentFormattingParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            options: Default::default(),
            work_done_progress_params: Default::default(),
        };
        let edits = handle_formatting(&params, source, &result).unwrap_or_default();

        // Apply edits to the source and check the comment is still
        // present on its original line.
        let line1_edit = edits
            .iter()
            .find(|e| e.range.start.line == 1)
            .expect("expected an edit on line 1 (the Assets:Bank posting)");
        assert!(
            line1_edit.new_text.contains("; my comment"),
            "trailing comment dropped from canonical-formatted posting line; \
             got new_text = {:?}",
            line1_edit.new_text
        );
    }
}
