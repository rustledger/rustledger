//! Document highlight handler for highlighting all occurrences.
//!
//! Highlights all occurrences of the symbol under the cursor:
//! - Account names (all usages)
//! - Currency names (all usages)
//! - Payees (all transactions with same payee)

use lsp_types::{
    DocumentHighlight, DocumentHighlightKind, DocumentHighlightParams, Position, Range,
};
use rustledger_core::{Directive, SYNTHESIZED_FILE_ID};
use rustledger_parser::ParseResult;

use super::utils::{LineIndex, get_word_at_position, is_account_like, is_currency_like};

/// Handle a document highlight request.
pub fn handle_document_highlight(
    params: &DocumentHighlightParams,
    source: &str,
    parse_result: &ParseResult,
) -> Option<Vec<DocumentHighlight>> {
    let position = params.text_document_position_params.position;
    let line_idx = position.line as usize;
    let lines: Vec<&str> = source.lines().collect();
    let line = lines.get(line_idx)?;

    // Get the word at the cursor position
    let (word, _, _) = get_word_at_position(line, position.character as usize)?;

    let mut highlights = Vec::new();
    // Build the line index once and share it across collectors: each
    // directive (and posting) used to trigger an O(n) byte→line scan,
    // which scales quadratically on large files.
    let line_index = LineIndex::new(source);

    // Check if it's an account
    if is_account_like(&word) {
        collect_account_highlights(source, parse_result, &line_index, &word, &mut highlights);
    }
    // Check if it's a currency
    else if is_currency_like(&word, parse_result) {
        collect_currency_highlights(source, parse_result, &line_index, &word, &mut highlights);
    }
    // Check if it's a payee (inside quotes)
    else if is_in_quotes(line, position.character as usize) {
        collect_payee_highlights(source, parse_result, &line_index, &word, &mut highlights);
    }

    if highlights.is_empty() {
        None
    } else {
        Some(highlights)
    }
}

/// Collect all highlights for an account.
fn collect_account_highlights(
    source: &str,
    parse_result: &ParseResult,
    line_index: &LineIndex,
    account: &str,
    highlights: &mut Vec<DocumentHighlight>,
) {
    for spanned in &parse_result.directives {
        let (start_line, _) = line_index.offset_to_position(spanned.span.start);

        match &spanned.value {
            Directive::Open(open) => {
                if open.account.as_ref() == account
                    && let Some(range) = find_in_line(source, start_line, account)
                {
                    highlights.push(DocumentHighlight {
                        range,
                        kind: Some(DocumentHighlightKind::WRITE), // Definition
                    });
                }
            }
            Directive::Close(close) => {
                if close.account.as_ref() == account
                    && let Some(range) = find_in_line(source, start_line, account)
                {
                    highlights.push(DocumentHighlight {
                        range,
                        kind: Some(DocumentHighlightKind::WRITE),
                    });
                }
            }
            Directive::Balance(bal) => {
                if bal.account.as_ref() == account
                    && let Some(range) = find_in_line(source, start_line, account)
                {
                    highlights.push(DocumentHighlight {
                        range,
                        kind: Some(DocumentHighlightKind::READ),
                    });
                }
            }
            Directive::Pad(pad) => {
                if pad.account.as_ref() == account
                    && let Some(range) = find_in_line(source, start_line, account)
                {
                    highlights.push(DocumentHighlight {
                        range,
                        kind: Some(DocumentHighlightKind::READ),
                    });
                }
                if pad.source_account.as_ref() == account {
                    // Find second occurrence
                    let line_text = source.lines().nth(start_line as usize).unwrap_or("");
                    if let Some(first_pos) = line_text.find(account) {
                        let after_first = first_pos + account.len();
                        if let Some(second_pos) = line_text[after_first..].find(account) {
                            let actual_pos = after_first + second_pos;
                            highlights.push(DocumentHighlight {
                                range: Range {
                                    start: Position::new(start_line, actual_pos as u32),
                                    end: Position::new(
                                        start_line,
                                        (actual_pos + account.len()) as u32,
                                    ),
                                },
                                kind: Some(DocumentHighlightKind::READ),
                            });
                        }
                    }
                }
            }
            Directive::Note(note) => {
                if note.account.as_ref() == account
                    && let Some(range) = find_in_line(source, start_line, account)
                {
                    highlights.push(DocumentHighlight {
                        range,
                        kind: Some(DocumentHighlightKind::READ),
                    });
                }
            }
            Directive::Document(doc) => {
                if doc.account.as_ref() == account
                    && let Some(range) = find_in_line(source, start_line, account)
                {
                    highlights.push(DocumentHighlight {
                        range,
                        kind: Some(DocumentHighlightKind::READ),
                    });
                }
            }
            Directive::Transaction(txn) => {
                // Per-posting span lookup (see #1142): the prior
                // `start_line + 1 + i` arithmetic broke whenever a
                // transaction had interleaved posting-level metadata.
                for spanned_posting in &txn.postings {
                    if spanned_posting.file_id == SYNTHESIZED_FILE_ID {
                        continue;
                    }
                    if spanned_posting.account.as_ref() == account {
                        let (posting_line, _) =
                            line_index.offset_to_position(spanned_posting.span.start);
                        if let Some(range) = find_in_line(source, posting_line, account) {
                            highlights.push(DocumentHighlight {
                                range,
                                kind: Some(DocumentHighlightKind::READ),
                            });
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

/// Collect all highlights for a currency.
fn collect_currency_highlights(
    source: &str,
    parse_result: &ParseResult,
    line_index: &LineIndex,
    currency: &str,
    highlights: &mut Vec<DocumentHighlight>,
) {
    for spanned in &parse_result.directives {
        let directive_text = &source[spanned.span.start..spanned.span.end];
        let (start_line, _) = line_index.offset_to_position(spanned.span.start);

        let is_declaration =
            matches!(&spanned.value, Directive::Commodity(c) if c.currency.as_ref() == currency);

        // Find all occurrences of the currency in this directive
        for (line_offset, line) in directive_text.lines().enumerate() {
            let mut search_start = 0;
            while let Some(pos) = line[search_start..].find(currency) {
                let actual_pos = search_start + pos;

                // Verify word boundaries
                let before_ok = actual_pos == 0
                    || !line
                        .chars()
                        .nth(actual_pos - 1)
                        .unwrap_or(' ')
                        .is_alphanumeric();
                let after_ok = actual_pos + currency.len() >= line.len()
                    || !line
                        .chars()
                        .nth(actual_pos + currency.len())
                        .unwrap_or(' ')
                        .is_alphanumeric();

                if before_ok && after_ok {
                    let ref_line = start_line + line_offset as u32;
                    highlights.push(DocumentHighlight {
                        range: Range {
                            start: Position::new(ref_line, actual_pos as u32),
                            end: Position::new(ref_line, (actual_pos + currency.len()) as u32),
                        },
                        kind: Some(if is_declaration && line_offset == 0 {
                            DocumentHighlightKind::WRITE
                        } else {
                            DocumentHighlightKind::READ
                        }),
                    });
                }

                search_start = actual_pos + currency.len();
            }
        }
    }

    // Deduplicate
    highlights.sort_by(|a, b| {
        a.range
            .start
            .line
            .cmp(&b.range.start.line)
            .then(a.range.start.character.cmp(&b.range.start.character))
    });
    highlights.dedup_by(|a, b| a.range == b.range);
}

/// Collect all highlights for a payee.
fn collect_payee_highlights(
    source: &str,
    parse_result: &ParseResult,
    line_index: &LineIndex,
    payee: &str,
    highlights: &mut Vec<DocumentHighlight>,
) {
    for spanned in &parse_result.directives {
        if let Directive::Transaction(txn) = &spanned.value
            && let Some(ref txn_payee) = txn.payee
            && txn_payee.as_ref() == payee
        {
            let (line, _) = line_index.offset_to_position(spanned.span.start);
            let line_text = source.lines().nth(line as usize).unwrap_or("");

            if let Some(start) = line_text.find(&format!("\"{}\"", payee)) {
                highlights.push(DocumentHighlight {
                    range: Range {
                        start: Position::new(line, (start + 1) as u32),
                        end: Position::new(line, (start + 1 + payee.len()) as u32),
                    },
                    kind: Some(DocumentHighlightKind::READ),
                });
            }
        }
    }
}

/// Find a string in a specific line.
fn find_in_line(source: &str, line_num: u32, needle: &str) -> Option<Range> {
    let line = source.lines().nth(line_num as usize)?;
    let col = line.find(needle)?;
    Some(Range {
        start: Position::new(line_num, col as u32),
        end: Position::new(line_num, (col + needle.len()) as u32),
    })
}

fn is_in_quotes(line: &str, col: usize) -> bool {
    let chars: Vec<char> = line.chars().collect();
    let mut in_quotes = false;

    for (i, c) in chars.iter().enumerate() {
        if i >= col {
            break;
        }
        if *c == '"' {
            in_quotes = !in_quotes;
        }
    }

    in_quotes
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    #[test]
    fn test_highlight_account() {
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food
2024-01-31 balance Assets:Bank 100 USD
"#;
        let result = parse(source);
        let uri: lsp_types::Uri = "file:///test.beancount".parse().unwrap();

        let params = DocumentHighlightParams {
            text_document_position_params: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier { uri },
                position: Position::new(0, 16), // On "Assets:Bank"
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let highlights = handle_document_highlight(&params, source, &result);
        assert!(highlights.is_some());

        let highlights = highlights.unwrap();
        // Should find: open (write), posting (read), balance (read) = 3
        assert_eq!(highlights.len(), 3);

        // First should be WRITE (definition)
        assert_eq!(highlights[0].kind, Some(DocumentHighlightKind::WRITE));
    }

    #[test]
    fn test_highlight_currency() {
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food  5.00 USD
"#;
        let result = parse(source);
        let uri: lsp_types::Uri = "file:///test.beancount".parse().unwrap();

        let params = DocumentHighlightParams {
            text_document_position_params: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier { uri },
                position: Position::new(0, 28), // On "USD"
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let highlights = handle_document_highlight(&params, source, &result);
        assert!(highlights.is_some());

        let highlights = highlights.unwrap();
        // Should find USD in: open, posting 1, posting 2 = 3
        assert_eq!(highlights.len(), 3);
    }

    /// Regression test for the read-only sibling of #1142.
    ///
    /// Pre-fix, `posting_line = txn_start_line + 1 + i` put the second
    /// posting's highlight on the metadata line between the postings.
    /// Per-posting span lookup must put each highlight on the actual
    /// posting line.
    #[test]
    fn test_highlight_account_with_interleaved_metadata_1142() {
        let source = "\
2024-01-01 open Assets:Bank USD
2024-01-15 * \"Test\"
  Assets:Bank  -5.00 USD
    effective_date: 2024-01-20
  Expenses:Food  5.00 USD
    effective_date: 2024-01-21
";
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "parse errors: {:?}",
            result.errors
        );

        let uri: lsp_types::Uri = "file:///test.beancount".parse().unwrap();
        let params = DocumentHighlightParams {
            text_document_position_params: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier { uri },
                position: Position::new(0, 16), // on "Assets:Bank" in open
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let highlights = handle_document_highlight(&params, source, &result)
            .expect("Assets:Bank has at least the Open + 1 posting");

        // Lines 3 and 5 contain `effective_date:`; the posting is on
        // line 2 (after the Open + transaction header). No highlight
        // should land on a metadata line.
        let metadata_lines = [3u32, 5u32];
        for h in &highlights {
            assert!(
                !metadata_lines.contains(&h.range.start.line),
                "highlight landed on metadata line: {h:?}"
            );
        }
        // Positive assertion: the Assets:Bank posting on line 2 must be
        // highlighted (the bug used to point at line 3 instead).
        assert!(
            highlights.iter().any(|h| h.range.start.line == 2),
            "Assets:Bank posting on line 2 should be highlighted; got {highlights:?}"
        );
    }
}
