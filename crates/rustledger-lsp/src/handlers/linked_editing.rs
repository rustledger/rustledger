//! Linked editing range handler for simultaneous editing.
//!
//! Provides ranges that can be edited together:
//! - Account names: edit all occurrences simultaneously
//! - Currency names: edit all occurrences simultaneously

use lsp_types::{LinkedEditingRangeParams, LinkedEditingRanges, Position, Range};
use rustledger_core::{Directive, SYNTHESIZED_FILE_ID};
use rustledger_parser::ParseResult;

use super::utils::{LineIndex, get_word_at_position, is_account_like, is_currency_like};

/// Handle a linked editing range request.
pub fn handle_linked_editing_range(
    params: &LinkedEditingRangeParams,
    source: &str,
    parse_result: &ParseResult,
) -> Option<LinkedEditingRanges> {
    let position = params.text_document_position_params.position;
    let line_idx = position.line as usize;
    let lines: Vec<&str> = source.lines().collect();
    let line = lines.get(line_idx)?;

    // Get the word at the cursor position
    let (word, _, _) = get_word_at_position(line, position.character as usize)?;

    let mut ranges = Vec::new();
    // Build the line index once and share it across collectors —
    // otherwise each posting/directive lookup is an O(n) scan.
    let line_index = LineIndex::new(source);

    // Check if it's an account
    if is_account_like(&word) {
        collect_account_ranges(source, parse_result, &line_index, &word, &mut ranges);
    }
    // Check if it's a currency
    else if is_currency_like(&word, parse_result) {
        collect_currency_ranges(parse_result, &line_index, &word, &mut ranges);
    }

    if ranges.is_empty() {
        None
    } else {
        // Account pattern: uppercase start, can contain colons, letters, numbers, hyphens
        let word_pattern = if is_account_like(&word) {
            Some(r"[A-Z][A-Za-z0-9:-]*".to_string())
        } else {
            Some(r"[A-Z][A-Z0-9]*".to_string())
        };

        Some(LinkedEditingRanges {
            ranges,
            word_pattern,
        })
    }
}

/// Collect all ranges for an account.
fn collect_account_ranges(
    source: &str,
    parse_result: &ParseResult,
    line_index: &LineIndex,
    account: &str,
    ranges: &mut Vec<Range>,
) {
    for spanned in &parse_result.directives {
        let (start_line, _) = line_index.offset_to_position(spanned.span.start);

        match &spanned.value {
            Directive::Open(open) => {
                if open.account.as_ref() == account
                    && let Some(range) = find_in_line(source, start_line, account)
                {
                    ranges.push(range);
                }
            }
            Directive::Close(close) => {
                if close.account.as_ref() == account
                    && let Some(range) = find_in_line(source, start_line, account)
                {
                    ranges.push(range);
                }
            }
            Directive::Balance(bal) => {
                if bal.account.as_ref() == account
                    && let Some(range) = find_in_line(source, start_line, account)
                {
                    ranges.push(range);
                }
            }
            Directive::Pad(pad) => {
                if pad.account.as_ref() == account
                    && let Some(range) = find_in_line(source, start_line, account)
                {
                    ranges.push(range);
                }
                if pad.source_account.as_ref() == account {
                    let line_text = source.lines().nth(start_line as usize).unwrap_or("");
                    if let Some(first_pos) = line_text.find(account) {
                        let after_first = first_pos + account.len();
                        if let Some(second_pos) = line_text[after_first..].find(account) {
                            let actual_pos = after_first + second_pos;
                            ranges.push(Range {
                                start: Position::new(start_line, actual_pos as u32),
                                end: Position::new(start_line, (actual_pos + account.len()) as u32),
                            });
                        }
                    }
                }
            }
            Directive::Note(note) => {
                if note.account.as_ref() == account
                    && let Some(range) = find_in_line(source, start_line, account)
                {
                    ranges.push(range);
                }
            }
            Directive::Document(doc) => {
                if doc.account.as_ref() == account
                    && let Some(range) = find_in_line(source, start_line, account)
                {
                    ranges.push(range);
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
                            ranges.push(range);
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

/// Collect all ranges for a currency.
/// Collect linked-edit ranges for a currency.
///
/// Walks the parser's `currency_occurrences` index for exact spans
/// — same pattern as `rename::collect_currency_rename_edits` and
/// siblings. The previous string-search implementation matched
/// currency-code substrings in payee strings, account-name segments,
/// and comments, then included them in the linked-edit range set —
/// so as the user typed, the unrelated text would mutate alongside
/// the real currency tokens.
fn collect_currency_ranges(
    parse_result: &ParseResult,
    line_index: &LineIndex,
    currency: &str,
    ranges: &mut Vec<Range>,
) {
    for occurrence in &parse_result.currency_occurrences {
        if occurrence.value != currency {
            continue;
        }
        let (start_line, start_col) = line_index.offset_to_position(occurrence.span.start);
        let (end_line, end_col) = line_index.offset_to_position(occurrence.span.end);
        ranges.push(Range {
            start: Position::new(start_line, start_col),
            end: Position::new(end_line, end_col),
        });
    }

    // Defensive dedup — see `rename::collect_currency_rename_edits`
    // for the rationale; the parser is forward-advancing so today
    // every occurrence is unique, but the dedup costs nothing and
    // protects against future parser refactors.
    ranges.sort_by(|a, b| {
        a.start
            .line
            .cmp(&b.start.line)
            .then(a.start.character.cmp(&b.start.character))
    });
    ranges.dedup();
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

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    #[test]
    fn test_linked_editing_account() {
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food
2024-01-31 balance Assets:Bank 100 USD
"#;
        let result = parse(source);
        let uri: lsp_types::Uri = "file:///test.beancount".parse().unwrap();

        let params = LinkedEditingRangeParams {
            text_document_position_params: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier { uri },
                position: Position::new(0, 16), // On "Assets:Bank"
            },
            work_done_progress_params: Default::default(),
        };

        let result = handle_linked_editing_range(&params, source, &result);
        assert!(result.is_some());

        let ranges = result.unwrap();
        // Should find: open, posting, balance = 3 ranges
        assert_eq!(ranges.ranges.len(), 3);
        // Should have account word pattern
        assert!(ranges.word_pattern.is_some());
    }

    #[test]
    fn test_linked_editing_currency() {
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food  5.00 USD
"#;
        let result = parse(source);
        let uri: lsp_types::Uri = "file:///test.beancount".parse().unwrap();

        let params = LinkedEditingRangeParams {
            text_document_position_params: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier { uri },
                position: Position::new(0, 28), // On "USD"
            },
            work_done_progress_params: Default::default(),
        };

        let result = handle_linked_editing_range(&params, source, &result);
        assert!(result.is_some());

        let ranges = result.unwrap();
        // Should find USD in: open, posting 1, posting 2 = 3 ranges
        assert_eq!(ranges.ranges.len(), 3);
    }

    /// Regression test for currency linked-editing false positives.
    /// See `rename::test_rename_currency_no_false_positives` for the
    /// fuller rationale.
    ///
    /// Linked editing is especially sensitive to false positives:
    /// each range gets mutated *together* as the user types, so a
    /// false-positive range inside an account name or a payee
    /// string would silently corrupt that text. The AST-driven
    /// `currency_occurrences` walk makes that impossible.
    #[test]
    fn test_linked_editing_currency_no_false_positives() {
        let source = r#"2024-01-01 open Assets:USD-Reserve
2024-01-01 commodity USD
2024-01-15 * "USD-to-EUR transfer"
  Assets:USD-Reserve  -100 USD
  Assets:Bank          100 USD
"#;
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "parse errors: {:?}",
            result.errors
        );
        let uri: lsp_types::Uri = "file:///test.beancount".parse().unwrap();

        let params = LinkedEditingRangeParams {
            text_document_position_params: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier { uri },
                position: Position::new(1, 21), // on `USD` of `commodity USD`
            },
            work_done_progress_params: Default::default(),
        };

        let ranges = handle_linked_editing_range(&params, source, &result)
            .expect("linked editing returns Some");

        // Expected: 3 ranges — `commodity USD`, `-100 USD`,
        // `100 USD`. Bespoke string-search would have produced 5
        // (the payee substring and the account-name substring
        // would have been mutated alongside, corrupting unrelated
        // text as the user typed).
        assert_eq!(
            ranges.ranges.len(),
            3,
            "expected 3 linked-edit ranges, got {}: {:#?}",
            ranges.ranges.len(),
            ranges.ranges
        );
    }
}
