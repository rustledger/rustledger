//! Selection range handler for smart selection expansion.
//!
//! Provides hierarchical selection ranges for:
//! - Word -> Account segment -> Full account -> Posting -> Transaction
//! - Word -> Amount -> Posting -> Transaction

use lsp_types::{Position, Range, SelectionRange, SelectionRangeParams};
use rustledger_core::{Directive, SYNTHESIZED_FILE_ID};
use rustledger_parser::ParseResult;

use super::utils::{LineIndex, PositionEncoding, is_word_char};

/// Handle a selection range request.
pub fn handle_selection_range(
    params: &SelectionRangeParams,
    source: &str,
    parse_result: &ParseResult,
    encoding: PositionEncoding,
) -> Option<Vec<SelectionRange>> {
    let line_index = LineIndex::new(source, encoding);
    let mut results = Vec::new();

    for position in &params.positions {
        if let Some(range) = compute_selection_range(source, parse_result, &line_index, *position) {
            results.push(range);
        } else {
            // Return a simple range at the position if we can't compute anything
            results.push(SelectionRange {
                range: Range {
                    start: *position,
                    end: *position,
                },
                parent: None,
            });
        }
    }

    Some(results)
}

/// Compute the selection range hierarchy for a position.
fn compute_selection_range(
    source: &str,
    parse_result: &ParseResult,
    line_index: &LineIndex,
    position: Position,
) -> Option<SelectionRange> {
    let lines: Vec<&str> = source.lines().collect();
    let _line_text = lines.get(position.line as usize)?;
    let col = position.character as usize;

    // Word at cursor — interpreted via the LineIndex's encoding (the
    // `col` here is already in the negotiated encoding because it
    // came from `position.character`).
    let word_range = get_word_range(line_index, position.line, col);

    // Find the containing directive
    let mut containing_directive: Option<(Range, &Directive)> = None;

    for spanned in &parse_result.directives {
        let (start_line, start_col) = line_index.offset_to_position(spanned.span.start);
        let (end_line, end_col) = line_index.offset_to_position(spanned.span.end);

        let dir_range = Range {
            start: Position::new(start_line, start_col),
            end: Position::new(end_line, end_col),
        };

        if position.line >= start_line && position.line <= end_line {
            containing_directive = Some((dir_range, &spanned.value));
            break;
        }
    }

    // Build the selection hierarchy
    match containing_directive {
        Some((dir_range, Directive::Transaction(txn))) => {
            // Resolve each posting's line from its own span (see #1142):
            // the prior `dir_start_line + 1 + i` arithmetic broke
            // whenever a transaction had interleaved posting-level
            // metadata, putting the cursor-test on the wrong row.
            for spanned_posting in &txn.postings {
                if spanned_posting.file_id == SYNTHESIZED_FILE_ID {
                    continue;
                }
                let posting = &**spanned_posting;
                let (posting_line, _) = line_index.offset_to_position(spanned_posting.span.start);

                if position.line == posting_line {
                    // We're in a posting line. Build the posting
                    // range from (line, 0) to (line, end-of-line) —
                    // the end column comes from converting the
                    // line's byte length through line_index so it
                    // matches the negotiated encoding.
                    let posting_line_text = line_index.line_text(posting_line).unwrap_or("");
                    let posting_end = line_index
                        .byte_in_line_to_position(posting_line, posting_line_text.len())
                        .unwrap_or_else(|| Position::new(posting_line, 0));
                    let posting_range = Range {
                        start: Position::new(posting_line, 0),
                        end: posting_end,
                    };

                    // Check if cursor is on account
                    let account_str = posting.account.to_string();
                    if let Some(account_range) =
                        find_account_range(line_index, position.line, &account_str)
                    {
                        // Word -> Account segment -> Full account -> Posting -> Transaction
                        let segment_range =
                            get_account_segment_range(line_index, position.line, col);

                        return Some(build_hierarchy(vec![
                            word_range,
                            segment_range,
                            Some(account_range),
                            Some(posting_range),
                            Some(dir_range),
                        ]));
                    }

                    // Word -> Posting -> Transaction
                    return Some(build_hierarchy(vec![
                        word_range,
                        Some(posting_range),
                        Some(dir_range),
                    ]));
                }
            }

            // We're in the transaction header line
            // Word -> Transaction
            Some(build_hierarchy(vec![word_range, Some(dir_range)]))
        }
        Some((dir_range, _)) => {
            // Other directive types: Word -> Directive
            Some(build_hierarchy(vec![word_range, Some(dir_range)]))
        }
        None => {
            // Just return word range
            word_range.map(|r| SelectionRange {
                range: r,
                parent: None,
            })
        }
    }
}

/// Build a hierarchy of selection ranges from a list of ranges.
fn build_hierarchy(ranges: Vec<Option<Range>>) -> SelectionRange {
    let valid_ranges: Vec<Range> = ranges.into_iter().flatten().collect();

    if valid_ranges.is_empty() {
        return SelectionRange {
            range: Range {
                start: Position::new(0, 0),
                end: Position::new(0, 0),
            },
            parent: None,
        };
    }

    let mut result: Option<SelectionRange> = None;

    // Build from outermost to innermost
    for range in valid_ranges.into_iter().rev() {
        result = Some(SelectionRange {
            range,
            parent: result.map(Box::new),
        });
    }

    result.unwrap()
}

/// Get the range of the word at a (line, encoded col) position.
///
/// `encoded_col` is in the LineIndex's negotiated encoding (UTF-8
/// bytes or UTF-16 code units). The returned `Range` is also in the
/// negotiated encoding. Pre-round-19 treated `col` as a char index
/// and emitted columns by char count — wrong under either negotiated
/// encoding for non-ASCII content.
fn get_word_range(line_index: &LineIndex<'_>, line_num: u32, encoded_col: usize) -> Option<Range> {
    let line = line_index.line_text(line_num)?;
    // Map the encoded col to a byte offset within the line so we can
    // walk word boundaries by byte (is_word_char is well-defined on
    // chars; we iterate chars but track byte cursor).
    let line_start = line_index.line_start_byte(line_num)?;
    let cursor_byte = line_index
        .position_to_offset(line_num, encoded_col as u32)?
        .checked_sub(line_start)?;

    // Walk left from cursor until a non-word char (or start of line).
    let mut start_byte = cursor_byte;
    while let Some(prev_char_byte) = line[..start_byte].char_indices().next_back() {
        let (b, c) = prev_char_byte;
        if !is_word_char(c) {
            break;
        }
        start_byte = b;
    }
    // Walk right from cursor until a non-word char (or end of line).
    let mut end_byte = cursor_byte;
    for (b, c) in line[cursor_byte..].char_indices() {
        if !is_word_char(c) {
            break;
        }
        end_byte = cursor_byte + b + c.len_utf8();
    }

    if start_byte == end_byte {
        return None;
    }

    let start = line_index.byte_in_line_to_position(line_num, start_byte)?;
    let end = line_index.byte_in_line_to_position(line_num, end_byte)?;
    Some(Range { start, end })
}

/// Get the range of the account segment around `(line_num,
/// encoded_col)` — the text between adjacent colons or whitespace.
fn get_account_segment_range(
    line_index: &LineIndex<'_>,
    line_num: u32,
    encoded_col: usize,
) -> Option<Range> {
    let line = line_index.line_text(line_num)?;
    let line_start = line_index.line_start_byte(line_num)?;
    let cursor_byte = line_index
        .position_to_offset(line_num, encoded_col as u32)?
        .checked_sub(line_start)?;

    let mut start_byte = cursor_byte;
    while let Some((b, c)) = line[..start_byte].char_indices().next_back() {
        if c == ':' || c.is_whitespace() {
            break;
        }
        start_byte = b;
    }
    let mut end_byte = cursor_byte;
    for (b, c) in line[cursor_byte..].char_indices() {
        if c == ':' || c.is_whitespace() {
            break;
        }
        end_byte = cursor_byte + b + c.len_utf8();
    }

    if start_byte == end_byte {
        return None;
    }

    let start = line_index.byte_in_line_to_position(line_num, start_byte)?;
    let end = line_index.byte_in_line_to_position(line_num, end_byte)?;
    Some(Range { start, end })
}

/// Find the range of an account in a line — encoding-aware via the
/// LineIndex. Pre-round-19 emitted raw byte offsets as columns.
fn find_account_range(line_index: &LineIndex<'_>, line_num: u32, account: &str) -> Option<Range> {
    let line = line_index.line_text(line_num)?;
    let pos = line.find(account)?;
    let start = line_index.byte_in_line_to_position(line_num, pos)?;
    let end = line_index.byte_in_line_to_position(line_num, pos + account.len())?;
    Some(Range { start, end })
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    #[test]
    fn test_selection_range_in_transaction() {
        let source = r#"2024-01-15 * "Coffee Shop"
  Assets:Bank:Checking  -5.00 USD
  Expenses:Food
"#;
        let result = parse(source);
        let params = SelectionRangeParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            positions: vec![Position::new(1, 10)], // In "Bank" segment
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let ranges = handle_selection_range(&params, source, &result, PositionEncoding::Utf16);
        assert!(ranges.is_some());

        let ranges = ranges.unwrap();
        assert_eq!(ranges.len(), 1);

        // Should have nested ranges
        let range = &ranges[0];
        assert!(range.parent.is_some()); // Has parent (should be account or posting)
    }

    #[test]
    fn test_get_word_range() {
        let source = "  Assets:Bank  -5.00 USD\n";
        let line_index = LineIndex::new(source, PositionEncoding::Utf8);
        let range = get_word_range(&line_index, 0, 10);
        assert!(range.is_some());

        let range = range.unwrap();
        assert_eq!(range.start.character, 2);
        assert_eq!(range.end.character, 13); // "Assets:Bank"
    }
}
