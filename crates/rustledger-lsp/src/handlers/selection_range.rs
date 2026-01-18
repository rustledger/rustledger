//! Selection range handler for smart selection expansion.
//!
//! Provides hierarchical selection ranges for:
//! - Word -> Account segment -> Full account -> Posting -> Transaction
//! - Word -> Amount -> Posting -> Transaction

use lsp_types::{Position, Range, SelectionRange, SelectionRangeParams};
use rustledger_core::Directive;
use rustledger_parser::ParseResult;

use super::utils::{is_word_char, LineIndex};

/// Handle a selection range request.
pub fn handle_selection_range(
    params: &SelectionRangeParams,
    source: &str,
    parse_result: &ParseResult,
) -> Option<Vec<SelectionRange>> {
    let line_index = LineIndex::new(source);
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
    let line = lines.get(position.line as usize)?;
    let col = position.character as usize;

    // First, find the word at cursor
    let word_range = get_word_range(line, col, position.line);

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
            // Check if we're in a posting
            let (dir_start_line, _) = (dir_range.start.line, dir_range.start.character);

            for (i, posting) in txn.postings.iter().enumerate() {
                let posting_line = dir_start_line + 1 + i as u32;

                if position.line == posting_line {
                    // We're in a posting line
                    let posting_range = Range {
                        start: Position::new(posting_line, 0),
                        end: Position::new(
                            posting_line,
                            lines
                                .get(posting_line as usize)
                                .map(|l| l.len())
                                .unwrap_or(0) as u32,
                        ),
                    };

                    // Check if cursor is on account
                    let account_str = posting.account.to_string();
                    if let Some(account_range) =
                        find_account_range(line, &account_str, position.line)
                    {
                        // Word -> Account segment -> Full account -> Posting -> Transaction
                        let segment_range = get_account_segment_range(line, col, position.line);

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

/// Get the range of the word at a position.
fn get_word_range(line: &str, col: usize, line_num: u32) -> Option<Range> {
    if col > line.len() {
        return None;
    }

    let chars: Vec<char> = line.chars().collect();

    // Find word start
    let mut start = col;
    while start > 0 && is_word_char(chars.get(start - 1).copied().unwrap_or(' ')) {
        start -= 1;
    }

    // Find word end
    let mut end = col;
    while end < chars.len() && is_word_char(chars[end]) {
        end += 1;
    }

    if start == end {
        return None;
    }

    Some(Range {
        start: Position::new(line_num, start as u32),
        end: Position::new(line_num, end as u32),
    })
}

/// Get the range of an account segment (between colons).
fn get_account_segment_range(line: &str, col: usize, line_num: u32) -> Option<Range> {
    if col > line.len() {
        return None;
    }

    let chars: Vec<char> = line.chars().collect();

    // Find segment start (stop at colon or whitespace)
    let mut start = col;
    while start > 0 {
        let c = chars.get(start - 1).copied().unwrap_or(' ');
        if c == ':' || c.is_whitespace() {
            break;
        }
        start -= 1;
    }

    // Find segment end (stop at colon or whitespace)
    let mut end = col;
    while end < chars.len() {
        let c = chars[end];
        if c == ':' || c.is_whitespace() {
            break;
        }
        end += 1;
    }

    if start == end {
        return None;
    }

    Some(Range {
        start: Position::new(line_num, start as u32),
        end: Position::new(line_num, end as u32),
    })
}

/// Find the range of an account in a line.
fn find_account_range(line: &str, account: &str, line_num: u32) -> Option<Range> {
    let pos = line.find(account)?;
    Some(Range {
        start: Position::new(line_num, pos as u32),
        end: Position::new(line_num, (pos + account.len()) as u32),
    })
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

        let ranges = handle_selection_range(&params, source, &result);
        assert!(ranges.is_some());

        let ranges = ranges.unwrap();
        assert_eq!(ranges.len(), 1);

        // Should have nested ranges
        let range = &ranges[0];
        assert!(range.parent.is_some()); // Has parent (should be account or posting)
    }

    #[test]
    fn test_get_word_range() {
        let line = "  Assets:Bank  -5.00 USD";
        let range = get_word_range(line, 10, 0);
        assert!(range.is_some());

        let range = range.unwrap();
        assert_eq!(range.start.character, 2);
        assert_eq!(range.end.character, 13); // "Assets:Bank"
    }
}
