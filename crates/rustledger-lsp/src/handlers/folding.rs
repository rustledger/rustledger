//! Folding ranges handler for collapsible regions.
//!
//! Provides folding ranges for:
//! - Multi-line transactions (with postings)
//! - Sections marked by comments (e.g., "; === Section ===")
//! - Consecutive directives of the same type

use lsp_types::{FoldingRange, FoldingRangeKind, FoldingRangeParams};
use rustledger_core::Directive;
use rustledger_parser::ParseResult;

use super::utils::LineIndex;

/// Handle a folding range request.
pub fn handle_folding_ranges(
    _params: &FoldingRangeParams,
    source: &str,
    parse_result: &ParseResult,
) -> Option<Vec<FoldingRange>> {
    let mut ranges = Vec::new();

    // Build line index once for O(log n) lookups
    let line_index = LineIndex::new(source);

    // Add folding ranges for transactions (multi-line)
    for spanned in &parse_result.directives {
        if let Directive::Transaction(txn) = &spanned.value
            && !txn.postings.is_empty()
        {
            let (start_line, _) = line_index.offset_to_position(spanned.span.start);
            let (end_line, _) = line_index.offset_to_position(spanned.span.end);

            // Only fold if spans multiple lines
            if end_line > start_line {
                ranges.push(FoldingRange {
                    start_line,
                    start_character: None,
                    end_line,
                    end_character: None,
                    kind: Some(FoldingRangeKind::Region),
                    collapsed_text: Some(format_transaction_summary(txn)),
                });
            }
        }
    }

    // Add folding ranges for comment sections
    let lines: Vec<&str> = source.lines().collect();
    let mut section_start: Option<(u32, &str)> = None;

    for (line_num, line) in lines.iter().enumerate() {
        let trimmed = line.trim();

        // Check for section headers (e.g., "; === Section ===" or ";; Section")
        if is_section_header(trimmed) {
            // End previous section
            if let Some((start, _title)) = section_start
                && line_num as u32 > start + 1
            {
                ranges.push(FoldingRange {
                    start_line: start,
                    start_character: None,
                    end_line: line_num as u32 - 1,
                    end_character: None,
                    kind: Some(FoldingRangeKind::Region),
                    collapsed_text: None,
                });
            }
            section_start = Some((line_num as u32, trimmed));
        }
    }

    // Close final section
    if let Some((start, _title)) = section_start {
        let end = lines.len() as u32;
        if end > start + 1 {
            ranges.push(FoldingRange {
                start_line: start,
                start_character: None,
                end_line: end - 1,
                end_character: None,
                kind: Some(FoldingRangeKind::Region),
                collapsed_text: None,
            });
        }
    }

    // Add folding ranges for consecutive comment blocks
    let mut comment_start: Option<u32> = None;
    for (line_num, line) in lines.iter().enumerate() {
        let trimmed = line.trim();

        if trimmed.starts_with(';') && !is_section_header(trimmed) {
            if comment_start.is_none() {
                comment_start = Some(line_num as u32);
            }
        } else if let Some(start) = comment_start {
            let end = line_num as u32 - 1;
            if end > start + 2 {
                // Only fold if 3+ comment lines
                ranges.push(FoldingRange {
                    start_line: start,
                    start_character: None,
                    end_line: end,
                    end_character: None,
                    kind: Some(FoldingRangeKind::Comment),
                    collapsed_text: None,
                });
            }
            comment_start = None;
        }
    }

    // Sort and deduplicate
    ranges.sort_by_key(|a| a.start_line);
    ranges.dedup_by(|a, b| a.start_line == b.start_line && a.end_line == b.end_line);

    if ranges.is_empty() {
        None
    } else {
        Some(ranges)
    }
}

/// Format a transaction summary for collapsed text.
fn format_transaction_summary(txn: &rustledger_core::Transaction) -> String {
    let date = txn.date.format("%Y-%m-%d");

    if let Some(ref payee) = txn.payee {
        format!("{} {} ...", date, payee)
    } else if !txn.narration.is_empty() {
        let narration = txn.narration.to_string();
        let truncated = if narration.len() > 30 {
            format!("{}...", &narration[..30])
        } else {
            narration
        };
        format!("{} {} ...", date, truncated)
    } else {
        format!("{} Transaction ({} postings)", date, txn.postings.len())
    }
}

/// Check if a line is a section header comment.
fn is_section_header(line: &str) -> bool {
    // Match patterns like:
    // ; === Section ===
    // ;; Section
    // ; --- Section ---
    // ; ### Section
    if !line.starts_with(';') {
        return false;
    }

    let content = line.trim_start_matches(';').trim();

    // Check for decorated headers
    content.starts_with("===")
        || content.starts_with("---")
        || content.starts_with("###")
        || content.starts_with("***")
        || (content.len() > 3 && content.chars().take(3).all(|c| c == '='))
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    #[test]
    fn test_folding_transaction() {
        let source = r#"2024-01-15 * "Coffee Shop" "Morning coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food
"#;
        let result = parse(source);
        let params = FoldingRangeParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let ranges = handle_folding_ranges(&params, source, &result);
        assert!(ranges.is_some());

        let ranges = ranges.unwrap();
        assert!(!ranges.is_empty());

        // Transaction should fold from line 0 to line 2
        let txn_fold = ranges.iter().find(|r| r.start_line == 0);
        assert!(txn_fold.is_some());
    }

    #[test]
    fn test_is_section_header() {
        assert!(is_section_header("; === Expenses ==="));
        assert!(is_section_header("; --- Income ---"));
        assert!(is_section_header("; ### Assets"));
        assert!(!is_section_header("; Just a comment"));
        assert!(!is_section_header("2024-01-01 open Assets:Bank"));
    }
}
