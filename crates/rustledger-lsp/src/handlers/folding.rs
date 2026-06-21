//! Folding ranges handler for collapsible regions.
//!
//! Provides folding ranges for:
//! - Multi-line transactions (with postings)
//! - Sections marked by comments (e.g., "; === Section ===")
//! - Consecutive directives of the same type

use lsp_types::{FoldingRange, FoldingRangeKind, FoldingRangeParams};
use rustledger_core::Directive;
use rustledger_parser::ParseResult;

use super::utils::{LineIndex, PositionEncoding, trim_span_end};

/// Handle a folding range request.
pub fn handle_folding_ranges(
    _params: &FoldingRangeParams,
    source: &str,
    parse_result: &ParseResult,
    encoding: PositionEncoding,
) -> Option<Vec<FoldingRange>> {
    let mut ranges = Vec::new();

    // Build line index once for O(log n) lookups
    let line_index = LineIndex::new(source, encoding);

    // Add folding ranges for transactions (multi-line)
    for spanned in &parse_result.directives {
        if let Directive::Transaction(txn) = &spanned.value
            && !txn.postings.is_empty()
        {
            let (start_line, _) = line_index.offset_to_position(spanned.span.start);
            // Trim the span end so the fold doesn't swallow trailing blank
            // lines and the next directive's header (which made folds overlap).
            let (end_line, _) =
                line_index.offset_to_position(trim_span_end(source, spanned.span.end));

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
    let date = txn.date.to_string();

    if let Some(ref payee) = txn.payee {
        format!("{} {} ...", date, payee)
    } else if !txn.narration.is_empty() {
        let narration = txn.narration.to_string();
        // Truncate by characters, not bytes: byte-slicing (`&narration[..30]`)
        // panics when byte 30 falls inside a multibyte UTF-8 char, e.g. Korean
        // (3 bytes/char) — issue #1415.
        let truncated = if narration.chars().count() > 30 {
            let prefix: String = narration.chars().take(30).collect();
            format!("{prefix}...")
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

    /// Regression for #1415: folding must not panic on a non-ASCII narration
    /// longer than the 30-char truncation threshold. The old code byte-sliced
    /// `&narration[..30]`, which panics when byte 30 falls inside a multibyte
    /// UTF-8 char (e.g. Korean, 3 bytes/char).
    #[test]
    fn folding_long_non_ascii_narration_does_not_panic() {
        // 26 ASCII chars then Korean, so byte 30 lands inside a 3-byte char.
        let narration = "aaaaaaaaaaaaaaaaaaaaaaaaaa가나다라마바사";
        // The exact condition the old byte-slice violated.
        assert!(!narration.is_char_boundary(30));
        assert!(narration.chars().count() > 30);

        let source =
            format!("2024-01-15 * \"{narration}\"\n  Assets:Bank  -5.00 USD\n  Expenses:Food\n");
        let result = parse(&source);
        let params = FoldingRangeParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        // Must not panic, and the collapsed summary truncates on a char boundary.
        let ranges =
            handle_folding_ranges(&params, &source, &result, PositionEncoding::Utf16).unwrap();
        let txn_fold = ranges
            .iter()
            .find(|r| r.start_line == 0)
            .expect("transaction fold range");
        let collapsed = txn_fold.collapsed_text.as_ref().expect("collapsed summary");
        assert!(collapsed.ends_with("..."), "got: {collapsed}");
    }

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

        let ranges = handle_folding_ranges(&params, source, &result, PositionEncoding::Utf16);
        assert!(ranges.is_some());

        let ranges = ranges.unwrap();
        assert!(!ranges.is_empty());

        // Transaction should fold from line 0 to line 2
        let txn_fold = ranges.iter().find(|r| r.start_line == 0);
        assert!(txn_fold.is_some());
    }

    #[test]
    fn test_folding_does_not_overshoot_into_next_directive() {
        // Two transactions separated by blank lines. The first fold must end at
        // its last posting (line 2), NOT extend across the blanks into T2's
        // header (line 5) — which would make folds overlap and hide T2.
        let source = "2024-01-15 * \"T1\"\n  Assets:Bank  -5 USD\n  Expenses:Food  5 USD\n\n\n2024-01-20 * \"T2\"\n  Assets:Bank  -3 USD\n  Expenses:Food  3 USD\n";
        let result = parse(source);
        assert!(result.errors.is_empty(), "no parse errors");
        let params = FoldingRangeParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };
        let ranges =
            handle_folding_ranges(&params, source, &result, PositionEncoding::Utf16).unwrap();
        let t1 = ranges.iter().find(|r| r.start_line == 0).expect("T1 fold");
        assert_eq!(
            t1.end_line, 2,
            "T1 fold must end at its last posting, not overshoot"
        );
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
