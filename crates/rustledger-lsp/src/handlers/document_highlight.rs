//! Document highlight handler for highlighting all occurrences.
//!
//! Highlights all occurrences of the symbol under the cursor:
//! - Account names (all usages)
//! - Currency names (all usages)
//! - Payees (all transactions with same payee)

use lsp_types::{
    DocumentHighlight, DocumentHighlightKind, DocumentHighlightParams, Position, Range,
};
use rustledger_core::Directive;
use rustledger_parser::ParseResult;

use super::utils::{
    LineIndex, PositionEncoding, account_declaration_spans, commodity_declaration_spans,
    get_word_at_position, is_account_like, is_currency_like,
};

/// Handle a document highlight request.
pub fn handle_document_highlight(
    params: &DocumentHighlightParams,
    source: &str,
    parse_result: &ParseResult,
    encoding: PositionEncoding,
) -> Option<Vec<DocumentHighlight>> {
    let position = params.text_document_position_params.position;
    let line_idx = position.line as usize;
    let lines: Vec<&str> = source.lines().collect();
    let line = lines.get(line_idx)?;

    // Get the word at the cursor position
    let (word, _, _) = get_word_at_position(line, position.character as usize, encoding)?;

    let mut highlights = Vec::new();
    // Build the line index once and share it across collectors: each
    // directive (and posting) used to trigger an O(n) byte→line scan,
    // which scales quadratically on large files.
    let line_index = LineIndex::new(source, encoding);

    // Check if it's an account
    if is_account_like(&word) {
        collect_account_highlights(parse_result, &line_index, &word, &mut highlights);
    }
    // Check if it's a currency
    else if is_currency_like(&word, parse_result) {
        collect_currency_highlights(parse_result, &line_index, &word, &mut highlights);
    }
    // Check if it's a payee (inside quotes)
    else if is_in_quotes(line, position.character as usize) {
        collect_payee_highlights(parse_result, &line_index, &word, &mut highlights);
    }

    if highlights.is_empty() {
        None
    } else {
        Some(highlights)
    }
}

/// Collect all highlights for an account.
///
/// Walks the parser's `account_occurrences` index (every `ACCOUNT`
/// token with exact source spans). Occurrences whose span equals
/// an `Open` or `Close` directive's declared-account span (per
/// [`account_declaration_spans`]) surface as `WRITE` — both
/// directives are lifecycle-boundary "declarations" in the LSP
/// sense, matching the legacy pre-#1262-phase-5.5 substring-search
/// implementation. All other occurrences (balance / pad / note /
/// document / posting / ACCOUNT-typed metadata) surface as
/// `READ`. Same shape as `collect_currency_highlights`. The
/// previous shape walked the typed directives and ran substring
/// searches, producing false-positive highlights for any account-
/// name fragment appearing in a payee string, STRING-typed
/// metadata value, or comment.
fn collect_account_highlights(
    parse_result: &ParseResult,
    line_index: &LineIndex,
    account: &str,
    highlights: &mut Vec<DocumentHighlight>,
) {
    let declaration_spans = account_declaration_spans(parse_result);

    for occurrence in &parse_result.account_occurrences {
        if occurrence.value != account {
            continue;
        }
        let (start_line, start_col) = line_index.offset_to_position(occurrence.span.start);
        let (end_line, end_col) = line_index.offset_to_position(occurrence.span.end);
        let is_declaration = declaration_spans.contains(&occurrence.span);
        highlights.push(DocumentHighlight {
            range: Range {
                start: Position::new(start_line, start_col),
                end: Position::new(end_line, end_col),
            },
            kind: Some(if is_declaration {
                DocumentHighlightKind::WRITE
            } else {
                DocumentHighlightKind::READ
            }),
        });
    }

    highlights.sort_by(|a, b| {
        a.range
            .start
            .line
            .cmp(&b.range.start.line)
            .then(a.range.start.character.cmp(&b.range.start.character))
    });
    highlights.dedup_by(|a, b| a.range == b.range);
}

/// Collect all highlights for a currency.
///
/// Walks the parser's `currency_occurrences` index for exact spans;
/// see `rename.rs::collect_currency_rename_edits` for the rationale.
///
/// Occurrences whose span equals a `Commodity`-declaration span
/// (see `commodity_declaration_spans` for the precise definition;
/// importantly, *not* just "any currency token inside a Commodity
/// directive span" — that would misclassify metadata-value currency
/// tokens as declarations) are surfaced as `WRITE`, all others as
/// `READ`.
fn collect_currency_highlights(
    parse_result: &ParseResult,
    line_index: &LineIndex,
    currency: &str,
    highlights: &mut Vec<DocumentHighlight>,
) {
    let declaration_spans = commodity_declaration_spans(parse_result);

    for occurrence in &parse_result.currency_occurrences {
        if occurrence.value != currency {
            continue;
        }
        let (start_line, start_col) = line_index.offset_to_position(occurrence.span.start);
        let (end_line, end_col) = line_index.offset_to_position(occurrence.span.end);
        let is_declaration = declaration_spans.contains(&occurrence.span);
        highlights.push(DocumentHighlight {
            range: Range {
                start: Position::new(start_line, start_col),
                end: Position::new(end_line, end_col),
            },
            kind: Some(if is_declaration {
                DocumentHighlightKind::WRITE
            } else {
                DocumentHighlightKind::READ
            }),
        });
    }

    // Deduplicate by range.
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
            let line_text = line_index.line_text(line).unwrap_or("");

            if let Some(quote_byte) = line_text.find(&format!("\"{}\"", payee))
                && let Some(start) = line_index.byte_in_line_to_position(line, quote_byte + 1)
                && let Some(end) =
                    line_index.byte_in_line_to_position(line, quote_byte + 1 + payee.len())
            {
                highlights.push(DocumentHighlight {
                    range: Range { start, end },
                    kind: Some(DocumentHighlightKind::READ),
                });
            }
        }
    }
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

        let highlights =
            handle_document_highlight(&params, source, &result, PositionEncoding::Utf16);
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

        let highlights =
            handle_document_highlight(&params, source, &result, PositionEncoding::Utf16);
        assert!(highlights.is_some());

        let highlights = highlights.unwrap();
        // Should find USD in: open, posting 1, posting 2 = 3
        assert_eq!(highlights.len(), 3);
    }

    /// Regression test for currency-highlight false positives. See
    /// `rename.rs::test_rename_currency_no_false_positives` for the
    /// fuller rationale.
    #[test]
    fn test_highlight_currency_no_false_positives() {
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

        let params = DocumentHighlightParams {
            text_document_position_params: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier { uri },
                position: Position::new(1, 21), // on the `USD` of `commodity USD`
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let highlights =
            handle_document_highlight(&params, source, &result, PositionEncoding::Utf16)
                .expect("highlights returns Some");

        // Expected: 3 highlights — declaration + 2 postings. Bespoke
        // string-search would have produced 5 (payee + 2 account
        // substrings + 2 postings + 1 declaration ... and the
        // account-substring highlights would have visually
        // corrupted the rendered highlight overlay on screen).
        assert_eq!(
            highlights.len(),
            3,
            "expected 3 currency highlights, got {}: {highlights:#?}",
            highlights.len()
        );

        // Exactly one highlight should be WRITE (the commodity
        // declaration); the other two should be READ.
        let write_count = highlights
            .iter()
            .filter(|h| h.kind == Some(DocumentHighlightKind::WRITE))
            .count();
        assert_eq!(write_count, 1, "expected exactly one WRITE highlight");
    }

    /// Regression test for the metadata-currency misclassification
    /// bug (Copilot #3270930001). A `Currency`-typed metadata value
    /// inside a Commodity directive must not be classified as a
    /// declaration.
    #[test]
    fn test_currency_in_commodity_metadata_is_read_not_write() {
        let source = r#"2024-01-01 commodity USD
  parent: USD
2024-01-15 * "Coffee"
  Assets:Bank  -5.00 USD
"#;
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
                position: Position::new(0, 21), // on `USD` of `commodity USD`
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let highlights =
            handle_document_highlight(&params, source, &result, PositionEncoding::Utf16)
                .expect("highlights returns Some");

        // 3 highlights total: declaration + metadata reference + posting.
        assert_eq!(highlights.len(), 3, "{highlights:#?}");

        // Exactly ONE should be WRITE — the declaration on line 0.
        // A buggy containment-only check would also mark
        // `parent: USD` (line 1) as WRITE, giving us 2.
        let write_count = highlights
            .iter()
            .filter(|h| h.kind == Some(DocumentHighlightKind::WRITE))
            .count();
        assert_eq!(
            write_count, 1,
            "expected exactly one WRITE (the declaration); got {write_count} in {highlights:#?}"
        );
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

        let highlights =
            handle_document_highlight(&params, source, &result, PositionEncoding::Utf16)
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

    /// Regression test for account-highlight false positives -
    /// phase 5.5 of the CST migration (#1262). Same shape as
    /// `references::test_find_account_references_no_false_positives`.
    /// The CST-backed walk emits exactly two highlights (one WRITE
    /// for the Open, one READ for the posting); the substring-search
    /// shape would have produced 5 (including phantom highlights in
    /// the payee string, STRING-typed metadata value, and comment).
    #[test]
    fn test_highlight_account_no_false_positives() {
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-15 * "Assets:Bank transfer note"
  Assets:Bank  -5.00 USD
    memo: "moved Assets:Bank balance"
  Expenses:Food
; rebalanced Assets:Bank yesterday
"#;
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
                position: Position::new(0, 16), // on `Assets:Bank` of the open
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };
        let highlights =
            handle_document_highlight(&params, source, &result, PositionEncoding::Utf16)
                .expect("highlights returns Some");
        assert_eq!(
            highlights.len(),
            2,
            "expected 2 account highlights, got {}: {highlights:#?}",
            highlights.len()
        );
        // Pin source lines + kinds + widths so a future regression
        // that emits two zero-width ranges, both on the same line,
        // or with kinds swapped is caught.
        let summary: Vec<(u32, Option<DocumentHighlightKind>, u32)> = highlights
            .iter()
            .map(|h| {
                (
                    h.range.start.line,
                    h.kind,
                    h.range.end.character - h.range.start.character,
                )
            })
            .collect();
        assert_eq!(
            summary,
            vec![
                (0, Some(DocumentHighlightKind::WRITE), 11),
                (2, Some(DocumentHighlightKind::READ), 11),
            ],
            "expected line 0 WRITE + line 2 READ, both 11 cols wide, got {summary:?}"
        );
    }

    /// Phase-5.5 policy: a `Close` directive's account is a
    /// lifecycle-boundary declaration and surfaces as `WRITE`,
    /// matching the legacy pre-#1262-phase-5.5 substring-search
    /// behavior. This test pins the policy so a future change that
    /// reclassifies `Close` cannot silently flip the highlight
    /// kind seen by editors.
    #[test]
    fn test_highlight_account_close_is_write() {
        let source = "\
2024-01-01 open Assets:Bank USD
2024-06-15 * \"Coffee\"
  Assets:Bank  -5.00 USD
  Expenses:Food
2024-12-31 close Assets:Bank
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
                position: Position::new(0, 16), // on `Assets:Bank` of the open
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };
        let highlights =
            handle_document_highlight(&params, source, &result, PositionEncoding::Utf16)
                .expect("highlights returns Some");

        let by_line: Vec<(u32, Option<DocumentHighlightKind>)> = highlights
            .iter()
            .map(|h| (h.range.start.line, h.kind))
            .collect();
        assert_eq!(
            by_line,
            vec![
                (0, Some(DocumentHighlightKind::WRITE)), // open
                (2, Some(DocumentHighlightKind::READ)),  // posting
                (4, Some(DocumentHighlightKind::WRITE)), // close
            ],
            "expected open=WRITE, posting=READ, close=WRITE; got {by_line:?}"
        );
    }
}
