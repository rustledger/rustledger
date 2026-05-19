//! Find references handler for locating all usages.
//!
//! Provides references for:
//! - Account names (all usages across directives)
//! - Currency names (all usages across directives)
//! - Payees (all transactions with same payee)

use super::utils::{LineIndex, get_word_at_position, is_account_like, is_currency_like};
use lsp_types::{Location, Position, Range, ReferenceParams, Uri};
use rustledger_core::{Directive, SYNTHESIZED_FILE_ID};
use rustledger_parser::ParseResult;

/// Handle a find references request.
pub fn handle_references(
    params: &ReferenceParams,
    source: &str,
    parse_result: &ParseResult,
    uri: &Uri,
) -> Option<Vec<Location>> {
    let position = params.text_document_position.position;
    let include_declaration = params.context.include_declaration;

    let line_idx = position.line as usize;
    let lines: Vec<&str> = source.lines().collect();
    let line = lines.get(line_idx)?;

    // Get the word at the cursor position
    let (word, _, _) = get_word_at_position(line, position.character as usize)?;

    let mut locations = Vec::new();
    // Build the line index once and share it across collectors —
    // otherwise each posting/directive lookup is an O(n) scan.
    let line_index = LineIndex::new(source);

    // Check if it's an account
    if is_account_like(&word) {
        collect_account_references(
            source,
            parse_result,
            &line_index,
            &word,
            uri,
            include_declaration,
            &mut locations,
        );
    }
    // Check if it's a currency
    else if is_currency_like(&word, parse_result) {
        collect_currency_references(
            source,
            parse_result,
            &line_index,
            &word,
            uri,
            include_declaration,
            &mut locations,
        );
    }
    // Check if it's a payee (inside quotes on a transaction line)
    else if is_in_quotes(line, position.character as usize) {
        collect_payee_references(
            source,
            parse_result,
            &line_index,
            &word,
            uri,
            &mut locations,
        );
    }

    if locations.is_empty() {
        None
    } else {
        Some(locations)
    }
}

/// Collect all references to an account.
fn collect_account_references(
    source: &str,
    parse_result: &ParseResult,
    line_index: &LineIndex,
    account: &str,
    uri: &Uri,
    include_declaration: bool,
    locations: &mut Vec<Location>,
) {
    for spanned in &parse_result.directives {
        match &spanned.value {
            Directive::Open(open) => {
                if open.account.as_ref() == account
                    && include_declaration
                    && let Some(loc) = find_in_directive(
                        source,
                        line_index,
                        spanned.span.start,
                        spanned.span.end,
                        account,
                        uri,
                    )
                {
                    locations.push(loc);
                }
            }
            Directive::Close(close) => {
                if close.account.as_ref() == account
                    && let Some(loc) = find_in_directive(
                        source,
                        line_index,
                        spanned.span.start,
                        spanned.span.end,
                        account,
                        uri,
                    )
                {
                    locations.push(loc);
                }
            }
            Directive::Balance(bal) => {
                if bal.account.as_ref() == account
                    && let Some(loc) = find_in_directive(
                        source,
                        line_index,
                        spanned.span.start,
                        spanned.span.end,
                        account,
                        uri,
                    )
                {
                    locations.push(loc);
                }
            }
            Directive::Pad(pad) => {
                if pad.account.as_ref() == account
                    && let Some(loc) = find_in_directive(
                        source,
                        line_index,
                        spanned.span.start,
                        spanned.span.end,
                        account,
                        uri,
                    )
                {
                    locations.push(loc);
                }
                if pad.source_account.as_ref() == account {
                    // Find the second account mention
                    let directive_text = &source[spanned.span.start..spanned.span.end];
                    if let Some(first_pos) = directive_text.find(account) {
                        let after_first = first_pos + account.len();
                        if let Some(second_pos) = directive_text[after_first..].find(account) {
                            let actual_pos = after_first + second_pos;
                            let (line, _) = line_index.offset_to_position(spanned.span.start);
                            locations.push(Location {
                                uri: uri.clone(),
                                range: Range {
                                    start: Position::new(line, actual_pos as u32),
                                    end: Position::new(line, (actual_pos + account.len()) as u32),
                                },
                            });
                        }
                    }
                }
            }
            Directive::Note(note) => {
                if note.account.as_ref() == account
                    && let Some(loc) = find_in_directive(
                        source,
                        line_index,
                        spanned.span.start,
                        spanned.span.end,
                        account,
                        uri,
                    )
                {
                    locations.push(loc);
                }
            }
            Directive::Document(doc) => {
                if doc.account.as_ref() == account
                    && let Some(loc) = find_in_directive(
                        source,
                        line_index,
                        spanned.span.start,
                        spanned.span.end,
                        account,
                        uri,
                    )
                {
                    locations.push(loc);
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
                        if let Some(line_text) = source.lines().nth(posting_line as usize)
                            && let Some(col) = line_text.find(account)
                        {
                            locations.push(Location {
                                uri: uri.clone(),
                                range: Range {
                                    start: Position::new(posting_line, col as u32),
                                    end: Position::new(posting_line, (col + account.len()) as u32),
                                },
                            });
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

/// Collect all references to a currency.
fn collect_currency_references(
    source: &str,
    parse_result: &ParseResult,
    line_index: &LineIndex,
    currency: &str,
    uri: &Uri,
    include_declaration: bool,
    locations: &mut Vec<Location>,
) {
    for spanned in &parse_result.directives {
        let directive_text = &source[spanned.span.start..spanned.span.end];
        let (start_line, _) = line_index.offset_to_position(spanned.span.start);

        // Check if directive contains this currency
        let is_declaration =
            matches!(&spanned.value, Directive::Commodity(c) if c.currency.as_ref() == currency);

        if is_declaration && !include_declaration {
            continue;
        }

        // Find all occurrences of the currency in this directive
        for (line_offset, line) in directive_text.lines().enumerate() {
            let mut search_start = 0;
            while let Some(pos) = line[search_start..].find(currency) {
                let actual_pos = search_start + pos;

                // Verify it's a word boundary
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
                    locations.push(Location {
                        uri: uri.clone(),
                        range: Range {
                            start: Position::new(ref_line, actual_pos as u32),
                            end: Position::new(ref_line, (actual_pos + currency.len()) as u32),
                        },
                    });
                }

                search_start = actual_pos + currency.len();
            }
        }
    }

    // Deduplicate by range
    locations.sort_by(|a, b| {
        a.range
            .start
            .line
            .cmp(&b.range.start.line)
            .then(a.range.start.character.cmp(&b.range.start.character))
    });
    locations.dedup_by(|a, b| a.range == b.range);
}

/// Collect all references to a payee.
fn collect_payee_references(
    source: &str,
    parse_result: &ParseResult,
    line_index: &LineIndex,
    payee: &str,
    uri: &Uri,
    locations: &mut Vec<Location>,
) {
    for spanned in &parse_result.directives {
        if let Directive::Transaction(txn) = &spanned.value
            && let Some(ref txn_payee) = txn.payee
            && txn_payee.as_ref() == payee
        {
            let (line, _) = line_index.offset_to_position(spanned.span.start);
            let line_text = source.lines().nth(line as usize).unwrap_or("");

            // Find the payee in quotes
            if let Some(start) = line_text.find(&format!("\"{}\"", payee)) {
                locations.push(Location {
                    uri: uri.clone(),
                    range: Range {
                        start: Position::new(line, (start + 1) as u32),
                        end: Position::new(line, (start + 1 + payee.len()) as u32),
                    },
                });
            }
        }
    }
}

/// Find a string in a directive and create a location.
fn find_in_directive(
    source: &str,
    line_index: &LineIndex,
    start_offset: usize,
    end_offset: usize,
    needle: &str,
    uri: &Uri,
) -> Option<Location> {
    let directive_text = &source[start_offset..end_offset];
    let (start_line, start_col) = line_index.offset_to_position(start_offset);

    for (line_offset, line) in directive_text.lines().enumerate() {
        if let Some(col) = line.find(needle) {
            let ref_line = start_line + line_offset as u32;
            let ref_col = if line_offset == 0 {
                start_col + col as u32
            } else {
                col as u32
            };

            return Some(Location {
                uri: uri.clone(),
                range: Range {
                    start: Position::new(ref_line, ref_col),
                    end: Position::new(ref_line, ref_col + needle.len() as u32),
                },
            });
        }
    }

    None
}

/// Check if position is inside quotes.
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
    fn test_find_account_references() {
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food
2024-01-31 balance Assets:Bank 100 USD
"#;
        let result = parse(source);
        let uri: Uri = "file:///test.beancount".parse().unwrap();

        let params = ReferenceParams {
            text_document_position: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier { uri: uri.clone() },
                position: Position::new(0, 16), // On "Assets:Bank"
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
            context: lsp_types::ReferenceContext {
                include_declaration: true,
            },
        };

        let refs = handle_references(&params, source, &result, &uri);
        assert!(refs.is_some());

        let refs = refs.unwrap();
        // Should find: open, posting, balance = 3 references
        assert_eq!(refs.len(), 3);
    }

    #[test]
    fn test_find_currency_references() {
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food  5.00 USD
"#;
        let result = parse(source);
        let uri: Uri = "file:///test.beancount".parse().unwrap();

        let params = ReferenceParams {
            text_document_position: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier { uri: uri.clone() },
                position: Position::new(0, 28), // On "USD"
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
            context: lsp_types::ReferenceContext {
                include_declaration: true,
            },
        };

        let refs = handle_references(&params, source, &result, &uri);
        assert!(refs.is_some());

        let refs = refs.unwrap();
        // Should find USD in: open, posting 1, posting 2 = 3 references
        assert_eq!(refs.len(), 3);
    }

    /// Regression test for the read-only sibling of #1142.
    ///
    /// Pre-fix, the reference range for the second posting landed on
    /// the metadata line between postings. With per-posting span
    /// lookup, every reference points at its actual posting line.
    #[test]
    fn test_find_account_references_with_interleaved_metadata_1142() {
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

        let uri: Uri = "file:///test.beancount".parse().unwrap();
        let params = ReferenceParams {
            text_document_position: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier { uri: uri.clone() },
                position: Position::new(0, 16), // on "Assets:Bank" in open
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
            context: lsp_types::ReferenceContext {
                include_declaration: true,
            },
        };

        let refs = handle_references(&params, source, &result, &uri)
            .expect("at least the Open definition + 1 posting reference");

        let metadata_lines = [3u32, 5u32];
        for r in &refs {
            assert!(
                !metadata_lines.contains(&r.range.start.line),
                "reference range landed on a metadata line: {r:?}"
            );
        }
        // The Assets:Bank posting is on line 2 (the second posting,
        // Expenses:Food, is on line 4 and isn't a reference to
        // Assets:Bank, so we only verify the positive lines we expect).
        let lines: Vec<u32> = refs.iter().map(|r| r.range.start.line).collect();
        assert!(
            lines.contains(&2),
            "Assets:Bank posting on line 2 should appear in refs; got {lines:?}"
        );
    }
}
