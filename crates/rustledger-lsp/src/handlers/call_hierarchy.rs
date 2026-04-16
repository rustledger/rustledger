//! Call hierarchy handler for navigating account-transaction relationships.
//!
//! In beancount semantics:
//! - An account is like a "function"
//! - A transaction "calls" an account when it has a posting to that account
//! - Incoming calls: transactions that post TO this account
//! - Outgoing calls: from a transaction, the other accounts it touches

use lsp_types::{
    CallHierarchyIncomingCall, CallHierarchyIncomingCallsParams, CallHierarchyItem,
    CallHierarchyOutgoingCall, CallHierarchyOutgoingCallsParams, CallHierarchyPrepareParams,
    Position, Range, SymbolKind, Uri,
};
use rustledger_core::Directive;
use rustledger_parser::ParseResult;
use std::collections::HashMap;

use super::utils::{byte_offset_to_position, get_word_at_position, is_account_like};

/// Handle a prepare call hierarchy request.
/// Returns the account at the cursor position as a CallHierarchyItem.
pub fn handle_prepare_call_hierarchy(
    params: &CallHierarchyPrepareParams,
    source: &str,
    parse_result: &ParseResult,
    uri: &Uri,
) -> Option<Vec<CallHierarchyItem>> {
    let position = params.text_document_position_params.position;
    let line_idx = position.line as usize;
    let lines: Vec<&str> = source.lines().collect();
    let line = lines.get(line_idx)?;

    // Get the word at the cursor position
    let (word, start, end) = get_word_at_position(line, position.character as usize)?;

    // Check if it's an account
    if !is_account_like(&word) {
        return None;
    }

    // Verify the account exists in the parse result
    if !account_exists(&word, parse_result) {
        return None;
    }

    let item = CallHierarchyItem {
        name: word.clone(),
        kind: SymbolKind::FUNCTION, // Use Function for "callable" semantics
        tags: None,
        detail: Some("Account".to_string()),
        uri: uri.clone(),
        range: Range {
            start: Position::new(position.line, start as u32),
            end: Position::new(position.line, end as u32),
        },
        selection_range: Range {
            start: Position::new(position.line, start as u32),
            end: Position::new(position.line, end as u32),
        },
        data: Some(serde_json::json!({ "account": word })),
    };

    Some(vec![item])
}

/// Handle incoming calls request.
/// Returns all transactions that post to this account.
pub fn handle_incoming_calls(
    params: &CallHierarchyIncomingCallsParams,
    source: &str,
    parse_result: &ParseResult,
    uri: &Uri,
) -> Option<Vec<CallHierarchyIncomingCall>> {
    let account = params
        .item
        .data
        .as_ref()
        .and_then(|v| v.get("account"))
        .and_then(|v| v.as_str())
        .unwrap_or(&params.item.name);

    let mut calls: Vec<CallHierarchyIncomingCall> = Vec::new();

    // Find all transactions that reference this account
    for spanned in &parse_result.directives {
        if let Directive::Transaction(txn) = &spanned.value {
            let posting_indices: Vec<usize> = txn
                .postings
                .iter()
                .enumerate()
                .filter(|(_, p)| p.account.as_ref() == account)
                .map(|(i, _)| i)
                .collect();

            if posting_indices.is_empty() {
                continue;
            }

            // Get transaction location
            let (txn_line, _) = byte_offset_to_position(source, spanned.span.start);

            // Build transaction description
            let description = format!("{} {} \"{}\"", txn.date, txn.flag, txn.narration.as_ref());

            // Find the ranges where this account appears in the transaction
            let from_ranges: Vec<Range> = posting_indices
                .iter()
                .filter_map(|&idx| {
                    let posting_line = txn_line + 1 + idx as u32;
                    let line_text = source.lines().nth(posting_line as usize)?;
                    let col = line_text.find(account)?;
                    Some(Range {
                        start: Position::new(posting_line, col as u32),
                        end: Position::new(posting_line, (col + account.len()) as u32),
                    })
                })
                .collect();

            if from_ranges.is_empty() {
                continue;
            }

            let txn_item = CallHierarchyItem {
                name: description,
                kind: SymbolKind::EVENT, // Use Event for transactions
                tags: None,
                detail: Some(format!("{} postings", txn.postings.len())),
                uri: uri.clone(),
                range: Range {
                    start: Position::new(txn_line, 0),
                    end: Position::new(txn_line + txn.postings.len() as u32 + 1, 0),
                },
                selection_range: Range {
                    start: Position::new(txn_line, 0),
                    end: Position::new(txn_line, 10), // Just the date portion
                },
                data: Some(serde_json::json!({
                    "type": "transaction",
                    "line": txn_line
                })),
            };

            calls.push(CallHierarchyIncomingCall {
                from: txn_item,
                from_ranges,
            });
        }
    }

    if calls.is_empty() { None } else { Some(calls) }
}

/// Handle outgoing calls request.
/// For an account: returns nothing (accounts don't "call" other things).
/// For a transaction (identified by data): returns all accounts it posts to.
pub fn handle_outgoing_calls(
    params: &CallHierarchyOutgoingCallsParams,
    source: &str,
    parse_result: &ParseResult,
    uri: &Uri,
) -> Option<Vec<CallHierarchyOutgoingCall>> {
    // Check if this is a transaction
    let data = params.item.data.as_ref()?;
    let item_type = data.get("type").and_then(|v| v.as_str())?;

    if item_type != "transaction" {
        // Accounts don't have outgoing calls
        return None;
    }

    let txn_line = data.get("line").and_then(|v| v.as_u64())? as u32;

    // Find the transaction at this line
    for spanned in &parse_result.directives {
        if let Directive::Transaction(txn) = &spanned.value {
            let (line, _) = byte_offset_to_position(source, spanned.span.start);

            if line != txn_line {
                continue;
            }

            // Collect unique accounts from postings
            let mut account_postings: HashMap<String, Vec<usize>> = HashMap::new();

            for (idx, posting) in txn.postings.iter().enumerate() {
                let account = posting.account.to_string();
                account_postings.entry(account).or_default().push(idx);
            }

            let calls: Vec<CallHierarchyOutgoingCall> = account_postings
                .into_iter()
                .filter_map(|(account, indices)| {
                    // Find where this account is defined (open directive)
                    let account_location = find_account_definition(source, parse_result, &account);
                    let (_acc_line, acc_range) = match account_location {
                        Some(loc) => loc,
                        None => {
                            // Fallback: use first posting location
                            let posting_line = line + 1 + indices[0] as u32;
                            let line_text = source.lines().nth(posting_line as usize)?;
                            let col = line_text.find(&account)?;
                            (
                                posting_line,
                                Range {
                                    start: Position::new(posting_line, col as u32),
                                    end: Position::new(posting_line, (col + account.len()) as u32),
                                },
                            )
                        }
                    };

                    // Ranges where this account is "called" from the transaction
                    let from_ranges: Vec<Range> = indices
                        .iter()
                        .filter_map(|&idx| {
                            let posting_line = line + 1 + idx as u32;
                            let line_text = source.lines().nth(posting_line as usize)?;
                            let col = line_text.find(&account)?;
                            Some(Range {
                                start: Position::new(posting_line, col as u32),
                                end: Position::new(posting_line, (col + account.len()) as u32),
                            })
                        })
                        .collect();

                    let account_item = CallHierarchyItem {
                        name: account.clone(),
                        kind: SymbolKind::FUNCTION,
                        tags: None,
                        detail: Some("Account".to_string()),
                        uri: uri.clone(),
                        range: acc_range,
                        selection_range: acc_range,
                        data: Some(serde_json::json!({ "account": account })),
                    };

                    Some(CallHierarchyOutgoingCall {
                        to: account_item,
                        from_ranges,
                    })
                })
                .collect();

            return if calls.is_empty() { None } else { Some(calls) };
        }
    }

    None
}

/// Find where an account is defined (open directive).
fn find_account_definition(
    source: &str,
    parse_result: &ParseResult,
    account: &str,
) -> Option<(u32, Range)> {
    for spanned in &parse_result.directives {
        if let Directive::Open(open) = &spanned.value
            && open.account.as_ref() == account
        {
            let (line, _) = byte_offset_to_position(source, spanned.span.start);
            let line_text = source.lines().nth(line as usize)?;
            let col = line_text.find(account)?;
            return Some((
                line,
                Range {
                    start: Position::new(line, col as u32),
                    end: Position::new(line, (col + account.len()) as u32),
                },
            ));
        }
    }
    None
}

/// Check if an account exists in the parse result.
fn account_exists(account: &str, parse_result: &ParseResult) -> bool {
    for spanned in &parse_result.directives {
        match &spanned.value {
            Directive::Open(open) if open.account.as_ref() == account => return true,
            Directive::Close(close) if close.account.as_ref() == account => return true,
            Directive::Balance(bal) if bal.account.as_ref() == account => return true,
            Directive::Transaction(txn)
                if txn.postings.iter().any(|p| p.account.as_ref() == account) =>
            {
                return true;
            }
            _ => {}
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    #[test]
    fn test_prepare_call_hierarchy() {
        let source = r#"2024-01-01 open Assets:Bank:Checking USD
2024-01-15 * "Coffee"
  Assets:Bank:Checking  -5.00 USD
  Expenses:Food
"#;
        let result = parse(source);
        let uri: Uri = "file:///test.beancount".parse().unwrap();

        let params = CallHierarchyPrepareParams {
            text_document_position_params: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier { uri: uri.clone() },
                position: Position::new(0, 20), // On "Assets:Bank:Checking"
            },
            work_done_progress_params: Default::default(),
        };

        let items = handle_prepare_call_hierarchy(&params, source, &result, &uri);
        assert!(items.is_some());

        let items = items.unwrap();
        assert_eq!(items.len(), 1);
        assert_eq!(items[0].name, "Assets:Bank:Checking");
        assert_eq!(items[0].kind, SymbolKind::FUNCTION);
    }

    #[test]
    fn test_incoming_calls() {
        let source = r#"2024-01-01 open Assets:Bank:Checking USD
2024-01-15 * "Coffee"
  Assets:Bank:Checking  -5.00 USD
  Expenses:Food
2024-01-16 * "Lunch"
  Assets:Bank:Checking  -10.00 USD
  Expenses:Food
"#;
        let result = parse(source);
        let uri: Uri = "file:///test.beancount".parse().unwrap();

        let item = CallHierarchyItem {
            name: "Assets:Bank:Checking".to_string(),
            kind: SymbolKind::FUNCTION,
            tags: None,
            detail: Some("Account".to_string()),
            uri: uri.clone(),
            range: Range::default(),
            selection_range: Range::default(),
            data: Some(serde_json::json!({ "account": "Assets:Bank:Checking" })),
        };

        let params = CallHierarchyIncomingCallsParams {
            item,
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let calls = handle_incoming_calls(&params, source, &result, &uri);
        assert!(calls.is_some());

        let calls = calls.unwrap();
        assert_eq!(calls.len(), 2); // Two transactions reference this account
    }

    #[test]
    fn test_outgoing_calls_from_transaction() {
        let source = r#"2024-01-01 open Assets:Bank:Checking USD
2024-01-01 open Expenses:Food
2024-01-15 * "Coffee"
  Assets:Bank:Checking  -5.00 USD
  Expenses:Food
"#;
        let result = parse(source);
        let uri: Uri = "file:///test.beancount".parse().unwrap();

        let item = CallHierarchyItem {
            name: "2024-01-15 * \"Coffee\"".to_string(),
            kind: SymbolKind::EVENT,
            tags: None,
            detail: None,
            uri: uri.clone(),
            range: Range::default(),
            selection_range: Range::default(),
            data: Some(serde_json::json!({
                "type": "transaction",
                "line": 2
            })),
        };

        let params = CallHierarchyOutgoingCallsParams {
            item,
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let calls = handle_outgoing_calls(&params, source, &result, &uri);
        assert!(calls.is_some());

        let calls = calls.unwrap();
        assert_eq!(calls.len(), 2); // Two accounts in this transaction
    }
}
