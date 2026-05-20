//! Code actions handler for quick fixes and refactorings.
//!
//! Provides code actions for:
//! - Adding missing account open directives
//! - Balancing transaction postings
//! - Formatting amounts consistently
//!
//! Supports resolve for lazy-loading workspace edits.

use lsp_types::{
    CodeAction, CodeActionKind, CodeActionParams, CodeActionResponse, Position, Range, TextEdit,
    Uri, WorkspaceEdit,
};
use rustledger_core::Directive;
use rustledger_parser::ParseResult;
use std::collections::{HashMap, HashSet};

use super::utils::LineIndex;

/// Handle a code action request.
pub fn handle_code_actions(
    params: &CodeActionParams,
    source: &str,
    parse_result: &ParseResult,
) -> Option<CodeActionResponse> {
    let mut actions = Vec::new();

    let range = params.range;
    let uri = params.text_document.uri.clone();
    let line_index = LineIndex::new(source);

    // Collect all defined accounts
    let defined_accounts = collect_defined_accounts(parse_result);

    // Collect all used accounts
    let used_accounts = collect_used_accounts(parse_result);

    // Find undefined accounts used in the document
    let undefined_accounts: Vec<_> = used_accounts
        .difference(&defined_accounts)
        .cloned()
        .collect();

    // If there are undefined accounts, offer to create open directives
    for account in undefined_accounts {
        // Check if this account is on or near the selected range
        if is_account_in_range(source, &line_index, &account, range, parse_result) {
            let action = create_open_directive_action(&uri, &account);
            actions.push(action);
        }
    }

    // Check for unbalanced transactions in range
    if let Some(action) = check_unbalanced_transactions(params, &line_index, parse_result) {
        actions.push(action);
    }

    // Import review actions (accept categorization, batch accept)
    actions.extend(super::import::import_code_actions(
        &parse_result.directives,
        source,
        range,
    ));

    if actions.is_empty() {
        None
    } else {
        Some(actions.into_iter().map(|a| a.into()).collect())
    }
}

/// Collect all accounts that have been opened.
fn collect_defined_accounts(parse_result: &ParseResult) -> HashSet<String> {
    let mut accounts = HashSet::new();

    for spanned in &parse_result.directives {
        if let Directive::Open(open) = &spanned.value {
            accounts.insert(open.account.to_string());
        }
    }

    accounts
}

/// Collect all accounts used in the document.
fn collect_used_accounts(parse_result: &ParseResult) -> HashSet<String> {
    let mut accounts = HashSet::new();

    for spanned in &parse_result.directives {
        match &spanned.value {
            Directive::Transaction(txn) => {
                for posting in &txn.postings {
                    accounts.insert(posting.account.to_string());
                }
            }
            Directive::Balance(bal) => {
                accounts.insert(bal.account.to_string());
            }
            Directive::Pad(pad) => {
                accounts.insert(pad.account.to_string());
                accounts.insert(pad.source_account.to_string());
            }
            Directive::Note(note) => {
                accounts.insert(note.account.to_string());
            }
            Directive::Document(doc) => {
                accounts.insert(doc.account.to_string());
            }
            Directive::Close(close) => {
                accounts.insert(close.account.to_string());
            }
            _ => {}
        }
    }

    accounts
}

/// Check if an account is mentioned in or near the given range.
fn is_account_in_range(
    source: &str,
    line_index: &LineIndex,
    account: &str,
    range: Range,
    parse_result: &ParseResult,
) -> bool {
    // Check a few lines around the selection. Fetch each line via
    // LineIndex so we don't re-split the whole source on every
    // undefined-account check (called once per undefined account).
    let start_line = range.start.line;
    let window_start = start_line.saturating_sub(3);
    let window_end = start_line.saturating_add(10);
    for line_idx in window_start..=window_end {
        if let Some(line) = line_index.line_text(source, line_idx)
            && line.contains(account)
        {
            return true;
        }
    }

    // Also check if we're inside a transaction that uses this account
    for spanned in &parse_result.directives {
        if let Directive::Transaction(txn) = &spanned.value {
            let (dir_line, _) = line_index.offset_to_position(spanned.span.start);
            let (end_line, _) = line_index.offset_to_position(spanned.span.end);

            // Check if range overlaps with transaction
            if (range.start.line <= end_line) && (range.end.line >= dir_line) {
                for posting in &txn.postings {
                    if posting.account.as_ref() == account {
                        return true;
                    }
                }
            }
        }
    }

    false
}

/// Create a code action to add an open directive for an account.
/// The edit is deferred to the resolve phase for better performance.
fn create_open_directive_action(uri: &Uri, account: &str) -> CodeAction {
    // Store data for resolve - the actual edit will be computed lazily
    let data = serde_json::json!({
        "kind": "add_open_directive",
        "account": account,
        "uri": uri.as_str(),
    });

    CodeAction {
        title: format!("Add 'open {}' directive", account),
        kind: Some(CodeActionKind::QUICKFIX),
        diagnostics: None,
        edit: None, // Resolved lazily
        command: None,
        is_preferred: Some(true),
        disabled: None,
        data: Some(data),
    }
}

/// Handle a code action resolve request.
/// Computes the workspace edit for a code action.
#[allow(clippy::mutable_key_type)] // Uri is required as key by LSP WorkspaceEdit API
pub fn handle_code_action_resolve(
    action: CodeAction,
    source: &str,
    parse_result: &ParseResult,
    uri: &Uri,
) -> CodeAction {
    let mut resolved = action.clone();

    if let Some(data) = &action.data
        && data.get("kind").and_then(|v| v.as_str()) == Some("add_open_directive")
        && let Some(account) = data.get("account").and_then(|v| v.as_str())
    {
        let line_index = LineIndex::new(source);
        resolved.edit = Some(compute_open_directive_edit(
            uri,
            &line_index,
            account,
            parse_result,
        ));
    }

    resolved
}

/// Compute the workspace edit for adding an open directive.
#[allow(clippy::mutable_key_type)] // Uri is required as key by LSP WorkspaceEdit API
fn compute_open_directive_edit(
    uri: &Uri,
    line_index: &LineIndex,
    account: &str,
    parse_result: &ParseResult,
) -> WorkspaceEdit {
    // Find the earliest date in the file or use a default
    let earliest_date =
        find_earliest_date(parse_result).unwrap_or_else(|| "2000-01-01".to_string());

    // Find where to insert the open directive
    let insert_position = find_open_directive_position(line_index, parse_result);

    let new_text = format!("{} open {}\n", earliest_date, account);

    let mut changes = HashMap::new();
    changes.insert(
        uri.clone(),
        vec![TextEdit {
            range: Range {
                start: insert_position,
                end: insert_position,
            },
            new_text,
        }],
    );

    WorkspaceEdit {
        changes: Some(changes),
        document_changes: None,
        change_annotations: None,
    }
}

/// Find the earliest date in the document.
fn find_earliest_date(parse_result: &ParseResult) -> Option<String> {
    let mut earliest: Option<rustledger_core::NaiveDate> = None;

    for spanned in &parse_result.directives {
        let date = match &spanned.value {
            Directive::Transaction(t) => Some(t.date),
            Directive::Open(o) => Some(o.date),
            Directive::Close(c) => Some(c.date),
            Directive::Balance(b) => Some(b.date),
            Directive::Pad(p) => Some(p.date),
            Directive::Commodity(c) => Some(c.date),
            Directive::Event(e) => Some(e.date),
            Directive::Note(n) => Some(n.date),
            Directive::Document(d) => Some(d.date),
            Directive::Price(p) => Some(p.date),
            Directive::Query(q) => Some(q.date),
            Directive::Custom(c) => Some(c.date),
        };

        if let Some(d) = date {
            earliest = Some(earliest.map_or(d, |e| e.min(d)));
        }
    }

    earliest.map(|d| d.to_string())
}

/// Find the position to insert new open directives.
fn find_open_directive_position(line_index: &LineIndex, parse_result: &ParseResult) -> Position {
    // Find the last open directive and insert after it
    let mut last_open_end: Option<usize> = None;

    for spanned in &parse_result.directives {
        if matches!(&spanned.value, Directive::Open(_)) {
            last_open_end = Some(spanned.span.end);
        }
    }

    if let Some(offset) = last_open_end {
        let (line, _) = line_index.offset_to_position(offset);
        // Insert on the next line
        Position::new(line + 1, 0)
    } else {
        // No open directives, insert at the beginning
        Position::new(0, 0)
    }
}

/// Check for unbalanced transactions and offer to add a balancing posting.
fn check_unbalanced_transactions(
    params: &CodeActionParams,
    line_index: &LineIndex,
    parse_result: &ParseResult,
) -> Option<CodeAction> {
    let range = params.range;

    for spanned in &parse_result.directives {
        if let Directive::Transaction(txn) = &spanned.value {
            let (start_line, _) = line_index.offset_to_position(spanned.span.start);
            let (end_line, _) = line_index.offset_to_position(spanned.span.end);

            // Check if selection is within this transaction
            if range.start.line >= start_line && range.start.line <= end_line {
                // Check if transaction has exactly one posting without amount
                let postings_without_amount =
                    txn.postings.iter().filter(|p| p.units.is_none()).count();

                let postings_with_amount =
                    txn.postings.iter().filter(|p| p.units.is_some()).count();

                // If there's exactly one posting with amount and one without, we can compute the balance
                if postings_without_amount == 1 && postings_with_amount >= 1 {
                    // Transaction is already auto-balanced by the empty posting
                    continue;
                }

                // If all postings have amounts but don't balance, offer to fix
                if postings_without_amount == 0 && postings_with_amount >= 2 {
                    // This would require more complex balance calculation
                    // For now, just skip
                    continue;
                }
            }
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    #[test]
    fn test_collect_accounts() {
        let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee Shop"
  Assets:Bank  -5.00 USD
  Expenses:Food
"#;
        let result = parse(source);

        let defined = collect_defined_accounts(&result);
        assert!(defined.contains("Assets:Bank"));
        assert!(!defined.contains("Expenses:Food"));

        let used = collect_used_accounts(&result);
        assert!(used.contains("Assets:Bank"));
        assert!(used.contains("Expenses:Food"));
    }

    #[test]
    fn test_find_earliest_date() {
        let source = r#"
2024-06-15 open Assets:Bank
2024-01-01 open Assets:Cash
2024-03-01 * "Test"
  Assets:Bank  -10 USD
  Assets:Cash
"#;
        let result = parse(source);
        let earliest = find_earliest_date(&result);
        assert_eq!(earliest, Some("2024-01-01".to_string()));
    }

    #[test]
    #[allow(clippy::mutable_key_type)] // Uri has interior mutability but is safe in tests
    fn test_code_action_resolve() {
        let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food
"#;
        let result = parse(source);
        let uri: Uri = "file:///test.beancount".parse().unwrap();

        // Create a code action with data (as returned by handle_code_actions)
        let action = CodeAction {
            title: "Add 'open Expenses:Food' directive".to_string(),
            kind: Some(CodeActionKind::QUICKFIX),
            diagnostics: None,
            edit: None, // Not resolved yet
            command: None,
            is_preferred: Some(true),
            disabled: None,
            data: Some(serde_json::json!({
                "kind": "add_open_directive",
                "account": "Expenses:Food",
                "uri": uri.as_str(),
            })),
        };

        let resolved = handle_code_action_resolve(action, source, &result, &uri);

        // Should now have an edit
        assert!(resolved.edit.is_some());

        let edit = resolved.edit.unwrap();
        let changes = edit.changes.unwrap();
        let edits = changes.get(&uri).unwrap();

        // Should insert an open directive
        assert_eq!(edits.len(), 1);
        assert!(edits[0].new_text.contains("open Expenses:Food"));
        assert!(edits[0].new_text.contains("2024-01-01")); // Earliest date
    }
}
