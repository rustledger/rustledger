//! Type hierarchy handler for navigating account hierarchies.
//!
//! Provides hierarchical navigation for Beancount accounts:
//! - Supertypes: Assets:Bank:Checking → Assets:Bank → Assets
//! - Subtypes: Assets → Assets:Bank, Assets:Cash, etc.

use lsp_types::{
    Position, Range, SymbolKind, TypeHierarchyItem, TypeHierarchyPrepareParams,
    TypeHierarchySubtypesParams, TypeHierarchySupertypesParams, Uri,
};
use rustledger_core::Directive;
use rustledger_parser::ParseResult;
use std::collections::HashSet;

use super::utils::{LineIndex, PositionEncoding, get_word_at_position, is_account_like};

/// Handle a prepare type hierarchy request.
/// Returns the account at the cursor position as a TypeHierarchyItem.
pub fn handle_prepare_type_hierarchy(
    params: &TypeHierarchyPrepareParams,
    source: &str,
    parse_result: &ParseResult,
    uri: &Uri,
    encoding: PositionEncoding,
) -> Option<Vec<TypeHierarchyItem>> {
    let position = params.text_document_position_params.position;
    let line_idx = position.line as usize;
    let lines: Vec<&str> = source.lines().collect();
    let line = lines.get(line_idx)?;

    // Get the word at the cursor position
    let (word, start, end) = get_word_at_position(line, position.character as usize, encoding)?;

    // Check if it's an account
    if !is_account_like(&word) {
        return None;
    }

    // Verify the account exists in the parse result
    if !account_exists(&word, parse_result) {
        return None;
    }

    let item = TypeHierarchyItem {
        name: word.clone(),
        kind: SymbolKind::CLASS, // Use Class for accounts (hierarchical)
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
        data: Some(serde_json::Value::String(word)),
    };

    Some(vec![item])
}

/// Handle a supertypes request.
/// Returns the parent account in the hierarchy.
pub fn handle_supertypes(
    params: &TypeHierarchySupertypesParams,
    source: &str,
    parse_result: &ParseResult,
    uri: &Uri,
    encoding: PositionEncoding,
) -> Option<Vec<TypeHierarchyItem>> {
    let account = params
        .item
        .data
        .as_ref()
        .and_then(|v| v.as_str())
        .unwrap_or(&params.item.name);

    // Get parent account by removing the last segment
    let parent = get_parent_account(account)?;

    // Find where this parent account is defined or used
    let line_index = LineIndex::new(source, encoding);
    let location = find_account_location(source, &line_index, parse_result, &parent)?;

    let item = TypeHierarchyItem {
        name: parent.clone(),
        kind: SymbolKind::CLASS,
        tags: None,
        detail: Some("Account".to_string()),
        uri: uri.clone(),
        range: location,
        selection_range: location,
        data: Some(serde_json::Value::String(parent)),
    };

    Some(vec![item])
}

/// Handle a subtypes request.
/// Returns all child accounts in the hierarchy.
pub fn handle_subtypes(
    params: &TypeHierarchySubtypesParams,
    source: &str,
    parse_result: &ParseResult,
    uri: &Uri,
    encoding: PositionEncoding,
) -> Option<Vec<TypeHierarchyItem>> {
    let account = params
        .item
        .data
        .as_ref()
        .and_then(|v| v.as_str())
        .unwrap_or(&params.item.name);

    // Collect all child accounts (direct children only)
    let children = get_child_accounts(account, parse_result);

    if children.is_empty() {
        return None;
    }

    let line_index = LineIndex::new(source, encoding);
    let items: Vec<TypeHierarchyItem> = children
        .into_iter()
        .filter_map(|child| {
            let location = find_account_location(source, &line_index, parse_result, &child)?;
            Some(TypeHierarchyItem {
                name: child.clone(),
                kind: SymbolKind::CLASS,
                tags: None,
                detail: Some("Account".to_string()),
                uri: uri.clone(),
                range: location,
                selection_range: location,
                data: Some(serde_json::Value::String(child)),
            })
        })
        .collect();

    if items.is_empty() { None } else { Some(items) }
}

/// Get the parent account by removing the last segment.
fn get_parent_account(account: &str) -> Option<String> {
    let parts: Vec<&str> = account.split(':').collect();
    if parts.len() <= 1 {
        return None;
    }
    Some(parts[..parts.len() - 1].join(":"))
}

/// Get all direct child accounts.
fn get_child_accounts(parent: &str, parse_result: &ParseResult) -> Vec<String> {
    let mut children = HashSet::new();
    let prefix = format!("{}:", parent);
    let parent_depth = parent.matches(':').count();

    for spanned in &parse_result.directives {
        let accounts = get_accounts_from_directive(&spanned.value);

        for account in accounts {
            if account.starts_with(&prefix) {
                // Check if this is a direct child (only one more segment)
                let child_depth = account.matches(':').count();
                if child_depth == parent_depth + 1 {
                    children.insert(account);
                } else if child_depth > parent_depth + 1 {
                    // Extract the direct child
                    let parts: Vec<&str> = account.split(':').collect();
                    let direct_child = parts[..parent_depth + 2].join(":");
                    children.insert(direct_child);
                }
            }
        }
    }

    let mut result: Vec<String> = children.into_iter().collect();
    result.sort();
    result
}

/// Get all accounts from a directive.
fn get_accounts_from_directive(directive: &Directive) -> Vec<String> {
    match directive {
        Directive::Open(open) => vec![open.account.to_string()],
        Directive::Close(close) => vec![close.account.to_string()],
        Directive::Balance(bal) => vec![bal.account.to_string()],
        Directive::Pad(pad) => {
            vec![pad.account.to_string(), pad.source_account.to_string()]
        }
        Directive::Note(note) => vec![note.account.to_string()],
        Directive::Document(doc) => vec![doc.account.to_string()],
        Directive::Transaction(txn) => txn.postings.iter().map(|p| p.account.to_string()).collect(),
        _ => vec![],
    }
}

/// Check if an account exists in the parse result.
fn account_exists(account: &str, parse_result: &ParseResult) -> bool {
    for spanned in &parse_result.directives {
        let accounts = get_accounts_from_directive(&spanned.value);
        if accounts.iter().any(|a| a == account) {
            return true;
        }
    }
    false
}

/// Find the location where an account is defined or first used.
fn find_account_location(
    source: &str,
    line_index: &LineIndex,
    parse_result: &ParseResult,
    account: &str,
) -> Option<Range> {
    // First try to find an open directive
    for spanned in &parse_result.directives {
        if let Directive::Open(open) = &spanned.value
            && open.account.as_ref() == account
        {
            let (line, _) = line_index.offset_to_position(spanned.span.start);
            let line_text = line_index.line_text(line)?;
            if let Some(col) = line_text.find(account) {
                let start = line_index.byte_in_line_to_position(line, col)?;
                let end = line_index.byte_in_line_to_position(line, col + account.len())?;
                return Some(Range { start, end });
            }
        }
    }

    // Fall back to first usage. Walk directive lines via a tracked
    // absolute byte cursor so each match's position is routed
    // through the encoding-aware LineIndex. Pre-round-19 emitted
    // raw byte offsets as columns, broken under UTF-16 on non-ASCII.
    for spanned in &parse_result.directives {
        let accounts = get_accounts_from_directive(&spanned.value);
        if accounts.iter().any(|a| a == account) {
            let directive_text = &source[spanned.span.start..spanned.span.end];
            let mut byte_cursor = spanned.span.start;
            for line_content in directive_text.lines() {
                if let Some(col) = line_content.find(account) {
                    let needle_start = byte_cursor + col;
                    let needle_end = needle_start + account.len();
                    let (sl, sc) = line_index.offset_to_position(needle_start);
                    let (el, ec) = line_index.offset_to_position(needle_end);
                    return Some(Range {
                        start: Position::new(sl, sc),
                        end: Position::new(el, ec),
                    });
                }
                byte_cursor += line_content.len();
                let remaining = &source[byte_cursor.min(spanned.span.end)..spanned.span.end];
                if remaining.starts_with("\r\n") {
                    byte_cursor += 2;
                } else if remaining.starts_with('\n') {
                    byte_cursor += 1;
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
    fn test_get_parent_account() {
        assert_eq!(
            get_parent_account("Assets:Bank:Checking"),
            Some("Assets:Bank".to_string())
        );
        assert_eq!(
            get_parent_account("Assets:Bank"),
            Some("Assets".to_string())
        );
        assert_eq!(get_parent_account("Assets"), None);
    }

    #[test]
    fn test_get_child_accounts() {
        let source = r#"2024-01-01 open Assets:Bank:Checking
2024-01-01 open Assets:Bank:Savings
2024-01-01 open Assets:Cash
2024-01-01 open Assets:Investments:Stocks
"#;
        let result = parse(source);

        let children = get_child_accounts("Assets", &result);
        assert!(children.contains(&"Assets:Bank".to_string()));
        assert!(children.contains(&"Assets:Cash".to_string()));
        assert!(children.contains(&"Assets:Investments".to_string()));

        let bank_children = get_child_accounts("Assets:Bank", &result);
        assert!(bank_children.contains(&"Assets:Bank:Checking".to_string()));
        assert!(bank_children.contains(&"Assets:Bank:Savings".to_string()));
    }

    #[test]
    fn test_prepare_type_hierarchy() {
        let source = r#"2024-01-01 open Assets:Bank:Checking USD
2024-01-15 * "Coffee"
  Assets:Bank:Checking  -5.00 USD
  Expenses:Food
"#;
        let result = parse(source);
        let uri: Uri = "file:///test.beancount".parse().unwrap();

        let params = TypeHierarchyPrepareParams {
            text_document_position_params: lsp_types::TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier { uri: uri.clone() },
                position: Position::new(0, 20), // On "Assets:Bank:Checking"
            },
            work_done_progress_params: Default::default(),
        };

        let items =
            handle_prepare_type_hierarchy(&params, source, &result, &uri, PositionEncoding::Utf16);
        assert!(items.is_some());

        let items = items.unwrap();
        assert_eq!(items.len(), 1);
        assert_eq!(items[0].name, "Assets:Bank:Checking");
    }
}
