//! Workspace symbols handler for cross-file symbol search.
//!
//! Provides symbol search across all open documents:
//! - Account names
//! - Currency/commodity names
//! - Payees
//! - Tags

use lsp_types::{
    Location, Position, Range, SymbolInformation, SymbolKind, Uri, WorkspaceSymbolParams,
};
use rustledger_core::Directive;
use rustledger_parser::ParseResult;
use std::collections::HashSet;
use std::sync::Arc;

use super::utils::{LineIndex, PositionEncoding};

/// Handle a workspace symbol request.
pub fn handle_workspace_symbols(
    params: &WorkspaceSymbolParams,
    documents: &[(Uri, String, Arc<ParseResult>)],
    encoding: PositionEncoding,
) -> Option<Vec<SymbolInformation>> {
    let query = params.query.to_lowercase();
    let mut symbols = Vec::new();
    let mut seen_accounts: HashSet<String> = HashSet::new();
    let mut seen_currencies: HashSet<String> = HashSet::new();

    for (uri, source, parse_result) in documents {
        collect_symbols_from_document(
            uri,
            source,
            parse_result,
            &query,
            &mut symbols,
            &mut seen_accounts,
            &mut seen_currencies,
            encoding,
        );
    }

    if symbols.is_empty() {
        None
    } else {
        Some(symbols)
    }
}

/// Collect symbols from a single document.
#[allow(deprecated)] // SymbolInformation::deprecated field is deprecated but required
#[allow(clippy::too_many_arguments)]
fn collect_symbols_from_document(
    uri: &Uri,
    source: &str,
    parse_result: &ParseResult,
    query: &str,
    symbols: &mut Vec<SymbolInformation>,
    seen_accounts: &mut HashSet<String>,
    seen_currencies: &mut HashSet<String>,
    encoding: PositionEncoding,
) {
    let line_index = LineIndex::new(source, encoding);
    for spanned in &parse_result.directives {
        let (line, col) = line_index.offset_to_position(spanned.span.start);
        let location = Location {
            uri: uri.clone(),
            range: Range {
                start: Position::new(line, col),
                end: Position::new(line, col + 10),
            },
        };

        match &spanned.value {
            Directive::Open(open) => {
                let account = open.account.to_string();
                if !seen_accounts.contains(&account)
                    && (query.is_empty() || account.to_lowercase().contains(query))
                {
                    symbols.push(SymbolInformation {
                        name: account.clone(),
                        kind: SymbolKind::CLASS,
                        tags: None,
                        deprecated: None,
                        location: location.clone(),
                        container_name: Some("Accounts".to_string()),
                    });
                    seen_accounts.insert(account);
                }

                // Also index currencies from open directive
                for curr in &open.currencies {
                    let curr_str = curr.to_string();
                    if !seen_currencies.contains(&curr_str)
                        && (query.is_empty() || curr_str.to_lowercase().contains(query))
                    {
                        symbols.push(SymbolInformation {
                            name: curr_str.clone(),
                            kind: SymbolKind::CONSTANT,
                            tags: None,
                            deprecated: None,
                            location: location.clone(),
                            container_name: Some("Currencies".to_string()),
                        });
                        seen_currencies.insert(curr_str);
                    }
                }
            }

            Directive::Commodity(comm) => {
                let curr = comm.currency.to_string();
                if !seen_currencies.contains(&curr)
                    && (query.is_empty() || curr.to_lowercase().contains(query))
                {
                    symbols.push(SymbolInformation {
                        name: curr.clone(),
                        kind: SymbolKind::CONSTANT,
                        tags: None,
                        deprecated: None,
                        location,
                        container_name: Some("Currencies".to_string()),
                    });
                    seen_currencies.insert(curr);
                }
            }

            Directive::Transaction(txn) => {
                // Index payees
                if let Some(ref payee) = txn.payee {
                    let payee_str = payee.to_string();
                    if query.is_empty() || payee_str.to_lowercase().contains(query) {
                        symbols.push(SymbolInformation {
                            name: payee_str,
                            kind: SymbolKind::STRING,
                            tags: None,
                            deprecated: None,
                            location: location.clone(),
                            container_name: Some("Payees".to_string()),
                        });
                    }
                }

                // Index accounts used in postings (if not already seen)
                for posting in &txn.postings {
                    let account = posting.account.to_string();
                    if !seen_accounts.contains(&account)
                        && (query.is_empty() || account.to_lowercase().contains(query))
                    {
                        // Don't add - only show defined accounts in workspace symbols
                        // This prevents duplicates and focuses on declarations
                    }
                }
            }

            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    #[test]
    fn test_workspace_symbols() {
        let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food
2024-01-01 commodity EUR
"#;
        let uri: Uri = "file:///test.beancount".parse().unwrap();
        let result = Arc::new(parse(source));
        let docs = vec![(uri, source.to_string(), result)];

        let params = WorkspaceSymbolParams {
            query: "".to_string(),
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let symbols = handle_workspace_symbols(&params, &docs, PositionEncoding::Utf16);
        assert!(symbols.is_some());
        let symbols = symbols.unwrap();

        // Should have: Assets:Bank, Expenses:Food, USD, EUR
        assert!(symbols.iter().any(|s| s.name == "Assets:Bank"));
        assert!(symbols.iter().any(|s| s.name == "USD"));
        assert!(symbols.iter().any(|s| s.name == "EUR"));
    }

    #[test]
    fn test_workspace_symbols_filtered() {
        let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food
"#;
        let uri: Uri = "file:///test.beancount".parse().unwrap();
        let result = Arc::new(parse(source));
        let docs = vec![(uri, source.to_string(), result)];

        let params = WorkspaceSymbolParams {
            query: "bank".to_string(),
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let symbols = handle_workspace_symbols(&params, &docs, PositionEncoding::Utf16);
        assert!(symbols.is_some());
        let symbols = symbols.unwrap();

        // Should only have Assets:Bank
        assert_eq!(symbols.len(), 1);
        assert_eq!(symbols[0].name, "Assets:Bank");
    }
}
