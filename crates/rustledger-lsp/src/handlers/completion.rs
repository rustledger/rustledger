//! Completion handler for autocompletion.
//!
//! Provides context-aware completions for:
//! - Account names (after posting indentation or in directives)
//! - Currencies (after amounts)
//! - Directives (after dates)
//! - Payees and narrations (in transaction headers)

use crate::ledger_state::LedgerState;
use lsp_types::{
    CompletionItem, CompletionItemKind, CompletionParams, CompletionResponse, Position,
};
use rustledger_core::Directive;
use rustledger_parser::ParseResult;

/// Standard Beancount account types.
const ACCOUNT_TYPES: &[&str] = &["Assets", "Liabilities", "Equity", "Income", "Expenses"];

/// Default currencies to suggest when no currencies are found in the document.
const DEFAULT_CURRENCIES: &[&str] = &["USD", "EUR", "GBP"];

/// Standard Beancount directives.
const DIRECTIVES: &[&str] = &[
    "open",
    "close",
    "commodity",
    "balance",
    "pad",
    "event",
    "query",
    "note",
    "document",
    "custom",
    "price",
    "txn",
    "*",
    "!",
];

/// Completion context detected from cursor position.
#[derive(Debug, Clone, PartialEq)]
pub enum CompletionContext {
    /// At the start of a line (expecting date or directive)
    LineStart,
    /// After a date (expecting directive keyword or flag)
    AfterDate,
    /// After directive keyword (expecting account)
    ExpectingAccount,
    /// Inside an account name (after colon)
    AccountSegment {
        /// The prefix typed so far (e.g., "Assets:")
        prefix: String,
    },
    /// After an amount (expecting currency)
    ExpectingCurrency,
    /// Inside a string (payee/narration)
    InsideString,
    /// Unknown context
    Unknown,
}

/// Handle a completion request.
///
/// If `ledger_state` is provided, completions will include data from the full ledger
/// (all included files), not just the current file.
pub fn handle_completion(
    params: &CompletionParams,
    source: &str,
    parse_result: &ParseResult,
    ledger_state: Option<&LedgerState>,
) -> Option<CompletionResponse> {
    let position = params.text_document_position.position;
    let uri = &params.text_document_position.text_document.uri;
    let context = detect_context(source, position);

    tracing::debug!("Completion context: {:?} at {:?}", context, position);

    let mut items = match context {
        CompletionContext::LineStart => complete_line_start(),
        CompletionContext::AfterDate => complete_after_date(),
        CompletionContext::ExpectingAccount => complete_account_start(parse_result, ledger_state),
        CompletionContext::AccountSegment { prefix } => {
            complete_account_segment(&prefix, parse_result, ledger_state)
        }
        CompletionContext::ExpectingCurrency => complete_currency(parse_result, ledger_state),
        CompletionContext::InsideString => complete_payee(parse_result, ledger_state),
        CompletionContext::Unknown => return None,
    };

    // Add URI to each item's data for resolve
    let uri_data = serde_json::json!({ "uri": uri.as_str() });
    for item in &mut items {
        item.data = Some(uri_data.clone());
    }

    if items.is_empty() {
        None
    } else {
        Some(CompletionResponse::Array(items))
    }
}

/// Detect the completion context from cursor position.
fn detect_context(source: &str, position: Position) -> CompletionContext {
    let line = get_line(source, position.line as usize);

    // Get text before cursor
    let col = position.character as usize;
    let before_cursor = if col <= line.len() {
        &line[..col]
    } else {
        line
    };

    let trimmed = before_cursor.trim_start();

    // Check if we're at the start of a posting (indented line)
    // This must come before the empty check since an indented line
    // with just spaces should be expecting an account.
    if before_cursor.starts_with("  ") || before_cursor.starts_with('\t') {
        // Empty indented line means expecting an account
        if trimmed.is_empty() {
            return CompletionContext::ExpectingAccount;
        }
        // Inside a posting - could be account or amount
        let posting_content = trimmed;

        // Check if there's already an account (contains colon and space after)
        if posting_content.contains(':') && posting_content.contains(' ') {
            // After account, might be expecting amount or currency
            let parts: Vec<&str> = posting_content.split_whitespace().collect();
            if parts.len() >= 2 {
                // Check if last part looks like a number
                if let Some(last) = parts.last()
                    && (last.parse::<f64>().is_ok() || last.ends_with('.'))
                {
                    return CompletionContext::ExpectingCurrency;
                }
            }
            return CompletionContext::Unknown;
        }

        // Check if typing an account segment
        if let Some(colon_pos) = posting_content.rfind(':') {
            let prefix = &posting_content[..colon_pos + 1];
            return CompletionContext::AccountSegment {
                prefix: prefix.to_string(),
            };
        }

        // Starting an account name
        return CompletionContext::ExpectingAccount;
    }

    // Empty or whitespace only at line start (not indented)
    if trimmed.is_empty() {
        return CompletionContext::LineStart;
    }

    // Check for date at line start (YYYY-MM-DD pattern)
    if trimmed.len() >= 10 && is_date_like(&trimmed[..10]) {
        let after_date = trimmed[10..].trim_start();
        if after_date.is_empty() {
            return CompletionContext::AfterDate;
        }

        // Check for directive keywords
        for directive in DIRECTIVES {
            if let Some(rest) = after_date.strip_prefix(directive) {
                let after_directive = rest.trim_start();
                if after_directive.is_empty() || !after_directive.contains(' ') {
                    // After directive, expecting account for most directives
                    match *directive {
                        "open" | "close" | "balance" | "pad" | "note" | "document" => {
                            if let Some(colon_pos) = after_directive.rfind(':') {
                                return CompletionContext::AccountSegment {
                                    prefix: after_directive[..colon_pos + 1].to_string(),
                                };
                            }
                            return CompletionContext::ExpectingAccount;
                        }
                        _ => return CompletionContext::Unknown,
                    }
                }
            }
        }

        // After date but no recognized directive yet
        return CompletionContext::AfterDate;
    }

    // Check if inside a quoted string
    let quote_count = before_cursor.chars().filter(|&c| c == '"').count();
    if quote_count % 2 == 1 {
        return CompletionContext::InsideString;
    }

    CompletionContext::Unknown
}

/// Get a specific line from source.
fn get_line(source: &str, line_num: usize) -> &str {
    source.lines().nth(line_num).unwrap_or("")
}

/// Check if a string looks like a date (YYYY-MM-DD).
fn is_date_like(s: &str) -> bool {
    if s.len() != 10 {
        return false;
    }
    let chars: Vec<char> = s.chars().collect();
    chars[4] == '-'
        && chars[7] == '-'
        && chars.iter().enumerate().all(|(i, c)| {
            if i == 4 || i == 7 {
                *c == '-'
            } else {
                c.is_ascii_digit()
            }
        })
}

/// Complete at line start (date template).
fn complete_line_start() -> Vec<CompletionItem> {
    let today = chrono::Local::now().format("%Y-%m-%d").to_string();
    vec![CompletionItem {
        label: today.clone(),
        kind: Some(CompletionItemKind::VALUE),
        detail: Some("Today's date".to_string()),
        insert_text: Some(format!("{} ", today)),
        ..Default::default()
    }]
}

/// Complete after a date (directive keywords).
fn complete_after_date() -> Vec<CompletionItem> {
    DIRECTIVES
        .iter()
        .map(|&d| {
            let detail = match d {
                "open" => "Open an account",
                "close" => "Close an account",
                "commodity" => "Define a commodity/currency",
                "balance" => "Assert account balance",
                "pad" => "Pad account to target",
                "event" => "Record an event",
                "query" => "Define a named query",
                "note" => "Add a note to an account",
                "document" => "Link a document",
                "custom" => "Custom directive",
                "price" => "Record a price",
                "txn" | "*" => "Transaction (complete)",
                "!" => "Transaction (incomplete)",
                _ => "",
            };
            CompletionItem {
                label: d.to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some(detail.to_string()),
                insert_text: Some(format!("{} ", d)),
                ..Default::default()
            }
        })
        .collect()
}

/// Complete account name start (account types).
fn complete_account_start(
    parse_result: &ParseResult,
    ledger_state: Option<&LedgerState>,
) -> Vec<CompletionItem> {
    // First, offer standard account types
    let mut items: Vec<CompletionItem> = ACCOUNT_TYPES
        .iter()
        .map(|&t| CompletionItem {
            label: format!("{}:", t),
            kind: Some(CompletionItemKind::FOLDER),
            detail: Some(format!("{} account type", t)),
            ..Default::default()
        })
        .collect();

    // Collect known accounts from the current file and ledger state
    let known_accounts = get_all_accounts(parse_result, ledger_state);
    for account in known_accounts.iter().take(20) {
        items.push(CompletionItem {
            label: account.clone(),
            kind: Some(CompletionItemKind::VARIABLE),
            detail: Some("Known account".to_string()),
            ..Default::default()
        });
    }

    items
}

/// Complete account segment after colon.
fn complete_account_segment(
    prefix: &str,
    parse_result: &ParseResult,
    ledger_state: Option<&LedgerState>,
) -> Vec<CompletionItem> {
    let known_accounts = get_all_accounts(parse_result, ledger_state);

    // Find accounts that start with this prefix
    let matching: Vec<_> = known_accounts
        .iter()
        .filter(|a| a.starts_with(prefix))
        .collect();

    // Extract unique next segments
    let mut segments: Vec<String> = matching
        .iter()
        .filter_map(|a| {
            let after_prefix = &a[prefix.len()..];
            let next_segment = after_prefix.split(':').next()?;
            if next_segment.is_empty() {
                None
            } else {
                Some(next_segment.to_string())
            }
        })
        .collect();

    segments.sort();
    segments.dedup();

    segments
        .into_iter()
        .map(|seg| {
            let full = format!("{}{}", prefix, seg);
            // Check if this is a complete account or has more segments
            let has_more = matching
                .iter()
                .any(|a| a.starts_with(&format!("{}:", full)));
            CompletionItem {
                label: seg.clone(),
                kind: Some(if has_more {
                    CompletionItemKind::FOLDER
                } else {
                    CompletionItemKind::VARIABLE
                }),
                detail: Some(if has_more {
                    "Account segment".to_string()
                } else {
                    "Account".to_string()
                }),
                insert_text: Some(if has_more { format!("{}:", seg) } else { seg }),
                ..Default::default()
            }
        })
        .collect()
}

/// Complete currency after amount.
fn complete_currency(
    parse_result: &ParseResult,
    ledger_state: Option<&LedgerState>,
) -> Vec<CompletionItem> {
    let currencies = get_all_currencies(parse_result, ledger_state);

    currencies
        .into_iter()
        .map(|c| CompletionItem {
            label: c.clone(),
            kind: Some(CompletionItemKind::UNIT),
            detail: Some("Currency".to_string()),
            ..Default::default()
        })
        .collect()
}

/// Complete payee/narration inside string.
fn complete_payee(
    parse_result: &ParseResult,
    ledger_state: Option<&LedgerState>,
) -> Vec<CompletionItem> {
    let payees = get_all_payees(parse_result, ledger_state);

    payees
        .into_iter()
        .take(20)
        .map(|p| CompletionItem {
            label: p.clone(),
            kind: Some(CompletionItemKind::TEXT),
            detail: Some("Known payee".to_string()),
            ..Default::default()
        })
        .collect()
}

/// Get all accounts from the current file and ledger state.
fn get_all_accounts(parse_result: &ParseResult, ledger_state: Option<&LedgerState>) -> Vec<String> {
    let mut accounts = extract_accounts(parse_result);

    // Merge accounts from ledger state if available
    if let Some(state) = ledger_state {
        accounts.extend(state.accounts().iter().cloned());
    }

    accounts.sort();
    accounts.dedup();
    accounts
}

/// Get all currencies from the current file and ledger state.
fn get_all_currencies(
    parse_result: &ParseResult,
    ledger_state: Option<&LedgerState>,
) -> Vec<String> {
    let mut currencies = extract_currencies(parse_result);

    // Merge currencies from ledger state if available
    if let Some(state) = ledger_state {
        currencies.extend(state.currencies().iter().cloned());
    }

    currencies.sort();
    currencies.dedup();
    currencies
}

/// Get all payees from the current file and ledger state.
fn get_all_payees(parse_result: &ParseResult, ledger_state: Option<&LedgerState>) -> Vec<String> {
    let mut payees = extract_payees(parse_result);

    // Merge payees from ledger state if available
    if let Some(state) = ledger_state {
        payees.extend(state.payees().iter().cloned());
    }

    payees.sort();
    payees.dedup();
    payees
}

/// Extract all account names from parse result.
fn extract_accounts(parse_result: &ParseResult) -> Vec<String> {
    let mut accounts = Vec::new();

    for spanned_directive in &parse_result.directives {
        match &spanned_directive.value {
            Directive::Open(open) => {
                accounts.push(open.account.to_string());
            }
            Directive::Close(close) => {
                accounts.push(close.account.to_string());
            }
            Directive::Balance(bal) => {
                accounts.push(bal.account.to_string());
            }
            Directive::Pad(pad) => {
                accounts.push(pad.account.to_string());
                accounts.push(pad.source_account.to_string());
            }
            Directive::Transaction(txn) => {
                for posting in &txn.postings {
                    accounts.push(posting.account.to_string());
                }
            }
            _ => {}
        }
    }

    accounts.sort();
    accounts.dedup();
    accounts
}

/// Extract all currencies from parse result.
fn extract_currencies(parse_result: &ParseResult) -> Vec<String> {
    let mut currencies = Vec::new();

    for spanned_directive in &parse_result.directives {
        match &spanned_directive.value {
            Directive::Open(open) => {
                for currency in &open.currencies {
                    currencies.push(currency.to_string());
                }
            }
            Directive::Commodity(comm) => {
                currencies.push(comm.currency.to_string());
            }
            Directive::Balance(bal) => {
                currencies.push(bal.amount.currency.to_string());
            }
            Directive::Transaction(txn) => {
                for posting in &txn.postings {
                    if let Some(ref units) = posting.units
                        && let Some(currency) = units.currency()
                    {
                        currencies.push(currency.to_string());
                    }
                }
            }
            _ => {}
        }
    }

    // Add common defaults
    for currency in DEFAULT_CURRENCIES {
        currencies.push((*currency).to_string());
    }

    currencies.sort();
    currencies.dedup();
    currencies
}

/// Extract payees from transactions.
fn extract_payees(parse_result: &ParseResult) -> Vec<String> {
    let mut payees = Vec::new();

    for spanned_directive in &parse_result.directives {
        if let Directive::Transaction(txn) = &spanned_directive.value
            && let Some(ref payee) = txn.payee
        {
            payees.push(payee.to_string());
        }
    }

    payees.sort();
    payees.dedup();
    payees
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_date_like() {
        assert!(is_date_like("2024-01-15"));
        assert!(is_date_like("2000-12-31"));
        assert!(!is_date_like("2024/01/15"));
        assert!(!is_date_like("24-01-15"));
        assert!(!is_date_like("not-a-date"));
    }

    #[test]
    fn test_detect_context_line_start() {
        let source = "\n";
        let ctx = detect_context(source, Position::new(0, 0));
        assert_eq!(ctx, CompletionContext::LineStart);
    }

    #[test]
    fn test_detect_context_after_date() {
        let source = "2024-01-15 ";
        let ctx = detect_context(source, Position::new(0, 11));
        assert_eq!(ctx, CompletionContext::AfterDate);
    }

    #[test]
    fn test_detect_context_expecting_account() {
        let source = "  ";
        let ctx = detect_context(source, Position::new(0, 2));
        assert_eq!(ctx, CompletionContext::ExpectingAccount);
    }

    #[test]
    fn test_detect_context_account_segment() {
        let source = "  Assets:";
        let ctx = detect_context(source, Position::new(0, 9));
        assert_eq!(
            ctx,
            CompletionContext::AccountSegment {
                prefix: "Assets:".to_string()
            }
        );
    }
}
