//! Execute command handler for custom editor commands.
//!
//! Provides commands:
//! - rledger.insertDate: Insert today's date
//! - rledger.sortTransactions: Sort transactions by date
//! - rledger.alignAmounts: Align amounts in a region

use lsp_types::{ExecuteCommandParams, TextEdit, Uri, WorkspaceEdit};
use rustledger_core::Directive;
use rustledger_parser::ParseResult;
use std::collections::HashMap;

use super::utils::byte_offset_to_position;

/// Available commands.
pub const COMMANDS: &[&str] = &[
    "rledger.insertDate",
    "rledger.sortTransactions",
    "rledger.alignAmounts",
    "rledger.showAccountBalance",
];

/// Handle an execute command request.
pub fn handle_execute_command(
    params: &ExecuteCommandParams,
    source: &str,
    parse_result: &ParseResult,
    uri: &Uri,
) -> Option<serde_json::Value> {
    match params.command.as_str() {
        "rledger.insertDate" => handle_insert_date(),
        "rledger.sortTransactions" => handle_sort_transactions(source, parse_result, uri),
        "rledger.alignAmounts" => handle_align_amounts(source, uri),
        "rledger.showAccountBalance" => {
            handle_show_account_balance(&params.arguments, parse_result)
        }
        _ => {
            tracing::warn!("Unknown command: {}", params.command);
            None
        }
    }
}

/// Insert today's date at cursor.
fn handle_insert_date() -> Option<serde_json::Value> {
    let today = rustledger_core::NaiveDate::today().to_string();
    Some(serde_json::json!({
        "text": today
    }))
}

/// Sort all transactions by date.
fn handle_sort_transactions(
    source: &str,
    parse_result: &ParseResult,
    uri: &Uri,
) -> Option<serde_json::Value> {
    // Collect transactions with their spans
    let mut transactions: Vec<(rustledger_core::NaiveDate, usize, usize, String)> = Vec::new();

    for spanned in &parse_result.directives {
        if let Directive::Transaction(txn) = &spanned.value {
            let start = spanned.span.start;
            let end = spanned.span.end;
            let text = source[start..end].to_string();
            transactions.push((txn.date, start, end, text));
        }
    }

    if transactions.len() < 2 {
        return None; // Nothing to sort
    }

    // Check if already sorted
    let mut sorted = transactions.clone();
    sorted.sort_by_key(|(date, start, _, _)| (*date, *start));

    if transactions == sorted {
        return Some(serde_json::json!({
            "message": "Transactions are already sorted"
        }));
    }

    // Find the range that needs to be replaced (from first to last transaction)
    let first_start = transactions.iter().map(|(_, s, _, _)| *s).min()?;
    let last_end = transactions.iter().map(|(_, _, e, _)| *e).max()?;

    // Build the sorted text
    let sorted_text: String = sorted
        .iter()
        .map(|(_, _, _, text)| text.as_str())
        .collect::<Vec<_>>()
        .join("\n\n");

    // Create workspace edit
    let (start_line, start_col) = byte_offset_to_position(source, first_start);
    let (end_line, end_col) = byte_offset_to_position(source, last_end);

    let edit = TextEdit {
        range: lsp_types::Range {
            start: lsp_types::Position::new(start_line, start_col),
            end: lsp_types::Position::new(end_line, end_col),
        },
        new_text: sorted_text,
    };

    #[allow(clippy::mutable_key_type)]
    let mut changes = HashMap::new();
    changes.insert(uri.clone(), vec![edit]);

    let workspace_edit = WorkspaceEdit {
        changes: Some(changes),
        document_changes: None,
        change_annotations: None,
    };

    serde_json::to_value(workspace_edit).ok()
}

/// Align amounts in the document.
fn handle_align_amounts(source: &str, uri: &Uri) -> Option<serde_json::Value> {
    let lines: Vec<&str> = source.lines().collect();
    let mut edits: Vec<TextEdit> = Vec::new();

    // Find posting lines and their amount positions
    let mut posting_groups: Vec<Vec<(usize, usize, usize)>> = Vec::new(); // (line_idx, amount_start, amount_end)
    let mut current_group: Vec<(usize, usize, usize)> = Vec::new();

    for (line_idx, line) in lines.iter().enumerate() {
        let trimmed = line.trim_start();

        // Check if this is a posting line (indented, starts with account)
        if (line.starts_with("  ") || line.starts_with('\t')) && is_posting_line(trimmed) {
            if let Some((amount_start, amount_end)) = find_amount_position(line) {
                current_group.push((line_idx, amount_start, amount_end));
            }
        } else if !current_group.is_empty() {
            // End of transaction, save group
            posting_groups.push(std::mem::take(&mut current_group));
        }
    }

    // Don't forget the last group
    if !current_group.is_empty() {
        posting_groups.push(current_group);
    }

    // Process each group - align amounts to the rightmost position
    for group in posting_groups {
        if group.len() < 2 {
            continue;
        }

        // Find the maximum column where amounts should start
        let max_amount_col = group.iter().map(|(_, start, _)| *start).max().unwrap_or(0);

        // Create edits to align
        for (line_idx, amount_start, _amount_end) in group {
            if amount_start < max_amount_col {
                let padding = max_amount_col - amount_start;
                let line = lines[line_idx];

                // Find where the amount number starts (skip leading spaces)
                if let Some(num_start) = line[..amount_start]
                    .rfind(|c: char| !c.is_whitespace())
                    .map(|i| i + 1)
                {
                    edits.push(TextEdit {
                        range: lsp_types::Range {
                            start: lsp_types::Position::new(line_idx as u32, num_start as u32),
                            end: lsp_types::Position::new(line_idx as u32, amount_start as u32),
                        },
                        new_text: " ".repeat(padding + (amount_start - num_start)),
                    });
                }
            }
        }
    }

    if edits.is_empty() {
        return Some(serde_json::json!({
            "message": "No amounts to align"
        }));
    }

    #[allow(clippy::mutable_key_type)]
    let mut changes = HashMap::new();
    changes.insert(uri.clone(), edits);

    let workspace_edit = WorkspaceEdit {
        changes: Some(changes),
        document_changes: None,
        change_annotations: None,
    };

    serde_json::to_value(workspace_edit).ok()
}

/// Show account balance.
fn handle_show_account_balance(
    arguments: &[serde_json::Value],
    parse_result: &ParseResult,
) -> Option<serde_json::Value> {
    let account = arguments.first()?.as_str()?;

    // Calculate balance from all transactions
    let mut balances: HashMap<String, rustledger_core::Decimal> = HashMap::new();

    for spanned in &parse_result.directives {
        if let Directive::Transaction(txn) = &spanned.value {
            for posting in &txn.postings {
                if posting.account.as_ref() == account
                    && let Some(units) = &posting.units
                    && let Some(number) = units.number()
                {
                    let currency = units.currency().unwrap_or("???").to_string();
                    *balances.entry(currency).or_default() += number;
                }
            }
        }
    }

    if balances.is_empty() {
        return Some(serde_json::json!({
            "account": account,
            "message": "No transactions found for this account"
        }));
    }

    let balance_str: String = balances
        .iter()
        .map(|(currency, amount)| format!("{} {}", amount, currency))
        .collect::<Vec<_>>()
        .join(", ");

    Some(serde_json::json!({
        "account": account,
        "balance": balance_str,
        "balances": balances
    }))
}

/// Check if a line looks like a posting.
fn is_posting_line(trimmed: &str) -> bool {
    trimmed.starts_with("Assets")
        || trimmed.starts_with("Liabilities")
        || trimmed.starts_with("Equity")
        || trimmed.starts_with("Income")
        || trimmed.starts_with("Expenses")
}

/// Find the position of an amount in a posting line.
fn find_amount_position(line: &str) -> Option<(usize, usize)> {
    // Look for a number pattern (possibly negative)
    let mut in_number = false;
    let mut number_start = 0;

    for (i, c) in line.char_indices() {
        if !in_number {
            if c == '-' || c.is_ascii_digit() {
                in_number = true;
                number_start = i;
            }
        } else if !c.is_ascii_digit() && c != '.' && c != ',' {
            // End of number
            return Some((number_start, i));
        }
    }

    if in_number {
        Some((number_start, line.len()))
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    #[test]
    fn test_insert_date() {
        let result = handle_insert_date();
        assert!(result.is_some());

        let value = result.unwrap();
        let text = value.get("text").and_then(|v| v.as_str()).unwrap();
        // Should be in YYYY-MM-DD format
        assert_eq!(text.len(), 10);
        assert!(text.chars().nth(4) == Some('-'));
        assert!(text.chars().nth(7) == Some('-'));
    }

    #[test]
    fn test_show_account_balance() {
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-15 * "Deposit"
  Assets:Bank  100.00 USD
  Income:Salary
2024-01-20 * "Coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food
"#;
        let result = parse(source);

        let args = vec![serde_json::json!("Assets:Bank")];
        let balance = handle_show_account_balance(&args, &result);
        assert!(balance.is_some());

        let value = balance.unwrap();
        let balance_str = value.get("balance").and_then(|v| v.as_str()).unwrap();
        assert!(balance_str.contains("95")); // 100 - 5 = 95
        assert!(balance_str.contains("USD"));
    }

    #[test]
    fn test_is_posting_line() {
        assert!(is_posting_line("Assets:Bank  100 USD"));
        assert!(is_posting_line("Expenses:Food"));
        assert!(!is_posting_line("2024-01-15 * \"Coffee\""));
        assert!(!is_posting_line("open Assets:Bank"));
    }

    #[test]
    fn test_find_amount_position() {
        let line = "  Assets:Bank  100.00 USD";
        let pos = find_amount_position(line);
        assert!(pos.is_some());
        let (start, _end) = pos.unwrap();
        assert!(line[start..].starts_with("100"));
    }
}
