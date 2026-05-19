//! Execute command handler for custom editor commands.
//!
//! Provides commands:
//! - rledger.insertDate: Insert today's date
//! - rledger.sortTransactions: Sort transactions by date
//! - rledger.alignAmounts: Align amounts in a region

use lsp_types::{
    DocumentFormattingParams, ExecuteCommandParams, TextDocumentIdentifier, TextEdit, Uri,
    WorkspaceEdit,
};
use rustledger_core::Directive;
use rustledger_parser::ParseResult;
use std::collections::HashMap;

use super::formatting::handle_formatting;
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
        "rledger.alignAmounts" => handle_align_amounts(source, parse_result, uri),
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
    let today = jiff::Zoned::now().date().to_string();
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

/// Align amounts in the document by delegating to the document
/// formatter ([`handle_formatting`]).
///
/// The formatting handler is now the canonical alignment path: it
/// looks up each posting's source line via its `Spanned<Posting>` span
/// (so interleaved metadata is preserved — see #1142), aligns amounts
/// to `AMOUNT_COLUMN`, and uses a single shared `LineIndex` for
/// O(log lines) offset lookups. The previous bespoke logic here
/// duplicated that pipeline with a regex-style line scanner and its
/// own "max-existing-column" alignment heuristic, which produced
/// different output than `rledger format` and the LSP's own
/// `textDocument/formatting` request — exactly the kind of duplicate
/// code path #1142 warned about.
fn handle_align_amounts(
    source: &str,
    parse_result: &ParseResult,
    uri: &Uri,
) -> Option<serde_json::Value> {
    // Synthesize the formatting params. `handle_formatting` ignores
    // its `_params` argument today (everything it needs comes from
    // `source` + `parse_result`), but we still construct a real
    // `DocumentFormattingParams` so future option-driven behavior
    // (e.g. tab size, alignment column) lands automatically.
    let params = DocumentFormattingParams {
        text_document: TextDocumentIdentifier { uri: uri.clone() },
        options: Default::default(),
        work_done_progress_params: Default::default(),
    };
    let edits: Vec<TextEdit> = handle_formatting(&params, source, parse_result).unwrap_or_default();

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
    fn test_align_amounts_delegates_to_formatter() {
        // The command now reuses `handle_formatting`, so it inherits
        // every fix the formatter has (per-posting span lookup,
        // metadata preservation, etc.). Smoke-test the delegation
        // returns a WorkspaceEdit shape on a misaligned source and the
        // "no work" shape on already-aligned input.
        use lsp_types::Uri;

        let misaligned = "2024-01-15 * \"Coffee\"\n  Assets:Bank  -5.00 USD\n  Expenses:Food\n";
        let result = parse(misaligned);
        let uri: Uri = "file:///test.beancount".parse().unwrap();
        let out =
            handle_align_amounts(misaligned, &result, &uri).expect("align should return a value");
        assert!(
            out.get("changes").is_some(),
            "misaligned input should produce a WorkspaceEdit with changes, got {out:?}"
        );

        // A canonically-aligned source should produce the "no edits"
        // shape (the formatter sees nothing to change).
        let aligned = "2024-01-15 open Assets:Bank USD\n";
        let aligned_parsed = parse(aligned);
        let out2 = handle_align_amounts(aligned, &aligned_parsed, &uri)
            .expect("align should always return some value");
        assert!(
            out2.get("message").is_some(),
            "no-op input should return a message-only shape, got {out2:?}"
        );
    }
}
