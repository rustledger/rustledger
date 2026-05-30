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

use super::formatting::format_document;
use super::utils::{LineIndex, document_format_config};

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
    let line_index = LineIndex::new(source);
    let (start_line, start_col) = line_index.offset_to_position(first_start);
    let (end_line, end_col) = line_index.offset_to_position(last_end);

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

/// Align amounts in the document by delegating to the shared
/// document formatter ([`format_document`]).
///
/// The formatting handler is the canonical alignment path now and it
/// delegates further to [`rustledger_core::format_posting_line`] with
/// file-wide resolved widths, the same geometry `rledger format` uses on
/// disk. So this command, the LSP's `textDocument/formatting` request,
/// and the CLI all produce identical output for a given `FormatConfig`. The previous bespoke
/// logic here ran its own regex-style line scanner with a
/// "max-existing-column" alignment heuristic, which produced output
/// that matched none of the canonical paths — the kind of duplicate
/// code path #1142 warned about.
fn handle_align_amounts(
    source: &str,
    parse_result: &ParseResult,
    uri: &Uri,
) -> Option<serde_json::Value> {
    // `workspace/executeCommand` does NOT carry the client's
    // formatting preferences — those only travel with
    // `textDocument/formatting`. Express that explicitly by passing
    // `None` to `document_format_config`: when that helper grows
    // real options handling, the executeCommand path will fall back
    // to server defaults rather than silently mirroring an absent
    // client value.
    let config = document_format_config(None);
    let edits: Vec<TextEdit> = format_document(source, parse_result, &config).unwrap_or_default();

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
    fn test_align_amounts_produces_canonical_alignment() {
        // Goes beyond a shape-only smoke test: applies the emitted edits
        // to the source and asserts the amounts line up at the file-wide
        // auto column (the same geometry `rledger format` uses on disk).
        // Pins the contract that `rledger.alignAmounts`,
        // `textDocument/formatting`, and `rledger format` agree on the
        // canonical alignment — now a *document-wide* property, not a
        // fixed column. The two postings have different-length accounts,
        // so the widest prefix (Assets:Bank:Checking) drives the column;
        // a per-line formatter would align each to its own number and
        // fail the cross-line assertion below.
        use lsp_types::Uri;

        let misaligned =
            "2024-01-15 * \"Coffee\"\n  Assets:Bank:Checking -5.00 USD\n  Expenses:Food 5.00 USD\n";
        let result = parse(misaligned);
        let uri: Uri = "file:///test.beancount".parse().unwrap();
        let out =
            handle_align_amounts(misaligned, &result, &uri).expect("align should return a value");

        let changes = out.get("changes").and_then(|v| v.as_object()).unwrap();
        let edits = changes.values().next().unwrap().as_array().unwrap();
        assert!(!edits.is_empty(), "misaligned input must produce edits");

        // The number field begins two columns past the widest account
        // prefix; the widest number (`-5.00`) fills the field exactly, so
        // it starts right at that column.
        let expected_num_col = "  Assets:Bank:Checking".chars().count() + 2;
        let applied = apply_lsp_text_edits(misaligned, edits);
        let bank_line = applied
            .lines()
            .find(|l| l.contains("Assets:Bank:Checking"))
            .expect("Assets:Bank:Checking line should still exist after edit");
        let food_line = applied
            .lines()
            .find(|l| l.contains("Expenses:Food"))
            .expect("Expenses:Food line should still exist after edit");
        let dash_pos = bank_line.find("-5.00").expect("amount survived the edit");
        assert_eq!(
            dash_pos, expected_num_col,
            "widest-number amount should start at the file-wide column \
             ({expected_num_col}); got line {bank_line:?}"
        );
        // Cross-line: both currencies must land at the same column — the
        // load-bearing property a per-line formatter would break.
        assert_eq!(
            bank_line.find("USD"),
            food_line.find("USD"),
            "currencies must align across postings; got {bank_line:?} / {food_line:?}"
        );

        // No-op shape: a canonically-aligned source should return the
        // "no work" message.
        let aligned = "2024-01-15 open Assets:Bank USD\n";
        let aligned_parsed = parse(aligned);
        let out2 = handle_align_amounts(aligned, &aligned_parsed, &uri)
            .expect("align should always return some value");
        assert!(
            out2.get("message").is_some(),
            "no-op input should return a message-only shape, got {out2:?}"
        );
    }

    /// Apply a JSON array of LSP `TextEdit` objects to `source`,
    /// returning the resulting text. Test-local helper — the LSP
    /// production path applies edits client-side, so this just
    /// mirrors what an editor would do, sorted bottom-to-top so each
    /// replacement's offsets stay valid. Handles multi-line edit ranges
    /// by translating `(line, character)` LSP positions to byte offsets
    /// against the source.
    fn apply_lsp_text_edits(source: &str, edits: &[serde_json::Value]) -> String {
        let mut typed: Vec<(u32, u32, u32, u32, String)> = edits
            .iter()
            .map(|e| {
                let r = e.get("range").unwrap();
                let s = r.get("start").unwrap();
                let n = r.get("end").unwrap();
                (
                    s.get("line").and_then(|v| v.as_u64()).unwrap() as u32,
                    s.get("character").and_then(|v| v.as_u64()).unwrap() as u32,
                    n.get("line").and_then(|v| v.as_u64()).unwrap() as u32,
                    n.get("character").and_then(|v| v.as_u64()).unwrap() as u32,
                    e.get("newText")
                        .and_then(|v| v.as_str())
                        .unwrap()
                        .to_string(),
                )
            })
            .collect();
        // Apply from the end so earlier edits' offsets don't shift.
        typed.sort_by_key(|t| std::cmp::Reverse((t.0, t.1)));

        let mut out = source.to_string();
        for (sl, sc, el, ec, new_text) in typed {
            let to_byte = |out: &str, line: u32, ch: u32| -> usize {
                out.split_inclusive('\n')
                    .take(line as usize)
                    .map(str::len)
                    .sum::<usize>()
                    + ch as usize
            };
            let start = to_byte(&out, sl, sc);
            let end = to_byte(&out, el, ec);
            out.replace_range(start..end, &new_text);
        }
        out
    }
}
