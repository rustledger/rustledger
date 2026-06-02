//! Execute command handler for custom editor commands.
//!
//! Provides commands:
//! - rledger.insertDate: Insert today's date
//! - rledger.sortTransactions: Sort transactions by date
//! - rledger.alignAmounts: Align amounts in a region

use lsp_types::{
    ExecuteCommandParams, MessageType, ShowMessageParams, TextEdit, Uri, WorkspaceEdit,
};
use rustledger_core::Directive;
use rustledger_parser::ParseResult;
use std::collections::HashMap;

use super::formatting::format_document;
use super::utils::{LineIndex, PositionEncoding, document_format_config};

/// Argument key clients can pass to suppress informational no-op
/// notifications (the "already sorted" / "no transactions to sort"
/// toasts that interactive users see). Format-on-save hooks and
/// chained automation pass `{"silent": true}` to opt out; the default
/// (no argument or `silent: false`) preserves toasts so command-
/// palette users get feedback when nothing happened.
const SILENT_ARG_KEY: &str = "silent";

fn is_silent_invocation(arguments: &[serde_json::Value]) -> bool {
    arguments
        .iter()
        .filter_map(serde_json::Value::as_object)
        .any(|obj| {
            obj.get(SILENT_ARG_KEY)
                .and_then(serde_json::Value::as_bool)
                .unwrap_or(false)
        })
}

/// Available commands.
pub const COMMANDS: &[&str] = &[
    "rledger.insertDate",
    "rledger.sortTransactions",
    "rledger.alignAmounts",
    "rledger.showAccountBalance",
];

/// Result of an executeCommand handler.
///
/// `response` is the JSON-RPC response body (returned to the caller).
/// `show_message` is an optional `window/showMessage` notification the
/// dispatcher should emit alongside the response. Commands like
/// `rledger.alignAmounts` use this to surface "Cannot align: file has
/// parse errors" feedback that clients (VS Code etc.) would otherwise
/// drop on the floor since executeCommand has no spec-defined way to
/// surface human-readable errors.
#[derive(Debug, Default)]
pub struct ExecuteCommandResponse {
    /// JSON value returned to the client as the `workspace/executeCommand`
    /// response (often a `WorkspaceEdit` to apply, sometimes a small JSON
    /// payload like an inserted-date result).
    pub response: Option<serde_json::Value>,
    /// Optional `window/showMessage` notification the dispatcher sends
    /// alongside the response — used for human-readable feedback that
    /// the executeCommand response shape can't carry.
    pub show_message: Option<ShowMessageParams>,
}

impl ExecuteCommandResponse {
    fn json(value: serde_json::Value) -> Self {
        Self {
            response: Some(value),
            show_message: None,
        }
    }

    fn none() -> Self {
        Self::default()
    }

    fn warn(message: impl Into<String>) -> Self {
        Self {
            response: None,
            show_message: Some(ShowMessageParams {
                typ: MessageType::WARNING,
                message: message.into(),
            }),
        }
    }

    /// Info-level notification — used for no-op acknowledgments where
    /// the user explicitly invoked a command and nothing happened
    /// (e.g. "already sorted", "no transactions to sort"). Distinct
    /// from `warn` so editor themes can style the two differently;
    /// VS Code's `window.showInformationMessage` is non-modal whereas
    /// `showWarningMessage` is more attention-grabbing.
    fn info(message: impl Into<String>) -> Self {
        Self {
            response: None,
            show_message: Some(ShowMessageParams {
                typ: MessageType::INFO,
                message: message.into(),
            }),
        }
    }
}

/// Handle an execute command request.
pub fn handle_execute_command(
    params: &ExecuteCommandParams,
    source: &str,
    parse_result: &ParseResult,
    uri: &Uri,
    encoding: PositionEncoding,
) -> ExecuteCommandResponse {
    match params.command.as_str() {
        "rledger.insertDate" => {
            ExecuteCommandResponse::json(handle_insert_date().unwrap_or(serde_json::Value::Null))
        }
        "rledger.sortTransactions" => {
            let silent = is_silent_invocation(&params.arguments);
            handle_sort_transactions(source, parse_result, uri, silent, encoding)
        }
        "rledger.alignAmounts" => handle_align_amounts(source, parse_result, uri, encoding),
        "rledger.showAccountBalance" => {
            handle_show_account_balance(&params.arguments, parse_result)
        }
        _ => {
            tracing::warn!("Unknown command: {}", params.command);
            ExecuteCommandResponse::none()
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
///
/// `silent` distinguishes interactive invocations (command palette,
/// default) from chained automation (format-on-save hooks that pass
/// `{"silent": true}` as the first argument). Both paths return the
/// same JSON response on success; on a no-op (`<2 transactions` or
/// already-sorted), interactive callers get an info-level
/// `window/showMessage` so they know the command did fire and just
/// had nothing to do, while silent callers get a fully empty response
/// to avoid spamming a toast on every save.
fn handle_sort_transactions(
    source: &str,
    parse_result: &ParseResult,
    uri: &Uri,
    silent: bool,
    encoding: PositionEncoding,
) -> ExecuteCommandResponse {
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
        // Interactive callers (command palette, default) see an info
        // toast so they know the command fired and just had nothing
        // actionable. Chained automation (format-on-save) passes
        // `silent: true` to suppress the toast.
        if silent {
            return ExecuteCommandResponse::none();
        }
        return ExecuteCommandResponse::info(
            "No transactions to sort (the file has fewer than 2 transactions).",
        );
    }

    let mut sorted = transactions.clone();
    sorted.sort_by_key(|(date, start, _, _)| (*date, *start));

    if transactions == sorted {
        // Same interactive vs silent split as the <2 case above.
        if silent {
            return ExecuteCommandResponse::none();
        }
        return ExecuteCommandResponse::info("Transactions are already sorted by date.");
    }

    let Some(first_start) = transactions.iter().map(|(_, s, _, _)| *s).min() else {
        return ExecuteCommandResponse::none();
    };
    let Some(last_end) = transactions.iter().map(|(_, _, e, _)| *e).max() else {
        return ExecuteCommandResponse::none();
    };

    let sorted_text: String = sorted
        .iter()
        .map(|(_, _, _, text)| text.as_str())
        .collect::<Vec<_>>()
        .join("\n\n");

    let line_index = LineIndex::new(source, encoding);
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

    match serde_json::to_value(workspace_edit) {
        Ok(v) => ExecuteCommandResponse::json(v),
        Err(_) => ExecuteCommandResponse::none(),
    }
}

/// Align amounts in the document by delegating to the *canonical*
/// document formatter ([`format_document`]).
///
/// `format_document` runs the same `rustledger_parser::format_source`
/// pipeline as `rledger format`, so the column widths this command
/// resolves agree with the on-disk output. The previous bespoke logic
/// here ran a regex-style line scanner with a "max-existing-column"
/// alignment heuristic that matched neither the LSP `textDocument/
/// formatting` request nor the CLI — the duplicate-code-path class
/// issue #1142 warned about.
///
/// **Parse-error semantics.** On a file with parse errors,
/// `format_document` returns `None` and this command surfaces a
/// dedicated "cannot align" message rather than running the surface-
/// cleanup fallback that `handle_formatting` uses. The command's name
/// promises alignment; emitting whitespace-only edits under it would
/// silently mutate the buffer in ways the user did not request.
fn handle_align_amounts(
    source: &str,
    parse_result: &ParseResult,
    uri: &Uri,
    encoding: PositionEncoding,
) -> ExecuteCommandResponse {
    // `workspace/executeCommand` does NOT carry the client's
    // formatting preferences — those only travel with
    // `textDocument/formatting`. Express that explicitly by passing
    // `None` to `document_format_config`: when that helper grows
    // real options handling, the executeCommand path will fall back
    // to server defaults rather than silently mirroring an absent
    // client value.
    let config = document_format_config(None);
    let Some(edits) = format_document(source, parse_result, &config, encoding) else {
        // Parse errors: surface via window/showMessage so the user
        // actually sees the failure. executeCommand responses are
        // discarded by VS Code etc.; showMessage is the spec-mandated
        // way to display a textual error.
        if !parse_result.errors.is_empty() {
            return ExecuteCommandResponse::warn(format!(
                "Cannot align amounts: source has {} parse error(s); fix them first",
                parse_result.errors.len()
            ));
        }
        return ExecuteCommandResponse::warn("No amounts to align");
    };

    if edits.is_empty() {
        return ExecuteCommandResponse::warn("No amounts to align");
    }

    #[allow(clippy::mutable_key_type)]
    let mut changes = HashMap::new();
    changes.insert(uri.clone(), edits);

    let workspace_edit = WorkspaceEdit {
        changes: Some(changes),
        document_changes: None,
        change_annotations: None,
    };

    match serde_json::to_value(workspace_edit) {
        Ok(v) => ExecuteCommandResponse::json(v),
        Err(_) => ExecuteCommandResponse::none(),
    }
}

/// Show account balance.
fn handle_show_account_balance(
    arguments: &[serde_json::Value],
    parse_result: &ParseResult,
) -> ExecuteCommandResponse {
    let Some(account) = arguments.first().and_then(|a| a.as_str()) else {
        return ExecuteCommandResponse::warn(
            "rledger.showAccountBalance: account argument missing",
        );
    };

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
        return ExecuteCommandResponse::warn(format!(
            "No transactions found for account '{account}'"
        ));
    }

    let balance_str: String = balances
        .iter()
        .map(|(currency, amount)| format!("{amount} {currency}"))
        .collect::<Vec<_>>()
        .join(", ");

    ExecuteCommandResponse::json(serde_json::json!({
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
        let response = handle_show_account_balance(&args, &result);
        let value = response.response.expect("expected a JSON response");
        let balance_str = value.get("balance").and_then(|v| v.as_str()).unwrap();
        assert!(balance_str.contains("95")); // 100 - 5 = 95
        assert!(balance_str.contains("USD"));
    }

    /// Unknown account: response.is_none(), feedback surfaces via
    /// window/showMessage so editors that don't subscribe to the
    /// executeCommand return value still see the warning.
    #[test]
    fn show_account_balance_unknown_account_surfaces_show_message() {
        let source = "2024-01-01 open Assets:Bank USD\n";
        let result = parse(source);
        let args = vec![serde_json::json!("Assets:Missing")];
        let response = handle_show_account_balance(&args, &result);
        assert!(response.response.is_none());
        let msg = response.show_message.expect("expected showMessage");
        assert!(msg.message.contains("No transactions"), "{msg:?}");
    }

    /// Missing first argument: previously a silent None; now a
    /// showMessage so misbehaving clients (and human users invoking
    /// the command without an argument) see the diagnostic.
    #[test]
    fn show_account_balance_missing_arg_surfaces_show_message() {
        let result = parse("");
        let response = handle_show_account_balance(&[], &result);
        assert!(response.response.is_none());
        let msg = response.show_message.expect("expected showMessage");
        assert!(msg.message.contains("account argument"), "{msg:?}");
    }

    /// First argument present but not a string (e.g., null or an
    /// object from a buggy client) also surfaces the same diagnostic.
    #[test]
    fn show_account_balance_wrong_type_arg_surfaces_show_message() {
        let result = parse("");
        let args = vec![serde_json::json!(null)];
        let response = handle_show_account_balance(&args, &result);
        assert!(response.response.is_none());
        let msg = response.show_message.expect("expected showMessage");
        assert!(msg.message.contains("account argument"), "{msg:?}");

        let args = vec![serde_json::json!({"oops": "object"})];
        let response = handle_show_account_balance(&args, &result);
        assert!(response.response.is_none());
        assert!(response.show_message.is_some());
    }

    /// `handle_sort_transactions` no-op behavior is split on the
    /// `silent` flag: interactive callers (command palette default,
    /// `silent=false`) get an info-level `showMessage` so they know
    /// the command fired; chained automation (format-on-save hooks
    /// passing `silent=true`) gets a fully empty response so toasts
    /// don't pop on every save. These tests pin BOTH halves of the
    /// contract — a future revert in either direction surfaces here.
    #[test]
    fn sort_transactions_empty_file_silent_mode_is_silent() {
        use lsp_types::Uri;
        let result = parse("");
        let uri: Uri = "file:///test.beancount".parse().unwrap();
        let response = handle_sort_transactions("", &result, &uri, true, PositionEncoding::Utf16);
        assert!(response.response.is_none(), "expected silent response");
        assert!(
            response.show_message.is_none(),
            "expected no showMessage in silent mode, got {:?}",
            response.show_message
        );
    }

    #[test]
    fn sort_transactions_empty_file_interactive_shows_info() {
        use lsp_types::Uri;
        let result = parse("");
        let uri: Uri = "file:///test.beancount".parse().unwrap();
        let response = handle_sort_transactions("", &result, &uri, false, PositionEncoding::Utf16);
        assert!(response.response.is_none());
        let msg = response.show_message.expect("expected info showMessage");
        assert_eq!(msg.typ, MessageType::INFO);
        assert!(
            msg.message.contains("No transactions to sort"),
            "expected 'No transactions to sort' info, got {msg:?}"
        );
    }

    #[test]
    fn sort_transactions_single_transaction_silent_mode_is_silent() {
        use lsp_types::Uri;
        let source = "2024-01-01 * \"Solo\"\n  Assets:Bank  -5.00 USD\n  Expenses:Food\n";
        let result = parse(source);
        let uri: Uri = "file:///test.beancount".parse().unwrap();
        let response =
            handle_sort_transactions(source, &result, &uri, true, PositionEncoding::Utf16);
        assert!(response.response.is_none());
        assert!(response.show_message.is_none());
    }

    #[test]
    fn sort_transactions_single_transaction_interactive_shows_info() {
        use lsp_types::Uri;
        let source = "2024-01-01 * \"Solo\"\n  Assets:Bank  -5.00 USD\n  Expenses:Food\n";
        let result = parse(source);
        let uri: Uri = "file:///test.beancount".parse().unwrap();
        let response =
            handle_sort_transactions(source, &result, &uri, false, PositionEncoding::Utf16);
        assert!(response.response.is_none());
        let msg = response.show_message.expect("expected info showMessage");
        assert_eq!(msg.typ, MessageType::INFO);
    }

    #[test]
    fn sort_transactions_already_sorted_silent_mode_is_silent() {
        use lsp_types::Uri;
        let source = "2024-01-01 * \"A\"\n  Assets:Bank  -1.00 USD\n  Expenses:Food\n\n2024-02-01 * \"B\"\n  Assets:Bank  -2.00 USD\n  Expenses:Food\n";
        let result = parse(source);
        let uri: Uri = "file:///test.beancount".parse().unwrap();
        let response =
            handle_sort_transactions(source, &result, &uri, true, PositionEncoding::Utf16);
        assert!(
            response.response.is_none(),
            "already-sorted in silent mode should be silent, got {:?}",
            response.response
        );
        assert!(response.show_message.is_none());
    }

    #[test]
    fn sort_transactions_already_sorted_interactive_shows_info() {
        use lsp_types::Uri;
        let source = "2024-01-01 * \"A\"\n  Assets:Bank  -1.00 USD\n  Expenses:Food\n\n2024-02-01 * \"B\"\n  Assets:Bank  -2.00 USD\n  Expenses:Food\n";
        let result = parse(source);
        let uri: Uri = "file:///test.beancount".parse().unwrap();
        let response =
            handle_sort_transactions(source, &result, &uri, false, PositionEncoding::Utf16);
        assert!(response.response.is_none());
        let msg = response.show_message.expect("expected info showMessage");
        assert_eq!(msg.typ, MessageType::INFO);
        assert!(
            msg.message.contains("already sorted"),
            "expected 'already sorted' info, got {msg:?}"
        );
    }

    #[test]
    fn sort_transactions_out_of_order_produces_edit() {
        use lsp_types::Uri;
        // B before A by date: actually needs sorting.
        let source = "2024-02-01 * \"B\"\n  Assets:Bank  -2.00 USD\n  Expenses:Food\n\n2024-01-01 * \"A\"\n  Assets:Bank  -1.00 USD\n  Expenses:Food\n";
        let result = parse(source);
        let uri: Uri = "file:///test.beancount".parse().unwrap();
        let response =
            handle_sort_transactions(source, &result, &uri, false, PositionEncoding::Utf16);
        assert!(
            response.response.is_some(),
            "out-of-order should produce a WorkspaceEdit"
        );
    }

    /// `is_silent_invocation` extracts the `silent` flag from the
    /// command's `arguments` array. Default (no args) is interactive;
    /// `{"silent": true}` opts out; anything else is interactive.
    #[test]
    fn silent_invocation_arg_parser() {
        assert!(!is_silent_invocation(&[]));
        assert!(!is_silent_invocation(&[serde_json::json!({})]));
        assert!(!is_silent_invocation(&[
            serde_json::json!({"silent": false})
        ]));
        assert!(is_silent_invocation(&[serde_json::json!({"silent": true})]));
        // Non-object argument: ignored.
        assert!(!is_silent_invocation(&[serde_json::json!("silent")]));
        assert!(!is_silent_invocation(&[serde_json::json!(true)]));
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
        let response = handle_align_amounts(misaligned, &result, &uri, PositionEncoding::Utf16);
        let out = response
            .response
            .expect("align should return a JSON response");

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

        // No-op shape: a canonically-aligned source returns no JSON
        // response and a showMessage notification ("No amounts to
        // align") instead.
        let aligned = "2024-01-15 open Assets:Bank USD\n";
        let aligned_parsed = parse(aligned);
        let response2 =
            handle_align_amounts(aligned, &aligned_parsed, &uri, PositionEncoding::Utf16);
        assert!(
            response2.response.is_none(),
            "no-op input should not return a workspace edit, got {:?}",
            response2.response
        );
        let msg = response2
            .show_message
            .expect("no-op input should surface a showMessage notification");
        assert!(
            msg.message.contains("No amounts to align"),
            "expected 'no amounts' message, got {msg:?}"
        );
    }

    /// Apply a JSON array of LSP `TextEdit` objects to `source`,
    /// returning the resulting text. Translates each `(line, character)`
    /// LSP position to a byte offset, treating `character` as UTF-16 code
    /// units per the LSP 3.17 default — matching what `minimal_diff_edit`
    /// produces on the server side.
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
            // Build a fresh LineIndex for the mutating buffer on every
            // edit so byte offsets reflect the current state. Test-
            // only path; production handlers build the index once per
            // request and apply edits client-side.
            let idx = crate::handlers::utils::LineIndex::new(
                &out,
                crate::handlers::utils::PositionEncoding::Utf16,
            );
            let start = idx.position_to_offset(sl, sc).expect("start in bounds");
            let end = idx.position_to_offset(el, ec).expect("end in bounds");
            out.replace_range(start..end, &new_text);
        }
        out
    }
}
