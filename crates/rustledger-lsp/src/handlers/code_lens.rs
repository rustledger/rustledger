//! Code lens handler for showing inline information.
//!
//! Provides code lenses above:
//! - Account open directives (showing transaction count)
//! - Transactions (showing posting count and currencies)
//! - Balance assertions (with verification status)
//!
//! Supports resolve for lazy-loading expensive balance calculations.

use lsp_types::{CodeLens, CodeLensParams, Command, Position, Range};
use rustledger_booking::BookingEngine;
use rustledger_core::NaiveDate;
use rustledger_core::{BookingMethod, Decimal, Directive};
use rustledger_parser::{ParseResult, Spanned};
use std::collections::HashMap;

use super::utils::{LineIndex, PositionEncoding};

/// Handle a code lens request.
pub fn handle_code_lens(
    params: &CodeLensParams,
    source: &str,
    parse_result: &ParseResult,
    encoding: PositionEncoding,
) -> Option<Vec<CodeLens>> {
    let line_index = LineIndex::new(source, encoding);
    let mut lenses = Vec::new();
    let uri = params.text_document.uri.as_str();

    // Collect account usage statistics
    let account_stats = collect_account_stats(parse_result);

    for spanned in &parse_result.directives {
        let (line, _) = line_index.offset_to_position(spanned.span.start);

        match &spanned.value {
            Directive::Open(open) => {
                let account = open.account.to_string();
                let stats = account_stats.get(&account);

                let txn_count = stats.map(|s| s.transaction_count).unwrap_or(0);
                let currencies: Vec<String> =
                    open.currencies.iter().map(|c| c.to_string()).collect();

                let title = if txn_count > 0 {
                    if currencies.is_empty() {
                        format!("{} transactions", txn_count)
                    } else {
                        format!("{} transactions | {}", txn_count, currencies.join(", "))
                    }
                } else if !currencies.is_empty() {
                    currencies.join(", ")
                } else {
                    "No transactions".to_string()
                };

                lenses.push(CodeLens {
                    range: Range {
                        start: Position::new(line, 0),
                        end: Position::new(line, 0),
                    },
                    command: Some(Command {
                        title,
                        command: "rledger.showAccountDetails".to_string(),
                        arguments: Some(vec![serde_json::json!(account)]),
                    }),
                    data: Some(serde_json::json!({ "uri": uri })),
                });
            }
            Directive::Transaction(txn) => {
                let posting_count = txn.postings.len();
                let currencies: Vec<String> = txn
                    .postings
                    .iter()
                    .filter_map(|p| {
                        p.units
                            .as_ref()
                            .and_then(|u| u.currency().map(String::from))
                    })
                    .collect::<std::collections::HashSet<_>>()
                    .into_iter()
                    .collect();

                let title = if currencies.is_empty() {
                    format!("{} postings", posting_count)
                } else {
                    format!("{} postings | {}", posting_count, currencies.join(", "))
                };

                lenses.push(CodeLens {
                    range: Range {
                        start: Position::new(line, 0),
                        end: Position::new(line, 0),
                    },
                    command: Some(Command {
                        title,
                        command: "rledger.showTransactionDetails".to_string(),
                        arguments: None,
                    }),
                    data: Some(serde_json::json!({ "uri": uri })),
                });
            }
            Directive::Balance(bal) => {
                // Store data for resolve - verification is deferred
                let data = serde_json::json!({
                    "uri": uri,
                    "kind": "balance",
                    "account": bal.account.to_string(),
                    "date": bal.date.to_string(),
                    "expected_amount": bal.amount.number.to_string(),
                    "expected_currency": bal.amount.currency.to_string(),
                });

                lenses.push(CodeLens {
                    range: Range {
                        start: Position::new(line, 0),
                        end: Position::new(line, 0),
                    },
                    command: None, // Resolved lazily
                    data: Some(data),
                });
            }
            _ => {}
        }
    }

    // Import summary lens (e.g., "12 imported | 3 need review")
    lenses.extend(super::import::import_code_lens(
        &parse_result.directives,
        source,
        encoding,
    ));

    if lenses.is_empty() {
        None
    } else {
        Some(lenses)
    }
}

/// Handle a code lens resolve request.
/// Computes expensive balance verification on demand.
///
/// When `ledger_directives` is provided (multi-file mode), the balance calculation
/// considers all transactions from the full ledger, not just the current file.
/// This fixes issue #470 where balance assertions depending on transactions in
/// other included files would incorrectly show as unresolved.
pub fn handle_code_lens_resolve(
    lens: CodeLens,
    parse_result: &ParseResult,
    ledger_directives: Option<&[Spanned<Directive>]>,
) -> CodeLens {
    let mut resolved = lens.clone();
    let mut processed_balance = false;

    if let Some(data) = &lens.data
        && data.get("kind").and_then(|v| v.as_str()) == Some("balance")
    {
        processed_balance = true;

        let account = data.get("account").and_then(|v| v.as_str()).unwrap_or("");
        let date_str = data.get("date").and_then(|v| v.as_str()).unwrap_or("");
        let expected_amount = data
            .get("expected_amount")
            .and_then(|v| v.as_str())
            .and_then(|s| s.parse::<Decimal>().ok())
            .unwrap_or_default();
        let expected_currency = data
            .get("expected_currency")
            .and_then(|v| v.as_str())
            .unwrap_or("");

        // Parse the date
        let date = date_str.parse::<NaiveDate>().ok();

        // Calculate actual balance up to this date.
        // Use full ledger directives if available (multi-file mode), otherwise fall back
        // to single-file directives.
        // TODO: Consider caching booked directives in LedgerState for large ledgers.
        let actual_balance = calculate_balance_at_date(
            ledger_directives.unwrap_or(&parse_result.directives),
            account,
            date,
        );
        let actual_amount = actual_balance
            .get(expected_currency)
            .copied()
            .unwrap_or_default();

        // Only show codelens for passing balance assertions.
        // Failed assertions are shown as diagnostics (standard IDE behavior).
        // Showing both would duplicate information (issue #491).
        if actual_amount == expected_amount {
            resolved.command = Some(Command {
                title: format!("✓ Balance: {} {}", expected_amount, expected_currency),
                command: "rledger.showBalanceDetails".to_string(),
                arguments: Some(vec![serde_json::json!({
                    "account": account,
                    "status": "verified",
                    "expected": format!("{} {}", expected_amount, expected_currency),
                    "actual": format!("{} {}", actual_amount, expected_currency),
                })]),
            });
        }
        // For mismatches, command stays None - diagnostic will show the error.
    }

    // Ensure a command is set for non-balance lenses or malformed balance data.
    // This prevents "Unresolved lens ..." from appearing in the editor.
    // We don't apply this to processed balance assertions - those intentionally
    // have no command when mismatched (shown via diagnostics instead).
    if !processed_balance && resolved.command.is_none() {
        resolved.command = Some(Command {
            title: "Balance assertion".to_string(),
            command: "rledger.noop".to_string(),
            arguments: None,
        });
    }

    resolved
}

/// Calculate the balance of an account at a specific date.
///
/// This function runs booking/interpolation before calculating balances,
/// matching the behavior of validation. Without booking, auto-filled postings
/// would not be counted in the balance.
///
/// Accepts directives directly to support both single-file and multi-file modes.
fn calculate_balance_at_date(
    directives_in: &[Spanned<Directive>],
    account: &str,
    date: Option<rustledger_core::NaiveDate>,
) -> HashMap<String, Decimal> {
    // Clone and sort directives by date (required for correct booking)
    let mut directives: Vec<Spanned<Directive>> = directives_in.to_vec();
    directives.sort_by_cached_key(|d| {
        (
            d.value.date(),
            d.value.priority(),
            d.value.has_cost_reduction(),
        )
    });

    // Run booking/interpolation to fill in missing amounts
    let mut booking_engine = BookingEngine::with_method(BookingMethod::Strict);
    booking_engine.register_account_methods(directives.iter().map(|s| &s.value));
    for spanned in &mut directives {
        if let Directive::Transaction(txn) = &mut spanned.value
            && let Ok(result) = booking_engine.book_and_interpolate(txn)
        {
            booking_engine.apply(&result.transaction);
            *txn = result.transaction;
        }
    }

    // Calculate balance from booked transactions
    let mut balances: HashMap<String, Decimal> = HashMap::new();

    for spanned in &directives {
        if let Directive::Transaction(txn) = &spanned.value {
            // Only include transactions before the balance date
            if let Some(d) = date
                && txn.date >= d
            {
                continue;
            }

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

    balances
}

/// Statistics for an account.
#[derive(Default)]
struct AccountStats {
    transaction_count: usize,
}

/// Collect statistics about account usage.
fn collect_account_stats(parse_result: &ParseResult) -> HashMap<String, AccountStats> {
    let mut stats: HashMap<String, AccountStats> = HashMap::new();

    for spanned in &parse_result.directives {
        if let Directive::Transaction(txn) = &spanned.value {
            for posting in &txn.postings {
                let account = posting.account.to_string();
                stats.entry(account).or_default().transaction_count += 1;
            }
        }
    }

    stats
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    #[test]
    fn test_code_lens_accounts() {
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food
2024-01-16 * "Lunch"
  Assets:Bank  -10.00 USD
  Expenses:Food
"#;
        let result = parse(source);
        let params = CodeLensParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let lenses = handle_code_lens(&params, source, &result, PositionEncoding::Utf16);
        assert!(lenses.is_some());

        let lenses = lenses.unwrap();
        // Should have: 1 open + 2 transactions = 3 lenses
        assert_eq!(lenses.len(), 3);

        // First lens is for the open directive
        assert!(
            lenses[0]
                .command
                .as_ref()
                .unwrap()
                .title
                .contains("2 transactions")
        );
    }

    #[test]
    fn test_code_lens_balance() {
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-31 balance Assets:Bank 100 USD
"#;
        let result = parse(source);
        let params = CodeLensParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };

        let lenses = handle_code_lens(&params, source, &result, PositionEncoding::Utf16);
        assert!(lenses.is_some());

        let lenses = lenses.unwrap();
        // Balance lens should have data but no command (resolved lazily)
        let balance_lens = lenses.iter().find(|l| {
            l.data
                .as_ref()
                .and_then(|d| d.get("kind"))
                .and_then(|v| v.as_str())
                == Some("balance")
        });
        assert!(balance_lens.is_some());
        assert!(balance_lens.unwrap().command.is_none());
    }

    #[test]
    fn test_code_lens_resolve_balance_match() {
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-15 * "Deposit"
  Assets:Bank  100.00 USD
  Income:Salary
2024-01-31 balance Assets:Bank 100 USD
"#;
        let result = parse(source);

        // Create a code lens like what handle_code_lens would return
        let lens = CodeLens {
            range: Range {
                start: Position::new(4, 0),
                end: Position::new(4, 0),
            },
            command: None,
            data: Some(serde_json::json!({
                "kind": "balance",
                "account": "Assets:Bank",
                "date": "2024-01-31",
                "expected_amount": "100",
                "expected_currency": "USD",
            })),
        };

        let resolved = handle_code_lens_resolve(lens, &result, None);
        assert!(resolved.command.is_some());

        let cmd = resolved.command.unwrap();
        assert!(cmd.title.contains("✓")); // Should show checkmark for match
        assert!(cmd.title.contains("100"));
    }

    #[test]
    fn test_code_lens_resolve_balance_mismatch() {
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-15 * "Deposit"
  Assets:Bank  50.00 USD
  Income:Salary
2024-01-31 balance Assets:Bank 100 USD
"#;
        let result = parse(source);

        let lens = CodeLens {
            range: Range {
                start: Position::new(4, 0),
                end: Position::new(4, 0),
            },
            command: None,
            data: Some(serde_json::json!({
                "kind": "balance",
                "account": "Assets:Bank",
                "date": "2024-01-31",
                "expected_amount": "100",
                "expected_currency": "USD",
            })),
        };

        let resolved = handle_code_lens_resolve(lens, &result, None);

        // For mismatched balances, codelens should NOT have a command.
        // The error is shown via diagnostics instead (issue #491).
        assert!(
            resolved.command.is_none(),
            "Mismatched balance should not show codelens (diagnostic handles it)"
        );
    }

    #[test]
    fn test_code_lens_resolve_with_auto_filled_posting() {
        // This tests that booking is run before balance calculation.
        // The Income:Salary posting has no amount - it should be auto-filled to -100 USD.
        // After booking, Assets:Bank should have 100 USD and balance should pass.
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-01 open Income:Salary USD
2024-01-15 * "Deposit"
  Assets:Bank  100.00 USD
  Income:Salary
2024-01-31 balance Assets:Bank 100 USD
"#;
        let result = parse(source);

        let lens = CodeLens {
            range: Range {
                start: Position::new(5, 0),
                end: Position::new(5, 0),
            },
            command: None,
            data: Some(serde_json::json!({
                "kind": "balance",
                "account": "Assets:Bank",
                "date": "2024-01-31",
                "expected_amount": "100",
                "expected_currency": "USD",
            })),
        };

        let resolved = handle_code_lens_resolve(lens, &result, None);

        // With booking, the auto-filled posting is counted and balance should pass
        assert!(
            resolved.command.is_some(),
            "Balance with auto-filled posting should pass after booking"
        );

        let cmd = resolved.command.unwrap();
        assert!(
            cmd.title.contains("✓"),
            "Should show checkmark for passing balance. Got: {}",
            cmd.title
        );
    }

    #[test]
    fn test_code_lens_resolve_missing_data() {
        // Test that resolve always returns a command, even with missing/malformed data.
        // This prevents "Unresolved lens ..." from appearing in the editor.
        let source = r#"2024-01-01 open Assets:Bank USD"#;
        let result = parse(source);

        // Lens with no data at all
        let lens = CodeLens {
            range: Range {
                start: Position::new(0, 0),
                end: Position::new(0, 0),
            },
            command: None,
            data: None,
        };

        let resolved = handle_code_lens_resolve(lens, &result, None);
        assert!(
            resolved.command.is_some(),
            "Lens must always have a command after resolve"
        );
    }

    #[test]
    fn test_code_lens_resolve_multifile_balance() {
        // Test that balance verification uses full ledger directives when provided.
        // This is the fix for issue #470: balance assertions that depend on
        // transactions in other included files should verify correctly.

        // The "current file" (bank.bean) has a balance assertion for 4950 USD
        let bank_source = r#"2024-01-01 open Assets:Bank:Checking USD
2024-01-15 * "Paycheck"
  Assets:Bank:Checking  5000 USD
  Income:Salary
2024-01-21 balance Assets:Bank:Checking 4950 USD
"#;
        let bank_result = parse(bank_source);

        // The "other file" (credit_card.bean) has the -50 USD transaction
        let credit_card_source = r#"2024-01-01 open Liabilities:Credit-Card
2024-01-20 * "Pay off credit card"
  Assets:Bank:Checking  -50 USD
  Liabilities:Credit-Card
"#;
        let credit_card_result = parse(credit_card_source);

        // Combine directives as the loader would
        let mut full_directives = bank_result.directives.clone();
        full_directives.extend(credit_card_result.directives.clone());

        // Create a lens for the balance assertion on line 4 (0-indexed)
        let lens = CodeLens {
            range: Range {
                start: Position::new(4, 0),
                end: Position::new(4, 0),
            },
            command: None,
            data: Some(serde_json::json!({
                "kind": "balance",
                "account": "Assets:Bank:Checking",
                "date": "2024-01-21",
                "expected_amount": "4950",
                "expected_currency": "USD",
            })),
        };

        // Without full ledger (single-file mode) - balance would be 5000, mismatch!
        let resolved_single = handle_code_lens_resolve(lens.clone(), &bank_result, None);
        assert!(
            resolved_single.command.is_none(),
            "Single-file mode should see mismatch (5000 != 4950)"
        );

        // With full ledger (multi-file mode) - balance is 5000 - 50 = 4950, match!
        let resolved_multi = handle_code_lens_resolve(lens, &bank_result, Some(&full_directives));
        assert!(
            resolved_multi.command.is_some(),
            "Multi-file mode should see match (5000 - 50 = 4950)"
        );

        let cmd = resolved_multi.command.unwrap();
        assert!(
            cmd.title.contains("✓"),
            "Should show checkmark. Got: {}",
            cmd.title
        );
        assert!(
            cmd.title.contains("4950"),
            "Should show correct balance. Got: {}",
            cmd.title
        );
    }

    #[test]
    fn test_code_lens_resolve_wrong_kind() {
        // Test that resolve handles data with wrong/missing "kind" field
        let source = r#"2024-01-01 open Assets:Bank USD"#;
        let result = parse(source);

        let lens = CodeLens {
            range: Range {
                start: Position::new(0, 0),
                end: Position::new(0, 0),
            },
            command: None,
            data: Some(serde_json::json!({
                "kind": "unknown",
                "account": "Assets:Bank",
            })),
        };

        let resolved = handle_code_lens_resolve(lens, &result, None);
        assert!(
            resolved.command.is_some(),
            "Lens must always have a command after resolve"
        );
    }
}
