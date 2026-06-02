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
                // Store data for resolve: real verification is deferred to
                // handle_code_lens_resolve because booking the full ledger
                // is O(N) and the cost is paid per balance assertion.
                let data = serde_json::json!({
                    "uri": uri,
                    "kind": "balance",
                    "account": bal.account.to_string(),
                    "date": bal.date.to_string(),
                    "expected_amount": bal.amount.number.to_string(),
                    "expected_currency": bal.amount.currency.to_string(),
                });

                // Placeholder command set on the initial response so
                // clients never render the literal "Unresolved lens"
                // string for balance lenses during the resolve
                // round-trip window (issue #1245). If `codeLens/resolve`
                // never lands (cancellation race in nvim's LSP client,
                // dropped response, etc.), the user still sees a
                // sensible title instead of "Unresolved lens".
                //
                // The resolve handler overwrites this with either the
                // real `✓ Balance: ... USD` title (passing assertion)
                // or `⚠ Balance: ... USD (see diagnostic)` (failing
                // assertion). For failing assertions the diagnostic
                // remains the source of truth on the actual error
                // (issue #491); the resolved lens title is a brief
                // pointer so the lens stays meaningful instead of
                // sitting forever on the "(checking…)" placeholder.
                let placeholder = Command {
                    title: format!(
                        "Balance: {} {} (checking…)",
                        bal.amount.number, bal.amount.currency
                    ),
                    command: "rledger.noop".to_string(),
                    arguments: None,
                };

                lenses.push(CodeLens {
                    range: Range {
                        start: Position::new(line, 0),
                        end: Position::new(line, 0),
                    },
                    command: Some(placeholder),
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

        // On passing assertions, show the verified-balance lens.
        // On failing assertions, the error is surfaced via diagnostics
        // (standard IDE behavior; showing both would duplicate the
        // information, see issue #491), so we replace the placeholder
        // with a brief "(see diagnostic)" callout rather than letting
        // it stand as a falsely-passing-looking string.
        //
        // Crucially, we ALWAYS set `resolved.command` here. The
        // pre-#1245 path of leaving `command = None` for mismatches
        // surfaced as nvim rendering the literal string "Unresolved
        // lens" once the resolve response landed (issue #1245).
        resolved.command = Some(if actual_amount == expected_amount {
            Command {
                title: format!("✓ Balance: {} {}", expected_amount, expected_currency),
                command: "rledger.showBalanceDetails".to_string(),
                arguments: Some(vec![serde_json::json!({
                    "account": account,
                    "status": "verified",
                    "expected": format!("{} {}", expected_amount, expected_currency),
                    "actual": format!("{} {}", actual_amount, expected_currency),
                })]),
            }
        } else {
            Command {
                title: format!(
                    "⚠ Balance: {} {} (see diagnostic)",
                    expected_amount, expected_currency
                ),
                command: "rledger.noop".to_string(),
                arguments: None,
            }
        });
    }

    // Ensure a command is set for non-balance lenses or malformed
    // balance data — `command: None` makes nvim render the literal
    // string "Unresolved lens" once the resolve response lands (see
    // issue #1245). The `!processed_balance` guard is now mostly
    // defensive: as of #1245, balance lenses ALWAYS receive a command
    // in the kind == "balance" branch above (✓ on match, ⚠ on
    // mismatch), so this fallback only fires for non-balance kinds or
    // for balance data so malformed that we couldn't parse it. The
    // guard prevents this fallback from overwriting the structured
    // balance titles in the (impossible-today) case where the balance
    // branch somehow left `command` unset.
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
        // Balance lens carries data for deferred verification, plus a
        // placeholder command set on the initial response so nvim
        // never renders the literal "Unresolved lens" string during
        // the resolve round-trip window (issue #1245). The real ✓ or
        // ⚠ title lands once `codeLens/resolve` returns.
        let balance_lens = lenses
            .iter()
            .find(|l| {
                l.data
                    .as_ref()
                    .and_then(|d| d.get("kind"))
                    .and_then(|v| v.as_str())
                    == Some("balance")
            })
            .expect("balance lens emitted");
        let cmd = balance_lens
            .command
            .as_ref()
            .expect("balance lens carries placeholder command (issue #1245)");
        assert!(
            cmd.title.contains("checking"),
            "placeholder title should mark the lens as still-resolving; got {:?}",
            cmd.title
        );
        assert_eq!(cmd.command, "rledger.noop");
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

        // Mismatched balances are surfaced via diagnostics (#491), so
        // the lens still does NOT duplicate the amount/✓ marker. But
        // it MUST carry SOME command, otherwise nvim renders the
        // literal "Unresolved lens" string for the line (issue #1245).
        // We use a "⚠ ... (see diagnostic)" callout that points the
        // user at the diagnostic without duplicating its content.
        let cmd = resolved
            .command
            .as_ref()
            .expect("mismatched balance must carry a command (issue #1245)");
        assert!(
            cmd.title.contains("see diagnostic"),
            "mismatched balance lens should point at the diagnostic; got {:?}",
            cmd.title
        );
        assert_eq!(cmd.command, "rledger.noop");
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

        // Without full ledger (single-file mode) the balance comes out to
        // 5000 (no offsetting -50 from credit_card.bean), so the assertion
        // mismatches. Pre-#1245 this surfaced as `command: None`; now we
        // emit the "⚠ ... (see diagnostic)" callout so nvim never renders
        // the literal "Unresolved lens" string.
        let resolved_single = handle_code_lens_resolve(lens.clone(), &bank_result, None);
        let single_cmd = resolved_single
            .command
            .as_ref()
            .expect("mismatched balance must carry a command (issue #1245)");
        assert!(
            single_cmd.title.contains("see diagnostic"),
            "single-file mismatch should point at the diagnostic; got {:?}",
            single_cmd.title
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

    /// Regression for issue #1245: balance lenses must NEVER be emitted
    /// with `command: None`, because nvim's LSP client renders that as
    /// the literal string "Unresolved lens" until the resolve response
    /// lands and is processed. If the resolve races with a cancellation
    /// (or never lands), the lens stays visible as "Unresolved lens"
    /// for the lifetime of the session. The placeholder command we emit
    /// on the initial response, plus the always-set command on resolve,
    /// together break that failure mode.
    ///
    /// The user's reproduction (`balance Assets:Bank:Checking 5 USD`
    /// on date `2024-01-03` after a `+5 USD` posting on `2024-01-01`)
    /// passes server-side for both `2024-01-02` and `2024-01-03`. The
    /// observed inconsistency was a client-side timing artifact of the
    /// `command: None` round-trip window; this test pins the invariant
    /// that closes that window.
    #[test]
    fn issue_1245_balance_lens_always_has_command() {
        // Sanity: both initial-emission and resolve paths must produce
        // a command for both passing and failing balance assertions.
        for (label, expected) in [
            ("passing match", "5"),
            ("mismatch", "999"), // forces mismatch path
        ] {
            let source = format!(
                "2024-01-01 open Assets:Bank:Checking USD\n\
                 2024-01-01 open Income:Salary\n\
                 \n\
                 2024-01-01 * \"Paycheck\"\n  \
                   Assets:Bank:Checking  5 USD\n  \
                   Income:Salary\n\
                 \n\
                 2024-01-03 balance Assets:Bank:Checking {expected} USD\n"
            );
            let parse_result = parse(&source);
            let params = CodeLensParams {
                text_document: lsp_types::TextDocumentIdentifier {
                    uri: "file:///test.beancount".parse().unwrap(),
                },
                work_done_progress_params: Default::default(),
                partial_result_params: Default::default(),
            };

            // 1. Initial emission must carry a placeholder command.
            let lenses = handle_code_lens(
                &params,
                &source,
                &parse_result,
                super::PositionEncoding::Utf16,
            )
            .expect("lenses emitted");
            let balance_lens = lenses
                .iter()
                .find(|l| {
                    l.data
                        .as_ref()
                        .and_then(|d| d.get("kind"))
                        .and_then(|v| v.as_str())
                        == Some("balance")
                })
                .unwrap_or_else(|| panic!("[{label}] balance lens was not emitted"))
                .clone();
            assert!(
                balance_lens.command.is_some(),
                "[{label}] initial balance lens must carry a placeholder command (issue #1245); \
                 nvim renders `command: None` as the literal string \"Unresolved lens\""
            );

            // 2. After resolve, the command must remain set (replaced
            //    with the real ✓ or ⚠ callout, never reset to None).
            let resolved = handle_code_lens_resolve(balance_lens, &parse_result, None);
            assert!(
                resolved.command.is_some(),
                "[{label}] resolved balance lens must carry a command (issue #1245)"
            );
        }
    }
}
