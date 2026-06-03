//! Code lens handler for showing inline information.
//!
//! Provides code lenses above:
//! - Account open directives (showing transaction count)
//! - Transactions (showing posting count and currencies)
//! - Balance assertions (with verification status)
//!
//! # Eager resolution
//!
//! Balance lenses are computed eagerly inside [`handle_code_lens`].
//! Pre-#1253, balance lenses shipped with `command: None` plus a `data`
//! payload that [`handle_code_lens_resolve`] consulted on a subsequent
//! `codeLens/resolve` round-trip. That deferred-resolve pattern was
//! standard LSP, but it exposed the lens to a known race in nvim's
//! built-in LSP client: when the resolve response races with a
//! cancellation (visible in the user's LSP log as
//! `"Cannot find request with id N whilst attempting to cancel"`),
//! the response is silently discarded and the lens stays on whatever
//! placeholder shipped with the initial response. #1245 surfaced this
//! as `"Unresolved lens"`; #1249 mitigated by introducing a
//! `"Balance: X USD (checking…)"` placeholder, but the stuck-checking
//! symptom (#1253) showed the race was still observable. The right
//! fix is to skip the resolve round-trip entirely: ship the final
//! `✓` or `⚠` title on the initial response.
//!
//! Cost: one booking pass per `textDocument/codeLens` request. M
//! balance assertions cost O(N + M) total (book once, iterate M
//! times) instead of the previous O(M × N) (book per resolve).
//! [`handle_code_lens_resolve`] is kept as a defensive fallback for
//! any future lens kind that genuinely needs deferred resolution.

use lsp_types::{CodeLens, CodeLensParams, Command, Position, Range};
use rust_decimal::MathematicalOps;
use rustledger_booking::BookingEngine;
use rustledger_core::{BookingMethod, Decimal, Directive, NaiveDate};
use rustledger_parser::{ParseResult, Spanned};
use std::collections::HashMap;
use std::str::FromStr;

use super::utils::{LineIndex, PositionEncoding};

/// Balance assertions use 2x the `tolerance_multiplier` option.
/// Mirrors `BALANCE_TOLERANCE_MULTIPLIER` in
/// `rustledger-validate/src/validators/balance.rs`; the constant is
/// duplicated here rather than re-exported to avoid widening the
/// validator crate's public API.
const BALANCE_TOLERANCE_MULTIPLIER: Decimal = Decimal::TWO;

/// Default value of `options.tolerance_multiplier`, matching
/// `ValidationOptions::default()` (`Decimal::new(5, 1)` = 0.5).
const DEFAULT_TOLERANCE_MULTIPLIER_NUM: i64 = 5;
const DEFAULT_TOLERANCE_MULTIPLIER_SCALE: u32 = 1;

/// Handle a code lens request.
///
/// `ledger_directives` is the full multi-file ledger snapshot (taken
/// on the main loop while locks are cheap). When provided, balance
/// assertions are validated against the full ledger; when `None`, the
/// validator falls back to the current file's parse result. This is
/// the same multi-file behavior the pre-#1253 resolve path supported
/// (issue #470).
pub fn handle_code_lens(
    params: &CodeLensParams,
    source: &str,
    parse_result: &ParseResult,
    ledger_directives: Option<&[Spanned<Directive>]>,
    encoding: PositionEncoding,
) -> Option<Vec<CodeLens>> {
    let line_index = LineIndex::new(source, encoding);
    let mut lenses = Vec::new();
    let uri = params.text_document.uri.as_str();

    // Collect account usage statistics
    let account_stats = collect_account_stats(parse_result);

    // Book the directives ONCE. The booked result feeds every balance
    // lens lookup in this request (booking is O(N), each lookup is
    // O(N), total O(N + M*N) for M assertions; pre-#1253 each resolve
    // re-booked, so the same total but per-lens latency dropped).
    // `None` ledger_directives falls back to the current file's
    // parse_result, matching the resolve path's behavior in
    // single-file mode.
    //
    // Fast path: skip booking entirely when the file has no balance
    // directives. Open/transaction lenses don't read `booked_directives`,
    // so for the common-case file (zero balance assertions) we save
    // an O(N) booking pass on every codeLens request. The caller in
    // `main_loop.rs` does the same pre-scan to skip cloning the full
    // ledger directives vector under the read lock.
    let has_balance = parse_result
        .directives
        .iter()
        .any(|s| matches!(s.value, Directive::Balance(_)));
    let booking_method = resolve_booking_method_from_options(parse_result);
    let booked_directives = if has_balance {
        book_directives_once(
            ledger_directives.unwrap_or(&parse_result.directives),
            booking_method,
        )
    } else {
        Vec::new()
    };
    let tolerance_multiplier = default_tolerance_multiplier();

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
                // Eagerly verify the assertion against the booked
                // directives. No data payload + no resolve round-trip
                // means no exposure to nvim's resolve-cancellation
                // race (issues #1245 / #1253); the user sees the
                // final ✓ or ⚠ title on the initial response.
                let actual_amount =
                    balance_at_date_from_booked(&booked_directives, &bal.account, Some(bal.date))
                        .get(bal.amount.currency.as_ref())
                        .copied()
                        .unwrap_or_default();

                // Match the validator's tolerance comparison
                // (validators/balance.rs:222-247). Strict equality
                // here would emit a ⚠ for an amount the validator
                // accepts (e.g. 99.999 vs 100.00 USD at the default
                // ±0.005 tolerance), which would point the user at a
                // diagnostic that doesn't exist — the same dead-link
                // UX #1253 set out to prevent.
                let tolerance =
                    balance_tolerance(bal.amount.number, bal.tolerance, tolerance_multiplier);
                let difference = (actual_amount - bal.amount.number).abs();

                let command = if difference <= tolerance {
                    // Passing assertion: informational title, no
                    // click action. Uses `rledger.noop` (matching the
                    // failing branch below and the pre-eager path) so
                    // strict clients that filter on advertised
                    // commands don't dead-link the lens. A future
                    // "show balance details" command can be added
                    // here once its handler is registered in
                    // `execute_command::COMMANDS`.
                    Command {
                        title: format!("✓ Balance: {} {}", bal.amount.number, bal.amount.currency),
                        command: "rledger.noop".to_string(),
                        arguments: None,
                    }
                } else {
                    // Failing assertions: the real error is surfaced
                    // via diagnostics (issue #491). The lens title
                    // points the user at the diagnostic rather than
                    // duplicating its content.
                    Command {
                        title: format!(
                            "⚠ Balance: {} {} (see diagnostic)",
                            bal.amount.number, bal.amount.currency
                        ),
                        command: "rledger.noop".to_string(),
                        arguments: None,
                    }
                };

                lenses.push(CodeLens {
                    range: Range {
                        start: Position::new(line, 0),
                        end: Position::new(line, 0),
                    },
                    command: Some(command),
                    data: None,
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

/// Handle a `codeLens/resolve` request.
///
/// As of #1253 every lens kind [`handle_code_lens`] emits ships
/// fully-resolved (balance lenses included — see the eager-resolve
/// rationale in this module's rustdoc). This handler is therefore
/// defensive: if any future lens kind ever ships with
/// `command: None`, the fallback below guarantees the client renders
/// something sensible rather than nvim's literal `"Unresolved lens"`
/// string. The signature deliberately takes no parse_result or
/// ledger directives, so `try_dispatch_async`'s CodeLensResolve
/// branch can skip its hot-path read-lock + Vec clone. A future
/// resolve-using lens kind that genuinely needs that data should add
/// it back as a parameter (and pay the snapshot cost then, not now).
pub fn handle_code_lens_resolve(lens: CodeLens) -> CodeLens {
    let mut resolved = lens;
    if resolved.command.is_none() {
        resolved.command = Some(Command {
            title: "rledger lens".to_string(),
            command: "rledger.noop".to_string(),
            arguments: None,
        });
    }
    resolved
}

/// Sort + book a directive list once, returning the full directive
/// list in chronological order with each transaction booked and
/// interpolated in place.
///
/// Non-transaction directives pass through unchanged. The returned
/// vector is suitable for any number of subsequent
/// [`balance_at_date_from_booked`] lookups, which is how
/// [`handle_code_lens`] amortizes booking cost across all balance
/// lenses in a file (O(N) booking + O(M) lookups, vs O(M*N) for the
/// pre-#1253 per-resolve approach).
///
/// Booking matches the validator's behavior; without it, auto-filled
/// postings (Income:Salary with no explicit amount, etc.) wouldn't
/// be counted toward the asserted account's balance.
///
/// `default_method` is the workspace default (driven by
/// `option "booking_method" "..."` if set, else
/// `BookingMethod::Strict`). Per-account methods declared on `Open`
/// directives are layered on top by `register_account_methods`, so
/// the only thing this argument controls is what FIFO/LIFO/AVERAGE
/// accounts WITHOUT an explicit per-account method use.
fn book_directives_once(
    directives_in: &[Spanned<Directive>],
    default_method: BookingMethod,
) -> Vec<Spanned<Directive>> {
    let mut directives: Vec<Spanned<Directive>> = directives_in.to_vec();
    directives.sort_by_cached_key(|d| {
        (
            d.value.date(),
            d.value.priority(),
            d.value.has_cost_reduction(),
        )
    });

    let mut booking_engine = BookingEngine::with_method(default_method);
    booking_engine.register_account_methods(directives.iter().map(|s| &s.value));
    for spanned in &mut directives {
        if let Directive::Transaction(txn) = &mut spanned.value
            && let Ok(result) = booking_engine.book_and_interpolate(txn)
        {
            booking_engine.apply(&result.transaction);
            *txn = result.transaction;
        }
    }

    directives
}

/// Compute the tolerance for a balance assertion, mirroring the
/// validator at `rustledger-validate/src/validators/balance.rs`:
/// - explicit `~ tolerance` on the directive always wins
/// - otherwise: `tolerance_multiplier * 2 * 10^(-scale)` for decimal
///   amounts, exact match for integers
///
/// Lenses don't have access to the booked `ValidationState` (where
/// `options.tolerance_multiplier` lives in the full pipeline), so
/// `tolerance_multiplier` is passed in from
/// [`default_tolerance_multiplier`] today and could be threaded from
/// `option "inferred_tolerance_multiplier"` in a follow-up. Files
/// that override the multiplier are rare; the default is what the
/// vast majority of users hit.
fn balance_tolerance(
    expected: Decimal,
    explicit: Option<Decimal>,
    tolerance_multiplier: Decimal,
) -> Decimal {
    if let Some(t) = explicit {
        return t;
    }
    let scale = expected.scale();
    if scale > 0 {
        let quantum = Decimal::TEN.powi(-i64::from(scale));
        tolerance_multiplier * BALANCE_TOLERANCE_MULTIPLIER * quantum
    } else {
        Decimal::ZERO
    }
}

/// Returns the validator's default `tolerance_multiplier`
/// (`Decimal::new(5, 1)` = 0.5; see
/// `rustledger-validate::ValidationOptions::default`).
#[inline]
fn default_tolerance_multiplier() -> Decimal {
    Decimal::new(
        DEFAULT_TOLERANCE_MULTIPLIER_NUM,
        DEFAULT_TOLERANCE_MULTIPLIER_SCALE,
    )
}

/// Resolve the workspace default booking method from
/// `parse_result.options` (the parser exposes raw `(key, value, span)`
/// tuples; we just scan for `"booking_method"`). Mirrors the loader's
/// `resolve_effective_booking_method`: file-level `option
/// "booking_method"` wins, otherwise default to Strict. Unknown
/// strings fall back to Strict rather than failing the lens.
fn resolve_booking_method_from_options(parse_result: &ParseResult) -> BookingMethod {
    parse_result
        .options
        .iter()
        .rev()
        .find_map(|(k, v, _)| {
            (k == "booking_method")
                .then(|| BookingMethod::from_str(v).ok())
                .flatten()
        })
        .unwrap_or(BookingMethod::Strict)
}

/// Sum postings to `account` from `booked` whose transaction date is
/// strictly before `date` (the Beancount semantic for balance
/// assertions: the asserted value is checked at the START of the
/// asserted day).
///
/// Caller is responsible for passing already-[`book_directives_once`]
/// output. Returns a per-currency map so a multi-currency account can
/// be validated against the asserted currency without losing the
/// others.
fn balance_at_date_from_booked(
    booked: &[Spanned<Directive>],
    account: &str,
    date: Option<NaiveDate>,
) -> HashMap<String, Decimal> {
    let mut balances: HashMap<String, Decimal> = HashMap::new();
    for spanned in booked {
        if let Directive::Transaction(txn) = &spanned.value {
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

        let lenses = handle_code_lens(&params, source, &result, None, PositionEncoding::Utf16);
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
    fn test_code_lens_balance_match_ships_resolved() {
        // Passing assertion: lens ships with `✓ Balance: ... USD` on
        // the initial textDocument/codeLens response. No data payload,
        // no resolve round-trip (issue #1253).
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-01 open Income:Salary
2024-01-15 * "Deposit"
  Assets:Bank  100.00 USD
  Income:Salary
2024-01-31 balance Assets:Bank 100.00 USD
"#;
        let result = parse(source);
        let params = code_lens_params();

        let balance_lens = find_balance_lens(
            handle_code_lens(&params, source, &result, None, PositionEncoding::Utf16)
                .expect("lenses emitted"),
        );
        let cmd = balance_lens
            .command
            .as_ref()
            .expect("balance lens ships fully-resolved (issue #1253)");
        assert!(
            cmd.title.contains('✓'),
            "passing assertion should ship with ✓; got {:?}",
            cmd.title
        );
        assert!(cmd.title.contains("100"));
        assert!(
            balance_lens.data.is_none(),
            "eager-resolved balance lens carries no resolve-data payload; \
             pre-#1253 the data payload triggered a codeLens/resolve \
             round-trip that nvim's client could race against \
             cancellation. got data = {:?}",
            balance_lens.data
        );
    }

    #[test]
    fn test_code_lens_balance_mismatch_ships_resolved() {
        // Failing assertion: lens ships with the `⚠ ... (see diagnostic)`
        // callout on the initial response. The actual error lives in
        // the diagnostic (#491); the lens points at it without
        // duplicating its content.
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-01 open Income:Salary
2024-01-15 * "Deposit"
  Assets:Bank  50.00 USD
  Income:Salary
2024-01-31 balance Assets:Bank 100 USD
"#;
        let result = parse(source);
        let params = code_lens_params();

        let balance_lens = find_balance_lens(
            handle_code_lens(&params, source, &result, None, PositionEncoding::Utf16)
                .expect("lenses emitted"),
        );
        let cmd = balance_lens
            .command
            .as_ref()
            .expect("balance lens ships fully-resolved");
        assert!(
            cmd.title.contains("see diagnostic"),
            "failing assertion should ship with `(see diagnostic)`; got {:?}",
            cmd.title
        );
        assert_eq!(cmd.command, "rledger.noop");
    }

    #[test]
    fn test_code_lens_balance_with_auto_filled_posting() {
        // Booking runs as part of the eager balance computation, so a
        // posting elided to be auto-filled (Income:Salary with no
        // explicit amount) still gets counted. Pre-eager-resolve this
        // lived in handle_code_lens_resolve; same coverage, new path.
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-01 open Income:Salary USD
2024-01-15 * "Deposit"
  Assets:Bank  100.00 USD
  Income:Salary
2024-01-31 balance Assets:Bank 100 USD
"#;
        let result = parse(source);
        let params = code_lens_params();

        let balance_lens = find_balance_lens(
            handle_code_lens(&params, source, &result, None, PositionEncoding::Utf16)
                .expect("lenses emitted"),
        );
        let cmd = balance_lens
            .command
            .as_ref()
            .expect("balance lens ships fully-resolved");
        assert!(
            cmd.title.contains('✓'),
            "auto-filled posting should book to 100 USD, passing the assertion; got {:?}",
            cmd.title
        );
    }

    /// Regression for the post-#1253 follow-up review: the eager
    /// balance check must mirror the validator's tolerance logic.
    /// Pre-fix this used strict `==`; the validator at
    /// `rustledger-validate/src/validators/balance.rs:222-247` accepts
    /// `(actual - expected).abs() <= tolerance`. For a 2-decimal
    /// amount like `100.00 USD`, default tolerance is
    /// `0.5 * 2 * 0.01 = 0.01`. An actual of `99.999 USD` (off by
    /// 0.001) is well within tolerance.
    ///
    /// If the lens reverted to strict equality, this test would fail:
    /// the balance would render `⚠ (see diagnostic)` while the
    /// validator passes silently, reintroducing the dead-link UX
    /// #1253 originally set out to prevent.
    #[test]
    fn balance_lens_honors_validator_tolerance() {
        // Choose actual amounts that round to slightly off the
        // asserted value. Three penny-fractional postings of
        // 33.333 USD sum to 99.999 USD; the assertion expects
        // 100.00 USD. The validator accepts (under tolerance);
        // the lens must too.
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-01 open Income:Misc
2024-01-02 * "A"
  Assets:Bank  33.333 USD
  Income:Misc
2024-01-02 * "B"
  Assets:Bank  33.333 USD
  Income:Misc
2024-01-02 * "C"
  Assets:Bank  33.333 USD
  Income:Misc
2024-01-31 balance Assets:Bank 100.00 USD
"#;
        let result = parse(source);
        let params = code_lens_params();

        let balance_lens = find_balance_lens(
            handle_code_lens(&params, source, &result, None, PositionEncoding::Utf16)
                .expect("lenses emitted"),
        );
        let cmd = balance_lens
            .command
            .as_ref()
            .expect("balance lens ships fully-resolved");
        assert!(
            cmd.title.contains('✓'),
            "actual 99.999 USD is within the default ±0.01 tolerance \
             of asserted 100.00 USD; lens must show ✓ to match the \
             validator. got {:?}",
            cmd.title
        );
    }

    #[test]
    fn test_code_lens_balance_uses_full_ledger_in_multi_file_mode() {
        // Issue #470 coverage: when ledger_directives carries the
        // full multi-file view, balance assertions whose offsetting
        // transaction lives in a different file resolve correctly.
        // Pre-#1253 this was tested through handle_code_lens_resolve;
        // post-#1253 the eager path in handle_code_lens consumes the
        // same multi-file snapshot.
        let bank_source = r#"2024-01-01 open Assets:Bank:Checking USD
2024-01-01 open Income:Salary
2024-01-01 open Liabilities:Credit-Card
2024-01-15 * "Paycheck"
  Assets:Bank:Checking  5000 USD
  Income:Salary
2024-01-21 balance Assets:Bank:Checking 4950 USD
"#;
        let bank_result = parse(bank_source);
        let credit_card_source = r#"2024-01-20 * "Pay off credit card"
  Assets:Bank:Checking  -50 USD
  Liabilities:Credit-Card
"#;
        let credit_card_result = parse(credit_card_source);
        let mut full_directives = bank_result.directives.clone();
        full_directives.extend(credit_card_result.directives.clone());

        let params = code_lens_params();

        // Single-file view: the -50 offset isn't visible, balance
        // appears to mismatch.
        let single_lens = find_balance_lens(
            handle_code_lens(
                &params,
                bank_source,
                &bank_result,
                None,
                PositionEncoding::Utf16,
            )
            .expect("lenses emitted"),
        );
        let single_cmd = single_lens.command.as_ref().expect("ships resolved");
        assert!(
            single_cmd.title.contains("see diagnostic"),
            "single-file mismatch should point at the diagnostic; got {:?}",
            single_cmd.title
        );

        // Multi-file view: the -50 offset is visible, balance matches.
        let multi_lens = find_balance_lens(
            handle_code_lens(
                &params,
                bank_source,
                &bank_result,
                Some(&full_directives),
                PositionEncoding::Utf16,
            )
            .expect("lenses emitted"),
        );
        let multi_cmd = multi_lens.command.as_ref().expect("ships resolved");
        assert!(
            multi_cmd.title.contains('✓') && multi_cmd.title.contains("4950"),
            "multi-file match should ship `✓ Balance: 4950 USD`; got {:?}",
            multi_cmd.title
        );
    }

    #[test]
    fn test_code_lens_resolve_fallback_for_command_none_lens() {
        // Defensive fallback inside handle_code_lens_resolve: even
        // though no lens kind emitted by handle_code_lens ships with
        // command:None today (eager resolution since #1253), if a
        // future contributor adds a resolve-using lens kind and forgets
        // to handle it, the fallback guarantees the client renders a
        // sensible string instead of nvim's literal "Unresolved lens".
        let lens = CodeLens {
            range: Range {
                start: Position::new(0, 0),
                end: Position::new(0, 0),
            },
            command: None,
            data: None,
        };
        let resolved = handle_code_lens_resolve(lens);
        let cmd = resolved
            .command
            .as_ref()
            .expect("fallback must populate command");
        assert_eq!(cmd.command, "rledger.noop");
    }

    /// Regression for issue #1253 / #1245: balance lenses must ship
    /// FULLY-RESOLVED on the initial `textDocument/codeLens` response
    /// (no `data` payload, no placeholder, no resolve round-trip).
    ///
    /// Pre-#1253 the lens shipped with a `(checking…)` placeholder
    /// command and a `data: { kind: "balance", ... }` payload; the
    /// real `✓` / `⚠` title was filled in by `codeLens/resolve`.
    /// Under nvim's resolve-cancellation race (visible in #1253's
    /// LSP log as `"Cannot find request with id N whilst attempting
    /// to cancel"`) the resolve response was silently discarded and
    /// the lens stayed on the placeholder forever. Eager resolution
    /// removes the round-trip and makes the race unreachable.
    ///
    /// This test pins both invariants: the final title shows the
    /// real status (no `(checking…)`), and there is no `data` field
    /// asking the client to re-resolve.
    #[test]
    fn issue_1253_balance_lens_ships_eagerly_resolved() {
        // The user's reproduction from #1253: salary posts 1000 USD
        // on 02-01, balance assertion on 02-02 expects 1000 USD.
        let source = "\
2012-01-01 open Assets:Bank
2012-01-01 open Income:Employment

2012-02-01 * \"Salary\"
  Assets:Bank                   1000 USD
  Income:Employment

2012-02-02 balance Assets:Bank  1000 USD
";
        let result = parse(source);
        let params = code_lens_params();

        let balance_lens = find_balance_lens(
            handle_code_lens(&params, source, &result, None, PositionEncoding::Utf16)
                .expect("lenses emitted"),
        );

        // 1. The final ✓ title is set on the initial response.
        let cmd = balance_lens
            .command
            .as_ref()
            .expect("balance lens ships fully-resolved");
        assert!(
            cmd.title.contains('✓'),
            "issue #1253: passing assertion must ship with the real ✓ \
             title on the initial response, not a `(checking…)` \
             placeholder that nvim could leave stuck. got {:?}",
            cmd.title
        );
        assert!(
            !cmd.title.contains("checking"),
            "issue #1253: title must not contain the `(checking…)` \
             placeholder; that's the stuck-state symptom. got {:?}",
            cmd.title
        );

        // 2. No `data` payload means no codeLens/resolve round-trip,
        //    which means no race window for nvim to cancel.
        assert!(
            balance_lens.data.is_none(),
            "issue #1253: balance lens must not carry a resolve-data \
             payload; the resolve round-trip is what nvim could race \
             against cancellation. got data = {:?}",
            balance_lens.data
        );
    }

    fn code_lens_params() -> CodeLensParams {
        CodeLensParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        }
    }

    fn find_balance_lens(lenses: Vec<CodeLens>) -> CodeLens {
        lenses
            .into_iter()
            .find(|l| {
                l.command
                    .as_ref()
                    .is_some_and(|c| c.title.contains("Balance:"))
            })
            .expect("balance lens emitted")
    }
}
