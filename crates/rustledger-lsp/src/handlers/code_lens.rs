//! Code lens handler for showing inline information.
//!
//! Provides code lenses above:
//! - Account open directives (showing transaction count)
//! - Transactions (showing posting count and currencies)
//! - Balance assertions (with verification status, sourced from the
//!   validator's already-computed diagnostic for the same file).
//!
//! # Verdict source: the validator's diagnostic cache
//!
//! Pre-#1264 the balance lens ran its own evaluator —
//! `parse → sort → book` over the parse result, without applying
//! plugins. That second pipeline silently disagreed with `rledger check`
//! on every ledger that relied on plugin output (`effective_date`,
//! `lazy_balance`, any user plugin that rewrites postings post-booking).
//! The dead-link UX was the symptom: `⚠ ... (see diagnostic)` while no
//! diagnostic existed because the validator (running the full pipeline)
//! agreed the assertion held.
//!
//! The fix is structural: stop having a second pipeline. The lens reads
//! `MainLoopState::diagnostics[uri]`, which `publish_diagnostics`
//! populates by running the validator over the same full pipeline
//! `rledger check` uses (synth-plugins → Early → book → regular-plugins
//! → Late). If the validator emitted an error at a balance directive's
//! line, the lens shows `⚠`; otherwise `✓`. When the cache hasn't been
//! populated yet (cold start before the first `publish_diagnostics`),
//! the lens shows a neutral `Balance: X USD` rather than lying.
//!
//! # Eager resolution (preserved from #1253)
//!
//! Lenses still ship with `command: Some(...)` and `data: None` on the
//! initial `textDocument/codeLens` response. No `codeLens/resolve`
//! round-trip, so no exposure to nvim's resolve-cancellation race
//! (#1245 / #1253). [`handle_code_lens_resolve`] remains as a defensive
//! fallback for any future lens kind that genuinely needs deferred
//! resolution.

use lsp_types::{
    CodeLens, CodeLensParams, Command, Diagnostic, DiagnosticSeverity, NumberOrString, Position,
    Range,
};
use rustledger_core::Directive;
use rustledger_parser::ParseResult;
use rustledger_validate::ErrorCode;
use std::collections::HashMap;

use super::diagnostics::validation_would_run;
use super::utils::{LineIndex, PositionEncoding};

/// Handle a code lens request.
///
/// `cached_diagnostics` is the validator's last-computed diagnostic
/// vector for this URI (held in `MainLoopState::diagnostics`). It
/// reflects the full-pipeline verdict the user would see from
/// `rledger check`. The lens consults it instead of running a parallel
/// evaluator.
///
/// `None` means the validator hasn't run for this file yet (cold start
/// between server initialization and the first `publish_diagnostics`
/// call). The balance lens then renders neutrally — never claiming a
/// verdict the lens cannot back up.
///
/// The balance lens ALSO renders neutrally when validation would have
/// been skipped for this buffer (parse errors elsewhere in the file,
/// or `source.len() > MAX_VALIDATION_FILE_SIZE`). Without this, the
/// diagnostic cache reads `Some(&[])` and the lens would render `✓`
/// for assertions the validator never evaluated — the inverse-symmetric
/// failure of #1264.
pub fn handle_code_lens(
    params: &CodeLensParams,
    source: &str,
    parse_result: &ParseResult,
    cached_diagnostics: Option<&[Diagnostic]>,
    encoding: PositionEncoding,
) -> Option<Vec<CodeLens>> {
    let line_index = LineIndex::new(source, encoding);
    let mut lenses = Vec::new();
    let uri = params.text_document.uri.as_str();
    // Even with a populated cache, the validator may have declined to
    // run (large file, or parse errors elsewhere). Treat that as cold-
    // start for the lens: the cache is `Some(&[])` not because the
    // assertion holds but because no balance verdict was computed.
    let verdict_diagnostics = if validation_would_run(source, parse_result) {
        cached_diagnostics
    } else {
        None
    };

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
                // Consult the validator's cached verdict; never re-derive.
                // See module rustdoc.
                let title = balance_lens_title(
                    bal.amount.number,
                    bal.amount.currency.as_ref(),
                    line,
                    verdict_diagnostics,
                );
                lenses.push(CodeLens {
                    range: Range {
                        start: Position::new(line, 0),
                        end: Position::new(line, 0),
                    },
                    command: Some(Command {
                        title,
                        command: "rledger.noop".to_string(),
                        arguments: None,
                    }),
                    // No data payload: the lens ships fully-resolved on
                    // the initial response. Preserves the #1253 invariant
                    // that there is no resolve round-trip nvim could
                    // race against cancellation.
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

/// Error codes the lens treats as a balance-arithmetic failure on a
/// balance directive's line.
///
/// Pulled from [`ErrorCode`] (`pub const fn code() -> &'static str`)
/// instead of hardcoding the strings, so:
///
/// - **Renaming a variant** (e.g., `BalanceAssertionFailed` →
///   `BalanceMismatch`) breaks the lens build — the const-fn call
///   resolves a symbol that no longer exists.
/// - **Renumbering the string returned by `code()`** (e.g., `"E2001"`
///   → `"E2099"`) is detected and propagated automatically — the
///   lens build still passes and `BALANCE_ERROR_CODES` picks up the
///   new string, so the runtime match against the validator's
///   emitted code stays in sync without any manual update.
///
/// Hardcoding `&["E2001", "E2002", "E2004"]` would have given the
/// opposite property: renaming would have compiled silently, and only
/// renumbering at the validator side (without a corresponding lens
/// update) would have produced runtime drift. The const-fn bridge
/// trades the cheaper failure mode for the more expensive one.
///
/// The codes themselves:
///
/// - `E2001` ([`ErrorCode::BalanceAssertionFailed`]): asserted amount
///   != actual.
/// - `E2002` ([`ErrorCode::BalanceToleranceExceeded`]): difference is
///   beyond the explicit `~` tolerance.
/// - `E2004` ([`ErrorCode::MultiplePadForBalance`]): two effective
///   pads before the assertion. The validator's lib.rs:548-562 patches
///   the balance directive's span onto this error (it's constructed
///   with `bal.date` and no span of its own), so the diagnostic anchors
///   on the balance line — same as E2001/E2002. The user-facing failure
///   IS that the asserted balance can't be unambiguously verified.
///
/// Codes that may land at the balance line but describe a different
/// problem (`E1001 AccountNotOpen`, parse errors, plugin errors
/// patched onto the span) are deliberately excluded. Showing
/// `⚠ Balance: X USD (see diagnostic)` for those misattributes the
/// failure category: the user clicks the lens expecting a balance
/// arithmetic explanation and finds something unrelated. The lens
/// renders neutrally for those, letting the diagnostic itself speak.
///
/// `E2003 PadWithoutBalance` anchors on the pad directive, not the
/// balance directive, so it's not relevant to this list.
const BALANCE_ERROR_CODES: &[&str] = &[
    ErrorCode::BalanceAssertionFailed.code(),
    ErrorCode::BalanceToleranceExceeded.code(),
    ErrorCode::MultiplePadForBalance.code(),
];

/// Render the balance lens title for a balance directive on `line`.
///
/// `cached_diagnostics` is the validator's last-computed verdict for
/// this URI (after [`validation_would_run`] confirmed the validator
/// actually ran):
///
/// - `None`: the validator hasn't run yet for this file (cold start)
///   OR validation was skipped (parse errors, file too large). Render
///   neutrally — `Balance: X USD` with no ✓/⚠ symbol. Never claim a
///   verdict we can't back up.
/// - `Some(diags)` with a `BALANCE_ERROR_CODES` entry at `line`: the
///   validator emitted a real balance-arithmetic failure. Render
///   `⚠ Balance: X USD (see diagnostic)` — "see diagnostic" is a true
///   link by construction.
/// - `Some(diags)` with some OTHER non-HINT diagnostic at `line`
///   (e.g., `E1001` AccountNotOpen ERROR, `FutureDate` WARNING,
///   `DateOutOfOrder` INFORMATION) but NO `BALANCE_ERROR_CODES`:
///   the validator has something to say about this directive but
///   it isn't a balance-arithmetic failure. Render neutrally; don't
///   misattribute it as a balance failure AND don't claim ✓ on a
///   directive the validator is actively flagging.
/// - `Some(diags)` with no relevant diagnostic at `line`: the
///   validator says the assertion holds. Render `✓ Balance: X USD`.
fn balance_lens_title(
    amount: rustledger_core::Decimal,
    currency: &str,
    line: u32,
    cached_diagnostics: Option<&[Diagnostic]>,
) -> String {
    let amount_str = format!("Balance: {amount} {currency}");
    let Some(diags) = cached_diagnostics else {
        return amount_str;
    };
    if has_balance_error_at_line(diags, line) {
        format!("⚠ {amount_str} (see diagnostic)")
    } else if has_non_balance_error_at_line(diags, line) {
        // A diagnostic at this line is about something else; let it
        // surface independently. Don't claim ✓ (the assertion's
        // verdict is uncertain in the presence of an account/parse
        // error here) and don't claim ⚠ (the asserted arithmetic
        // isn't what failed).
        amount_str
    } else {
        format!("✓ {amount_str}")
    }
}

/// Does the diagnostic slice contain an ERROR with one of the
/// balance-arithmetic error codes anchored at `line.start`?
fn has_balance_error_at_line(diagnostics: &[Diagnostic], line: u32) -> bool {
    diagnostics.iter().any(|d| {
        d.range.start.line == line
            && d.severity == Some(DiagnosticSeverity::ERROR)
            && is_balance_error_code(d.code.as_ref())
    })
}

/// Does the diagnostic slice contain ANY non-balance diagnostic
/// (ERROR, WARNING, or INFORMATION severity) anchored at `line.start`?
///
/// Severity matters: a balance directive can carry a WARNING-severity
/// diagnostic (`FutureDate` E10002, `DateOutOfOrder` E10001, etc.) that
/// gets the balance directive's span patched onto it via
/// `validate/lib.rs:548-562`. If we filtered on ERROR only, the lens
/// would render `✓ Balance: X USD` for a directive the validator is
/// actively warning about — the same false-confidence pattern #1264
/// closed for plugins, just transposed to severity-filtering. Any
/// non-balance diagnostic at the line tells us "the validator has
/// something to say about this directive" and disqualifies the ✓.
///
/// HINT severity is excluded because hints are routinely produced as
/// code-action suggestions; treating them as "something is wrong"
/// would surface ✓-disqualifying noise on every code-action-eligible
/// line.
///
/// Diagnostics with a zero-width range anchored at `(0, 0)..(0, 0)`
/// are ALSO excluded: that's the sentinel for "I have no source span"
/// used by the plugin-error emitter at
/// `handlers/diagnostics.rs:325-329` (and any future spanless
/// diagnostic source). Treating them as anchored on line 0 would make
/// every balance directive on line 0 — common in scratch buffers and
/// include-only files — render neutral whenever a plugin happens to
/// fail. Keep the lens focused on directive-anchored diagnostics; the
/// global ones surface independently in the problems panel.
fn has_non_balance_error_at_line(diagnostics: &[Diagnostic], line: u32) -> bool {
    diagnostics.iter().any(|d| {
        d.range.start.line == line
            && !is_global_sentinel_range(&d.range)
            && matches!(
                d.severity,
                Some(DiagnosticSeverity::ERROR)
                    | Some(DiagnosticSeverity::WARNING)
                    | Some(DiagnosticSeverity::INFORMATION)
            )
            && !is_balance_error_code(d.code.as_ref())
    })
}

/// Returns true for the `(0, 0)..(0, 0)` sentinel that spanless
/// diagnostic emitters (plugin errors today) use when they have no
/// source location to attach. A diagnostic with this exact range is
/// "global to the file," not anchored on line 0.
fn is_global_sentinel_range(range: &Range) -> bool {
    range.start.line == 0
        && range.start.character == 0
        && range.end.line == 0
        && range.end.character == 0
}

fn is_balance_error_code(code: Option<&NumberOrString>) -> bool {
    match code {
        Some(NumberOrString::String(s)) => BALANCE_ERROR_CODES.contains(&s.as_str()),
        Some(NumberOrString::Number(n)) => {
            // Today every validator-emitted diagnostic code is a
            // String (see `validation_error_to_diagnostic` at
            // diagnostics.rs:~420). If a future contributor adds a
            // Number-coded path, this branch fires — debug builds get
            // a loud signal so the lens's filter can be updated;
            // release builds default to "not a balance code" to avoid
            // a spurious ⚠ on an unknown numeric code.
            debug_assert!(
                false,
                "lens received an unexpected numeric diagnostic code: {n}; \
                 update `is_balance_error_code` or normalize at the emitter",
            );
            false
        }
        None => false,
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
    use lsp_types::{DiagnosticSeverity, NumberOrString};
    use rustledger_parser::parse;

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

    /// Synthetic diagnostic at the given zero-based line with the given
    /// LSP error code and severity. Source string matches what the
    /// validator emits in production (`"rustledger"`, see
    /// `diagnostics.rs:145`) so any future filter on `source` would
    /// behave the same in tests and production.
    fn diagnostic_with_code_severity_at_line(
        code: &str,
        severity: DiagnosticSeverity,
        line: u32,
    ) -> Diagnostic {
        Diagnostic {
            range: Range {
                start: Position::new(line, 0),
                end: Position::new(line, 80),
            },
            severity: Some(severity),
            code: Some(NumberOrString::String(code.into())),
            code_description: None,
            source: Some("rustledger".into()),
            message: format!("{code} test diagnostic"),
            related_information: None,
            tags: None,
            data: None,
        }
    }

    /// Default-case: a balance-assertion-failed (E2001) ERROR
    /// diagnostic at `line`. The most common test fixture; non-default
    /// shapes go through `diagnostic_with_code_severity_at_line`
    /// directly so the chosen severity is visible at the call site.
    fn error_at_line(line: u32) -> Diagnostic {
        diagnostic_with_code_severity_at_line("E2001", DiagnosticSeverity::ERROR, line)
    }

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
        let params = code_lens_params();

        let lenses = handle_code_lens(&params, source, &result, Some(&[]), PositionEncoding::Utf16);
        let lenses = lenses.expect("lenses emitted");
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

    /// Cold-start case: no diagnostics have been computed yet for this
    /// URI. The lens MUST render the balance amount without a verdict
    /// symbol. Pre-#1264 the lens computed its own verdict locally and
    /// would emit ✓ or ⚠ based on its (plugin-less) approximation;
    /// post-#1264 it never claims a verdict it didn't get from the
    /// validator.
    #[test]
    fn balance_lens_neutral_when_diagnostics_not_yet_computed() {
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
        let cmd = balance_lens.command.as_ref().expect("ships resolved");
        assert!(
            !cmd.title.contains('✓') && !cmd.title.contains('⚠'),
            "cold start: lens must not claim a verdict before the \
             validator has run. got {:?}",
            cmd.title
        );
        assert!(cmd.title.starts_with("Balance:"));
        assert!(cmd.title.contains("100"));
    }

    /// Validator says PASS (empty diagnostics): lens shows ✓.
    #[test]
    fn balance_lens_shows_check_when_validator_passes() {
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-31 balance Assets:Bank 100.00 USD
"#;
        let result = parse(source);
        let params = code_lens_params();

        let balance_lens = find_balance_lens(
            handle_code_lens(&params, source, &result, Some(&[]), PositionEncoding::Utf16)
                .expect("lenses emitted"),
        );
        let cmd = balance_lens.command.as_ref().expect("ships resolved");
        assert!(cmd.title.contains('✓'), "got {:?}", cmd.title);
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

    /// Validator emitted an ERROR at the balance line: lens shows ⚠.
    /// The "see diagnostic" link is now true by construction — the
    /// diagnostic exists because we read it from the cache.
    #[test]
    fn balance_lens_shows_warning_when_validator_fails() {
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-31 balance Assets:Bank 100 USD
"#;
        let result = parse(source);
        let params = code_lens_params();

        // `2024-01-31 balance ...` is on line index 1 (zero-based) of
        // the source above.
        let diags = vec![error_at_line(1)];
        let balance_lens = find_balance_lens(
            handle_code_lens(
                &params,
                source,
                &result,
                Some(&diags),
                PositionEncoding::Utf16,
            )
            .expect("lenses emitted"),
        );
        let cmd = balance_lens.command.as_ref().expect("ships resolved");
        assert!(
            cmd.title.contains('⚠') && cmd.title.contains("see diagnostic"),
            "got {:?}",
            cmd.title
        );
        assert_eq!(cmd.command, "rledger.noop");
    }

    /// The lens MUST follow the diagnostic cache, not the parse result.
    /// Pre-#1264 a passing parse + missing-plugin pipeline could
    /// disagree with the validator (the bug in #1264). The new code path
    /// is verdict-from-cache; we pin that by feeding a parse whose
    /// "naive" answer would be ✓ together with an error diagnostic and
    /// asserting the lens shows ⚠ regardless.
    #[test]
    fn balance_lens_follows_diagnostic_cache_not_local_eval() {
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-01 open Income:Salary
2024-01-15 * "Deposit"
  Assets:Bank  100.00 USD
  Income:Salary
2024-01-31 balance Assets:Bank 100.00 USD
"#;
        let result = parse(source);
        let params = code_lens_params();

        // Locally this balance assertion would pass (deposit = 100,
        // assertion = 100). Feed an error diagnostic anyway and verify
        // the lens follows the diagnostic, not the parse.
        let diags = vec![error_at_line(5)];
        let balance_lens = find_balance_lens(
            handle_code_lens(
                &params,
                source,
                &result,
                Some(&diags),
                PositionEncoding::Utf16,
            )
            .expect("lenses emitted"),
        );
        let cmd = balance_lens.command.as_ref().expect("ships resolved");
        assert!(
            cmd.title.contains('⚠'),
            "lens must follow validator's verdict, not re-derive from \
             parse_result. got {:?}",
            cmd.title
        );
    }

    /// Inverse of the previous test: a parse whose naive evaluation
    /// would say ⚠ (mismatched amounts), but no diagnostic in the
    /// cache, must render ✓. This is the #1264 repro reduced to a unit
    /// test: the lens's old evaluator would have ⚠'d here, but the
    /// validator (running plugins) is right and the lens follows it.
    #[test]
    fn balance_lens_shows_check_when_parse_disagrees_but_validator_passes() {
        // Parse-time arithmetic says 1000 - 100 = 900, assertion claims
        // 1000. The OLD evaluator would emit ⚠. The new lens consults
        // the diagnostic cache; empty diagnostics mean validator passed.
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-01 open Income:Salary
2024-01-01 open Expenses:Food
2024-02-01 * "Salary"
  Assets:Bank  1000 USD
  Income:Salary
2024-02-03 * "Food"
  Assets:Bank  -100 USD
  Expenses:Food
2024-02-04 balance Assets:Bank 1000 USD
"#;
        let result = parse(source);
        let params = code_lens_params();

        let balance_lens = find_balance_lens(
            handle_code_lens(&params, source, &result, Some(&[]), PositionEncoding::Utf16)
                .expect("lenses emitted"),
        );
        let cmd = balance_lens.command.as_ref().expect("ships resolved");
        assert!(
            cmd.title.contains('✓'),
            "lens must trust the validator (empty diagnostics) even \
             when a naive parse-only reading would disagree. This is \
             the structural property that fixes #1264's effective_date \
             false positive: the validator runs plugins, the lens \
             trusts the validator. got {:?}",
            cmd.title
        );
    }

    /// When the buffer has parse errors elsewhere, `all_diagnostics`
    /// (diagnostics.rs:554) skips validation entirely; the cache for
    /// the URI then contains only parse-error diagnostics — none of
    /// which sit at the balance line. The lens MUST render neutrally
    /// in this case, not ✓: the validator did not evaluate the
    /// assertion. This is the inverse-symmetric failure of the #1264
    /// dead-link UX (silent ✓ instead of silent ⚠) — both come from
    /// the lens asserting verdicts it cannot back up.
    #[test]
    fn balance_lens_neutral_when_parse_errors_skip_validation() {
        // Open + balance directives come first (cleanly parsed, so the
        // balance lens is always emitted regardless of how the parser
        // recovers from the trailing garbage). The malformed line at
        // the END forces `parse_result.errors` to be non-empty without
        // making the test depend on parser-recovery behavior at the
        // top of the file.
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-31 balance Assets:Bank 100.00 USD
!!! syntax garbage on a trailing line
"#;
        let result = parse(source);
        assert!(
            !result.errors.is_empty(),
            "test setup: source must produce a parse error to exercise \
             the validation-skip branch. got errors = {:?}",
            result.errors,
        );
        let params = code_lens_params();

        // Diagnostic cache populated and contains nothing at the
        // balance line. Pre-fix the lens would have read this as
        // "validator approved" and rendered ✓.
        let balance_lens = find_balance_lens(
            handle_code_lens(&params, source, &result, Some(&[]), PositionEncoding::Utf16)
                .expect("lenses emitted"),
        );
        let cmd = balance_lens.command.as_ref().expect("ships resolved");
        assert!(
            !cmd.title.contains('✓') && !cmd.title.contains('⚠'),
            "parse-error skip path: lens must not claim a verdict the \
             validator never computed. got {:?}",
            cmd.title
        );
        assert!(cmd.title.starts_with("Balance:"));
    }

    /// A non-balance ERROR diagnostic at the balance directive's line
    /// (e.g., `E1001 AccountNotOpen`) must NOT render as
    /// `⚠ Balance: X USD (see diagnostic)`. The user clicking that
    /// lens would expect a balance-arithmetic explanation and instead
    /// see something unrelated. The lens renders neutrally; the
    /// non-balance diagnostic surfaces independently with its own
    /// (correct) message.
    #[test]
    fn balance_lens_neutral_on_non_balance_error_at_line() {
        let source = r#"2024-01-31 balance Assets:NeverOpened 0 USD
"#;
        let result = parse(source);
        let params = code_lens_params();

        // E1001 (account never opened) at the balance directive's line.
        let diags = vec![diagnostic_with_code_severity_at_line(
            "E1001",
            DiagnosticSeverity::ERROR,
            0,
        )];
        let balance_lens = find_balance_lens(
            handle_code_lens(
                &params,
                source,
                &result,
                Some(&diags),
                PositionEncoding::Utf16,
            )
            .expect("lenses emitted"),
        );
        let cmd = balance_lens.command.as_ref().expect("ships resolved");
        assert!(
            !cmd.title.contains('⚠') && !cmd.title.contains("see diagnostic"),
            "non-balance error (E1001) at the balance line must not \
             render as a balance arithmetic failure. got {:?}",
            cmd.title
        );
        assert!(
            !cmd.title.contains('✓'),
            "lens must not claim ✓ when an unrelated error blankets \
             the assertion's line — the assertion's status is uncertain. \
             got {:?}",
            cmd.title
        );
    }

    /// WARNING-severity diagnostics that anchor on the balance line —
    /// `FutureDate`, `DateOutOfOrder`, `AccountCloseNotEmpty` —
    /// disqualify ✓. Without this, the lens claims the assertion holds
    /// while the validator is actively flagging the directive's date or
    /// account state, which is the same false-confidence pattern #1264
    /// closed for plugins, just transposed to severity filtering.
    #[test]
    fn balance_lens_neutral_on_non_balance_warning_at_line() {
        let source = r#"2099-01-31 balance Assets:Bank 100 USD
"#;
        let result = parse(source);
        let params = code_lens_params();

        // E10002 (FutureDate) at WARNING severity — what the
        // validator actually emits for a balance directive dated
        // after `today`.
        let diags = vec![diagnostic_with_code_severity_at_line(
            "E10002",
            DiagnosticSeverity::WARNING,
            0,
        )];
        let balance_lens = find_balance_lens(
            handle_code_lens(
                &params,
                source,
                &result,
                Some(&diags),
                PositionEncoding::Utf16,
            )
            .expect("lenses emitted"),
        );
        let cmd = balance_lens.command.as_ref().expect("ships resolved");
        assert!(
            !cmd.title.contains('✓') && !cmd.title.contains('⚠'),
            "warning at the balance line must disqualify ✓; lens must \
             not claim a verdict while the validator is flagging the \
             directive. got {:?}",
            cmd.title
        );
    }

    /// INFORMATION-severity diagnostics at the balance line also
    /// disqualify ✓ — same rationale as WARNING, applied to
    /// `DateOutOfOrder` and similar advisory-level findings the
    /// validator anchors via the span-patch path.
    #[test]
    fn balance_lens_neutral_on_information_severity_at_line() {
        let source = r#"2024-01-31 balance Assets:Bank 100 USD
"#;
        let result = parse(source);
        let params = code_lens_params();

        let diags = vec![diagnostic_with_code_severity_at_line(
            "E10001",
            DiagnosticSeverity::INFORMATION,
            0,
        )];
        let balance_lens = find_balance_lens(
            handle_code_lens(
                &params,
                source,
                &result,
                Some(&diags),
                PositionEncoding::Utf16,
            )
            .expect("lenses emitted"),
        );
        let cmd = balance_lens.command.as_ref().expect("ships resolved");
        assert!(
            !cmd.title.contains('✓') && !cmd.title.contains('⚠'),
            "information-severity diagnostic at the balance line must \
             disqualify ✓. got {:?}",
            cmd.title
        );
    }

    /// HINT-severity diagnostics are excluded from the ✓-disqualifying
    /// set — code-action hints routinely anchor on directives, and
    /// treating them as "validator flagged this" would produce neutral
    /// titles on every code-action-eligible balance line.
    #[test]
    fn balance_lens_keeps_check_when_only_hint_at_line() {
        let source = r#"2024-01-31 balance Assets:Bank 100 USD
"#;
        let result = parse(source);
        let params = code_lens_params();

        let diags = vec![diagnostic_with_code_severity_at_line(
            "H1001",
            DiagnosticSeverity::HINT,
            0,
        )];
        let balance_lens = find_balance_lens(
            handle_code_lens(
                &params,
                source,
                &result,
                Some(&diags),
                PositionEncoding::Utf16,
            )
            .expect("lenses emitted"),
        );
        let cmd = balance_lens.command.as_ref().expect("ships resolved");
        assert!(
            cmd.title.contains('✓'),
            "HINT-severity must not disqualify ✓ — code-action hints \
             routinely anchor on directives. got {:?}",
            cmd.title
        );
    }

    /// Plugin errors (and any future spanless diagnostic) are emitted
    /// with the global sentinel range `(0,0)..(0,0)` per
    /// `handlers/diagnostics.rs:325-329`. A balance directive that
    /// happens to land on line 0 must NOT be marked neutral just
    /// because a plugin failed elsewhere in the file. The sentinel
    /// range exclusion keeps the lens focused on directive-anchored
    /// diagnostics; the global plugin error surfaces independently in
    /// the problems panel.
    #[test]
    fn balance_lens_ignores_global_sentinel_range_diagnostic() {
        // Balance directive IS on line 0 — the case where a naive
        // line-only filter would conflate the global plugin error with
        // a directive-anchored one.
        let source = "2024-01-31 balance Assets:Bank 100 USD\n";
        let result = parse(source);
        let params = code_lens_params();

        // Plugin-shaped diagnostic: ERROR severity, range (0,0)..(0,0),
        // non-balance code. Mirrors what diagnostics.rs:325-329 emits.
        let plugin_error = Diagnostic {
            range: Range {
                start: Position::new(0, 0),
                end: Position::new(0, 0),
            },
            severity: Some(DiagnosticSeverity::ERROR),
            code: Some(NumberOrString::String("PluginLoadFailed".into())),
            code_description: None,
            source: Some("rustledger".into()),
            message: "plugin failed to load".into(),
            related_information: None,
            tags: None,
            data: None,
        };
        let balance_lens = find_balance_lens(
            handle_code_lens(
                &params,
                source,
                &result,
                Some(&[plugin_error]),
                PositionEncoding::Utf16,
            )
            .expect("lenses emitted"),
        );
        let cmd = balance_lens.command.as_ref().expect("ships resolved");
        assert!(
            cmd.title.contains('✓'),
            "global-sentinel-range diagnostic (plugin error with no \
             source span) must not disqualify ✓ on a line-0 balance \
             directive; the sentinel range means 'global', not \
             'anchored on line 0'. got {:?}",
            cmd.title
        );
    }

    /// Defensive fallback inside handle_code_lens_resolve: even
    /// though no lens kind emitted by handle_code_lens ships with
    /// command:None today (eager resolution since #1253), if a
    /// future contributor adds a resolve-using lens kind and forgets
    /// to handle it, the fallback guarantees the client renders a
    /// sensible string instead of nvim's literal "Unresolved lens".
    #[test]
    fn test_code_lens_resolve_fallback_for_command_none_lens() {
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
    /// The #1264 refactor changed WHAT data the eager response carries
    /// (validator's verdict instead of a local re-derivation) but kept
    /// the eager-ship invariant.
    #[test]
    fn issue_1253_balance_lens_ships_eagerly_resolved() {
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
            handle_code_lens(&params, source, &result, Some(&[]), PositionEncoding::Utf16)
                .expect("lenses emitted"),
        );

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

        assert!(
            balance_lens.data.is_none(),
            "issue #1253: balance lens must not carry a resolve-data \
             payload; the resolve round-trip is what nvim could race \
             against cancellation. got data = {:?}",
            balance_lens.data
        );
    }
}
