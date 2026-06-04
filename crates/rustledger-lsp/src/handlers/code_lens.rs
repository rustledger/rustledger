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
    CodeLens, CodeLensParams, Command, Diagnostic, DiagnosticSeverity, Position, Range,
};
use rustledger_core::Directive;
use rustledger_parser::ParseResult;
use std::collections::HashMap;

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
                    cached_diagnostics,
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

/// Render the balance lens title for a balance directive on `line`.
///
/// `cached_diagnostics` is the validator's last-computed verdict for
/// this URI:
///
/// - `None`: the validator hasn't run yet for this file (cold start).
///   Render neutrally — `Balance: X USD` with no ✓/⚠ symbol. Never
///   claim a verdict we can't back up.
/// - `Some(diags)` with no error overlapping `line`: validator says the
///   assertion holds. Render `✓ Balance: X USD`.
/// - `Some(diags)` with an error overlapping `line`: validator already
///   surfaced the failure. Render `⚠ Balance: X USD (see diagnostic)` —
///   "see diagnostic" is a true link because the diagnostic exists by
///   construction.
fn balance_lens_title(
    amount: rustledger_core::Decimal,
    currency: &str,
    line: u32,
    cached_diagnostics: Option<&[Diagnostic]>,
) -> String {
    let amount_str = format!("Balance: {amount} {currency}");
    match cached_diagnostics {
        None => amount_str,
        Some(diags) => {
            if has_error_at_line(diags, line) {
                format!("⚠ {amount_str} (see diagnostic)")
            } else {
                format!("✓ {amount_str}")
            }
        }
    }
}

/// Does the diagnostic slice contain an ERROR-severity entry whose
/// range starts on `line`?
///
/// The validator emits balance-assertion failures with their range
/// anchored on the balance directive's line. Match on
/// `range.start.line` only (not full Range overlap) so a multi-line
/// diagnostic at this line still matches. Severity filter on `ERROR`
/// excludes Hint / Information entries (e.g., code-action suggestions)
/// that would otherwise mark a clean assertion as ⚠.
fn has_error_at_line(diagnostics: &[Diagnostic], line: u32) -> bool {
    diagnostics
        .iter()
        .any(|d| d.range.start.line == line && d.severity == Some(DiagnosticSeverity::ERROR))
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

    /// Synthetic ERROR diagnostic at the given zero-based line. Mirrors
    /// what `all_diagnostics` produces for a failed balance assertion;
    /// the lens treats anything matching this shape as the validator
    /// saying "this balance is wrong."
    fn error_at_line(line: u32) -> Diagnostic {
        Diagnostic {
            range: Range {
                start: Position::new(line, 0),
                end: Position::new(line, 80),
            },
            severity: Some(DiagnosticSeverity::ERROR),
            code: Some(NumberOrString::String("E2001".into())),
            code_description: None,
            source: Some("rledger".into()),
            message: "Balance assertion failed".into(),
            related_information: None,
            tags: None,
            data: None,
        }
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
