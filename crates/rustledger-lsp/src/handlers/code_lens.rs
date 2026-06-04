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
/// balance directive's line:
///
/// - `E2001`: balance assertion failed (asserted amount != actual)
/// - `E2002`: balance exceeds explicit tolerance
///
/// Other ERROR diagnostics that may also land on a balance directive's
/// line — `E1001 AccountNotOpen`, parse errors, plugin errors patched
/// onto the balance span — describe a different problem. Showing
/// `⚠ Balance: X USD (see diagnostic)` for those misattributes the
/// failure category: the user clicks the lens expecting a balance
/// arithmetic explanation and finds something unrelated. The lens
/// renders neutrally for those instead, letting the diagnostic itself
/// speak.
const BALANCE_ERROR_CODES: &[&str] = &["E2001", "E2002"];

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
/// - `Some(diags)` with some OTHER ERROR at `line` (e.g., `E1001`
///   AccountNotOpen) but NO `BALANCE_ERROR_CODES`: a non-balance
///   diagnostic happens to anchor here. Render neutrally; don't
///   misattribute it as a balance failure.
/// - `Some(diags)` with no ERROR at all at `line`: the validator
///   says the assertion holds. Render `✓ Balance: X USD`.
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

/// Does the diagnostic slice contain an ERROR at `line.start` whose
/// code is NOT one of the balance-arithmetic codes? (Used to decide
/// whether to render neutrally instead of ✓.)
fn has_non_balance_error_at_line(diagnostics: &[Diagnostic], line: u32) -> bool {
    diagnostics.iter().any(|d| {
        d.range.start.line == line
            && d.severity == Some(DiagnosticSeverity::ERROR)
            && !is_balance_error_code(d.code.as_ref())
    })
}

fn is_balance_error_code(code: Option<&NumberOrString>) -> bool {
    match code {
        Some(NumberOrString::String(s)) => BALANCE_ERROR_CODES.contains(&s.as_str()),
        _ => false,
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

    /// Synthetic ERROR diagnostic at the given zero-based line with
    /// the given LSP error code. Source string matches what the
    /// validator emits in production (`"rustledger"`, see
    /// `diagnostics.rs:145`) so any future filter on `source` would
    /// behave the same in tests and production.
    fn error_with_code_at_line(code: &str, line: u32) -> Diagnostic {
        Diagnostic {
            range: Range {
                start: Position::new(line, 0),
                end: Position::new(line, 80),
            },
            severity: Some(DiagnosticSeverity::ERROR),
            code: Some(NumberOrString::String(code.into())),
            code_description: None,
            source: Some("rustledger".into()),
            message: format!("{code} test diagnostic"),
            related_information: None,
            tags: None,
            data: None,
        }
    }

    /// Default-case: a balance-assertion-failed diagnostic at `line`.
    fn error_at_line(line: u32) -> Diagnostic {
        error_with_code_at_line("E2001", line)
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
        // First non-comment line is a syntax error (stray garbage),
        // forcing parse_result.errors to be non-empty.
        let source = r#"!!! syntax garbage on line 0
2024-01-01 open Assets:Bank USD
2024-01-31 balance Assets:Bank 100.00 USD
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
        let diags = vec![error_with_code_at_line("E1001", 0)];
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
