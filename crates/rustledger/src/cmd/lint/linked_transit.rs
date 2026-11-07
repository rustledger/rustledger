//! Read-only inspection of explicitly linked transit postings.
//!
//! The lint reads the booked ledger: each input is loaded, refused if it has
//! load errors (as `lint closed-nonempty` does), then run through
//! [`rustledger_loader::process`] with plugins, so an elided transit amount
//! is the amount booking computed and a `plugin` line runs as it does in
//! `check`. A processing error refuses the input too: a transaction booking
//! rejected is left out of the booked stream, and reporting its link as
//! `missing` (or its partner as matched) would be a misleading answer.
//!
//! A configuration that cannot match anything is said so, not answered with
//! an empty report: an `--account` that is not an account name is refused, a
//! leading `^` on `--link-prefix` is dropped with a note, and a configured
//! account the ledger never uses, or a prefix no link starts with, is a
//! warning. Warnings go where the CLI's warnings go (stderr, or the
//! `ag-rledger` envelope's `warnings`).

use anyhow::{Context, Result};
use clap::Parser;
use rustledger_core::{Amount, Directive, Link};
use rustledger_loader::{ErrorSeverity, LedgerError, LoadOptions, Loader};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::process::ExitCode;

use super::closed_nonempty::OutputFormat;
use crate::cmd::messages::Messages;
use crate::cmd::report_cmd::{Diagnostic, Diagnostics};

/// The codes of the warnings this lint emits, as carried in `ag-rledger`'s
/// `warnings`.
pub mod warning_codes {
    /// `--link-prefix` began with `^`, which was dropped: links are matched
    /// without it.
    pub const LINK_PREFIX_CARET: &str = "LINK_PREFIX_CARET";
    /// A configured `--account` appears nowhere in the ledger.
    pub const ACCOUNT_NOT_IN_LEDGER: &str = "ACCOUNT_NOT_IN_LEDGER";
    /// No link in the ledger starts with `--link-prefix`.
    pub const NO_LINK_MATCHES_PREFIX: &str = "NO_LINK_MATCHES_PREFIX";
}

/// Inspect linked transfer legs in the booked ledger.
#[derive(Parser, Debug)]
#[command(author, version, about)]
pub struct Args {
    /// Beancount files to scan, including their included files.
    #[arg(value_name = "FILE", required = true)]
    pub files: Vec<PathBuf>,
    /// Prefix of links to inspect, without the leading ^.
    #[arg(long, required = true)]
    pub link_prefix: String,
    /// Exact transit account name (repeat for multiple accounts).
    #[arg(long, required = true)]
    pub account: Vec<String>,
    /// Output format.
    #[arg(long, short = 'f', value_enum, default_value_t = OutputFormat::Text)]
    pub format: OutputFormat,
}

#[derive(Serialize)]
struct Location {
    file: String,
    line: usize,
}

struct Leg {
    location: Location,
    postings: Vec<(String, Option<Amount>)>,
    complex: bool,
}

#[derive(Serialize)]
struct Finding {
    link: String,
    status: &'static str,
    reason: &'static str,
    locations: Vec<Location>,
}

#[derive(Serialize)]
struct Report {
    findings: Vec<Finding>,
}

/// Run the lint on stdout, its warnings on stderr.
///
/// # Errors
/// Returns an error when the inputs cannot be safely inspected or output fails.
pub fn run(args: &Args) -> Result<ExitCode> {
    run_with_writer(
        args,
        &mut std::io::stdout().lock(),
        None,
        &mut std::io::stderr().lock(),
    )
}

/// `file:line: CODE: message` for each error, joined for one refusal.
fn describe_errors<'a>(errors: impl Iterator<Item = &'a LedgerError>) -> String {
    errors
        .map(|err| {
            let at = err
                .location
                .as_ref()
                .map(|l| format!("{}:{}: ", l.file.display(), l.line))
                .unwrap_or_default();
            format!("{at}{}: {}", err.code, err.message)
        })
        .collect::<Vec<_>>()
        .join("; ")
}

/// Inspect booked transactions and write an advisory report.
///
/// The report goes to `out`. Warnings (a dropped `^`, an account or prefix
/// the ledger never uses, a processing warning) go to `warnings` when given,
/// else to `err` as `warning: ...` lines.
///
/// # Errors
/// Returns an error when the inputs cannot be safely inspected, when an
/// `--account` is not a valid account name, or when output fails.
pub fn run_with_writer<W: std::io::Write>(
    args: &Args,
    out: &mut W,
    warnings: Option<&mut dyn Diagnostics>,
    err: &mut dyn std::io::Write,
) -> Result<ExitCode> {
    let messages = &mut Messages::new(err, warnings);
    anyhow::ensure!(!args.files.is_empty(), "at least one file is required");
    // Links are written `^xfer-a` but matched as `xfer-a`, so `^xfer-` is
    // an easy slip that would match nothing. Dropped, with a note.
    let link_prefix = match args.link_prefix.strip_prefix('^') {
        Some(stripped) => {
            messages.warn(
                warning_codes::LINK_PREFIX_CARET,
                format!(
                    "--link-prefix {}: links are matched without the leading ^; using {stripped}",
                    args.link_prefix
                ),
            );
            stripped
        }
        None => args.link_prefix.as_str(),
    };
    anyhow::ensure!(!link_prefix.is_empty(), "--link-prefix must not be empty");
    anyhow::ensure!(
        !args.account.is_empty() && args.account.iter().all(|a| !a.is_empty()),
        "at least one non-empty --account is required"
    );
    for account in &args.account {
        anyhow::ensure!(
            rustledger_parser::is_valid_account_name(account),
            "--account {account}: not a valid account name \
             (expected two or more `:`-separated components, such as Assets:Transit)"
        );
    }
    let accounts: BTreeSet<&str> = args.account.iter().map(String::as_str).collect();
    let mut seen_accounts: BTreeSet<&str> = BTreeSet::new();
    let mut any_link_matches = false;
    // Booking only: validation diagnostics (an unopened account, a failed
    // balance assertion) do not change the amounts this lint compares, and
    // `rledger check` is where they belong.
    let options = LoadOptions {
        run_plugins: true,
        validate: false,
        plugin_max_time_secs: crate::plugin_budget::max_time_secs(),
        plugin_max_memory_mb: crate::plugin_budget::max_memory_mb(),
        ..Default::default()
    };
    let mut groups: BTreeMap<String, BTreeMap<(PathBuf, usize), Leg>> = BTreeMap::new();
    for path in &args.files {
        let result = Loader::new()
            .load(path)
            .with_context(|| format!("failed to load {}", path.display()))?;
        anyhow::ensure!(
            result.errors.is_empty(),
            "{}: cannot inspect source with load errors: {}",
            path.display(),
            result
                .errors
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("; ")
        );
        let ledger = rustledger_loader::process(result, &options)
            .with_context(|| format!("failed to process {}", path.display()))?;
        let mut errors = ledger
            .errors
            .iter()
            .filter(|e| e.severity == ErrorSeverity::Error)
            .peekable();
        anyhow::ensure!(
            errors.peek().is_none(),
            "{}: cannot inspect a ledger with processing errors: {}",
            path.display(),
            describe_errors(errors)
        );
        for warning in ledger
            .errors
            .iter()
            .filter(|e| e.severity == ErrorSeverity::Warning)
        {
            let line = format!("warning: {}", describe_errors(std::iter::once(warning)));
            messages.emit_as(
                Diagnostic {
                    code: Some(warning.code.clone()),
                    ..Diagnostic::message(warning.message.clone())
                },
                line,
            );
        }
        for directive in &ledger.directives {
            let txn = match &directive.value {
                Directive::Open(open) => {
                    if let Some(account) = accounts.get(open.account.as_str()) {
                        seen_accounts.insert(account);
                    }
                    continue;
                }
                Directive::Transaction(txn) => txn,
                _ => continue,
            };
            for posting in &txn.postings {
                if let Some(account) = accounts.get(posting.account.as_str()) {
                    seen_accounts.insert(account);
                }
            }
            let links: Vec<&str> = txn
                .links
                .iter()
                .map(Link::as_str)
                .filter(|l| l.starts_with(link_prefix))
                .collect();
            if links.is_empty() {
                continue;
            }
            any_link_matches = true;
            let source = ledger
                .source_map
                .get(directive.file_id as usize)
                .context("linked transaction has no source location")?;
            let canonical = source
                .path
                .canonicalize()
                .with_context(|| format!("cannot identify source {}", source.path.display()))?;
            let key = (canonical.clone(), directive.span.start);
            let (line, _) = source.line_col(directive.span.start);
            let multiple_links = links.len() > 1;
            for link in links {
                groups
                    .entry(link.to_string())
                    .or_default()
                    .entry(key.clone())
                    .or_insert_with(|| Leg {
                        location: Location {
                            file: canonical.display().to_string(),
                            line,
                        },
                        postings: txn
                            .postings
                            .iter()
                            .filter(|p| accounts.contains(p.account.as_str()))
                            .map(|p| {
                                (
                                    p.account.as_str().to_string(),
                                    p.units.as_ref().and_then(|u| u.as_amount()).cloned(),
                                )
                            })
                            .collect(),
                        complex: multiple_links
                            || txn.postings.len() != 2
                            || txn
                                .postings
                                .iter()
                                .any(|p| p.cost.is_some() || p.price.is_some()),
                    });
            }
        }
    }

    // A misspelled account or prefix matches nothing, which would otherwise
    // read as a clean "No linked transit transfers found."
    for account in &accounts {
        if !seen_accounts.contains(account) {
            let message =
                format!("--account {account}: the ledger never opens or posts to this account");
            let line = format!("warning: {message}");
            messages.emit_as(
                Diagnostic {
                    code: Some(warning_codes::ACCOUNT_NOT_IN_LEDGER.to_string()),
                    account: Some((*account).to_string()),
                    ..Diagnostic::message(message)
                },
                line,
            );
        }
    }
    if !any_link_matches {
        messages.warn(
            warning_codes::NO_LINK_MATCHES_PREFIX,
            format!(
                "--link-prefix {link_prefix}: no link in the ledger starts with ^{link_prefix}"
            ),
        );
    }

    let mut findings = Vec::new();
    for (link, legs) in groups {
        let legs: Vec<Leg> = legs.into_values().collect();
        if legs.iter().all(|leg| leg.postings.is_empty()) {
            continue;
        }
        let (status, reason) = if legs.len() > 2 || legs.iter().any(|l| l.postings.len() > 1) {
            ("ambiguous", "multiple transactions or transit postings")
        } else if legs.iter().any(|l| l.complex) {
            ("ambiguous", "unsupported complex transaction")
        } else if legs.len() < 2 || legs.iter().any(|l| l.postings.is_empty()) {
            ("missing", "a linked transit leg is missing")
        } else {
            let (account_a, amount_a) = &legs[0].postings[0];
            let (account_b, amount_b) = &legs[1].postings[0];
            match (amount_a, amount_b) {
                (Some(a), Some(b))
                    if account_a == account_b
                        && a.currency == b.currency
                        && !a.number.is_zero()
                        && a.number == -b.number =>
                {
                    ("matched", "opposite equal transit amounts")
                }
                (Some(_), Some(_)) => (
                    "mismatch",
                    "transit account, currency, amount, or direction differs",
                ),
                // Booking completes every posting it accepts; an amount it
                // left incomplete is not one this lint can compare.
                _ => ("ambiguous", "transit amount was not booked"),
            }
        };
        findings.push(Finding {
            link,
            status,
            reason,
            locations: legs.into_iter().map(|l| l.location).collect(),
        });
    }
    match args.format {
        OutputFormat::Json => {
            writeln!(out, "{}", crate::cmd::to_json_pretty(&Report { findings })?)?;
        }
        OutputFormat::Text => {
            if findings.is_empty() {
                writeln!(out, "No linked transit transfers found.")?;
            }
            for finding in findings {
                writeln!(
                    out,
                    "^{}: {}: {}",
                    finding.link, finding.status, finding.reason
                )?;
                for location in finding.locations {
                    writeln!(out, "  {}:{}", location.file, location.line)?;
                }
            }
        }
    }
    Ok(ExitCode::SUCCESS)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cmd::report_cmd::CollectedDiagnostics;
    use std::fs;

    fn inspect(files: Vec<PathBuf>, accounts: &[&str]) -> Result<serde_json::Value> {
        inspect_with_warnings(files, "xfer-", accounts).map(|(report, _)| report)
    }

    /// The JSON report and the warnings, collected as `ag-rledger` does.
    fn inspect_with_warnings(
        files: Vec<PathBuf>,
        link_prefix: &str,
        accounts: &[&str],
    ) -> Result<(serde_json::Value, Vec<Diagnostic>)> {
        let args = Args {
            files,
            link_prefix: link_prefix.into(),
            account: accounts.iter().map(|a| (*a).into()).collect(),
            format: OutputFormat::Json,
        };
        let mut output = Vec::new();
        let mut warnings = CollectedDiagnostics::default();
        let mut err = Vec::new();
        run_with_writer(&args, &mut output, Some(&mut warnings), &mut err)?;
        assert!(err.is_empty(), "{}", String::from_utf8_lossy(&err));
        Ok((serde_json::from_slice(&output)?, warnings.0))
    }

    fn codes(warnings: &[Diagnostic]) -> Vec<&str> {
        warnings.iter().filter_map(|w| w.code.as_deref()).collect()
    }

    fn transaction(link: &str, transit: &str, other: &str) -> String {
        format!("2024-01-01 * \"transfer\" ^{link}\n  {transit}\n  {other}\n")
    }

    #[test]
    fn checks_exact_pairs_and_reports_all_mismatch_kinds() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("main.bean");
        let mut source = String::new();
        let pairs = [
            (
                "xfer-match",
                "Assets:Transit 100.00 USD",
                "Assets:Transit -100 USD",
                "matched",
            ),
            (
                "xfer-reverse",
                "Assets:Transit -0.01 USD",
                "Assets:Transit 0.010 USD",
                "matched",
            ),
            (
                "xfer-max",
                "Assets:Transit 79228162514264337593543950335 USD",
                "Assets:Transit -79228162514264337593543950335 USD",
                "matched",
            ),
            (
                "xfer-amount",
                "Assets:Transit 100 USD",
                "Assets:Transit -90 USD",
                "mismatch",
            ),
            (
                "xfer-currency",
                "Assets:Transit 100 USD",
                "Assets:Transit -100 EUR",
                "mismatch",
            ),
            (
                "xfer-direction",
                "Assets:Transit 100 USD",
                "Assets:Transit 100 USD",
                "mismatch",
            ),
            (
                "xfer-account",
                "Assets:Transit 100 USD",
                "Assets:OtherTransit -100 USD",
                "mismatch",
            ),
            (
                // Booking prunes the elided `Assets:Cash` it fills from a zero
                // residual (as beancount does), so each leg books to one
                // posting and is no simple two-posting transfer.
                "xfer-zero",
                "Assets:Transit 0 USD",
                "Assets:Transit 0 USD",
                "ambiguous",
            ),
        ];
        for (link, a, b, _) in pairs {
            source.push_str(&transaction(link, a, "Assets:Cash"));
            source.push_str(&transaction(link, b, "Assets:Cash"));
        }
        source.push_str(&transaction(
            "xfer-missing",
            "Assets:Transit 2 USD",
            "Assets:Cash",
        ));
        source.push_str(&transaction(
            "xfer-no-second-leg",
            "Assets:Transit 2 USD",
            "Assets:Cash",
        ));
        source.push_str(&transaction(
            "xfer-no-second-leg",
            "Assets:Cash 2 USD",
            "Equity:Capital",
        ));
        source.push_str(&transaction(
            "unrelated",
            "Assets:Transit 2 USD",
            "Assets:Cash",
        ));
        source.push_str(&transaction(
            "xfer-no-transit",
            "Assets:Cash 2 USD",
            "Equity:Capital",
        ));
        fs::write(&path, source).unwrap();
        let report = inspect(vec![path], &["Assets:Transit", "Assets:OtherTransit"]).unwrap();
        let findings = report["findings"].as_array().unwrap();
        assert_eq!(findings.len(), pairs.len() + 2);
        for (link, _, _, status) in pairs {
            let found = findings.iter().find(|f| f["link"] == link).unwrap();
            assert_eq!(found["status"], status, "{link}");
            assert_eq!(found["locations"].as_array().unwrap().len(), 2);
        }
        assert_eq!(
            findings
                .iter()
                .find(|f| f["link"] == "xfer-missing")
                .unwrap()["status"],
            "missing"
        );
        assert_eq!(
            findings
                .iter()
                .find(|f| f["link"] == "xfer-no-second-leg")
                .unwrap()["status"],
            "missing"
        );
    }

    #[test]
    fn refuses_ambiguous_or_unsupported_cases() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("main.bean");
        let mut source = String::new();
        source.push_str(&transaction(
            "xfer-cost",
            "Assets:Transit 2 USD @ 2 EUR",
            "Assets:Cash",
        ));
        source.push_str(&transaction(
            "xfer-cost",
            "Assets:Transit -2 USD",
            "Assets:Cash",
        ));
        source.push_str("2024-01-01 * \"fee\" ^xfer-fee\n  Assets:Transit 2 USD\n  Assets:Cash -3 USD\n  Expenses:Fee 1 USD\n");
        source.push_str(&transaction(
            "xfer-fee",
            "Assets:Transit -2 USD",
            "Assets:Cash",
        ));
        source.push_str("2024-01-01 * \"multiple\" ^xfer-multi\n  Assets:Transit 1 USD\n  Assets:Transit 1 USD\n  Assets:Cash -2 USD\n");
        source.push_str(&transaction(
            "xfer-multi",
            "Assets:Transit -2 USD",
            "Assets:Cash",
        ));
        for _ in 0..3 {
            source.push_str(&transaction(
                "xfer-three",
                "Assets:Transit 2 USD",
                "Assets:Cash",
            ));
        }
        source.push_str(
            "2024-01-01 * \"two links\" ^xfer-a ^xfer-b\n  Assets:Transit 2 USD\n  Assets:Cash\n",
        );
        fs::write(&path, source).unwrap();
        let report = inspect(vec![path], &["Assets:Transit"]).unwrap();
        for finding in report["findings"].as_array().unwrap() {
            assert_eq!(finding["status"], "ambiguous", "{finding}");
        }
        assert_eq!(report["findings"].as_array().unwrap().len(), 6);
    }

    #[test]
    fn deduplicates_included_files_and_rejects_bad_input() {
        let dir = tempfile::tempdir().unwrap();
        let child = dir.path().join("child.bean");
        let parent = dir.path().join("main.bean");
        fs::write(
            &child,
            transaction("xfer-shared", "Assets:Transit 3 USD", "Assets:Cash"),
        )
        .unwrap();
        fs::write(
            &parent,
            format!(
                "include \"child.bean\"\n{}",
                transaction("xfer-shared", "Assets:Transit -3 USD", "Assets:Cash")
            ),
        )
        .unwrap();
        let report = inspect(
            vec![parent.clone(), child.clone(), parent],
            &["Assets:Transit"],
        )
        .unwrap();
        assert_eq!(report["findings"][0]["status"], "matched");
        assert_eq!(
            report["findings"][0]["locations"].as_array().unwrap().len(),
            2
        );
        fs::write(&child, "2024-01-01 * \"broken\"\n  not an account\n").unwrap();
        assert!(inspect(vec![child.clone()], &["Assets:Transit"]).is_err());
        // An unknown plugin is a processing error: refused, not inspected
        // with the plugin silently skipped.
        fs::write(&child, "plugin \"example\"\n").unwrap();
        assert!(inspect(vec![child], &["Assets:Transit"]).is_err());
    }

    #[test]
    fn test_run_with_writer_matches_elided_transit_amount() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("main.bean");
        fs::write(
            &path,
            concat!(
                "2026-01-02 * \"Send\" ^xfer-a\n",
                "  Assets:Cash     -100.00 USD\n",
                "  Assets:Transit\n",
                "2026-01-03 * \"Receive\" ^xfer-a\n",
                "  Assets:Transit  -100.00 USD\n",
                "  Assets:Bank\n",
            ),
        )
        .unwrap();
        let report = inspect(vec![path], &["Assets:Transit"]).unwrap();
        assert_eq!(report["findings"][0]["link"], "xfer-a", "{report}");
        assert_eq!(report["findings"][0]["status"], "matched", "{report}");
    }

    #[test]
    fn test_run_with_writer_runs_ledger_plugins() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("main.bean");
        fs::write(
            &path,
            concat!(
                "plugin \"beancount.plugins.auto_accounts\"\n",
                "2026-01-02 * \"Send\" ^xfer-a\n",
                "  Assets:Cash     -100.00 USD\n",
                "  Assets:Transit\n",
                "2026-01-03 * \"Receive\" ^xfer-a\n",
                "  Assets:Transit  -90.00 USD\n",
                "  Assets:Bank\n",
            ),
        )
        .unwrap();
        let report = inspect(vec![path], &["Assets:Transit"]).unwrap();
        assert_eq!(report["findings"][0]["status"], "mismatch", "{report}");
    }

    #[test]
    fn test_run_with_writer_refuses_booking_errors() {
        // Two elided postings cannot be booked; the transaction is dropped
        // from the booked stream, so reporting `^xfer-a` as `missing` would
        // be misleading. The lint refuses instead.
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("main.bean");
        fs::write(
            &path,
            concat!(
                "2026-01-02 * \"Send\" ^xfer-a\n",
                "  Assets:Cash     -100.00 USD\n",
                "  Assets:Transit\n",
                "2026-01-03 * \"Receive\" ^xfer-a\n",
                "  Assets:Transit\n",
                "  Assets:Bank\n",
            ),
        )
        .unwrap();
        let err = inspect(vec![path], &["Assets:Transit"]).unwrap_err();
        assert!(err.to_string().contains("processing errors"), "{err:#}");
    }

    #[test]
    fn refuses_empty_scope_and_reports_missing_include() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("main.bean");
        fs::write(&path, "include \"missing.bean\"\n").unwrap();
        assert!(inspect(vec![path.clone()], &["Assets:Transit"]).is_err());
        fs::write(&path, "").unwrap();
        assert!(inspect(vec![path.clone()], &[]).is_err());
        let args = Args {
            files: vec![path],
            link_prefix: String::new(),
            account: vec!["Assets:Transit".into()],
            format: OutputFormat::Json,
        };
        assert!(run_with_writer(&args, &mut Vec::new(), None, &mut Vec::new()).is_err());
    }

    /// A matched pair on `Assets:Transit`, for the configuration tests.
    fn matched_pair(dir: &std::path::Path) -> PathBuf {
        let path = dir.join("main.bean");
        fs::write(
            &path,
            format!(
                "{}{}",
                transaction("xfer-a", "Assets:Transit 5 USD", "Assets:Cash"),
                transaction("xfer-a", "Assets:Transit -5 USD", "Assets:Cash"),
            ),
        )
        .unwrap();
        path
    }

    #[test]
    fn test_run_with_writer_rejects_invalid_account_name() {
        let dir = tempfile::tempdir().unwrap();
        let path = matched_pair(dir.path());
        for bad in [
            "Transit",
            "assets:transit",
            "Assets:Transit:",
            "Assets Transit",
        ] {
            let err = inspect(vec![path.clone()], &["Assets:Transit", bad]).unwrap_err();
            assert!(
                err.to_string()
                    .contains(&format!("--account {bad}: not a valid account name")),
                "{bad}: {err:#}"
            );
        }
    }

    #[test]
    fn test_run_with_writer_strips_leading_caret_with_note() {
        let dir = tempfile::tempdir().unwrap();
        let path = matched_pair(dir.path());
        let (report, warnings) =
            inspect_with_warnings(vec![path], "^xfer-", &["Assets:Transit"]).unwrap();
        assert_eq!(report["findings"][0]["status"], "matched", "{report}");
        assert_eq!(codes(&warnings), vec![warning_codes::LINK_PREFIX_CARET]);
        assert!(warnings[0].message.contains("using xfer-"), "{warnings:?}");
        let dir = tempfile::tempdir().unwrap();
        let path = matched_pair(dir.path());
        assert!(inspect_with_warnings(vec![path], "^", &["Assets:Transit"]).is_err());
    }

    #[test]
    fn test_run_with_writer_warns_on_unused_account_and_unmatched_prefix() {
        let dir = tempfile::tempdir().unwrap();
        let path = matched_pair(dir.path());
        let (report, warnings) =
            inspect_with_warnings(vec![path.clone()], "xfer-", &["Assets:Transit"]).unwrap();
        assert_eq!(report["findings"][0]["status"], "matched", "{report}");
        assert!(warnings.is_empty(), "{warnings:?}");

        let (report, warnings) =
            inspect_with_warnings(vec![path.clone()], "xfer-", &["Assets:Transitt"]).unwrap();
        assert_eq!(report["findings"], serde_json::json!([]), "{report}");
        assert_eq!(codes(&warnings), vec![warning_codes::ACCOUNT_NOT_IN_LEDGER]);
        assert!(
            warnings[0].message.contains("Assets:Transitt"),
            "{warnings:?}"
        );

        let (_, warnings) =
            inspect_with_warnings(vec![path], "transfer-", &["Assets:Transit"]).unwrap();
        assert_eq!(
            codes(&warnings),
            vec![warning_codes::NO_LINK_MATCHES_PREFIX]
        );
    }

    #[test]
    fn test_run_with_writer_writes_warnings_to_err_without_a_sink() {
        let dir = tempfile::tempdir().unwrap();
        let path = matched_pair(dir.path());
        let args = Args {
            files: vec![path],
            link_prefix: "^xfer-".into(),
            account: vec!["Assets:Transit".into(), "Assets:Transitt".into()],
            format: OutputFormat::Text,
        };
        let mut out = Vec::new();
        let mut err = Vec::new();
        run_with_writer(&args, &mut out, None, &mut err).unwrap();
        assert_eq!(
            String::from_utf8(err).unwrap(),
            "warning: --link-prefix ^xfer-: links are matched without the leading ^; using xfer-\n\
             warning: --account Assets:Transitt: the ledger never opens or posts to this account\n"
        );
        assert!(
            String::from_utf8(out)
                .unwrap()
                .starts_with("^xfer-a: matched"),
        );
    }
}
