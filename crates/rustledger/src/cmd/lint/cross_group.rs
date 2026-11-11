//! Report booked transactions touching more than one configured account group.

use anyhow::{Context, Result};
use clap::Parser;
use rustledger_core::Directive;
use rustledger_validate::is_advisory_only_code;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::process::ExitCode;

use super::OutputFormat;
use super::load::{TransactionSites, describe_error, load_booked};
use crate::cmd::messages::Messages;
use crate::cmd::report_cmd::{Diagnostic, Diagnostics};

/// Report transactions that touch more than one configured account group.
#[derive(Parser, Debug)]
#[command(author, version, about)]
pub struct Args {
    /// Beancount files to scan, including their included files.
    #[arg(value_name = "FILE", required = true)]
    pub files: Vec<PathBuf>,
    /// Group and account prefixes, e.g. UnitA=Assets:UnitA,Income:UnitA.
    /// Repeat for each group.
    #[arg(long, required = true, value_name = "NAME=PREFIX[,PREFIX...]")]
    pub group: Vec<String>,
    /// Exit 1 if any cross-group transactions are found.
    #[arg(long)]
    pub fail_on_findings: bool,
    /// Output format.
    #[arg(long, short = 'f', value_enum, default_value_t = OutputFormat::Text)]
    pub format: OutputFormat,
}

#[derive(Serialize, PartialEq, Eq)]
struct Finding {
    file: String,
    line: usize,
    date: String,
    narration: String,
    groups: BTreeMap<String, BTreeSet<String>>,
}

#[derive(Serialize)]
struct Report {
    findings: Vec<Finding>,
    unassigned_accounts: usize,
}

fn matches_prefix(account: &str, prefix: &str) -> bool {
    account == prefix
        || account
            .strip_prefix(prefix)
            .is_some_and(|tail| tail.starts_with(':'))
}

fn parse_groups(values: &[String]) -> Result<BTreeMap<String, BTreeSet<String>>> {
    let mut groups: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for value in values.iter().flat_map(|value| value.split(';')) {
        let (name, prefixes) = value
            .split_once('=')
            .context("--group must be NAME=PREFIX[,PREFIX...]")?;
        anyhow::ensure!(
            !name.is_empty()
                && name
                    .chars()
                    .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-'),
            "--group {value}: group name must contain only letters, digits, '_' or '-'"
        );
        for prefix in prefixes.split(',') {
            anyhow::ensure!(
                rustledger_parser::is_valid_account_name(prefix),
                "--group {name}: invalid account prefix {prefix:?}"
            );
            groups
                .entry(name.to_string())
                .or_default()
                .insert(prefix.to_string());
        }
    }
    anyhow::ensure!(
        groups.len() >= 2,
        "at least two distinct --group names are required"
    );
    let mut assigned: Vec<(&str, &str)> = Vec::new();
    for (name, prefixes) in &groups {
        for prefix in prefixes {
            for (other_name, other_prefix) in &assigned {
                anyhow::ensure!(
                    name == other_name
                        || !(matches_prefix(prefix, other_prefix)
                            || matches_prefix(other_prefix, prefix)),
                    "overlapping prefixes {prefix} ({name}) and {other_prefix} ({other_name})"
                );
            }
            assigned.push((name, prefix));
        }
    }
    Ok(groups)
}

/// Run the lint on stdout.
///
/// # Errors
/// Returns an error if configuration, loading, processing, or output fails.
pub fn run(args: &Args) -> Result<ExitCode> {
    run_with_writer(
        args,
        &mut std::io::stdout().lock(),
        None,
        &mut std::io::stderr().lock(),
    )
}

/// Run the lint with separate output and warning sinks.
///
/// # Errors
/// Returns an error if configuration, loading, processing, or output fails.
pub fn run_with_writer<W: std::io::Write>(
    args: &Args,
    out: &mut W,
    warnings: Option<&mut dyn Diagnostics>,
    err: &mut dyn std::io::Write,
) -> Result<ExitCode> {
    anyhow::ensure!(!args.files.is_empty(), "at least one file is required");
    let groups = parse_groups(&args.group)?;
    let mut messages = Messages::new(err, warnings);
    let mut used: BTreeSet<String> = BTreeSet::new();
    let mut unassigned: BTreeSet<String> = BTreeSet::new();
    let mut transactions: BTreeMap<(PathBuf, usize), (Finding, Vec<String>)> = BTreeMap::new();
    let mut sites = TransactionSites::default();
    let mut errors = BTreeSet::new();
    for path in &args.files {
        let ledger = load_booked(path)?;
        for error in &ledger.errors {
            if is_advisory_only_code(&error.code) {
                continue;
            }
            let description = describe_error(error);
            if errors.insert(description.clone()) {
                messages.emit_as(
                    Diagnostic {
                        code: Some(error.code.clone()),
                        file: error
                            .location
                            .as_ref()
                            .map(|l| l.file.display().to_string()),
                        line: error.location.as_ref().map(|l| l.line),
                        ..Diagnostic::message(error.message.clone())
                    },
                    format!("warning: {description}"),
                );
            }
        }
        let mut ledger_sites = sites.for_ledger(&ledger);
        for directive in &ledger.directives {
            if let Directive::Open(open) = &directive.value {
                for prefixes in groups.values() {
                    for prefix in prefixes {
                        if matches_prefix(open.account.as_str(), prefix) {
                            used.insert(prefix.clone());
                        }
                    }
                }
            }
            let Directive::Transaction(txn) = &directive.value else {
                continue;
            };
            let site = ledger_sites.site(directive);
            anyhow::ensure!(
                site.unidentified.is_none(),
                "{}:{}: cannot audit transaction: {}",
                site.file,
                site.line,
                site.unidentified.unwrap_or("unknown source location")
            );
            let mut matched: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
            let mut accounts = Vec::new();
            for posting in &txn.postings {
                let account = posting.account.as_str();
                accounts.push(account.to_string());
                let mut found = false;
                for (name, prefixes) in &groups {
                    for prefix in prefixes {
                        if matches_prefix(account, prefix) {
                            used.insert(prefix.clone());
                            matched
                                .entry(name.clone())
                                .or_default()
                                .insert(account.to_string());
                            found = true;
                        }
                    }
                }
                if !found {
                    unassigned.insert(account.to_string());
                }
            }
            let finding = Finding {
                file: site.file,
                line: site.line,
                date: txn.date.to_string(),
                narration: txn.narration.to_string(),
                groups: matched,
            };
            if let Some((previous, previous_accounts)) = transactions.get(&site.key) {
                anyhow::ensure!(
                    previous == &finding && previous_accounts == &accounts,
                    "{}:{}: transaction differs between input ledgers",
                    finding.file,
                    finding.line
                );
            } else {
                transactions.insert(site.key, (finding, accounts));
            }
        }
    }
    for prefixes in groups.values() {
        for prefix in prefixes {
            if !used.contains(prefix) {
                messages.warn(
                    "GROUP_PREFIX_NOT_IN_LEDGER",
                    format!("--group prefix {prefix}: no account opened or posted to matches it"),
                );
            }
        }
    }
    let findings: Vec<Finding> = transactions
        .into_values()
        .map(|(f, _)| f)
        .filter(|f| f.groups.len() >= 2)
        .collect();
    let failed = args.fail_on_findings && !findings.is_empty();
    let report = Report {
        findings,
        unassigned_accounts: unassigned.len(),
    };
    match args.format {
        OutputFormat::Json => writeln!(out, "{}", crate::cmd::to_json_pretty(&report)?)?,
        OutputFormat::Text => {
            for finding in &report.findings {
                writeln!(
                    out,
                    "{}:{}: {} {}",
                    rustledger_plugin::escape_untrusted_text(&finding.file),
                    finding.line,
                    finding.date,
                    rustledger_plugin::escape_untrusted_text(&finding.narration)
                )?;
                for (name, accounts) in &finding.groups {
                    writeln!(
                        out,
                        "  {name}: {}",
                        accounts.iter().cloned().collect::<Vec<_>>().join(", ")
                    )?;
                }
            }
            writeln!(
                out,
                "{} cross-group transaction(s); {} distinct unassigned posting account(s).",
                report.findings.len(),
                report.unassigned_accounts
            )?;
        }
    }
    Ok(if failed {
        ExitCode::from(1)
    } else {
        ExitCode::SUCCESS
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    const LEDGER: &str = concat!(
        "2024-01-01 open Assets:UnitA:Cash USD\n",
        "2024-01-01 open Assets:UnitA:Other USD\n",
        "2024-01-01 open Assets:UnitB:Cash USD\n",
        "2024-01-01 open Assets:UnitAB:Cash USD\n",
        "2024-01-01 open Expenses:UnitA USD\n",
        "2024-01-02 * \"same\"\n",
        "  Assets:UnitA:Cash -2 USD\n",
        "  Expenses:UnitA 2 USD\n",
        "2024-01-03 * \"cross\"\n",
        "  Assets:UnitA:Cash -3 USD\n",
        "  Assets:UnitB:Cash 3 USD\n",
        "2024-01-04 * \"unassigned\"\n",
        "  Assets:UnitA:Other -4 USD\n",
        "  Assets:UnitAB:Cash 4 USD\n",
    );

    fn args(files: Vec<PathBuf>) -> Args {
        Args {
            files,
            group: vec![
                "A=Assets:UnitA,Expenses:UnitA".into(),
                "B=Assets:UnitB".into(),
            ],
            fail_on_findings: false,
            format: OutputFormat::Json,
        }
    }

    fn inspect(args: &Args) -> Result<(ExitCode, serde_json::Value, String)> {
        let mut out = Vec::new();
        let mut err = Vec::new();
        let code = run_with_writer(args, &mut out, None, &mut err)?;
        Ok((code, serde_json::from_slice(&out)?, String::from_utf8(err)?))
    }

    #[test]
    fn test_cross_group_reports_crossings_and_unassigned() {
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("main.bean");
        fs::write(&file, LEDGER).unwrap();
        let (status, report, warnings) = inspect(&args(vec![file])).unwrap();
        assert_eq!(status, ExitCode::SUCCESS);
        assert_eq!(report["unassigned_accounts"], 1);
        let findings = report["findings"].as_array().unwrap();
        assert_eq!(findings.len(), 1);
        assert_eq!(findings[0]["line"], 9);
        assert_eq!(findings[0]["groups"]["A"][0], "Assets:UnitA:Cash");
        assert_eq!(findings[0]["groups"]["B"][0], "Assets:UnitB:Cash");
        assert!(warnings.is_empty(), "{warnings}");
    }

    #[test]
    fn test_cross_group_strict_and_unused_prefix() {
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("main.bean");
        fs::write(&file, LEDGER).unwrap();
        let mut args = args(vec![file]);
        args.group.push("C=Assets:Unused".into());
        args.fail_on_findings = true;
        let (status, _, warnings) = inspect(&args).unwrap();
        assert_eq!(status, ExitCode::from(1));
        assert!(warnings.contains("Assets:Unused"), "{warnings}");
    }

    #[test]
    fn test_cross_group_configuration_rejects_bad_and_overlapping_prefixes() {
        for groups in [
            vec!["A=Assets:UnitA"],
            vec!["A=Assets:UnitA", "B=Assets:UnitA"],
            vec!["A=Assets:UnitA", "B=Assets:UnitA:Cash"],
            vec!["A=Assets:UnitA,", "B=Assets:UnitB"],
            vec!["A=Assets:UnitA", "B=not-an-account"],
            vec!["A=Assets:UnitA", "Assets:UnitB"],
            vec!["A=Assets:UnitA;Assets:UnitB"],
            vec!["=Assets:UnitA", "B=Assets:UnitB"],
        ] {
            assert!(
                parse_groups(&groups.iter().map(|s| (*s).into()).collect::<Vec<_>>()).is_err(),
                "{groups:?}"
            );
        }
        assert!(!matches_prefix("Assets:UnitAB:Cash", "Assets:UnitA"));
        assert!(matches_prefix("Assets:UnitA", "Assets:UnitA"));
        assert!(matches_prefix("Assets:UnitA:Cash", "Assets:UnitA"));
        assert!(parse_groups(&["A=Assets:UnitA;B=Assets:UnitB".into()]).is_ok());
    }

    #[test]
    fn test_cross_group_deduplicates_included_files() {
        let dir = tempfile::tempdir().unwrap();
        let child = dir.path().join("child.bean");
        let main = dir.path().join("main.bean");
        fs::write(&child, LEDGER).unwrap();
        fs::write(&main, "include \"child.bean\"\n").unwrap();
        let (_, report, _) = inspect(&args(vec![main, child])).unwrap();
        assert_eq!(report["findings"].as_array().unwrap().len(), 1);
        assert_eq!(report["unassigned_accounts"], 1);
    }

    #[test]
    fn test_cross_group_refuses_unloadable_and_failed_plugins() {
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("main.bean");
        for content in [
            "include \"missing.bean\"\n",
            "plugin \"no_such_plugin\"\n",
            "2024-01-01 * \"unbookable\"\n  Assets:UnitA:Cash\n  Assets:UnitB:Cash\n",
        ] {
            fs::write(&file, content).unwrap();
            assert!(inspect(&args(vec![file.clone()])).is_err(), "{content}");
        }
    }

    #[test]
    fn test_cross_group_handles_successful_plugin() {
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("main.bean");
        fs::write(
            &file,
            concat!(
                "plugin \"beancount.plugins.auto_accounts\"\n",
                "2024-01-02 * \"move\"\n",
                "  Assets:UnitA:Cash -2 USD\n",
                "  Assets:UnitB:Cash 2 USD\n"
            ),
        )
        .unwrap();
        let (_, report, warnings) = inspect(&args(vec![file])).unwrap();
        assert_eq!(report["findings"].as_array().unwrap().len(), 1);
        assert!(!warnings.contains("processing failed"), "{warnings}");
    }

    #[test]
    fn test_cross_group_refuses_plugin_transactions_with_shared_locations() {
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("main.bean");
        fs::write(
            &file,
            concat!(
                "plugin \"beancount.plugins.forecast\"\n",
                "2024-01-01 open Assets:UnitA:Cash USD\n",
                "2024-01-01 open Assets:UnitB:Cash USD\n",
                "2024-01-02 # \"Move [MONTHLY REPEAT 2 TIMES]\"\n",
                "  Assets:UnitA:Cash -2 USD\n",
                "  Assets:UnitB:Cash 2 USD\n"
            ),
        )
        .unwrap();
        let error = inspect(&args(vec![file])).err().unwrap().to_string();
        assert!(error.contains("share one source location"), "{error}");
    }

    #[test]
    fn test_cross_group_passes_validation_errors_as_warnings() {
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("main.bean");
        fs::write(
            &file,
            concat!(
                "2024-01-01 open Assets:UnitA:Cash USD\n",
                "2024-01-02 * \"unopened\"\n",
                "  Assets:UnitA:Cash -2 USD\n",
                "  Assets:UnitB:Cash 2 USD\n"
            ),
        )
        .unwrap();
        let (_, report, warnings) = inspect(&args(vec![file])).unwrap();
        assert_eq!(report["findings"].as_array().unwrap().len(), 1);
        assert!(warnings.contains("Assets:UnitB:Cash"), "{warnings}");
    }

    #[test]
    fn test_cross_group_no_findings_in_strict_mode() {
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("main.bean");
        fs::write(
            &file,
            concat!(
                "2024-01-01 open Assets:UnitA:Cash USD\n",
                "2024-01-01 open Assets:UnitA:Other USD\n",
                "2024-01-01 open Assets:UnitB:Cash USD\n",
                "2024-01-02 * \"same\"\n",
                "  Assets:UnitA:Cash -2 USD\n",
                "  Assets:UnitA:Other 2 USD\n"
            ),
        )
        .unwrap();
        let mut args = args(vec![file]);
        args.fail_on_findings = true;
        let (status, report, _) = inspect(&args).unwrap();
        assert_eq!(status, ExitCode::SUCCESS);
        assert!(report["findings"].as_array().unwrap().is_empty());
    }
}
