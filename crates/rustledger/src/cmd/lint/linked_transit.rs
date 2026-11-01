//! Read-only inspection of explicitly linked transit postings.

use anyhow::{Context, Result};
use clap::Parser;
use rust_decimal::Decimal;
use rustledger_core::{Directive, Link};
use rustledger_loader::Loader;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::process::ExitCode;

use super::closed_nonempty::OutputFormat;

/// Inspect linked transfer legs in the unprocessed source.
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
    postings: Vec<(String, Option<(Decimal, String)>)>,
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

/// Run the lint on stdout.
///
/// # Errors
/// Returns an error when the inputs cannot be safely inspected or output fails.
pub fn run(args: &Args) -> Result<ExitCode> {
    run_with_writer(args, &mut std::io::stdout().lock())
}

/// Inspect source transactions and write an advisory report.
///
/// # Errors
/// Returns an error when the inputs cannot be safely inspected or output fails.
pub fn run_with_writer<W: std::io::Write>(args: &Args, out: &mut W) -> Result<ExitCode> {
    anyhow::ensure!(!args.files.is_empty(), "at least one file is required");
    anyhow::ensure!(
        !args.link_prefix.is_empty(),
        "--link-prefix must not be empty"
    );
    anyhow::ensure!(
        !args.account.is_empty() && args.account.iter().all(|a| !a.is_empty()),
        "at least one non-empty --account is required"
    );
    let accounts: BTreeSet<&str> = args.account.iter().map(String::as_str).collect();
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
        anyhow::ensure!(
            result.plugins.is_empty(),
            "{}: plugin directives are unsupported by linked-transit source inspection",
            path.display()
        );
        for directive in &result.directives {
            let Directive::Transaction(txn) = &directive.value else {
                continue;
            };
            let links: Vec<&str> = txn
                .links
                .iter()
                .map(Link::as_str)
                .filter(|l| l.starts_with(&args.link_prefix))
                .collect();
            if links.is_empty() {
                continue;
            }
            let source = result
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
                                    p.units
                                        .as_ref()
                                        .and_then(|u| u.as_amount())
                                        .map(|a| (a.number, a.currency.to_string())),
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

    let mut findings = Vec::new();
    for (link, legs) in groups {
        let legs: Vec<Leg> = legs.into_values().collect();
        if legs.iter().all(|leg| leg.postings.is_empty()) {
            continue;
        }
        let (status, reason) = if legs.len() > 2 || legs.iter().any(|l| l.postings.len() > 1) {
            ("ambiguous", "multiple transactions or transit postings")
        } else if legs
            .iter()
            .any(|l| l.complex || l.postings.iter().any(|(_, amount)| amount.is_none()))
        {
            (
                "ambiguous",
                "unsupported complex transaction or inferred transit amount",
            )
        } else if legs.len() < 2 || legs.iter().any(|l| l.postings.is_empty()) {
            ("missing", "a linked transit leg is missing")
        } else {
            let (account_a, amount_a) = &legs[0].postings[0];
            let (account_b, amount_b) = &legs[1].postings[0];
            match (amount_a, amount_b) {
                (Some((a, currency_a)), Some((b, currency_b)))
                    if account_a == account_b
                        && currency_a == currency_b
                        && !a.is_zero()
                        && *a == -*b =>
                {
                    ("matched", "opposite equal transit amounts")
                }
                (Some(_), Some(_)) => (
                    "mismatch",
                    "transit account, currency, amount, or direction differs",
                ),
                _ => ("ambiguous", "inferred transit amount"),
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
    use std::fs;

    fn inspect(files: Vec<PathBuf>, accounts: &[&str]) -> Result<serde_json::Value> {
        let args = Args {
            files,
            link_prefix: "xfer-".into(),
            account: accounts.iter().map(|a| (*a).into()).collect(),
            format: OutputFormat::Json,
        };
        let mut output = Vec::new();
        run_with_writer(&args, &mut output)?;
        Ok(serde_json::from_slice(&output)?)
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
                "xfer-zero",
                "Assets:Transit 0 USD",
                "Assets:Transit 0 USD",
                "mismatch",
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
            "xfer-inferred",
            "Assets:Transit",
            "Assets:Cash -2 USD",
        ));
        source.push_str(&transaction(
            "xfer-inferred",
            "Assets:Transit -2 USD",
            "Assets:Cash",
        ));
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
        assert_eq!(report["findings"].as_array().unwrap().len(), 7);
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
        fs::write(&child, "plugin \"example\"\n").unwrap();
        assert!(inspect(vec![child], &["Assets:Transit"]).is_err());
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
        assert!(run_with_writer(&args, &mut Vec::new()).is_err());
    }
}
