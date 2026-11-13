//! Report booked transactions touching more than one configured account group.
//!
//! The lint reads the booked ledger ([`load_booked`]) and the padding entries
//! its `pad` directives produce ([`rustledger_booking::process_pads`], the
//! expansion `rledger query` and the validator use), so a `pad` that moves an
//! amount between two groups is a finding like any transaction that does.
//!
//! A transaction a plugin inserted with no source location of its own
//! (`forecast`'s copies keep the template's, `effective_date`'s keep the
//! parent's) cannot be told apart from the others at its location. Such
//! transactions only refuse the run when, together, the transactions at that
//! location touch two or more groups: only then could they change the answer
//! (the unassigned-account count and the used prefixes do not depend on where
//! a transaction is).

use anyhow::{Context, Result};
use clap::Parser;
use rustledger_core::{Directive, Spanned, Transaction};
use rustledger_loader::Ledger;
use rustledger_validate::is_advisory_only_code;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::PathBuf;
use std::process::ExitCode;

use super::OutputFormat;
use super::load::{TransactionSites, describe_error, load_booked};
use crate::cmd::messages::Messages;
use crate::cmd::report_cmd::{Diagnostic, Diagnostics};

/// The codes of the warnings this lint emits, as carried in `ag-rledger`'s
/// `warnings`.
pub mod warning_codes {
    /// A `--group` prefix matches no account the ledger opens or posts to.
    pub const GROUP_PREFIX_NOT_IN_LEDGER: &str = "GROUP_PREFIX_NOT_IN_LEDGER";
}

/// Report transactions that touch more than one configured account group.
#[derive(Parser, Debug)]
#[command(author, version, about)]
pub struct Args {
    /// Beancount files to scan, including their included files.
    #[arg(value_name = "FILE", required = true)]
    pub files: Vec<PathBuf>,
    /// Group and account prefixes, e.g. UnitA=Assets:UnitA,Income:UnitA.
    /// Repeat for each group, or separate groups with ';' in one value
    /// (UnitA=Assets:UnitA;UnitB=Assets:UnitB). A prefix is an account name
    /// with a root and at least one component: a bare root such as
    /// Liabilities is refused.
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

/// A transaction's identity across inputs: its own source location, and for
/// a padding entry the `balance` it satisfies (one `pad` can pad several
/// currencies, each its own entry at the pad's location).
type Key = ((PathBuf, usize), Option<(PathBuf, usize)>);

/// Where a transaction or padding entry is, as the lint reports and
/// deduplicates it.
struct Site {
    key: Key,
    file: String,
    line: usize,
    /// Why it cannot be told apart from another transaction at its location,
    /// when it cannot.
    unidentified: Option<&'static str>,
    /// Whether this is a padding entry, whose narration is derived.
    padding: bool,
}

fn matches_prefix(account: &str, prefix: &str) -> bool {
    account == prefix
        || account
            .strip_prefix(prefix)
            .is_some_and(|tail| tail.starts_with(':'))
}

/// The usage every `--group` refusal ends with.
const GROUP_SYNTAX: &str = "each group must be NAME=PREFIX[,PREFIX...]";

fn parse_groups(values: &[String]) -> Result<BTreeMap<String, BTreeSet<String>>> {
    let mut groups: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for value in values {
        for segment in value.split(';') {
            anyhow::ensure!(
                !segment.is_empty(),
                "--group {value:?}: has an empty group (a stray ';'); {GROUP_SYNTAX}"
            );
            let (name, prefixes) = segment
                .split_once('=')
                .with_context(|| format!("--group {segment:?}: {GROUP_SYNTAX}"))?;
            anyhow::ensure!(
                !name.is_empty()
                    && name
                        .chars()
                        .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-'),
                "--group {segment}: group name must contain only letters, digits, '_' or '-'"
            );
            for prefix in prefixes.split(',') {
                // A bare root is not an account name; say so rather than
                // calling it invalid. Checked by the canonical validator on
                // the root with a component added, so it cannot drift.
                anyhow::ensure!(
                    prefix.contains(':')
                        || !rustledger_parser::is_valid_account_name(&format!("{prefix}:A")),
                    "--group {name}: account prefix {prefix:?} is a bare root; a prefix \
                     needs a root and at least one component, such as \"{prefix}:Example\""
                );
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

/// Which group each account is in, worked out once per distinct account.
///
/// Overlapping prefixes in different groups are refused, so an account is in
/// at most one group, and the answer for an account never changes: the cost
/// of a run does not grow with the number of groups after the first posting
/// to each account.
struct Classifier<'g> {
    /// Every `(group, prefix)` pair.
    prefixes: Vec<(&'g str, &'g str)>,
    groups_of: HashMap<String, Option<&'g str>>,
    /// The prefixes an opened or posted-to account matches.
    used: BTreeSet<&'g str>,
    /// Posting accounts in no group.
    unassigned: BTreeSet<String>,
}

impl<'g> Classifier<'g> {
    fn new(groups: &'g BTreeMap<String, BTreeSet<String>>) -> Self {
        Self {
            prefixes: groups
                .iter()
                .flat_map(|(name, prefixes)| {
                    prefixes.iter().map(move |p| (name.as_str(), p.as_str()))
                })
                .collect(),
            groups_of: HashMap::new(),
            used: BTreeSet::new(),
            unassigned: BTreeSet::new(),
        }
    }

    /// The group `account` is in, marking each prefix it matches as used.
    fn group(&mut self, account: &str) -> Option<&'g str> {
        if let Some(group) = self.groups_of.get(account) {
            return *group;
        }
        let mut group = None;
        for &(name, prefix) in &self.prefixes {
            if matches_prefix(account, prefix) {
                self.used.insert(prefix);
                group = Some(name);
            }
        }
        self.groups_of.insert(account.to_string(), group);
        group
    }

    /// The groups `txn`'s postings are in, with the accounts in each;
    /// counts each posting account in no group as unassigned.
    fn matched<'t>(&mut self, txn: &'t Transaction) -> BTreeMap<&'g str, BTreeSet<&'t str>> {
        let mut matched: BTreeMap<&'g str, BTreeSet<&'t str>> = BTreeMap::new();
        for posting in &txn.postings {
            let account = posting.account.as_str();
            if let Some(group) = self.group(account) {
                matched.entry(group).or_default().insert(account);
            } else if !self.unassigned.contains(account) {
                self.unassigned.insert(account.to_string());
            }
        }
        matched
    }
}

/// The transactions of one run, across its inputs.
struct Audit<'g> {
    classifier: Classifier<'g>,
    /// The transactions to report or compare across inputs. With one input
    /// only the cross-group ones are kept: a site is unique within a ledger,
    /// so there is nothing to compare the others with.
    transactions: BTreeMap<Key, (Finding, Vec<String>)>,
    keep_all: bool,
}

/// The groups the unidentified transactions at one location touch, with
/// where to report them and why they are unidentified.
type Unidentified<'g> = BTreeMap<Key, (String, usize, &'static str, BTreeSet<&'g str>)>;

impl<'g> Audit<'g> {
    /// Record `txn`, located by `locate` (called only when the location
    /// matters). An unidentified transaction touching a group goes into
    /// `unidentified`, to be refused if those at its location together cross
    /// groups.
    fn record(
        &mut self,
        txn: &Transaction,
        locate: impl FnOnce() -> Site,
        unidentified: &mut Unidentified<'g>,
    ) -> Result<()> {
        let matched = self.classifier.matched(txn);
        if matched.is_empty() && !self.keep_all {
            return Ok(());
        }
        let site = locate();
        if let Some(reason) = site.unidentified {
            if !matched.is_empty() {
                unidentified
                    .entry(site.key)
                    .or_insert_with(|| (site.file, site.line, reason, BTreeSet::new()))
                    .3
                    .extend(matched.keys());
            }
            return Ok(());
        }
        if matched.len() < 2 && !self.keep_all {
            return Ok(());
        }
        let finding = Finding {
            file: site.file,
            line: site.line,
            date: txn.date.to_string(),
            narration: txn.narration.to_string(),
            groups: matched
                .into_iter()
                .map(|(group, accounts)| {
                    (
                        group.to_string(),
                        accounts.into_iter().map(str::to_string).collect(),
                    )
                })
                .collect(),
        };
        let accounts: Vec<String> = txn.postings.iter().map(|p| p.account.to_string()).collect();
        if let Some((previous, previous_accounts)) = self.transactions.get(&site.key) {
            // A padding entry's narration states the padded amount, which
            // depends on what each input posted before the pad; like a
            // transaction's amounts, it is not compared. Its accounts are.
            let same = previous.file == finding.file
                && previous.line == finding.line
                && previous.date == finding.date
                && previous.groups == finding.groups
                && (site.padding || previous.narration == finding.narration)
                && previous_accounts == &accounts;
            anyhow::ensure!(
                same,
                "{}:{}: transaction differs between input ledgers",
                finding.file,
                finding.line
            );
        } else {
            self.transactions.insert(site.key, (finding, accounts));
        }
        Ok(())
    }
}

/// Where the padding entry for `pad` and `balance` is: at the `pad`, as
/// beancount locates it (and as `merge_with_padding_spanned` locates it for
/// `rledger query`).
///
/// A located pad identifies the entry, together with its balance: by the
/// balance's location, or, for a balance a plugin inserted with none, by its
/// date and currency (a pad pads each currency of a balance once). A pad a
/// plugin inserted with no location cannot be told apart from another: each
/// such entry gets a key of its own, numbered across the run by
/// `unlocated_pads`, so unrelated ones are never pooled.
fn padding_site(
    ledger: &Ledger,
    pad: &Spanned<Directive>,
    balance: &Spanned<Directive>,
    unlocated_pads: &mut usize,
) -> Site {
    let source_of = |d: &Spanned<Directive>| ledger.source_map.get(usize::from(d.file_id));
    if let Some(pad_source) = source_of(pad) {
        let (line, _) = pad_source.line_col(pad.span.start);
        let balance_key = source_of(balance).map_or_else(
            || {
                let what = match &balance.value {
                    Directive::Balance(b) => format!("{} {}", b.date, b.amount.currency),
                    other => other.date().to_string(),
                };
                (PathBuf::from(format!("<unlocated balance {what}>")), 0)
            },
            |source| (source.path.clone(), balance.span.start),
        );
        Site {
            key: ((pad_source.path.clone(), pad.span.start), Some(balance_key)),
            file: pad_source.path.display().to_string(),
            line,
            unidentified: None,
            padding: true,
        }
    } else {
        *unlocated_pads += 1;
        let (file, line) = ledger.source_map.placeholder(pad.file_id).map_or_else(
            || ("<plugin>".to_string(), 0),
            |(name, line)| (name.display().to_string(), line as usize),
        );
        Site {
            key: (
                (
                    PathBuf::from(format!("<unlocated pad {}>", *unlocated_pads)),
                    0,
                ),
                None,
            ),
            file,
            line,
            unidentified: Some(
                "a plugin inserted the pad of this padding entry, which has no source location",
            ),
            padding: true,
        }
    }
}

/// Record one input's transactions and padding entries, and refuse it when
/// unidentified transactions at one location together touch two or more
/// groups.
fn audit_ledger(
    audit: &mut Audit<'_>,
    sites: &mut TransactionSites,
    unlocated_pads: &mut usize,
    ledger: &Ledger,
) -> Result<()> {
    let mut unidentified = Unidentified::new();
    let mut ledger_sites = sites.for_ledger(ledger);
    let mut has_pads = false;
    for directive in &ledger.directives {
        match &directive.value {
            Directive::Open(open) => {
                audit.classifier.group(open.account.as_str());
            }
            Directive::Pad(_) => has_pads = true,
            Directive::Transaction(txn) => audit.record(
                txn,
                || {
                    let site = ledger_sites.site(directive);
                    Site {
                        key: (site.key, None),
                        file: site.file,
                        line: site.line,
                        unidentified: site.unidentified,
                        padding: false,
                    }
                },
                &mut unidentified,
            )?,
            _ => {}
        }
    }
    if has_pads {
        // The canonical pad expansion; its errors are the validator's,
        // already in `ledger.errors`.
        let plain: Vec<Directive> = ledger.directives.iter().map(|d| d.value.clone()).collect();
        let padding =
            rustledger_booking::process_pads(&plain, ledger.options.inferred_tolerance_multiplier);
        for (txn, origin) in padding
            .padding_transactions
            .iter()
            .zip(&padding.padding_origins)
        {
            let (pad, balance) = (
                &ledger.directives[origin.pad],
                &ledger.directives[origin.balance],
            );
            audit.record(
                txn,
                || padding_site(ledger, pad, balance, unlocated_pads),
                &mut unidentified,
            )?;
        }
    }
    if let Some((file, line, reason, touched)) =
        unidentified.into_values().find(|(_, _, _, g)| g.len() >= 2)
    {
        anyhow::bail!(
            "{file}:{line}: cannot audit transactions touching groups {}: {reason}",
            touched.into_iter().collect::<Vec<_>>().join(", ")
        );
    }
    Ok(())
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
    let mut audit = Audit {
        classifier: Classifier::new(&groups),
        transactions: BTreeMap::new(),
        keep_all: args.files.len() > 1,
    };
    let mut sites = TransactionSites::default();
    let mut unlocated_pads = 0;
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
        audit_ledger(&mut audit, &mut sites, &mut unlocated_pads, &ledger)?;
    }
    for (_, prefix) in &audit.classifier.prefixes {
        if !audit.classifier.used.contains(prefix) {
            messages.warn(
                warning_codes::GROUP_PREFIX_NOT_IN_LEDGER,
                format!("--group prefix {prefix}: no account opened or posted to matches it"),
            );
        }
    }
    let findings: Vec<Finding> = audit
        .transactions
        .into_values()
        .map(|(f, _)| f)
        .filter(|f| f.groups.len() >= 2)
        .collect();
    let failed = args.fail_on_findings && !findings.is_empty();
    let report = Report {
        findings,
        unassigned_accounts: audit.classifier.unassigned.len(),
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

    fn run_raw(args: &Args) -> Result<(ExitCode, String, String)> {
        let mut out = Vec::new();
        let mut err = Vec::new();
        let code = run_with_writer(args, &mut out, None, &mut err)?;
        Ok((code, String::from_utf8(out)?, String::from_utf8(err)?))
    }

    fn inspect(args: &Args) -> Result<(ExitCode, serde_json::Value, String)> {
        let (code, out, err) = run_raw(args)?;
        Ok((code, serde_json::from_str(&out)?, err))
    }

    fn write(dir: &std::path::Path, name: &str, content: &str) -> PathBuf {
        let path = dir.join(name);
        fs::write(&path, content).unwrap();
        path
    }

    fn refusal(groups: &[&str]) -> String {
        parse_groups(&groups.iter().map(|s| (*s).into()).collect::<Vec<_>>())
            .err()
            .unwrap_or_else(|| panic!("{groups:?} was accepted"))
            .to_string()
    }

    #[test]
    fn test_cross_group_reports_crossings_and_unassigned() {
        let dir = tempfile::tempdir().unwrap();
        let file = write(dir.path(), "main.bean", LEDGER);
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
    fn test_cross_group_text_output() {
        let dir = tempfile::tempdir().unwrap();
        let file = write(dir.path(), "main.bean", LEDGER);
        let mut args = args(vec![file.clone()]);
        args.format = OutputFormat::Text;
        let (status, out, warnings) = run_raw(&args).unwrap();
        assert_eq!(status, ExitCode::SUCCESS);
        assert_eq!(
            out,
            format!(
                "{}:9: 2024-01-03 cross\n  A: Assets:UnitA:Cash\n  B: Assets:UnitB:Cash\n\
                 1 cross-group transaction(s); 1 distinct unassigned posting account(s).\n",
                file.display()
            )
        );
        assert!(warnings.is_empty(), "{warnings}");
    }

    #[test]
    fn test_cross_group_strict_and_unused_prefix() {
        let dir = tempfile::tempdir().unwrap();
        let file = write(dir.path(), "main.bean", LEDGER);
        let mut args = args(vec![file]);
        args.group.push("C=Assets:Unused".into());
        args.fail_on_findings = true;
        let (status, _, warnings) = inspect(&args).unwrap();
        assert_eq!(status, ExitCode::from(1));
        assert_eq!(
            warnings,
            "warning: --group prefix Assets:Unused: no account opened or posted to matches it\n"
        );
    }

    /// A prefix only an `open` matches is used: no warning.
    #[test]
    fn test_cross_group_open_only_prefix_is_used() {
        let dir = tempfile::tempdir().unwrap();
        let file = write(
            dir.path(),
            "main.bean",
            &format!("{LEDGER}2024-01-01 open Assets:OnlyOpened:Cash USD\n"),
        );
        let mut args = args(vec![file]);
        args.group.push("C=Assets:OnlyOpened".into());
        let (_, report, warnings) = inspect(&args).unwrap();
        assert!(warnings.is_empty(), "{warnings}");
        // An opened account is not a posting account: not unassigned either.
        assert_eq!(report["unassigned_accounts"], 1);
    }

    #[test]
    fn test_cross_group_configuration_refusals_name_the_problem() {
        for (groups, want) in [
            (
                &["A=Assets:UnitA"][..],
                "at least two distinct --group names are required",
            ),
            (
                &["A=Assets:UnitA", "B=Assets:UnitA"],
                "overlapping prefixes Assets:UnitA (B) and Assets:UnitA (A)",
            ),
            // A later group's prefix nested under an earlier one's.
            (
                &["A=Assets:UnitA", "B=Assets:UnitA:Cash"],
                "overlapping prefixes Assets:UnitA:Cash (B) and Assets:UnitA (A)",
            ),
            // The reverse: a later group's prefix is the parent.
            (
                &["A=Assets:UnitA:Cash", "B=Assets:UnitA"],
                "overlapping prefixes Assets:UnitA (B) and Assets:UnitA:Cash (A)",
            ),
            (
                &["A=Assets:UnitA,", "B=Assets:UnitB"],
                "--group A: invalid account prefix \"\"",
            ),
            (
                &["A=Assets:UnitA", "B=not-an-account"],
                "--group B: invalid account prefix \"not-an-account\"",
            ),
            (
                &["A=Assets:UnitA", "Assets:UnitB"],
                "--group \"Assets:UnitB\": each group must be NAME=PREFIX[,PREFIX...]",
            ),
            (
                &["A=Assets:UnitA;Assets:UnitB"],
                "--group \"Assets:UnitB\": each group must be NAME=PREFIX[,PREFIX...]",
            ),
            (
                &["=Assets:UnitA", "B=Assets:UnitB"],
                "--group =Assets:UnitA: group name must contain only letters, digits, '_' or '-'",
            ),
            (
                &["A=Assets:UnitA;", "B=Assets:UnitB"],
                "--group \"A=Assets:UnitA;\": has an empty group (a stray ';'); \
                 each group must be NAME=PREFIX[,PREFIX...]",
            ),
            (
                &["A=Assets:UnitA", "L=Liabilities"],
                "--group L: account prefix \"Liabilities\" is a bare root; a prefix needs \
                 a root and at least one component, such as \"Liabilities:Example\"",
            ),
            // The suggestion does not use the group name, which may be
            // lowercase and so not a valid account component.
            (
                &["a=Liabilities", "B=Assets:UnitB"],
                "--group a: account prefix \"Liabilities\" is a bare root; a prefix needs \
                 a root and at least one component, such as \"Liabilities:Example\"",
            ),
        ] {
            assert_eq!(refusal(groups), want, "{groups:?}");
        }
        assert!(!matches_prefix("Assets:UnitAB:Cash", "Assets:UnitA"));
        assert!(matches_prefix("Assets:UnitA", "Assets:UnitA"));
        assert!(matches_prefix("Assets:UnitA:Cash", "Assets:UnitA"));
        let groups = parse_groups(&["A=Assets:UnitA;B=Assets:UnitB".into()]).unwrap();
        assert_eq!(groups.keys().collect::<Vec<_>>(), ["A", "B"]);
        // Overlap within one group is fine.
        assert!(parse_groups(&["A=Assets:UnitA,Assets:UnitA:Cash;B=Assets:UnitB".into()]).is_ok());
    }

    #[test]
    fn test_cross_group_deduplicates_included_files() {
        let dir = tempfile::tempdir().unwrap();
        let child = write(dir.path(), "child.bean", LEDGER);
        let main = write(dir.path(), "main.bean", "include \"child.bean\"\n");
        let (_, report, _) = inspect(&args(vec![main, child])).unwrap();
        assert_eq!(report["findings"].as_array().unwrap().len(), 1);
        assert_eq!(report["unassigned_accounts"], 1);
    }

    /// A file read by two inputs whose processing tells a transaction apart
    /// (here a plugin in one root renames an account) is refused rather than
    /// reported from whichever input came first.
    #[test]
    fn test_cross_group_refuses_transaction_differing_between_inputs() {
        let dir = tempfile::tempdir().unwrap();
        let child = write(
            dir.path(),
            "child.bean",
            concat!(
                "2024-01-01 open Assets:UnitA:Cash USD\n",
                "2024-01-01 open Assets:Other:Cash USD\n",
                "2024-01-02 * \"move\"\n",
                "  Assets:UnitA:Cash -2 USD\n",
                "  Assets:Other:Cash 2 USD\n",
            ),
        );
        let main = write(
            dir.path(),
            "main.bean",
            concat!(
                "plugin \"beancount_reds_plugins.rename_accounts.rename_accounts\" ",
                "\"{'Assets:Other': 'Assets:UnitB'}\"\n",
                "include \"child.bean\"\n",
            ),
        );
        let error = inspect(&args(vec![child.clone(), main]))
            .err()
            .unwrap()
            .to_string();
        assert_eq!(
            error,
            format!(
                "{}:3: transaction differs between input ledgers",
                child.display()
            )
        );
    }

    #[test]
    fn test_cross_group_refuses_unloadable_and_failed_plugins() {
        let dir = tempfile::tempdir().unwrap();
        for (content, want) in [
            (
                "include \"missing.bean\"\n",
                "cannot inspect source with load errors: ",
            ),
            (
                "plugin \"no_such_plugin\"\n",
                "cannot inspect a ledger whose processing failed: ",
            ),
            (
                "2024-01-01 * \"unbookable\"\n  Assets:UnitA:Cash\n  Assets:UnitB:Cash\n",
                "cannot inspect a ledger whose processing failed: ",
            ),
        ] {
            let file = write(dir.path(), "main.bean", content);
            let error = inspect(&args(vec![file.clone()]))
                .err()
                .unwrap()
                .to_string();
            assert!(
                error.starts_with(&format!("{}: {want}", file.display())),
                "{content}: {error}"
            );
        }
    }

    #[test]
    fn test_cross_group_handles_successful_plugin() {
        let dir = tempfile::tempdir().unwrap();
        let file = write(
            dir.path(),
            "main.bean",
            concat!(
                "plugin \"beancount.plugins.auto_accounts\"\n",
                "2024-01-02 * \"move\"\n",
                "  Assets:UnitA:Cash -2 USD\n",
                "  Assets:UnitB:Cash 2 USD\n"
            ),
        );
        let (_, report, warnings) = inspect(&args(vec![file])).unwrap();
        assert_eq!(report["findings"].as_array().unwrap().len(), 1);
        assert!(!warnings.contains("processing failed"), "{warnings}");
    }

    const FORECAST_OPENS: &str = concat!(
        "plugin \"beancount.plugins.forecast\"\n",
        "2024-01-01 open Assets:UnitA:Cash USD\n",
        "2024-01-01 open Assets:UnitB:Cash USD\n",
        "2024-01-01 open Assets:Other USD\n",
        "2024-01-01 open Expenses:Other USD\n",
    );

    /// `forecast`'s copies keep the template's location. When they touch
    /// two groups, which copy a finding is cannot be said: refused.
    #[test]
    fn test_cross_group_refuses_plugin_transactions_crossing_at_a_shared_location() {
        let dir = tempfile::tempdir().unwrap();
        let file = write(
            dir.path(),
            "main.bean",
            &format!(
                "{FORECAST_OPENS}{}",
                concat!(
                    "2024-01-02 # \"Move [MONTHLY REPEAT 2 TIMES]\"\n",
                    "  Assets:UnitA:Cash -2 USD\n",
                    "  Assets:UnitB:Cash 2 USD\n"
                )
            ),
        );
        let error = inspect(&args(vec![file.clone()]))
            .err()
            .unwrap()
            .to_string();
        assert_eq!(
            error,
            format!(
                "{}:6: cannot audit transactions touching groups A, B: several transactions \
                 share one source location (a plugin inserted one)",
                file.display()
            )
        );
    }

    /// A `forecast` of transactions touching no group does not stop the run.
    #[test]
    fn test_cross_group_answers_over_unrelated_forecast() {
        let dir = tempfile::tempdir().unwrap();
        let file = write(
            dir.path(),
            "main.bean",
            &format!(
                "{FORECAST_OPENS}{}",
                concat!(
                    "2024-01-02 # \"Rent [MONTHLY REPEAT 2 TIMES]\"\n",
                    "  Assets:Other -2 USD\n",
                    "  Expenses:Other 2 USD\n",
                    "2024-01-03 * \"cross\"\n",
                    "  Assets:UnitA:Cash -3 USD\n",
                    "  Assets:UnitB:Cash 3 USD\n",
                )
            ),
        );
        let (status, report, _) = inspect(&args(vec![file])).unwrap();
        assert_eq!(status, ExitCode::SUCCESS);
        let findings = report["findings"].as_array().unwrap();
        assert_eq!(findings.len(), 1, "{report}");
        assert_eq!(findings[0]["line"], 9);
        assert_eq!(report["unassigned_accounts"], 2);
    }

    /// A `forecast` within one group touches one group: it cannot cross.
    #[test]
    fn test_cross_group_answers_over_forecast_within_one_group() {
        let dir = tempfile::tempdir().unwrap();
        let file = write(
            dir.path(),
            "main.bean",
            &format!(
                "{FORECAST_OPENS}{}",
                concat!(
                    "2024-01-02 # \"Sweep [MONTHLY REPEAT 2 TIMES]\"\n",
                    "  Assets:UnitA:Cash -2 USD\n",
                    "  Assets:Other 2 USD\n",
                )
            ),
        );
        let (_, report, _) = inspect(&args(vec![file])).unwrap();
        assert!(
            report["findings"].as_array().unwrap().is_empty(),
            "{report}"
        );
    }

    const EFFECTIVE_DATE: &str = concat!(
        "plugin \"beancount_reds_plugins.effective_date.effective_date\"\n",
        "2024-01-01 open Assets:UnitA:Cash USD\n",
        "2024-01-01 open Assets:Other USD\n",
        "2024-01-01 open Expenses:Other USD\n",
        "2024-01-01 open Expenses:UnitB USD\n",
        "2024-01-01 open Liabilities:Hold:Expenses USD\n",
        "2024-01-01 open Assets:Hold:Expenses USD\n",
    );

    /// `effective_date` splits a transaction in two at one location. Split
    /// across groups, the two halves together cross: refused, though
    /// neither half crosses alone.
    #[test]
    fn test_cross_group_effective_date_split_across_groups_is_refused() {
        let dir = tempfile::tempdir().unwrap();
        let file = write(
            dir.path(),
            "main.bean",
            &format!(
                "{EFFECTIVE_DATE}{}",
                concat!(
                    "2024-01-02 * \"Pay\"\n",
                    "  Assets:UnitA:Cash -2 USD\n",
                    "  Expenses:UnitB 2 USD\n",
                    "    effective_date: 2024-01-05\n",
                )
            ),
        );
        let mut args = args(vec![file.clone()]);
        args.group = vec!["A=Assets:UnitA".into(), "B=Expenses:UnitB".into()];
        let error = inspect(&args).err().unwrap().to_string();
        assert_eq!(
            error,
            format!(
                "{}:8: cannot audit transactions touching groups A, B: several transactions \
                 share one source location (a plugin inserted one)",
                file.display()
            )
        );
    }

    /// An `effective_date` split of a transaction touching no group does not
    /// stop the run.
    #[test]
    fn test_cross_group_answers_over_unrelated_effective_date() {
        let dir = tempfile::tempdir().unwrap();
        let file = write(
            dir.path(),
            "main.bean",
            &format!(
                "{EFFECTIVE_DATE}{}",
                concat!(
                    "2024-01-02 * \"Pay\"\n",
                    "  Assets:Other -2 USD\n",
                    "  Expenses:Other 2 USD\n",
                    "    effective_date: 2024-01-05\n",
                )
            ),
        );
        let mut args = args(vec![file]);
        args.group = vec!["A=Assets:UnitA".into(), "B=Expenses:UnitB".into()];
        let (status, report, _) = inspect(&args).unwrap();
        assert_eq!(status, ExitCode::SUCCESS);
        assert!(
            report["findings"].as_array().unwrap().is_empty(),
            "{report}"
        );
    }

    const PAD_LEDGER: &str = concat!(
        "2024-01-01 open Assets:UnitA:Cash USD\n",
        "2024-01-01 open Assets:UnitB:Cash USD\n",
        "2024-01-02 pad Assets:UnitA:Cash Assets:UnitB:Cash\n",
        "2024-01-03 balance Assets:UnitA:Cash 5 USD\n",
    );

    /// A `pad` whose padding entry moves an amount between two groups is a
    /// finding at the pad, as `rledger query` locates the entry.
    #[test]
    fn test_cross_group_reports_padding_between_groups() {
        let dir = tempfile::tempdir().unwrap();
        let file = write(dir.path(), "main.bean", PAD_LEDGER);
        let (status, report, warnings) = inspect(&args(vec![file.clone()])).unwrap();
        assert_eq!(status, ExitCode::SUCCESS);
        // Only the prefix this ledger never uses is warned about.
        assert_eq!(
            warnings,
            "warning: --group prefix Expenses:UnitA: no account opened or posted to matches it\n"
        );
        assert_eq!(
            report["findings"],
            serde_json::json!([{
                "file": file.display().to_string(),
                "line": 3,
                "date": "2024-01-02",
                "narration": "(Padding inserted for Balance of 5 USD for difference 5 USD)",
                "groups": {"A": ["Assets:UnitA:Cash"], "B": ["Assets:UnitB:Cash"]},
            }])
        );

        let mut args = args(vec![file.clone()]);
        args.format = OutputFormat::Text;
        let (_, out, _) = run_raw(&args).unwrap();
        assert_eq!(
            out,
            format!(
                "{}:3: 2024-01-02 (Padding inserted for Balance of 5 USD for difference 5 USD)\n\
                 \x20 A: Assets:UnitA:Cash\n  B: Assets:UnitB:Cash\n\
                 1 cross-group transaction(s); 0 distinct unassigned posting account(s).\n",
                file.display()
            )
        );
    }

    /// One `pad` padding two currencies is two entries, both at the pad, and
    /// read twice (an included file also given as an input) still two.
    #[test]
    fn test_cross_group_padding_per_currency_and_deduplicated() {
        let dir = tempfile::tempdir().unwrap();
        let child = write(
            dir.path(),
            "child.bean",
            concat!(
                "2024-01-01 open Assets:UnitA:Cash\n",
                "2024-01-01 open Assets:UnitB:Cash\n",
                "2024-01-02 pad Assets:UnitA:Cash Assets:UnitB:Cash\n",
                "2024-01-03 balance Assets:UnitA:Cash 5 USD\n",
                "2024-01-03 balance Assets:UnitA:Cash 7 EUR\n",
            ),
        );
        let main = write(dir.path(), "main.bean", "include \"child.bean\"\n");
        let (_, report, _) = inspect(&args(vec![main, child])).unwrap();
        let findings = report["findings"].as_array().unwrap();
        assert_eq!(findings.len(), 2, "{report}");
        assert!(findings.iter().all(|f| f["line"] == 3), "{report}");
    }

    /// A pad within one group, or to an unassigned source, is not a finding;
    /// its source account counts as an unassigned posting account, as the
    /// padding entry posts to it.
    #[test]
    fn test_cross_group_padding_within_a_group_is_not_a_finding() {
        let dir = tempfile::tempdir().unwrap();
        let file = write(
            dir.path(),
            "main.bean",
            concat!(
                "2024-01-01 open Assets:UnitA:Cash USD\n",
                "2024-01-01 open Assets:UnitB:Cash USD\n",
                "2024-01-01 open Equity:Opening USD\n",
                "2024-01-02 pad Assets:UnitA:Cash Equity:Opening\n",
                "2024-01-03 balance Assets:UnitA:Cash 5 USD\n",
            ),
        );
        let (_, report, _) = inspect(&args(vec![file])).unwrap();
        assert!(
            report["findings"].as_array().unwrap().is_empty(),
            "{report}"
        );
        assert_eq!(report["unassigned_accounts"], 1);
    }

    #[test]
    fn test_cross_group_passes_validation_errors_as_warnings() {
        let dir = tempfile::tempdir().unwrap();
        let file = write(
            dir.path(),
            "main.bean",
            concat!(
                "2024-01-01 open Assets:UnitA:Cash USD\n",
                "2024-01-02 * \"unopened\"\n",
                "  Assets:UnitA:Cash -2 USD\n",
                "  Assets:UnitB:Cash 2 USD\n"
            ),
        );
        let (_, report, warnings) = inspect(&args(vec![file])).unwrap();
        assert_eq!(report["findings"].as_array().unwrap().len(), 1);
        assert!(warnings.contains("Assets:UnitB:Cash"), "{warnings}");
    }

    /// An advisory-only diagnostic (a close with a balance, which `check`
    /// stays silent on) is not passed on as a warning.
    #[test]
    fn test_cross_group_skips_advisory_only_diagnostics() {
        let dir = tempfile::tempdir().unwrap();
        let file = write(
            dir.path(),
            "main.bean",
            &format!("{LEDGER}2024-02-01 close Assets:UnitB:Cash\n"),
        );
        let ledger = load_booked(&file).unwrap();
        assert!(
            ledger.errors.iter().any(|e| is_advisory_only_code(&e.code)),
            "the fixture must carry an advisory diagnostic: {:?}",
            ledger.errors
        );
        let (_, _, warnings) = inspect(&args(vec![file])).unwrap();
        assert!(warnings.is_empty(), "{warnings}");
    }

    #[test]
    fn test_cross_group_no_findings_in_strict_mode() {
        let dir = tempfile::tempdir().unwrap();
        let file = write(
            dir.path(),
            "main.bean",
            concat!(
                "2024-01-01 open Assets:UnitA:Cash USD\n",
                "2024-01-01 open Assets:UnitA:Other USD\n",
                "2024-01-01 open Assets:UnitB:Cash USD\n",
                "2024-01-02 * \"same\"\n",
                "  Assets:UnitA:Cash -2 USD\n",
                "  Assets:UnitA:Other 2 USD\n"
            ),
        );
        let mut args = args(vec![file]);
        args.fail_on_findings = true;
        let (status, report, _) = inspect(&args).unwrap();
        assert_eq!(status, ExitCode::SUCCESS);
        assert!(report["findings"].as_array().unwrap().is_empty());
    }

    /// An account matching two prefixes of one group (one nested under the
    /// other) uses both: neither is reported as matching nothing.
    #[test]
    fn test_cross_group_nested_prefixes_in_one_group_are_both_used() {
        let dir = tempfile::tempdir().unwrap();
        let file = write(dir.path(), "main.bean", LEDGER);
        let mut args = args(vec![file]);
        args.group = vec![
            "A=Assets:UnitA,Assets:UnitA:Cash,Expenses:UnitA".into(),
            "B=Assets:UnitB".into(),
        ];
        let (_, report, warnings) = inspect(&args).unwrap();
        assert!(warnings.is_empty(), "{warnings}");
        assert_eq!(report["findings"].as_array().unwrap().len(), 1, "{report}");
    }

    /// The same pad read through two inputs that post different amounts
    /// before it pads a different amount, so its narration differs; its
    /// accounts do not, and it is one finding, not a refusal.
    #[test]
    fn test_cross_group_padding_amount_may_differ_between_inputs() {
        let dir = tempfile::tempdir().unwrap();
        let pad = write(
            dir.path(),
            "pad.bean",
            concat!(
                "2024-01-01 open Assets:UnitA:Cash USD\n",
                "2024-01-01 open Assets:UnitB:Cash USD\n",
                "2024-01-02 pad Assets:UnitA:Cash Assets:UnitB:Cash\n",
                "2024-01-03 balance Assets:UnitA:Cash 5 USD\n",
            ),
        );
        let root = write(
            dir.path(),
            "root.bean",
            concat!(
                "2024-01-01 open Equity:Other USD\n",
                "2024-01-02 * \"deposit\"\n",
                "  Assets:UnitA:Cash 2 USD\n",
                "  Equity:Other -2 USD\n",
                "include \"pad.bean\"\n",
            ),
        );
        let mut args = args(vec![root, pad.clone()]);
        args.group = vec!["A=Assets:UnitA".into(), "B=Assets:UnitB".into()];
        let (status, report, _) = inspect(&args).unwrap();
        assert_eq!(status, ExitCode::SUCCESS);
        assert_eq!(
            report["findings"],
            serde_json::json!([{
                "file": pad.display().to_string(),
                "line": 3,
                "date": "2024-01-02",
                // From the first input, where 2 USD was already there.
                "narration": "(Padding inserted for Balance of 5 USD for difference 3 USD)",
                "groups": {"A": ["Assets:UnitA:Cash"], "B": ["Assets:UnitB:Cash"]},
            }])
        );
    }

    /// Audit `content`'s booked ledger after `edit` moves directives to no
    /// source location (as a plugin inserting them would): the narration
    /// and line of each finding.
    fn audit_edited(
        content: &str,
        edit: impl Fn(&mut Spanned<Directive>),
    ) -> Result<Vec<(String, usize)>> {
        let dir = tempfile::tempdir()?;
        let file = write(dir.path(), "main.bean", content);
        let mut ledger = load_booked(&file)?;
        ledger.directives.iter_mut().for_each(edit);
        let groups = parse_groups(&["A=Assets:UnitA".into(), "B=Assets:UnitB".into()])?;
        let mut audit = Audit {
            classifier: Classifier::new(&groups),
            transactions: BTreeMap::new(),
            keep_all: false,
        };
        audit_ledger(
            &mut audit,
            &mut TransactionSites::default(),
            &mut 0,
            &ledger,
        )?;
        Ok(audit
            .transactions
            .into_values()
            .filter(|(f, _)| f.groups.len() >= 2)
            .map(|(f, _)| (f.narration, f.line))
            .collect())
    }

    fn unlocate_pads(d: &mut Spanned<Directive>) {
        if matches!(d.value, Directive::Pad(_)) {
            d.file_id = rustledger_core::SYNTHESIZED_FILE_ID;
        }
    }

    /// Pads a plugin inserted with no location are each their own: one
    /// padding group A, another group B, are not pooled into a crossing.
    /// One that crosses on its own is still refused.
    #[test]
    fn test_cross_group_unlocated_pads_are_not_pooled() {
        let separate = concat!(
            "2024-01-01 open Assets:UnitA:Cash USD\n",
            "2024-01-01 open Assets:UnitB:Cash USD\n",
            "2024-01-01 open Equity:Opening USD\n",
            "2024-01-02 pad Assets:UnitA:Cash Equity:Opening\n",
            "2024-01-02 pad Assets:UnitB:Cash Equity:Opening\n",
            "2024-01-03 balance Assets:UnitA:Cash 5 USD\n",
            "2024-01-03 balance Assets:UnitB:Cash 7 USD\n",
        );
        assert_eq!(audit_edited(separate, unlocate_pads).unwrap(), []);

        let error = audit_edited(PAD_LEDGER, unlocate_pads)
            .err()
            .unwrap()
            .to_string();
        assert_eq!(
            error,
            "<plugin>:0: cannot audit transactions touching groups A, B: a plugin \
             inserted the pad of this padding entry, which has no source location"
        );
    }

    /// A located pad whose balances a plugin inserted with no location is
    /// still identified by the pad: each padded currency is a finding at it.
    #[test]
    fn test_cross_group_padding_with_unlocated_balance_is_reported_at_the_pad() {
        let found = audit_edited(
            concat!(
                "2024-01-01 open Assets:UnitA:Cash\n",
                "2024-01-01 open Assets:UnitB:Cash\n",
                "2024-01-02 pad Assets:UnitA:Cash Assets:UnitB:Cash\n",
                "2024-01-03 balance Assets:UnitA:Cash 5 USD\n",
                "2024-01-03 balance Assets:UnitA:Cash 7 EUR\n",
            ),
            |d| {
                if matches!(d.value, Directive::Balance(_)) {
                    d.file_id = rustledger_core::SYNTHESIZED_FILE_ID;
                }
            },
        )
        .unwrap();
        assert_eq!(
            found,
            [
                (
                    "(Padding inserted for Balance of 7 EUR for difference 7 EUR)".to_string(),
                    3
                ),
                (
                    "(Padding inserted for Balance of 5 USD for difference 5 USD)".to_string(),
                    3
                ),
            ]
        );
    }
}
