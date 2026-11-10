//! Read-only inspection of explicitly linked transit postings.
//!
//! The lint reads the booked and validated ledger, as `rledger check` sees
//! it: each input is read by [`super::load::load_booked`], the lints' shared
//! loader, which refuses load errors and runs
//! [`rustledger_loader::process`] with plugins and validation. An elided
//! transit amount is the amount booking computed, and a `plugin` line runs
//! as it does in `check`.
//!
//! What processing reports is handled by what it can do to the answer:
//!
//! - An error that drops or alters transactions refuses the input (the
//!   shared loader does this, for `closed-nonempty` too): a
//!   transaction booking rejected is left out of the booked stream, and a
//!   plugin that failed (it could not run, its output was discarded, or a
//!   native plugin could not use its config and did nothing) left the
//!   directives other than it would have. Reporting a link as `missing`, or
//!   its partner as matched, over either would be a misleading answer.
//! - Any other error located on a linked transaction (an unbalanced leg, an
//!   unopened or closed account, a plugin's finding on that transaction)
//!   makes the link `ambiguous`, with the error as the reason: a leg `check`
//!   rejects is not a leg this lint can vouch for.
//! - Everything else (errors elsewhere in the ledger, errors with no
//!   transaction location such as `check_commodity`'s, and warnings) is
//!   passed through as a warning and does not refuse the input.
//!
//! A transaction a plugin inserted with no source location, or at a
//! location another transaction already has (`forecast`'s copies keep the
//! template's, `effective_date`'s keep the parent's), cannot be told from
//! another, so its link is `ambiguous` rather than merged into a match.
//!
//! A configuration that cannot match anything is said so, not answered with
//! an empty report: an `--account` that is not an account name is refused, a
//! leading `^` on `--link-prefix` is dropped with a note, and a configured
//! account the ledger never uses, or a prefix no link starts with, is a
//! warning. Warnings go where the CLI's warnings go (stderr, or the
//! `ag-rledger` envelope's `warnings`).

use anyhow::Result;
use clap::Parser;
use rustledger_core::{Amount, Directive, Link};
use rustledger_loader::ErrorSeverity;
use rustledger_validate::is_advisory_only_code;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::PathBuf;
use std::process::ExitCode;

use super::closed_nonempty::OutputFormat;
use super::load::{describe_error, load_booked};
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
    /// Exit 1 when a link ends in one of these statuses (comma-separated or
    /// repeated), as `check` exits 1 on an error; for CI or a pre-commit
    /// hook. Without it, findings are advisory and the exit status is 0.
    #[arg(long, value_enum, value_delimiter = ',', value_name = "STATUS")]
    pub fail_on: Vec<Status>,
    /// Output format.
    #[arg(long, short = 'f', value_enum, default_value_t = OutputFormat::Text)]
    pub format: OutputFormat,
}

/// What the lint concluded about one link.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, clap::ValueEnum)]
#[serde(rename_all = "lowercase")]
pub enum Status {
    /// Two transactions, one transit posting each, equal and opposite
    /// amounts in one currency on one account.
    Matched,
    /// Two comparable legs whose transit postings differ.
    Mismatch,
    /// Only one leg has a transit posting.
    Missing,
    /// The legs are not something this lint can compare safely.
    Ambiguous,
}

impl Status {
    /// Every status, in the order the count line lists them.
    pub const ALL: [Self; 4] = [
        Self::Matched,
        Self::Mismatch,
        Self::Missing,
        Self::Ambiguous,
    ];

    /// The lowercase name, as in the JSON and the text output.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Matched => "matched",
            Self::Mismatch => "mismatch",
            Self::Missing => "missing",
            Self::Ambiguous => "ambiguous",
        }
    }
}

impl std::fmt::Display for Status {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Serialize)]
struct Location {
    file: String,
    line: usize,
    /// The leg's postings to a configured transit account, as booked.
    transit: Vec<TransitPosting>,
}

/// One posting to a configured transit account, in the JSON report.
#[derive(Serialize)]
struct TransitPosting {
    account: String,
    /// `None` when booking left the amount incomplete.
    amount: Option<TransitAmount>,
}

/// A booked amount, its number as written (`"100.00"`), so no precision
/// is lost to a JSON float.
#[derive(Serialize)]
struct TransitAmount {
    number: String,
    currency: String,
}

/// Why two comparable transit postings are not a match, naming what
/// differs, or `None` when they match: one account, one currency, equal
/// non-zero amounts of opposite sign.
fn mismatch_reason(a: (&str, &Amount), b: (&str, &Amount)) -> Option<String> {
    let ((account_a, amount_a), (account_b, amount_b)) = (a, b);
    if account_a != account_b {
        Some(format!("account: {account_a} vs {account_b}"))
    } else if amount_a.currency != amount_b.currency {
        Some(format!("currency: {amount_a} vs {amount_b}"))
    } else if amount_a.number.is_zero() || amount_b.number.is_zero() {
        Some(format!("zero transit amount: {amount_a} vs {amount_b}"))
    } else if amount_a.number.is_sign_negative() == amount_b.number.is_sign_negative() {
        Some(format!("direction: {amount_a} vs {amount_b} (same sign)"))
    } else if amount_a.number != -amount_b.number {
        Some(format!("amount: {amount_a} vs {amount_b}"))
    } else {
        None
    }
}

struct Leg {
    location: Location,
    postings: Vec<(String, Option<Amount>)>,
    complex: bool,
    /// Indices into the run's [`Reported`] list of the errors located on
    /// this leg's transaction.
    errors: BTreeSet<usize>,
    /// Why the transaction cannot be told apart from another (see where it
    /// is set), which makes its link `ambiguous`.
    unidentified: Option<&'static str>,
}

#[derive(Serialize)]
struct Finding {
    link: String,
    status: Status,
    reason: String,
    locations: Vec<Location>,
}

#[derive(Serialize)]
struct Report {
    counts: Counts,
    findings: Vec<Finding>,
}

/// How many links ended in each status.
#[derive(Serialize, Clone, Copy, Default)]
struct Counts {
    matched: usize,
    mismatch: usize,
    missing: usize,
    ambiguous: usize,
}

impl Counts {
    fn of(findings: &[Finding]) -> Self {
        let mut counts = Self::default();
        for finding in findings {
            *match finding.status {
                Status::Matched => &mut counts.matched,
                Status::Mismatch => &mut counts.mismatch,
                Status::Missing => &mut counts.missing,
                Status::Ambiguous => &mut counts.ambiguous,
            } += 1;
        }
        counts
    }
}

/// `312 matched, 2 mismatch, 1 missing, 0 ambiguous`.
impl std::fmt::Display for Counts {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} matched, {} mismatch, {} missing, {} ambiguous",
            self.matched, self.mismatch, self.missing, self.ambiguous
        )
    }
}

/// A processing diagnostic this lint reports rather than refuses on: the
/// reason of an `ambiguous` link when it is on a leg, else a warning.
struct Reported {
    /// `file:line: CODE: message`, as [`describe_error`] writes it.
    described: String,
    code: String,
    message: String,
    /// Where the error is, for the warning's `file` and `line`.
    file: Option<String>,
    line: Option<usize>,
    /// Whether a finding names it, so it is not repeated as a warning.
    on_leg: bool,
}

/// Errors by the file and line they are located at: indices into the run's
/// [`Reported`] list.
type ErrorsByLine = HashMap<PathBuf, BTreeMap<usize, Vec<usize>>>;

/// The first and last line `span` covers in `source`. A directive's span
/// runs from its date to the start of the next directive, so for a
/// transaction it covers the header, the postings, and any blank or comment
/// lines before the next directive (none of which an error is located at).
fn span_lines(
    source: &rustledger_loader::SourceFile,
    span: rustledger_core::Span,
) -> (usize, usize) {
    let (first, _) = source.line_col(span.start);
    let (last, _) = source.line_col(span.end.saturating_sub(1).max(span.start));
    (first, last)
}

/// The errors located on lines `first..=last` of `file`: for a transaction,
/// the lines [`span_lines`] gives, so a plugin error located at one of its
/// postings is the transaction's too.
fn errors_within<'a>(
    by_line: &'a ErrorsByLine,
    file: &std::path::Path,
    first: usize,
    last: usize,
) -> impl Iterator<Item = usize> + 'a {
    by_line
        .get(file)
        .into_iter()
        .flat_map(move |lines| lines.range(first..=last))
        .flat_map(|(_, indices)| indices.iter().copied())
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

/// Inspect booked transactions and write an advisory report.
///
/// The report goes to `out`. Warnings (a dropped `^`, an account or prefix
/// the ledger never uses, a processing diagnostic not on a linked leg) go to
/// `warnings` when given, else to `err` as `warning: ...` lines.
///
/// # Errors
/// Returns an error when the inputs cannot be safely inspected (load errors,
/// a booking failure, a plugin failure), when an `--account` is not a valid
/// account name, or when output fails.
#[allow(clippy::too_many_lines)]
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
    let mut groups: BTreeMap<String, BTreeMap<(PathBuf, usize), Leg>> = BTreeMap::new();
    let mut reported: Vec<Reported> = Vec::new();
    // Plugin-inserted transactions with no source location, numbered so
    // that none is merged with another.
    let mut unlocated = 0usize;
    for path in &args.files {
        // Booking, plugins and validation, as `rledger check` runs them, so
        // a leg `check` rejects is not reported as matched. The shared lint
        // loader refuses load errors and booking or plugin failures; see the
        // module docs for what each other kind of error does to the answer.
        let ledger = load_booked(path)?;
        // The other errors, by the transaction each is located on: a
        // validator's by its span, a plugin's by its file and line.
        let mut by_span: HashMap<(u16, usize), Vec<usize>> = HashMap::new();
        let mut by_line = ErrorsByLine::new();
        for error in &ledger.errors {
            // `check` stays silent on these; `lint closed-nonempty` reports
            // them.
            if is_advisory_only_code(&error.code) {
                continue;
            }
            let index = reported.len();
            if error.severity == ErrorSeverity::Error {
                if let (Some(file_id), Some((start, _))) = (error.file_id, error.source_span) {
                    by_span.entry((file_id, start)).or_default().push(index);
                }
                if let Some(location) = &error.location {
                    by_line
                        .entry(location.file.clone())
                        .or_default()
                        .entry(location.line)
                        .or_default()
                        .push(index);
                }
            }
            reported.push(Reported {
                described: describe_error(error),
                code: error.code.clone(),
                message: error.message.clone(),
                file: error
                    .location
                    .as_ref()
                    .map(|l| l.file.display().to_string()),
                line: error.location.as_ref().map(|l| l.line),
                on_leg: false,
            });
        }
        // How many transactions each source location holds: more than one
        // means a plugin inserted a transaction at its parent's location.
        let mut located: HashMap<(u16, usize), usize> = HashMap::new();
        for directive in &ledger.directives {
            if matches!(directive.value, Directive::Transaction(_)) {
                *located
                    .entry((directive.file_id, directive.span.start))
                    .or_default() += 1;
            }
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
            // Where the transaction is, which is also how a transaction read
            // twice (an included file given again as an input) is told from
            // two transactions. A plugin-inserted one may have no source
            // location, or reuse its parent's: neither identifies it, so
            // its link is `ambiguous`, never merged into a match.
            let (key, location, at, unidentified) =
                if let Some(source) = ledger.source_map.get(directive.file_id as usize) {
                    // `path` is the file's identity (symlinks resolved, one
                    // path for every include of it), and the path the other
                    // lints print.
                    let (line, _) = source.line_col(directive.span.start);
                    // A plugin can locate an error at one of its postings.
                    let (_, last) = span_lines(source, directive.span);
                    let shared = located
                        .get(&(directive.file_id, directive.span.start))
                        .is_some_and(|&count| count > 1);
                    (
                        (source.path.clone(), directive.span.start),
                        (source.path.display().to_string(), line),
                        Some((source.path.clone(), line, last)),
                        shared.then_some(
                            "several transactions share one source location \
                             (a plugin inserted one)",
                        ),
                    )
                } else {
                    unlocated += 1;
                    let (file, line) = ledger
                        .source_map
                        .placeholder(directive.file_id)
                        .map_or_else(
                            || ("<plugin>".to_string(), 0),
                            |(name, line)| (name.display().to_string(), line as usize),
                        );
                    (
                        (PathBuf::from(format!("<unlocated {unlocated}>")), 0),
                        (file, line),
                        None,
                        Some("a plugin inserted this transaction, which has no source location"),
                    )
                };
            let errors: BTreeSet<usize> =
                by_span
                    .get(&(directive.file_id, directive.span.start))
                    .into_iter()
                    .flatten()
                    .copied()
                    .chain(at.iter().flat_map(|(file, first, last)| {
                        errors_within(&by_line, file, *first, *last)
                    }))
                    .collect();
            let multiple_links = links.len() > 1;
            for link in links {
                let leg = groups
                    .entry(link.to_string())
                    .or_default()
                    .entry(key.clone())
                    .or_insert_with(|| Leg {
                        location: Location {
                            file: location.0.clone(),
                            line: location.1,
                            transit: Vec::new(),
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
                        errors: BTreeSet::new(),
                        unidentified: None,
                    });
                // The same transaction read again from another input: what
                // either run reported on it counts.
                leg.errors.extend(errors.iter().copied());
                leg.unidentified = leg.unidentified.or(unidentified);
            }
        }
    }

    let mut findings = Vec::new();
    for (link, legs) in groups {
        let legs: Vec<Leg> = legs.into_values().collect();
        if legs.iter().all(|leg| leg.postings.is_empty()) {
            continue;
        }
        let on_legs: BTreeSet<usize> = legs.iter().flat_map(|l| l.errors.iter().copied()).collect();
        let (status, reason) = if !on_legs.is_empty() {
            for &index in &on_legs {
                reported[index].on_leg = true;
            }
            (
                Status::Ambiguous,
                format!(
                    "error on a linked transaction: {}",
                    on_legs
                        .iter()
                        .map(|&i| reported[i].described.as_str())
                        .collect::<BTreeSet<_>>()
                        .into_iter()
                        .collect::<Vec<_>>()
                        .join("; ")
                ),
            )
        } else if let Some(reason) = legs.iter().find_map(|l| l.unidentified) {
            (Status::Ambiguous, reason.to_string())
        } else if legs.len() > 2 || legs.iter().any(|l| l.postings.len() > 1) {
            (
                Status::Ambiguous,
                "multiple transactions or transit postings".to_string(),
            )
        } else if legs.iter().any(|l| l.complex) {
            (
                Status::Ambiguous,
                "unsupported complex transaction".to_string(),
            )
        } else if legs.len() < 2 || legs.iter().any(|l| l.postings.is_empty()) {
            (
                Status::Missing,
                "a linked transit leg is missing".to_string(),
            )
        } else {
            let (account_a, amount_a) = &legs[0].postings[0];
            let (account_b, amount_b) = &legs[1].postings[0];
            match (amount_a, amount_b) {
                (Some(a), Some(b)) => mismatch_reason((account_a, a), (account_b, b)).map_or_else(
                    || {
                        (
                            Status::Matched,
                            "opposite equal transit amounts".to_string(),
                        )
                    },
                    |reason| (Status::Mismatch, reason),
                ),
                // Booking completes every posting it accepts; an amount it
                // left incomplete is not one this lint can compare.
                _ => (
                    Status::Ambiguous,
                    "transit amount was not booked".to_string(),
                ),
            }
        };
        findings.push(Finding {
            link,
            status,
            reason,
            locations: legs
                .into_iter()
                .map(|leg| Location {
                    transit: leg
                        .postings
                        .into_iter()
                        .map(|(account, amount)| TransitPosting {
                            account,
                            amount: amount.map(|a| TransitAmount {
                                number: a.number.to_string(),
                                currency: a.currency.to_string(),
                            }),
                        })
                        .collect(),
                    ..leg.location
                })
                .collect(),
        });
    }

    // What processing reported off the linked legs, once each (an included
    // file given again as an input reports its errors twice).
    let mut passed: BTreeSet<&str> = BTreeSet::new();
    for item in reported.iter().filter(|r| !r.on_leg) {
        let line = item.described.as_str();
        if !passed.insert(line) {
            continue;
        }
        messages.emit_as(
            Diagnostic {
                code: Some(item.code.clone()),
                file: item.file.clone(),
                line: item.line,
                ..Diagnostic::message(item.message.clone())
            },
            format!("warning: {line}"),
        );
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

    // `--fail-on`: decided before the findings are consumed by the output.
    let failed = findings.iter().any(|f| args.fail_on.contains(&f.status));
    let counts = Counts::of(&findings);
    match args.format {
        OutputFormat::Json => {
            writeln!(
                out,
                "{}",
                crate::cmd::to_json_pretty(&Report { counts, findings })?
            )?;
        }
        OutputFormat::Text => {
            if findings.is_empty() {
                writeln!(out, "No linked transit transfers found.")?;
            } else {
                // Only what needs a look: on a ledger with hundreds of
                // transfers, listing every match hid the few problems. The
                // JSON keeps every finding.
                let mut listed = false;
                for finding in findings.iter().filter(|f| f.status != Status::Matched) {
                    listed = true;
                    writeln!(
                        out,
                        "^{}: {}: {}",
                        finding.link, finding.status, finding.reason
                    )?;
                    for location in &finding.locations {
                        writeln!(out, "  {}:{}", location.file, location.line)?;
                    }
                }
                if listed {
                    writeln!(out)?;
                }
                writeln!(out, "{counts}")?;
            }
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
    use crate::cmd::report_cmd::CollectedDiagnostics;
    use rustledger_loader::Loader;
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
            fail_on: Vec::new(),
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

    /// Opens for every account the tests post to, so validation passes on a
    /// well-formed leg.
    const OPENS: &str = "\
        2000-01-01 open Assets:Transit\n\
        2000-01-01 open Assets:OtherTransit\n\
        2000-01-01 open Assets:Cash\n\
        2000-01-01 open Assets:Bank\n\
        2000-01-01 open Equity:Capital\n\
        2000-01-01 open Expenses:Fee\n";

    /// Write `body` after [`OPENS`].
    fn write_ledger(path: &std::path::Path, body: impl AsRef<str>) -> std::io::Result<()> {
        fs::write(path, format!("{OPENS}{}", body.as_ref()))
    }

    fn transaction(link: &str, transit: &str, other: &str) -> String {
        format!("2024-01-01 * \"transfer\" ^{link}\n  {transit}\n  {other}\n")
    }

    /// `link`'s status is `status`; the link is named when it is not.
    #[track_caller]
    fn assert_status(report: &serde_json::Value, link: &str, status: &str) {
        let found = finding(report, link);
        assert_eq!(found["status"], status, "{link}: {found}");
    }

    #[test]
    fn test_run_with_writer_matches_equal_opposite_amounts() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("main.bean");
        let cases = [
            (
                "xfer-match",
                "Assets:Transit 100.00 USD",
                "Assets:Transit -100 USD",
            ),
            (
                "xfer-reverse",
                "Assets:Transit -0.01 USD",
                "Assets:Transit 0.010 USD",
            ),
        ];
        let mut source = String::new();
        for (link, a, b) in cases {
            source.push_str(&transaction(link, a, "Assets:Cash"));
            source.push_str(&transaction(link, b, "Assets:Cash"));
        }
        write_ledger(&path, source).unwrap();
        let report = inspect(vec![path], &["Assets:Transit"]).unwrap();
        for (link, _, _) in cases {
            assert_status(&report, link, "matched");
            let locations = finding(&report, link)["locations"]
                .as_array()
                .unwrap()
                .len();
            assert_eq!(locations, 2, "{link}: {report}");
        }
    }

    #[test]
    fn test_run_with_writer_zero_filled_leg_is_ambiguous() {
        // Booking prunes the elided `Assets:Cash` it fills from a zero
        // residual (as beancount does), so each leg books to one posting
        // and is no simple two-posting transfer.
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("main.bean");
        write_ledger(
            &path,
            format!(
                "{}{}",
                transaction("xfer-zero", "Assets:Transit 0 USD", "Assets:Cash"),
                transaction("xfer-zero", "Assets:Transit 0 USD", "Assets:Cash"),
            ),
        )
        .unwrap();
        let report = inspect(vec![path], &["Assets:Transit"]).unwrap();
        assert_status(&report, "xfer-zero", "ambiguous");
    }

    #[test]
    fn test_run_with_writer_reports_a_missing_leg() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("main.bean");
        let mut source = String::new();
        // One transaction only.
        source.push_str(&transaction(
            "xfer-missing",
            "Assets:Transit 2 USD",
            "Assets:Cash",
        ));
        // Two transactions, only one through the transit account.
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
        // Not reported: a link without the prefix, and a prefixed link
        // that never touches a transit account.
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
        write_ledger(&path, source).unwrap();
        let report = inspect(vec![path], &["Assets:Transit"]).unwrap();
        assert_status(&report, "xfer-missing", "missing");
        assert_status(&report, "xfer-no-second-leg", "missing");
        let links: Vec<&str> = report["findings"]
            .as_array()
            .unwrap()
            .iter()
            .map(|f| f["link"].as_str().unwrap())
            .collect();
        assert_eq!(links, ["xfer-missing", "xfer-no-second-leg"], "{report}");
    }

    #[test]
    fn test_run_with_writer_complex_legs_are_ambiguous() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("main.bean");
        let mut source = String::new();
        // A price on a leg.
        source.push_str(&transaction(
            "xfer-price",
            "Assets:Transit 2 USD @ 2 EUR",
            "Assets:Cash",
        ));
        source.push_str(&transaction(
            "xfer-price",
            "Assets:Transit -2 USD",
            "Assets:Cash",
        ));
        // A fee: three postings.
        source.push_str(
            "2024-01-01 * \"fee\" ^xfer-fee\n  Assets:Transit 2 USD\n  Assets:Cash -3 USD\n  Expenses:Fee 1 USD\n",
        );
        source.push_str(&transaction(
            "xfer-fee",
            "Assets:Transit -2 USD",
            "Assets:Cash",
        ));
        // Two transit postings on one leg.
        source.push_str(
            "2024-01-01 * \"multiple\" ^xfer-multi\n  Assets:Transit 1 USD\n  Assets:Transit 1 USD\n  Assets:Cash -2 USD\n",
        );
        source.push_str(&transaction(
            "xfer-multi",
            "Assets:Transit -2 USD",
            "Assets:Cash",
        ));
        // Three transactions on one link.
        for _ in 0..3 {
            source.push_str(&transaction(
                "xfer-three",
                "Assets:Transit 2 USD",
                "Assets:Cash",
            ));
        }
        // Two scoped links on one transaction.
        source.push_str(
            "2024-01-01 * \"two links\" ^xfer-a ^xfer-b\n  Assets:Transit 2 USD\n  Assets:Cash\n",
        );
        write_ledger(&path, source).unwrap();
        let report = inspect(vec![path], &["Assets:Transit"]).unwrap();
        let links = [
            "xfer-price",
            "xfer-fee",
            "xfer-multi",
            "xfer-three",
            "xfer-a",
            "xfer-b",
        ];
        for link in links {
            assert_status(&report, link, "ambiguous");
        }
        assert_eq!(
            report["findings"].as_array().unwrap().len(),
            links.len(),
            "{report}"
        );
    }

    #[test]
    fn test_run_with_writer_deduplicates_included_files() {
        let dir = tempfile::tempdir().unwrap();
        let child = dir.path().join("child.bean");
        let parent = dir.path().join("main.bean");
        write_ledger(
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
        let report = inspect(vec![parent.clone(), child, parent], &["Assets:Transit"]).unwrap();
        assert_status(&report, "xfer-shared", "matched");
        let locations = finding(&report, "xfer-shared")["locations"]
            .as_array()
            .unwrap()
            .len();
        assert_eq!(locations, 2, "{report}");
    }

    #[test]
    fn test_run_with_writer_refuses_load_errors_and_plugin_failures() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("main.bean");
        write_ledger(&path, "2024-01-01 * \"broken\"\n  not an account\n").unwrap();
        let err = inspect(vec![path.clone()], &["Assets:Transit"]).unwrap_err();
        assert!(err.to_string().contains("load errors"), "{err:#}");
        // An unknown plugin is a plugin failure: refused, not inspected with
        // the plugin silently skipped.
        write_ledger(&path, "plugin \"example\"\n").unwrap();
        let err = inspect(vec![path], &["Assets:Transit"]).unwrap_err();
        assert!(err.to_string().contains("processing failed"), "{err:#}");
    }

    #[test]
    fn test_run_with_writer_matches_elided_transit_amount() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("main.bean");
        write_ledger(
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
        write_ledger(
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
        write_ledger(
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
        assert!(err.to_string().contains("processing failed"), "{err:#}");
    }

    #[test]
    fn test_run_with_writer_refuses_empty_configuration_and_missing_include() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("main.bean");
        write_ledger(&path, "include \"missing.bean\"\n").unwrap();
        assert!(inspect(vec![path.clone()], &["Assets:Transit"]).is_err());
        write_ledger(&path, "").unwrap();
        assert!(inspect(vec![path.clone()], &[]).is_err());
        let args = Args {
            files: vec![path],
            link_prefix: String::new(),
            account: vec!["Assets:Transit".into()],
            fail_on: Vec::new(),
            format: OutputFormat::Json,
        };
        assert!(run_with_writer(&args, &mut Vec::new(), None, &mut Vec::new()).is_err());
    }

    /// A matched pair on `Assets:Transit`, for the configuration tests.
    fn matched_pair(dir: &std::path::Path) -> PathBuf {
        let path = dir.join("main.bean");
        write_ledger(
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
            fail_on: Vec::new(),
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
        assert_eq!(
            String::from_utf8(out).unwrap(),
            "1 matched, 0 mismatch, 0 missing, 0 ambiguous\n"
        );
    }

    /// The status and reason of `link` in `report`.
    fn finding<'a>(report: &'a serde_json::Value, link: &str) -> &'a serde_json::Value {
        report["findings"]
            .as_array()
            .unwrap()
            .iter()
            .find(|f| f["link"] == link)
            .unwrap_or_else(|| panic!("no finding for {link}: {report}"))
    }

    #[test]
    fn test_run_with_writer_validation_error_on_a_leg_is_ambiguous() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("main.bean");
        write_ledger(
            &path,
            concat!(
                // Unbalanced: the transit amounts agree, the leg does not.
                "2026-01-02 * \"Send\" ^xfer-unbalanced\n",
                "  Assets:Cash     -100.00 USD\n",
                "  Assets:Transit    90.00 USD\n",
                "2026-01-03 * \"Receive\" ^xfer-unbalanced\n",
                "  Assets:Transit   -90.00 USD\n",
                "  Assets:Bank       90.00 USD\n",
                // A leg on an account that was never opened.
                "2026-01-02 * \"Send\" ^xfer-unopened\n",
                "  Assets:Ghost    -5 USD\n",
                "  Assets:Transit   5 USD\n",
                "2026-01-03 * \"Receive\" ^xfer-unopened\n",
                "  Assets:Transit  -5 USD\n",
                "  Assets:Bank      5 USD\n",
                // A leg on the transit account after it was closed.
                "2026-02-01 close Assets:OtherTransit\n",
                "2026-01-10 * \"Send\" ^xfer-closed\n",
                "  Assets:Cash        -7 USD\n",
                "  Assets:OtherTransit 7 USD\n",
                "2026-03-01 * \"Receive\" ^xfer-closed\n",
                "  Assets:OtherTransit -7 USD\n",
                "  Assets:Bank          7 USD\n",
                // Elsewhere: an error on an unlinked transaction.
                "2026-04-01 * \"Unrelated\"\n",
                "  Assets:Cash  -1 USD\n",
                "  Assets:Bank   2 USD\n",
            ),
        )
        .unwrap();
        let (report, warnings) = inspect_with_warnings(
            vec![path],
            "xfer-",
            &["Assets:Transit", "Assets:OtherTransit"],
        )
        .unwrap();
        for (link, code) in [
            ("xfer-unbalanced", "E3001"),
            ("xfer-unopened", "E1001"),
            ("xfer-closed", "E1003"),
        ] {
            let found = finding(&report, link);
            assert_eq!(found["status"], "ambiguous", "{link}: {found}");
            assert!(
                found["reason"].as_str().unwrap().contains(code),
                "{link}: {found}"
            );
        }
        // The unlinked transaction's error is a warning, not a refusal and
        // not a finding; the errors on the legs are not repeated.
        assert_eq!(codes(&warnings), vec!["E3001"], "{warnings:?}");
        assert!(
            warnings[0].message.contains("residual 1 USD"),
            "{warnings:?}"
        );
        // Where it is, as a field: 6 opens, then the unrelated one at body
        // line 20.
        assert_eq!(warnings[0].line, Some(26), "{warnings:?}");
        assert!(
            warnings[0]
                .file
                .as_deref()
                .is_some_and(|f| f.ends_with("main.bean")),
            "{warnings:?}"
        );
    }

    #[test]
    fn test_run_with_writer_plugin_findings_are_warnings() {
        // check_commodity reports a currency per account, with no
        // transaction location (as beancount's `<check_commodity>`), so it is
        // a warning whether the undeclared currency is on a leg or elsewhere,
        // and the file is still inspected.
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("main.bean");
        fs::write(
            &path,
            format!(
                "plugin \"beancount.plugins.check_commodity\"\n\
                 2000-01-01 commodity USD\n{OPENS}{}{}{}",
                transaction("xfer-a", "Assets:Transit 5 CHF", "Assets:Cash"),
                transaction("xfer-a", "Assets:Transit -5 CHF", "Assets:Cash"),
                "2024-02-01 * \"Elsewhere\"\n  Assets:Cash  -1 EUR\n  Assets:Bank\n",
            ),
        )
        .unwrap();
        let (report, warnings) =
            inspect_with_warnings(vec![path], "xfer-", &["Assets:Transit"]).unwrap();
        assert_eq!(finding(&report, "xfer-a")["status"], "matched", "{report}");
        let messages: Vec<&str> = warnings.iter().map(|w| w.message.as_str()).collect();
        assert!(
            messages
                .iter()
                .any(|m| m.contains("'CHF' in 'Assets:Cash'"))
                && messages
                    .iter()
                    .any(|m| m.contains("'EUR' in 'Assets:Bank'")),
            "{warnings:?}"
        );
    }

    #[test]
    fn test_run_with_writer_inserted_transactions_at_a_shared_location_are_ambiguous() {
        // forecast's copies keep the template's location, so two copies of
        // one leg are at one place; merged as one transaction read twice,
        // they matched the receiving leg.
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("main.bean");
        fs::write(
            &path,
            format!(
                "plugin \"beancount.plugins.forecast\"\n{OPENS}{}",
                concat!(
                    "2026-01-02 # \"Send [MONTHLY REPEAT 2 TIMES]\" ^xfer-f\n",
                    "  Assets:Cash     -10 USD\n",
                    "  Assets:Transit   10 USD\n",
                    "2026-01-03 * \"Receive\" ^xfer-f\n",
                    "  Assets:Transit  -10 USD\n",
                    "  Assets:Bank      10 USD\n",
                ),
            ),
        )
        .unwrap();
        let report = inspect(vec![path], &["Assets:Transit"]).unwrap();
        let found = finding(&report, "xfer-f");
        assert_eq!(found["status"], "ambiguous", "{found}");
        assert!(
            found["reason"]
                .as_str()
                .unwrap()
                .contains("share one source location"),
            "{found}"
        );

        // effective_date inserts the moved posting's transaction at its
        // parent's location, with the parent's links.
        let path = dir.path().join("effective.bean");
        fs::write(
            &path,
            format!(
                "plugin \"beancount_reds_plugins.effective_date.effective_date\" \
                 \"{{'Assets:Transit': {{'earlier': 'Liabilities:Hold:Transit', \
                 'later': 'Assets:Hold:Transit'}}}}\"\n{OPENS}{}",
                concat!(
                    "2026-01-02 * \"Send\" ^xfer-e\n",
                    "  Assets:Cash     -100.00 USD\n",
                    "  Assets:Transit   100.00 USD\n",
                    "    effective_date: 2026-01-05\n",
                    "2026-01-06 * \"Receive\" ^xfer-e\n",
                    "  Assets:Transit  -100.00 USD\n",
                    "  Assets:Bank\n",
                ),
            ),
        )
        .unwrap();
        let report = inspect(vec![path], &["Assets:Transit"]).unwrap();
        let found = finding(&report, "xfer-e");
        assert_eq!(found["status"], "ambiguous", "{found}");
        assert!(
            found["reason"]
                .as_str()
                .unwrap()
                .contains("share one source location"),
            "{found}"
        );
    }

    #[test]
    fn test_run_with_writer_mismatch_names_what_differs() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("main.bean");
        let cases = [
            (
                "xfer-amount",
                "Assets:Transit 100.00 USD",
                "Assets:Transit -90.00 USD",
                "amount: 100.00 USD vs -90.00 USD",
            ),
            (
                "xfer-currency",
                "Assets:Transit 100 USD",
                "Assets:Transit -100 EUR",
                "currency: 100 USD vs -100 EUR",
            ),
            (
                "xfer-direction",
                "Assets:Transit 100 USD",
                "Assets:Transit 100 USD",
                "direction: 100 USD vs 100 USD (same sign)",
            ),
            (
                "xfer-account",
                "Assets:Transit 100 USD",
                "Assets:OtherTransit -100 USD",
                "account: Assets:Transit vs Assets:OtherTransit",
            ),
        ];
        let mut source = String::new();
        for (link, a, b, _) in cases {
            source.push_str(&transaction(link, a, "Assets:Cash"));
            source.push_str(&transaction(link, b, "Assets:Cash"));
        }
        // Both sides explicit, so booking keeps the zero postings.
        source.push_str(&transaction(
            "xfer-zero",
            "Assets:Transit 0 USD",
            "Assets:Cash 0 USD",
        ));
        source.push_str(&transaction(
            "xfer-zero",
            "Assets:Transit 0 USD",
            "Assets:Cash 0 USD",
        ));
        write_ledger(&path, source).unwrap();
        let report = inspect(vec![path], &["Assets:Transit", "Assets:OtherTransit"]).unwrap();
        for (link, _, _, reason) in cases
            .iter()
            .map(|&(link, a, b, reason)| (link, a, b, reason))
            .chain([("xfer-zero", "", "", "zero transit amount: 0 USD vs 0 USD")])
        {
            let found = finding(&report, link);
            assert_eq!(found["status"], "mismatch", "{link}: {found}");
            assert_eq!(found["reason"], reason, "{link}: {found}");
        }
        // The amounts are in the JSON, numbers as written.
        assert_eq!(
            finding(&report, "xfer-amount")["locations"][1]["transit"],
            serde_json::json!([{
                "account": "Assets:Transit",
                "amount": {"number": "-90.00", "currency": "USD"}
            }]),
            "{report}"
        );
    }

    #[test]
    fn test_run_with_writer_text_lists_only_what_did_not_match() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("main.bean");
        write_ledger(
            &path,
            format!(
                "{}{}{}{}",
                transaction("xfer-a", "Assets:Transit 5 USD", "Assets:Cash"),
                transaction("xfer-a", "Assets:Transit -5 USD", "Assets:Cash"),
                transaction("xfer-b", "Assets:Transit 5 USD", "Assets:Cash"),
                transaction("xfer-b", "Assets:Transit -4 USD", "Assets:Cash"),
            ),
        )
        .unwrap();
        let args = Args {
            files: vec![path.clone()],
            link_prefix: "xfer-".into(),
            account: vec!["Assets:Transit".into()],
            fail_on: Vec::new(),
            format: OutputFormat::Text,
        };
        let mut out = Vec::new();
        run_with_writer(&args, &mut out, None, &mut Vec::new()).unwrap();
        let file = path.display();
        assert_eq!(
            String::from_utf8(out).unwrap(),
            format!(
                "^xfer-b: mismatch: amount: 5 USD vs -4 USD\n  {file}:13\n  {file}:16\n\n\
                 1 matched, 1 mismatch, 0 missing, 0 ambiguous\n"
            )
        );
        // The JSON keeps the match, and the counts.
        let report = inspect(vec![path], &["Assets:Transit"]).unwrap();
        assert_eq!(report["findings"].as_array().unwrap().len(), 2, "{report}");
        assert_eq!(
            report["counts"],
            serde_json::json!({"matched": 1, "mismatch": 1, "missing": 0, "ambiguous": 0}),
            "{report}"
        );
    }

    /// A location names the file as the other lints do, here
    /// `closed-nonempty` on the same ledger, reached through a symlink.
    #[cfg(unix)]
    #[test]
    fn test_run_with_writer_prints_paths_as_the_other_lints_do() {
        let dir = tempfile::tempdir().unwrap();
        fs::create_dir(dir.path().join("real")).unwrap();
        std::os::unix::fs::symlink(dir.path().join("real"), dir.path().join("link")).unwrap();
        // Assets:Cash is closed holding 1 USD, for closed-nonempty to report.
        write_ledger(
            &dir.path().join("real/main.bean"),
            format!(
                "{}{}{}2030-01-01 close Assets:Cash\n",
                transaction("xfer-a", "Assets:Transit 5 USD", "Assets:Bank"),
                transaction("xfer-a", "Assets:Transit -5 USD", "Assets:Bank"),
                transaction("other", "Assets:Cash 1 USD", "Equity:Capital"),
            ),
        )
        .unwrap();
        let path = dir.path().join("link/main.bean");

        let report = inspect(vec![path.clone()], &["Assets:Transit"]).unwrap();
        let mut closed = Vec::new();
        super::super::closed_nonempty::run_with_writer(
            &super::super::closed_nonempty::Args {
                files: vec![path],
                format: OutputFormat::Json,
            },
            &mut closed,
        )
        .unwrap();
        let closed: serde_json::Value = serde_json::from_slice(&closed).unwrap();
        assert_eq!(
            finding(&report, "xfer-a")["locations"][0]["file"],
            closed["findings"][0]["file"],
            "{report}\n{closed}"
        );
    }

    #[test]
    fn test_run_with_writer_fail_on_exits_one_for_a_listed_status() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("main.bean");
        write_ledger(
            &path,
            format!(
                "{}{}{}",
                transaction("xfer-a", "Assets:Transit 5 USD", "Assets:Cash"),
                transaction("xfer-a", "Assets:Transit -5 USD", "Assets:Cash"),
                transaction("xfer-b", "Assets:Transit 5 USD", "Assets:Cash"),
            ),
        )
        .unwrap();
        let exit = |fail_on: Vec<Status>| {
            let args = Args {
                files: vec![path.clone()],
                link_prefix: "xfer-".into(),
                account: vec!["Assets:Transit".into()],
                fail_on,
                format: OutputFormat::Json,
            };
            run_with_writer(&args, &mut Vec::new(), None, &mut Vec::new()).unwrap()
        };
        // One match and one missing leg.
        assert_eq!(exit(vec![]), ExitCode::SUCCESS);
        assert_eq!(
            exit(vec![Status::Mismatch, Status::Ambiguous]),
            ExitCode::SUCCESS
        );
        assert_eq!(exit(vec![Status::Missing]), ExitCode::from(1));
        assert_eq!(
            exit(vec![Status::Mismatch, Status::Missing]),
            ExitCode::from(1)
        );
        // From the command line, comma-separated or repeated.
        for argv in [
            vec![
                "lint",
                "f",
                "--link-prefix",
                "x",
                "--account",
                "A:B",
                "--fail-on",
                "mismatch,missing",
            ],
            vec![
                "lint",
                "f",
                "--link-prefix",
                "x",
                "--account",
                "A:B",
                "--fail-on",
                "mismatch",
                "--fail-on",
                "missing",
            ],
        ] {
            let parsed = Args::try_parse_from(&argv).unwrap();
            assert_eq!(
                parsed.fail_on,
                vec![Status::Mismatch, Status::Missing],
                "{argv:?}"
            );
        }
        assert!(
            Args::try_parse_from([
                "lint",
                "f",
                "--link-prefix",
                "x",
                "--account",
                "A:B",
                "--fail-on",
                "nope"
            ])
            .is_err()
        );
    }

    /// A native plugin that cannot use its config returns the ledger as it
    /// was: a plugin failure, so the file is refused. With `rename_accounts`
    /// failing on a bad pattern, two clean legs read as `matched`, where the
    /// rename the config meant makes them `ambiguous`.
    #[test]
    fn test_run_with_writer_refuses_a_plugin_that_cannot_use_its_config() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("main.bean");
        let ledger = |pattern: &str| {
            format!(
                "plugin \"beancount.plugins.rename_accounts\" \"{{'{pattern}': 'Assets:Transit'}}\"\n\
                 {OPENS}{}{}",
                transaction("xfer-a", "Assets:Transit 5 USD", "Assets:Cash"),
                transaction("xfer-a", "Assets:Transit -5 USD", "Assets:Cash"),
            )
        };
        fs::write(&path, ledger("Assets:Cash(")).unwrap();
        let err = inspect(vec![path.clone()], &["Assets:Transit"]).unwrap_err();
        assert!(err.to_string().contains("processing failed"), "{err:#}");
        assert!(err.to_string().contains("rename_accounts"), "{err:#}");
        // The pattern fixed, the rename runs and each leg has two transit
        // postings.
        fs::write(&path, ledger("Assets:Cash")).unwrap();
        let report = inspect(vec![path], &["Assets:Transit"]).unwrap();
        assert_status(&report, "xfer-a", "ambiguous");
    }

    /// Every line in the range counts, header and postings alike; a line
    /// past it, or one in another file, does not.
    #[test]
    fn test_errors_within_takes_every_line_in_the_range() {
        let file = PathBuf::from("/ledger/main.bean");
        let mut by_line = ErrorsByLine::new();
        for (line, index) in [(10, 0), (12, 1), (13, 2), (20, 3)] {
            by_line
                .entry(file.clone())
                .or_default()
                .entry(line)
                .or_default()
                .push(index);
        }
        by_line
            .entry(PathBuf::from("/ledger/other.bean"))
            .or_default()
            .entry(11)
            .or_default()
            .push(4);
        // A range of lines 10 to 12, as span_lines gives for a transaction.
        let found: Vec<usize> = errors_within(&by_line, &file, 10, 12).collect();
        assert_eq!(found, [0, 1]);
        assert_eq!(
            errors_within(&by_line, std::path::Path::new("/ledger/none.bean"), 1, 99).count(),
            0
        );
    }

    /// The range of a real transaction: from its header up to the next
    /// directive, so its postings (and blank and comment lines after them)
    /// are in it, and the next transaction is not.
    #[test]
    fn test_span_lines_covers_a_parsed_transaction() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("main.bean");
        fs::write(
            &path,
            concat!(
                "2000-01-01 open Assets:Cash\n",
                "\n",
                "2024-01-01 * \"a\" ^xfer-a\n",
                "  Assets:Transit 5 USD\n",
                "  Assets:Cash\n",
                "\n",
                "; a comment\n",
                "2024-01-02 * \"b\"\n",
                "  Assets:Cash 1 USD\n",
                "  Assets:Transit\n",
            ),
        )
        .unwrap();
        let loaded = Loader::new().load(&path).unwrap();
        let file = &loaded.source_map.files()[0];
        let spans: Vec<(usize, usize)> = loaded
            .directives
            .iter()
            .filter(|d| matches!(d.value, Directive::Transaction(_)))
            .map(|d| span_lines(file, d.span))
            .collect();
        assert_eq!(spans.len(), 2, "{spans:?}");
        let (first, last) = spans[0];
        assert_eq!(first, 3, "{spans:?}");
        // Up to the line before the next directive: the comment.
        assert_eq!(last, 7, "{spans:?}");
        assert_eq!(spans[1].0, 8, "{spans:?}");
        // An error at the first transaction's second posting is its own,
        // not the next one's.
        let mut by_line = ErrorsByLine::new();
        by_line
            .entry(file.path.clone())
            .or_default()
            .entry(5)
            .or_default()
            .push(0);
        assert_eq!(errors_within(&by_line, &file.path, first, last).count(), 1);
        let (next_first, next_last) = spans[1];
        assert_eq!(
            errors_within(&by_line, &file.path, next_first, next_last).count(),
            0,
            "{spans:?}"
        );
    }
}
