//! `rledger lint closed-nonempty` — report accounts that are closed while
//! still holding a non-zero balance.
//!
//! Python beancount's `bean-check` does NOT flag this: closing an account
//! merely records that it is inactive from that date and does not require a
//! zero balance. So `rledger check` stays silent to match it (the underlying
//! validate diagnostic `E1004` / `AccountCloseNotEmpty` is marked
//! `rustledger_validate::ErrorCode::is_advisory_only`). This lint surfaces the
//! same advisory for users who want it — closing an account with a residual
//! balance is frequently a bookkeeping mistake (the balance is usually
//! transferred out first).
//!
//! This is a lint, not a check: finding accounts is not a failure, so the exit
//! code is `0` whether or not any are reported.
//!
//! The ledger is read by [`super::load::load_booked`], the lints' shared
//! loader, as `linked-transit` reads it. An input it cannot answer for is
//! refused with an `Err`, and `rledger lint` exits 2 (see
//! [`super::ERROR_EXIT_CODE`]): a missing file, load errors, a transaction
//! booking rejected, or a plugin that failed. A transaction booking dropped
//! never reaches the balances, and a failed plugin left the ledger other
//! than it would have, so "No accounts closed with a non-zero balance." over
//! either would be an answer the lint cannot vouch for.

use anyhow::Result;
use clap::Parser;
use rustledger_validate::ErrorCode;

use super::OutputFormat;
use serde::Serialize;
use std::path::PathBuf;
use std::process::ExitCode;

/// Validate code for "account closed with a non-zero balance", sourced from the
/// canonical [`ErrorCode`] so it can't drift from the enum.
const CLOSE_NONEMPTY_CODE: &str = ErrorCode::AccountCloseNotEmpty.code();

/// Report accounts that are closed while still holding a non-zero balance.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// Beancount files to scan. At least one is required.
    #[arg(value_name = "FILE", required = true)]
    pub files: Vec<PathBuf>,

    /// Output format.
    #[arg(long, short = 'f', value_enum, default_value_t = OutputFormat::Text)]
    pub format: OutputFormat,
}

/// One reported account close with a residual balance.
#[derive(Serialize)]
struct Finding {
    /// Source file the `close` directive lives in, if known.
    file: Option<String>,
    /// 1-based line of the `close` directive, if known.
    line: Option<usize>,
    /// The advisory message (account + residual positions).
    message: String,
}

/// The JSON report shape.
#[derive(Serialize)]
struct Report {
    findings: Vec<Finding>,
}

/// Run the lint, writing its report to stdout.
///
/// # Errors
/// Fails if any input file does not exist, has load errors, or cannot be
/// processed, or if booking or a plugin failed on it.
pub fn run(args: &Args) -> Result<ExitCode> {
    let mut stdout = std::io::stdout().lock();
    run_with_writer(args, &mut stdout)
}

/// Run the lint, writing the text/JSON report to `out`.
///
/// Reuses the canonical load+book+validate pipeline (`process` with
/// `validate: true`) so detection stays identical to what `check` computes —
/// the only difference is that `check` filters this advisory out while this
/// lint keeps only it.
///
/// # Errors
/// Fails if any input file does not exist, has load errors, or cannot be
/// processed, or if booking or a plugin failed on it.
pub fn run_with_writer<W: std::io::Write>(args: &Args, out: &mut W) -> Result<ExitCode> {
    let mut findings = Vec::new();
    for path in &args.files {
        // Refuses load errors and booking or plugin failures (see the
        // module docs), so a clean report is never printed over a ledger
        // this lint could not read whole.
        let ledger = super::load::load_booked(path)?;
        for err in &ledger.errors {
            if err.code == CLOSE_NONEMPTY_CODE {
                findings.push(Finding {
                    file: err.location.as_ref().map(|l| l.file.display().to_string()),
                    line: err.location.as_ref().map(|l| l.line),
                    message: err.message.clone(),
                });
            }
        }
    }

    match args.format {
        OutputFormat::Text => {
            if findings.is_empty() {
                writeln!(out, "No accounts closed with a non-zero balance.")?;
            } else {
                for f in &findings {
                    let loc = match (&f.file, f.line) {
                        (Some(file), Some(line)) => format!("{file}:{line}"),
                        (Some(file), None) => file.clone(),
                        _ => "<unknown>".to_string(),
                    };
                    writeln!(out, "{loc}: {}", f.message)?;
                }
                writeln!(
                    out,
                    "\n{} account(s) closed with a non-zero balance.",
                    findings.len()
                )?;
            }
        }
        OutputFormat::Json => {
            let report = Report { findings };
            writeln!(out, "{}", crate::cmd::to_json_pretty(&report)?)?;
        }
    }
    Ok(ExitCode::SUCCESS)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write as _;

    fn lint_text(content: &str) -> String {
        let mut file = tempfile::Builder::new()
            .suffix(".beancount")
            .tempfile()
            .unwrap();
        file.write_all(content.as_bytes()).unwrap();
        let args = Args {
            files: vec![file.path().to_path_buf()],
            format: OutputFormat::Text,
        };
        let mut buf: Vec<u8> = Vec::new();
        run_with_writer(&args, &mut buf).unwrap();
        String::from_utf8(buf).unwrap()
    }

    #[test]
    fn reports_account_closed_with_balance() {
        let out = lint_text(concat!(
            "2024-01-01 open Assets:Cash\n",
            "2024-01-01 open Equity:Opening-Balances\n",
            "2024-01-02 * \"deposit\"\n",
            "  Assets:Cash   100.00 USD\n",
            "  Equity:Opening-Balances\n",
            "2024-12-31 close Assets:Cash\n",
        ));
        assert!(
            out.contains("Assets:Cash"),
            "expected the closed account to be reported, got: {out}"
        );
        assert!(
            out.contains("1 account(s)"),
            "expected a one-account summary, got: {out}"
        );
    }

    #[test]
    fn silent_when_account_closed_empty() {
        let out = lint_text(concat!(
            "2024-01-01 open Assets:Cash\n",
            "2024-01-01 open Equity:Opening-Balances\n",
            "2024-01-02 * \"deposit\"\n",
            "  Assets:Cash   100.00 USD\n",
            "  Equity:Opening-Balances\n",
            "2024-06-01 * \"withdraw all\"\n",
            "  Assets:Cash  -100.00 USD\n",
            "  Equity:Opening-Balances\n",
            "2024-12-31 close Assets:Cash\n",
        ));
        assert!(
            out.contains("No accounts closed with a non-zero balance"),
            "expected no findings for a zero-balance close, got: {out}"
        );
    }

    #[test]
    fn errors_on_file_with_load_errors() {
        // A missing include surfaces as a load error; the lint must fail loudly
        // rather than silently report "no accounts" on a file it couldn't load.
        let mut file = tempfile::Builder::new()
            .suffix(".beancount")
            .tempfile()
            .unwrap();
        file.write_all(b"include \"definitely-missing-xyz.beancount\"\n")
            .unwrap();
        let args = Args {
            files: vec![file.path().to_path_buf()],
            format: OutputFormat::Text,
        };
        let mut buf: Vec<u8> = Vec::new();
        assert!(
            run_with_writer(&args, &mut buf).is_err(),
            "expected a hard error when the file has load errors"
        );
    }

    /// The refusal for `content`, which must leave nothing on `out`.
    fn refusal(content: &str) -> (String, String) {
        let mut file = tempfile::Builder::new()
            .suffix(".beancount")
            .tempfile()
            .unwrap();
        file.write_all(content.as_bytes()).unwrap();
        let args = Args {
            files: vec![file.path().to_path_buf()],
            format: OutputFormat::Text,
        };
        let mut buf: Vec<u8> = Vec::new();
        let err = run_with_writer(&args, &mut buf).unwrap_err().to_string();
        assert!(buf.is_empty(), "nothing is reported: {buf:?}");
        let shown = file.path().display().to_string();
        assert!(
            err.starts_with(&format!(
                "{shown}: cannot inspect a ledger whose processing failed: "
            )),
            "{err}"
        );
        (err, shown)
    }

    /// A transaction with two elided postings (which booking cannot resolve)
    /// and a `close`: the transaction is left out of the balances.
    const UNBOOKABLE: &str = concat!(
        "2024-01-01 open Assets:Cash\n",
        "2024-01-01 open Expenses:Food\n",
        "2024-01-02 * \"lunch\"\n",
        "  Assets:Cash\n",
        "  Expenses:Food\n",
        "2024-12-31 close Assets:Cash\n",
    );

    #[test]
    fn test_run_with_writer_refuses_a_booking_failure() {
        let (err, shown) = refusal(UNBOOKABLE);
        assert!(
            err.contains(&format!("{shown}:4: BOOK: interpolation failed")),
            "{err}"
        );
    }

    #[test]
    fn test_run_with_writer_refuses_a_plugin_failure() {
        let (err, _) = refusal("plugin \"no.such.plugin\"\n2024-01-01 open Assets:Cash\n");
        assert!(err.contains("E8004: "), "{err}");
        assert!(err.contains("no.such.plugin"), "{err}");
    }

    /// The ledger from #2899: a plugin that does not exist, the unbookable
    /// transaction and a `close`. This used to print "No accounts closed
    /// with a non-zero balance." and exit 0. Both failures are named.
    #[test]
    fn test_run_with_writer_refuses_failed_booking_and_plugins() {
        let (err, shown) = refusal(&format!("plugin \"no.such.plugin\"\n{UNBOOKABLE}"));
        assert!(
            err.contains(&format!("{shown}:5: BOOK: interpolation failed")),
            "{err}"
        );
        assert!(err.contains("E8004: "), "{err}");
    }
}
