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
//! code is `0` whether or not any are reported. Hard errors (missing file,
//! parse failure) propagate via `anyhow::Error`.

use anyhow::{Context, Result};
use clap::{Parser, ValueEnum};
use rustledger_loader::{LoadOptions, Loader};
use rustledger_validate::ErrorCode;
use serde::Serialize;
use std::path::PathBuf;
use std::process::ExitCode;

/// Validate code for "account closed with a non-zero balance", sourced from the
/// canonical [`ErrorCode`] so it can't drift from the enum.
const CLOSE_NONEMPTY_CODE: &str = ErrorCode::AccountCloseNotEmpty.code();

/// Output format for the report.
#[derive(Debug, Clone, Copy, Default, ValueEnum)]
pub enum OutputFormat {
    /// Human-readable text (default).
    #[default]
    Text,
    /// JSON: a single object with a `findings` array.
    Json,
}

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
/// Fails if any input file does not exist or cannot be parsed/processed.
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
/// Fails if any input file does not exist or cannot be parsed/processed.
pub fn run_with_writer<W: std::io::Write>(args: &Args, out: &mut W) -> Result<ExitCode> {
    let mut findings = Vec::new();
    let options = LoadOptions {
        run_plugins: true,
        validate: true,
        ..Default::default()
    };
    for path in &args.files {
        let load_result = Loader::new()
            .load(path)
            .with_context(|| format!("failed to load {}", path.display()))?;
        // The Loader surfaces parse/include errors in `errors` rather than
        // returning `Err`. We can't reliably analyze account closes in a file
        // that didn't parse, so fail loudly instead of reporting a misleading
        // "no accounts closed with a non-zero balance" for invalid input.
        if !load_result.errors.is_empty() {
            let joined = load_result
                .errors
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("; ");
            anyhow::bail!(
                "{}: cannot lint a file with load errors: {joined}",
                path.display()
            );
        }
        let ledger = rustledger_loader::process(load_result, &options)
            .with_context(|| format!("failed to process {}", path.display()))?;
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
            writeln!(out, "{}", serde_json::to_string_pretty(&report)?)?;
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
}
