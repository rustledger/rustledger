//! How a lint loads its inputs: the one place every `rledger lint`
//! subcommand gets its ledger from, so that no lint re-derives which load
//! and processing errors it may answer over.
//!
//! A lint reads its input at one of three levels:
//!
//! - [`load_booked`]: the ledger as `rledger check` sees it, booked, with
//!   plugins and validation run. A file with load errors is refused, and so
//!   is a ledger whose booking or plugins failed
//!   ([`LedgerError::is_booking_failure`], [`LedgerError::is_plugin_failure`]):
//!   either drops or alters transactions, so an answer over it could be
//!   wrong, and a clean "nothing found" would be the most misleading answer
//!   of all. The other processing errors are left in [`Ledger::errors`] for
//!   the lint to treat as it can (`linked-transit` makes a link `ambiguous`
//!   or passes the error on as a warning; `closed-nonempty` reads its
//!   advisory out of them). Used by `linked-transit` and `closed-nonempty`.
//! - [`load_clean`]: the parsed source, refused if it has load errors. Used
//!   by `transfers --apply`, which rewrites the source files and must not
//!   do so from a parse it cannot trust.
//! - [`load_source`]: the parsed source, load errors and all, for a lint
//!   that can still answer over what parsed. Such a lint must say that the
//!   input had load errors ([`warn_load_errors`]), so that it never prints a
//!   clean "no findings" over a file it only partly read. Used by
//!   `control-chars` (a control character is often what broke the parse, and
//!   the parser recovers enough to find it) and read-only `transfers`.
//!
//! The refusals are `Err`s: `rledger lint` reports them as `error: ...` and
//! exits with [`super::error_exit_code`].

use anyhow::{Context, Result};
use rustledger_loader::{Ledger, LedgerError, LoadError, LoadOptions, LoadResult, Loader};
use std::path::Path;

use crate::cmd::messages::Messages;

/// The code of the warning [`warn_load_errors`] emits, as carried in
/// `ag-rledger`'s `warnings`.
pub const LOAD_ERRORS: &str = "LOAD_ERRORS";

/// The processing `rledger check` runs: plugins (within the configured
/// budget) and validation.
fn check_options() -> LoadOptions {
    LoadOptions {
        run_plugins: true,
        validate: true,
        plugin_max_time_secs: crate::plugin_budget::max_time_secs(),
        plugin_max_memory_mb: crate::plugin_budget::max_memory_mb(),
        ..Default::default()
    }
}

/// `file:line: CODE: message`.
pub fn describe_error(err: &LedgerError) -> String {
    let at = err
        .location
        .as_ref()
        .map(|l| format!("{}:{}: ", l.file.display(), l.line))
        .unwrap_or_default();
    format!("{at}{}: {}", err.code, err.message)
}

/// [`describe_error`] for each error, joined for one message.
pub fn describe_errors<'a>(errors: impl Iterator<Item = &'a LedgerError>) -> String {
    errors.map(describe_error).collect::<Vec<_>>().join("; ")
}

/// Each load error, joined for one message.
fn describe_load_errors(errors: &[LoadError]) -> String {
    errors
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join("; ")
}

/// Load `path`, load errors and all.
///
/// A lint that answers over the result must call [`warn_load_errors`].
///
/// # Errors
/// Fails if `path` cannot be loaded at all (it does not exist, or cannot be
/// read).
pub fn load_source(path: &Path) -> Result<LoadResult> {
    Loader::new()
        .load(path)
        .with_context(|| format!("failed to load {}", path.display()))
}

/// Load `path`, refusing it if it has load errors (a parse error, a missing
/// include, ...).
///
/// # Errors
/// As [`load_source`], and when the file has load errors.
pub fn load_clean(path: &Path) -> Result<LoadResult> {
    let result = load_source(path)?;
    anyhow::ensure!(
        result.errors.is_empty(),
        "{}: cannot inspect source with load errors: {}",
        path.display(),
        describe_load_errors(&result.errors)
    );
    Ok(result)
}

/// Load `path` and process it as `rledger check` does.
///
/// Booking, plugins and validation run. Load errors, a booking failure, or a
/// plugin failure refuse the input; every other processing error is left in
/// [`Ledger::errors`].
///
/// # Errors
/// As [`load_clean`], when processing fails outright, and when it reports a
/// booking or plugin failure.
pub fn load_booked(path: &Path) -> Result<Ledger> {
    let result = load_clean(path)?;
    let ledger = rustledger_loader::process(result, &check_options())
        .with_context(|| format!("failed to process {}", path.display()))?;
    let mut refusals = ledger
        .errors
        .iter()
        .filter(|e| e.is_booking_failure() || e.is_plugin_failure())
        .peekable();
    anyhow::ensure!(
        refusals.peek().is_none(),
        "{}: cannot inspect a ledger whose processing failed: {}",
        path.display(),
        describe_errors(refusals)
    );
    Ok(ledger)
}

/// Warn, when `errors` is not empty, that the lint's answer over `path` may
/// be incomplete. A lint that reads its input with [`load_source`] calls
/// this for every input.
pub fn warn_load_errors(messages: &mut Messages<'_>, path: &Path, errors: &[LoadError]) {
    if errors.is_empty() {
        return;
    }
    messages.warn(
        LOAD_ERRORS,
        format!(
            "{}: has load errors, so findings may be incomplete: {}",
            path.display(),
            describe_load_errors(errors)
        ),
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cmd::report_cmd::CollectedDiagnostics;

    fn ledger(dir: &Path, body: &str) -> std::path::PathBuf {
        let path = dir.join("main.beancount");
        std::fs::write(&path, body).unwrap();
        path
    }

    /// A transaction with two elided postings cannot be booked, and a
    /// plugin that does not exist fails.
    const UNBOOKABLE: &str = concat!(
        "plugin \"no.such.plugin\"\n",
        "2024-01-01 open Assets:Cash\n",
        "2024-01-01 open Expenses:Food\n",
        "2024-01-02 * \"lunch\"\n",
        "  Assets:Cash\n",
        "  Expenses:Food\n",
        "2024-12-31 close Assets:Cash\n",
    );

    #[test]
    fn test_load_booked_refuses_booking_and_plugin_failures() {
        let dir = tempfile::tempdir().unwrap();
        let path = ledger(dir.path(), UNBOOKABLE);
        let err = load_booked(&path).unwrap_err().to_string();
        assert!(
            err.starts_with(&format!(
                "{}: cannot inspect a ledger whose processing failed: ",
                path.display()
            )),
            "{err}"
        );
        // Both failures are named, not just the first.
        assert!(err.contains("no.such.plugin"), "{err}");
        assert!(err.contains("; "), "{err}");
    }

    #[test]
    fn test_load_booked_keeps_other_errors_for_the_lint() {
        let dir = tempfile::tempdir().unwrap();
        // An unopened account is a validation error, not a refusal.
        let path = ledger(
            dir.path(),
            concat!(
                "2024-01-01 open Assets:Cash\n",
                "2024-01-02 * \"lunch\"\n",
                "  Assets:Cash  -1 USD\n",
                "  Expenses:Food\n",
            ),
        );
        let ledger = load_booked(&path).unwrap();
        assert!(!ledger.errors.is_empty());
    }

    #[test]
    fn test_load_clean_and_load_booked_refuse_load_errors() {
        let dir = tempfile::tempdir().unwrap();
        let path = ledger(dir.path(), "include \"missing-xyz.beancount\"\n");
        let want = format!(
            "{}: cannot inspect source with load errors: ",
            path.display()
        );
        let err = load_clean(&path).unwrap_err().to_string();
        assert!(err.starts_with(&want), "{err}");
        let err = load_booked(&path).unwrap_err().to_string();
        assert!(err.starts_with(&want), "{err}");
    }

    #[test]
    fn test_load_source_keeps_load_errors_and_warn_load_errors_says_so() {
        let dir = tempfile::tempdir().unwrap();
        let path = ledger(dir.path(), "include \"missing-xyz.beancount\"\n");
        let result = load_source(&path).unwrap();
        assert!(!result.errors.is_empty());

        let mut err = Vec::new();
        let mut sink = CollectedDiagnostics::default();
        warn_load_errors(
            &mut Messages::new(&mut err, Some(&mut sink)),
            &path,
            &result.errors,
        );
        assert_eq!(sink.0.len(), 1);
        assert_eq!(sink.0[0].code.as_deref(), Some(LOAD_ERRORS));
        assert!(
            sink.0[0].message.starts_with(&format!(
                "{}: has load errors, so findings may be incomplete: ",
                path.display()
            )),
            "{:?}",
            sink.0[0]
        );

        // Without a sink, it is a `warning:` line.
        let mut err = Vec::new();
        warn_load_errors(&mut Messages::new(&mut err, None), &path, &result.errors);
        assert!(
            String::from_utf8(err).unwrap().starts_with("warning: "),
            "expected a warning line"
        );
    }

    #[test]
    fn test_warn_load_errors_is_silent_without_errors() {
        let mut err = Vec::new();
        let mut sink = CollectedDiagnostics::default();
        warn_load_errors(
            &mut Messages::new(&mut err, Some(&mut sink)),
            Path::new("x.beancount"),
            &[],
        );
        assert!(sink.0.is_empty());
        assert!(err.is_empty());
    }
}
