//! Non-fatal advisory passes — lints.
//!
//! `rledger lint <NAME> <ARGS...>` runs a named lint over the given inputs and
//! reports issues without failing the build. The first lint is `transfers`,
//! which finds likely inter-account transfer pairs and (optionally) links
//! them with `^link:` tags.

use crate::cmd::report_cmd::Diagnostics;
use anyhow::Result;
use clap::{Parser, Subcommand};
use std::process::ExitCode;

pub mod closed_nonempty;
pub mod control_chars;
pub mod linked_transit;
pub mod transfers;

/// Run non-fatal advisory passes over one or more beancount files.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// The specific lint to run.
    #[command(subcommand)]
    pub lint: LintKind,
}

/// Available lints.
#[derive(Subcommand, Debug)]
pub enum LintKind {
    /// Detect inter-account transfer pairs.
    Transfers(transfers::Args),
    /// Check explicitly linked transfer legs through configured transit accounts.
    LinkedTransit(linked_transit::Args),
    /// Report accounts closed while still holding a non-zero balance.
    ///
    /// `check` stays silent on this to match `bean-check`; this lint is the
    /// place the advisory lives.
    ClosedNonempty(closed_nonempty::Args),
    /// Report control characters in the ledger's strings (narrations,
    /// payees, metadata, comments).
    ///
    /// `check` accepts them, as `bean-check` does; this lint finds them,
    /// usually left by imported or shared data.
    ControlChars(control_chars::Args),
}

/// Dispatch to the requested lint, writing its report to stdout.
///
/// # Errors
/// Propagates errors from the underlying lint implementation.
pub fn run(args: &Args) -> Result<ExitCode> {
    match &args.lint {
        LintKind::Transfers(t_args) => transfers::run(t_args),
        LintKind::LinkedTransit(t_args) => linked_transit::run(t_args),
        LintKind::ClosedNonempty(c_args) => closed_nonempty::run(c_args),
        LintKind::ControlChars(c_args) => control_chars::run(c_args),
    }
}

/// Dispatch to the requested lint, writing its report to `out`.
///
/// Writer-injectable variant used by `ag-rledger`; behavior otherwise
/// matches [`run`]. `warnings` and `err` are where a lint's warnings go (see
/// [`crate::cmd::messages::Messages`]); only `linked-transit` emits any.
///
/// # Errors
/// Propagates errors from the underlying lint implementation.
pub fn run_with_writer<W: std::io::Write>(
    args: &Args,
    out: &mut W,
    warnings: Option<&mut dyn Diagnostics>,
    err: &mut dyn std::io::Write,
) -> Result<ExitCode> {
    match &args.lint {
        LintKind::Transfers(t_args) => transfers::run_with_writer(t_args, out),
        LintKind::LinkedTransit(t_args) => {
            linked_transit::run_with_writer(t_args, out, warnings, err)
        }
        LintKind::ClosedNonempty(c_args) => closed_nonempty::run_with_writer(c_args, out),
        LintKind::ControlChars(c_args) => control_chars::run_with_writer(c_args, out),
    }
}

/// The exit status for a lint that could not run (a missing file, a file
/// that does not load, a configuration it refuses).
///
/// `linked-transit` exits 2, as `rledger check` does on a file it cannot
/// read, so that with `--fail-on` a 1 always means a finding. The other
/// lints exit 1, as they always have.
#[must_use]
pub const fn error_exit_code(args: &Args) -> u8 {
    match args.lint {
        LintKind::LinkedTransit(_) => 2,
        LintKind::Transfers(_) | LintKind::ClosedNonempty(_) | LintKind::ControlChars(_) => 1,
    }
}
