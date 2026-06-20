//! Non-fatal advisory passes — lints.
//!
//! `rledger lint <NAME> <ARGS...>` runs a named lint over the given inputs and
//! reports issues without failing the build. The first lint is `transfers`,
//! which finds likely inter-account transfer pairs and (optionally) links
//! them with `^link:` tags.

use anyhow::Result;
use clap::{Parser, Subcommand};
use std::process::ExitCode;

pub mod closed_nonempty;
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
    /// Report accounts closed while still holding a non-zero balance.
    ///
    /// `check` stays silent on this to match `bean-check`; this lint is the
    /// place the advisory lives.
    ClosedNonempty(closed_nonempty::Args),
}

/// Dispatch to the requested lint, writing its report to stdout.
///
/// # Errors
/// Propagates errors from the underlying lint implementation.
pub fn run(args: &Args) -> Result<ExitCode> {
    match &args.lint {
        LintKind::Transfers(t_args) => transfers::run(t_args),
        LintKind::ClosedNonempty(c_args) => closed_nonempty::run(c_args),
    }
}

/// Dispatch to the requested lint, writing its report to `out`.
///
/// Writer-injectable variant used by `ag-rledger`; behavior otherwise
/// matches [`run`].
///
/// # Errors
/// Propagates errors from the underlying lint implementation.
pub fn run_with_writer<W: std::io::Write>(args: &Args, out: &mut W) -> Result<ExitCode> {
    match &args.lint {
        LintKind::Transfers(t_args) => transfers::run_with_writer(t_args, out),
        LintKind::ClosedNonempty(c_args) => closed_nonempty::run_with_writer(c_args, out),
    }
}
