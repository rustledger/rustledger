//! The host's time budget and memory cap for WASM and Python plugins and
//! WASM importers.
//!
//! `rledger` and `ag-rledger` set them once at startup from the `[plugins]
//! max_time_secs` and `max_memory_mb` config keys, overridden by
//! `--plugin-max-time-secs` and `--plugin-max-memory-mb` ([`PluginBudgetArgs`],
//! the one definition both binaries parse). Every command that
//! runs a WASM or Python plugin or importer reads it from here, so the setting
//! applies to all of them rather than to whichever commands thread an
//! argument through.
//!
//! It is deliberately a host setting and not a ledger one: see
//! `rustledger_plugin::ResolvedPlugin::run_with_max_time_secs`.

use std::sync::OnceLock;

use clap::{Args, CommandFactory, FromArgMatches};

use crate::config::{MAX_PLUGIN_MEMORY_MB, PluginsConfig};

/// The global plugin-budget flags, defined once for both binaries.
///
/// `rledger` flattens this into its clap `Cli`. `ag-rledger` cannot (it
/// parses with `agcli`), so it hands the values it finds to
/// [`PluginBudgetArgs::parse_flags`], which runs them through this same
/// definition: the names, the ranges and the error text cannot drift between
/// the two. Before this was shared, `ag-rledger` had neither flag and
/// silently ignored both (#2522, #2552).
#[derive(Args, Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct PluginBudgetArgs {
    /// Time budget for each WASM or Python plugin call and WASM importer
    /// call: it is stopped
    /// within at most this many seconds, usually far sooner (default: 30, or
    /// `[plugins] max_time_secs` from the config file)
    #[arg(
        long,
        global = true,
        value_name = "SECS",
        value_parser = clap::value_parser!(u64).range(1..)
    )]
    pub plugin_max_time_secs: Option<u64>,

    /// Memory cap, in MiB, for each WASM or Python plugin or WASM importer
    /// call (default: 256, or `[plugins] max_memory_mb` from the config
    /// file; at most 4096). A Python plugin needs about 1.2 KB per
    /// transaction
    #[arg(
        long,
        global = true,
        value_name = "MB",
        value_parser = clap::value_parser!(u64).range(1..=MAX_PLUGIN_MEMORY_MB)
    )]
    pub plugin_max_memory_mb: Option<u64>,
}

/// A standalone clap command holding only [`PluginBudgetArgs`].
#[derive(clap::Parser)]
#[command(name = "rledger", no_binary_name = true)]
struct BudgetOnly {
    #[command(flatten)]
    budget: PluginBudgetArgs,
}

impl PluginBudgetArgs {
    /// The flags' long names, without the leading `--`, with each one's
    /// value placeholder (`("plugin-max-time-secs", "SECS")`).
    ///
    /// Read from the clap definition, so a flag added to the struct shows up
    /// here, in `ag-rledger`'s usage strings and in both binaries' alias
    /// expansion without anyone editing a list.
    #[must_use]
    pub fn flags() -> Vec<(String, String)> {
        BudgetOnly::command()
            .get_arguments()
            .filter_map(|arg| {
                let long = arg.get_long()?;
                let value = arg
                    .get_value_names()
                    .and_then(|names| names.first())
                    .map_or_else(|| "VALUE".to_string(), ToString::to_string);
                Some((long.to_string(), value))
            })
            .collect()
    }

    /// Parse `(long name, value)` pairs, as `ag-rledger` finds them, through
    /// the clap definition `rledger` uses.
    ///
    /// # Errors
    ///
    /// The clap error for an unknown name or a value out of range, with the
    /// same text `rledger` prints.
    pub fn parse_flags<'a>(
        pairs: impl IntoIterator<Item = (&'a str, &'a str)>,
    ) -> Result<Self, clap::Error> {
        let argv: Vec<String> = pairs
            .into_iter()
            .map(|(long, value)| format!("--{long}={value}"))
            .collect();
        let matches = BudgetOnly::command().try_get_matches_from(argv)?;
        BudgetOnly::from_arg_matches(&matches).map(|parsed| parsed.budget)
    }

    /// Set the process's budget: each flag, else its config key.
    ///
    /// Call once, before any command runs a plugin. The setters keep the
    /// first value they are given, so a config-only call made earlier
    /// would silently win over the flags.
    pub fn apply(&self, config: &PluginsConfig) {
        set_max_time_secs(
            self.plugin_max_time_secs
                .or(config.max_time_secs.map(std::num::NonZeroU64::get)),
        );
        set_max_memory_mb(self.plugin_max_memory_mb.or(config.max_memory_mb));
    }
}

static MAX_TIME_SECS: OnceLock<Option<u64>> = OnceLock::new();

/// Set the budget for the rest of the process. The first call wins;
/// later calls are ignored, since a budget that changed mid-run would
/// apply to some plugin calls and not others.
pub fn set_max_time_secs(secs: Option<u64>) {
    let _ = MAX_TIME_SECS.set(secs);
}

/// The configured budget in seconds, or `None` for the sandbox default
/// (30 seconds).
#[must_use]
pub fn max_time_secs() -> Option<u64> {
    MAX_TIME_SECS.get().copied().flatten()
}

static MAX_MEMORY_MB: OnceLock<Option<u64>> = OnceLock::new();

/// Set the memory cap, in MiB, for the rest of the process. The first
/// call wins, as for [`set_max_time_secs`].
pub fn set_max_memory_mb(mb: Option<u64>) {
    let _ = MAX_MEMORY_MB.set(mb);
}

/// The configured memory cap in MiB, or `None` for the sandbox default
/// (256 MiB).
#[must_use]
pub fn max_memory_mb() -> Option<u64> {
    MAX_MEMORY_MB.get().copied().flatten()
}

/// [`max_memory_mb`] in bytes.
#[must_use]
pub fn max_memory_bytes() -> Option<usize> {
    max_memory_mb().map(|mb| usize::try_from(mb.saturating_mul(1 << 20)).unwrap_or(usize::MAX))
}
