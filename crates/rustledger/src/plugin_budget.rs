//! The host's time budget for WASM and Python plugins and WASM importers.
//!
//! `rledger` sets it once at startup from the `[plugins] max_time_secs`
//! config key, overridden by `--plugin-max-time-secs`. Every command that
//! runs a WASM or Python plugin or importer reads it from here, so the setting
//! applies to all of them rather than to whichever commands thread an
//! argument through.
//!
//! It is deliberately a host setting and not a ledger one: see
//! `rustledger_plugin::ResolvedPlugin::run_with_max_time_secs`.

use std::sync::OnceLock;

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
