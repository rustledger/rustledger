//! Shared parse-cache load path for CLI commands.
//!
//! `parse()` (the CST parser) is the dominant cost of loading a large
//! ledger, and it is identical run-to-run for an unchanged file. The
//! loader already persists a parsed [`LoadResult`] to an on-disk cache
//! ([`load_cache_entry`] / [`save_cache_entry`]); `check` has used it
//! for a while. This helper factors that "load from cache, else parse
//! and save" step out so other commands (notably `report`, which had
//! no cache and re-parsed on every invocation) can reuse it.
//!
//! The returned [`LoadResult`] is the *parsed* stream (pre-booking);
//! callers feed it to [`rustledger_loader::process`] to book/validate,
//! exactly as the uncached path does. The cache is keyed by the main
//! file and shared across commands, so a `check` followed by a
//! `report` on the same file is a cache hit.

use anyhow::{Context, Result};
use std::path::Path;

use rustledger_loader::{
    CacheEntry, CachedOptions, CachedPlugin, LoadResult, Loader, cache_disabled_by_env,
    load_cache_entry, reintern_directives, save_cache_entry,
};

/// Load a file's parsed [`LoadResult`], using the on-disk parse cache
/// when one is present and valid. Returns `(result, from_cache)`.
///
/// `no_cache` (a CLI `--no-cache`-style flag) or the
/// `BEANCOUNT_DISABLE_LOAD_CACHE` env var disables both reading and
/// writing the cache. `verbose` gates the same progress lines `check`
/// emits.
///
/// # Errors
///
/// Propagates loader errors from a fresh parse (cache misses fall
/// through to `Loader::load`). A cache *save* failure is non-fatal and
/// only surfaced as a `verbose` warning.
pub fn load_result_cached(
    file: &Path,
    no_cache: bool,
    verbose: bool,
) -> Result<(LoadResult, bool)> {
    let cache_disabled = no_cache || cache_disabled_by_env();

    let cache_entry = if cache_disabled {
        None
    } else {
        load_cache_entry(file)
    };

    if let Some(mut entry) = cache_entry {
        if verbose {
            eprintln!("Loaded {} directives from cache", entry.directives.len());
        }

        // Re-intern strings to deduplicate memory before reconstruction.
        let dedup_count = reintern_directives(&mut entry.directives);
        if verbose {
            eprintln!("Re-interned strings ({dedup_count} deduplicated)");
        }

        // Reconstruct an equivalent `LoadResult` (source map, plugins,
        // and a rebuilt display context) - see `CacheEntry::into_load_result`.
        return Ok((entry.into_load_result(), true));
    }

    // Cache miss (or disabled): parse fresh.
    if verbose {
        eprintln!("Loading {}...", file.display());
    }
    let mut loader = Loader::new();
    let result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    // Save to cache unless disabled, or the load had errors / option
    // warnings (E7001-E7006 are not stored, so caching would silently
    // drop them on a later hit). Mirrors `check`.
    if !cache_disabled && result.errors.is_empty() && result.options.warnings.is_empty() {
        let files: Vec<String> = result
            .source_map
            .files()
            .iter()
            .map(|f| f.path.to_string_lossy().into_owned())
            .collect();
        let files = if files.is_empty() {
            vec![file.to_string_lossy().into_owned()]
        } else {
            files
        };

        let entry = CacheEntry {
            directives: result.directives.clone(),
            options: CachedOptions::from(&result.options),
            plugins: result
                .plugins
                .iter()
                .map(|p| CachedPlugin {
                    name: p.name.clone(),
                    config: p.config.clone(),
                    force_python: p.force_python,
                })
                .collect(),
            files,
        };

        if let Err(e) = save_cache_entry(file, &entry) {
            if verbose {
                eprintln!("Warning: failed to save cache: {e}");
            }
        } else if verbose {
            eprintln!("Saved {} directives to cache", result.directives.len());
        }
    }

    Ok((result, false))
}
