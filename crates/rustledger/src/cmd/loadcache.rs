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
    load_cache_entry, save_cache_entry,
};

/// Load a file's parsed [`LoadResult`], using the on-disk parse cache
/// when one is present and valid. Returns `(result, from_cache)`.
///
/// `no_cache` (a CLI `--no-cache`-style flag) or the
/// `BEANCOUNT_DISABLE_LOAD_CACHE` env var disables both reading and
/// writing the cache. `verbose` gates the same progress lines `check`
/// emits, written to `err` (the process's stderr for `rledger`, a buffer
/// for `ag-rledger`'s envelope).
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
    err: &mut dyn std::io::Write,
) -> Result<(LoadResult, bool)> {
    let cache_disabled = no_cache || cache_disabled_by_env();

    let cache_entry = if cache_disabled {
        None
    } else {
        load_cache_entry(file)
    };

    if let Some(entry) = cache_entry {
        if verbose {
            let _ = writeln!(
                err,
                "Loaded {} directives from cache",
                entry.directives.len()
            );
        }

        // No `reintern_directives` here. That pass exists because each parsed
        // FILE gets its own `StringInterner`, so the same account name in two
        // included files lands in two `Arc`s and `InternedStr`'s pointer-
        // equality fast path misses. A cache hit has no such split:
        // `load_cache_entry` deserializes under an `InternScope`, so equal
        // strings already share one `Arc` — the exact postcondition the walk
        // guarantees. Running it anyway re-hashed every string in every
        // directive to discover they were already shared, which cost 13.5M
        // instructions, 7.2% of a warm `check` on a 10,000-transaction ledger.
        //
        // `cache_hit_directives_share_one_arc_per_distinct_string` pins the
        // property this relies on.

        // Reconstruct an equivalent `LoadResult` (source map, plugins,
        // and a rebuilt display context) - see `CacheEntry::into_load_result`.
        return Ok((entry.into_load_result(), true));
    }

    // Cache miss (or disabled): parse fresh.
    if verbose {
        let _ = writeln!(err, "Loading {}...", file.display());
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
            // The opened spelling: a hit rebuilds each file's identity from
            // it, while its own includes and documents resolve against it
            // (#2635); the normalized path alone would lose a symlink.
            .map(|f| f.opened_path.to_string_lossy().into_owned())
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
                let _ = writeln!(err, "Warning: failed to save cache: {e}");
            }
        } else if verbose {
            let _ = writeln!(err, "Saved {} directives to cache", result.directives.len());
        }
    }

    Ok((result, false))
}

/// Refuse to report numbers derived from a file that failed to PARSE.
///
/// # Deliberate deviation from Python beancount
///
/// bean-query does NOT do this. Given a file with a lexer error it prints the
/// rows it could recover and exits 0, and beancount's loader likewise returns
/// the transactions it managed to parse. rledger matched that faithfully until
/// #1908.
///
/// We deviate because the output is not merely incomplete, it is *plausible*:
/// a truncated ledger yields numbers that look like an answer, with a success
/// status, on stdout that another program is probably consuming. For a tool
/// whose entire job is producing figures people rely on, confidently wrong is
/// worse than loudly broken. `rledger check` already refuses the same file, so
/// tolerating it here also made the CLI contradict itself: one command calls a
/// file unusable while another reports on it and claims success.
///
/// Scoped deliberately to PARSE errors. Validation errors — an account never
/// opened, a failed balance assertion — leave the entry stream complete and
/// the arithmetic sound, so those still report exactly as beancount does. That
/// is the common messy-ledger case and breaking it would be a real
/// compatibility loss for no safety gain.
///
/// It also refuses, as bean-query does (#2861), when a file that exists could
/// not be read: a decryption failure or an I/O error other than not-found
/// (an include naming a directory). bean-query raises an uncaught `OSError`
/// there and prints no rows; answering would silently leave the file out (a
/// locked gpg-agent would make every balance zero). Every other LOAD error
/// (an include of a missing file, an include cycle, a duplicate include, an
/// empty glob) is reported and the query answers, as bean-query answers.
///
/// This and [`bail_on_booking_errors`] are the CLI's application of the rule
/// every file-based query surface shares (#2861):
/// [`rustledger_loader::LoadError::blocks_queries`] and
/// [`rustledger_loader::LedgerError::blocks_queries`]. WASM and the FFI call
/// the same predicates; the `query_answer_rule` drift-guard tests pin them
/// together.
///
/// Deliberately NOT registered under `KNOWN_RUST_DIVERGENCES`: the BQL compat
/// suite's `load_valid_files` already requires `python_ok AND rust_ok`, so a
/// file neither tool can parse never reaches that comparison. Adding an entry
/// would imply a divergence the metric can never observe.
///
/// # Errors
///
/// Returns an error naming the file when the load reported a load error that
/// [`rustledger_loader::LoadError::blocks_queries`]: a parse error, or a file
/// that could not be read or decrypted.
pub fn bail_on_load_errors(raw: &rustledger_loader::LoadResult, file: &Path) -> Result<()> {
    // Sum the INNER errors, not the number of `ParseErrors` groups. There is
    // one group per file, so counting groups would report "1 parse error" for
    // a file with twenty, and for a tree of includes would count files rather
    // than problems.
    let blocking: Vec<&rustledger_loader::LoadError> =
        raw.errors.iter().filter(|e| e.blocks_queries()).collect();
    let parse_failures: usize = blocking
        .iter()
        .filter_map(|e| match e {
            rustledger_loader::LoadError::ParseErrors { errors, .. } => Some(errors.len()),
            _ => None,
        })
        .sum();
    let unread: Vec<String> = blocking
        .iter()
        .filter(|e| !matches!(e, rustledger_loader::LoadError::ParseErrors { .. }))
        .map(ToString::to_string)
        .collect();
    if !unread.is_empty() {
        anyhow::bail!(
            "{}: {} file(s) could not be read; refusing to report on a ledger \
             missing them. Run `rledger check {}` to see them.\n  {}",
            file.display(),
            unread.len(),
            file.display(),
            unread.join("\n  "),
        );
    }
    if parse_failures > 0 {
        anyhow::bail!(
            "{}: {parse_failures} parse error(s); refusing to report on a file that \
             did not parse. Run `rledger check {}` to see them.",
            file.display(),
            file.display(),
        );
    }
    Ok(())
}

/// Refuse to derive figures from a ledger whose transactions did not book.
///
/// The same principle as [`bail_on_load_errors`], one phase later. A booking
/// failure — an ambiguous STRICT lot match, a reduction with no matching lot —
/// leaves that transaction in the directive stream in PRE-BOOKING shape:
/// `run_booking` partitions failures out, and `finalize` re-merges them so the
/// user still sees their own input. That re-merge is documented as being "for
/// output", but nothing stopped the same directives flowing into computation.
///
/// The consequences were #1987, and they were worse than a wrong number:
///
/// * `report balances` realizes through `BookingEngine::apply`, whose
///   precondition is booked input. In debug it PANICKED (exit 101); in release
///   it dropped the reduction and reported 20 AAPL for an account holding 15.
/// * `query BALANCES` re-aggregates by lot key and printed a dangling `-5
///   AAPL` row, exiting 0.
///
/// So one surface crashed, the other answered wrongly, and neither said so in
/// its exit code. `apply` now reports the failure rather than asserting in one
/// build profile and ignoring it in the other; this stops the CLI reaching that
/// point at all, and says what to do about it.
///
/// The same gate refuses a ledger whose last `booking_method` value was
/// rejected and which is therefore booked with a method other than the one
/// it asks for (#2911, [`rustledger_loader::Options::query_refusal`]): the
/// option keeps its previous method, so every figure would be booked with a
/// method the ledger did not ask for. A later accepted value, or a rejected
/// one that reads as the method kept (`FIFO` then `fifo`), answers. Stricter
/// than bean-query, which answers with the kept method's figures; see
/// `Options::query_refusal` for why.
///
/// Together with [`bail_on_load_errors`] this is
/// [`rustledger_loader::Ledger::blocks_queries`], the one rule.
///
/// # Errors
///
/// When any directive failed to book, or the last `booking_method` value was
/// rejected and the ledger is booked with a method other than the one it
/// asks for.
pub fn bail_on_booking_errors(ledger: &rustledger_loader::Ledger, file: &Path) -> Result<()> {
    if let Some(refusal) = ledger.query_refusal() {
        anyhow::bail!(
            "{}: {}. Run `rledger check {}` to see it.",
            file.display(),
            refusal.message,
            file.display(),
        );
    }
    // Counting booking failures specifically. `ledger.errors` also carries
    // validation diagnostics, which do NOT leave the stream unbooked and must
    // not gate a report — `rledger check` is where those are read. Not by
    // code: a lot-matching failure carries its E4xxx code (#2631), which a
    // validator can raise too. Of the canonical query rule's blockers
    // (`LedgerError::blocks_queries`, #2861), `bail_on_load_errors` has
    // already refused the load-error half, so what is left is the booking
    // failures; this message names only those.
    debug_assert!(
        ledger
            .errors
            .iter()
            .all(|e| !e.blocks_queries() || e.is_booking_failure()),
        "a blocking load error reached the booking gate; call bail_on_load_errors first"
    );
    let failures: Vec<&str> = ledger
        .errors
        .iter()
        .filter(|e| e.is_booking_failure())
        .map(|e| e.message.as_str())
        .collect();
    if failures.is_empty() {
        debug_assert!(
            !ledger.blocks_queries(),
            "a ledger the canonical query rule blocks passed every gate"
        );
        return Ok(());
    }
    anyhow::bail!(
        "{}: {} transaction(s) could not be booked; refusing to derive figures \
         from a ledger whose lots did not resolve — the affected accounts would \
         be over-stated. Run `rledger check {}` to see them.\n  {}",
        file.display(),
        failures.len(),
        file.display(),
        failures.join("\n  "),
    );
}
