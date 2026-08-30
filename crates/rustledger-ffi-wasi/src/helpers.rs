//! Helper functions and utilities.

use std::collections::HashSet;

use rustledger_core::Directive;
use rustledger_parser::{Spanned, parse as parse_beancount};

use crate::types::{Error, Include, LedgerOptions, Plugin};

/// Simple line lookup for byte offset to line number conversion.
pub struct LineLookup {
    line_starts: Vec<usize>,
}

impl LineLookup {
    pub fn new(source: &str) -> Self {
        let mut line_starts = vec![0];
        for (i, c) in source.char_indices() {
            if c == '\n' {
                line_starts.push(i + 1);
            }
        }
        Self { line_starts }
    }

    pub fn byte_to_line(&self, byte_offset: usize) -> u32 {
        match self.line_starts.binary_search(&byte_offset) {
            Ok(line) => line as u32 + 1,
            Err(line) => line as u32,
        }
    }
}

/// Internal load result with all parsed data.
pub struct LoadResult {
    pub directives: Vec<Directive>,
    pub spanned_directives: Vec<Spanned<Directive>>,
    pub directive_lines: Vec<u32>,
    pub line_lookup: LineLookup,
    pub errors: Vec<Error>,
    pub options: LedgerOptions,
    pub plugins: Vec<Plugin>,
    pub includes: Vec<Include>,
}

/// Parse and interpolate source, returning directives with line numbers.
pub fn load_source(source: &str) -> LoadResult {
    let lookup = LineLookup::new(source);

    // Parse once to recover the declared `include` paths for the DTO. The
    // string surface has no real filesystem, so we cannot resolve includes; we
    // stub each as an empty file in the VFS below to preserve the historical
    // "list includes, don't resolve, don't error" contract.
    let parse_result = parse_beancount(source);
    let includes: Vec<Include> = parse_result
        .includes
        .iter()
        .map(|(path, span)| Include {
            path: path.clone(),
            lineno: lookup.byte_to_line(span.start),
        })
        .collect();

    // Route the string through the SAME canonical pipeline as `load_file`
    // (`sort → synth → book → regular → finalize`) via an in-memory VFS, rather
    // than re-implementing a partial loader here. This keeps source loads in
    // lock-step with the native loader: file-declared regular plugins
    // (`rename_accounts`, `split_expenses`, `currency_accounts`, …) and the
    // date sort now run, and any future pipeline phase reaches the FFI for free.
    // `validate: false` preserves this surface's load-only error contract
    // (booking errors surface; semantic validation is `ledger.validate`'s job).
    let mut vfs = rustledger_loader::VirtualFileSystem::new();
    vfs.add_file("<source>", source);
    let load_opts = rustledger_loader::LoadOptions {
        validate: false,
        ..Default::default()
    };
    let ledger = match rustledger_loader::Loader::new()
        .with_filesystem(Box::new(vfs))
        .load(std::path::Path::new("<source>"))
        .map_err(|e| e.to_string())
        .and_then(|raw| rustledger_loader::process(raw, &load_opts).map_err(|e| e.to_string()))
    {
        Ok(ledger) => ledger,
        Err(e) => {
            // Fatal load/process failure is unexpected for an in-memory source,
            // but surface it rather than panicking. Tag it `validate` (not the
            // default `parse`): a fatal process/plugin failure must not be
            // wrongly classified as a parse error, which would make the
            // `ledger.validate`/`query` handlers suppress validation entirely.
            return LoadResult {
                directives: Vec::new(),
                spanned_directives: Vec::new(),
                directive_lines: Vec::new(),
                line_lookup: lookup,
                errors: vec![Error::new(e).validate_phase()],
                options: LedgerOptions::default(),
                plugins: Vec::new(),
                includes,
            };
        }
    };

    // Rebuild the wire DTO from the canonical `Ledger`.
    let mut directives: Vec<Directive> = Vec::new();
    let mut directive_lines: Vec<u32> = Vec::new();
    let mut commodities: HashSet<String> = HashSet::new();
    for spanned in &ledger.directives {
        // Synth/plugin-generated directives carry a `file_id` absent from the
        // source map, so they fall through to line 0 — the "generated entry"
        // fingerprint embedders key on to forbid editing synthesized entries.
        let line = if ledger.source_map.get(spanned.file_id as usize).is_some() {
            lookup.byte_to_line(spanned.span.start)
        } else {
            0
        };
        directive_lines.push(line);

        match &spanned.value {
            Directive::Open(o) => {
                for c in &o.currencies {
                    commodities.insert(c.to_string());
                }
            }
            Directive::Commodity(c) => {
                commodities.insert(c.currency.to_string());
            }
            Directive::Transaction(t) => {
                for p in &t.postings {
                    if let Some(units) = &p.units
                        && let Some(amt) = units.as_amount()
                    {
                        commodities.insert(amt.currency.to_string());
                    }
                    if let Some(price) = &p.price
                        && let Some(amt) = price.amount()
                    {
                        commodities.insert(amt.currency.to_string());
                    }
                }
            }
            Directive::Balance(b) => {
                commodities.insert(b.amount.currency.to_string());
            }
            Directive::Price(p) => {
                commodities.insert(p.currency.to_string());
                commodities.insert(p.amount.currency.to_string());
            }
            _ => {}
        }

        directives.push(spanned.value.clone());
    }

    // The string surface has no filesystem, so declared `include` paths cannot
    // be resolved. Drop the resulting resolution failures (file-not-found /
    // glob no-match) for declared includes, preserving the "list includes,
    // don't resolve, don't error" contract uniformly for literal AND glob
    // paths (a literal VFS stub can't match a glob pattern). The includes stay
    // listed in the DTO; only their resolution errors are suppressed. The
    // filter is targeted — a parse-phase error that both names a declared
    // include path and reports a resolution failure — so it never masks a real
    // syntax error in the source itself. Path separators are normalized to `/`
    // on both sides: the loader renders paths via `Path::display()`, which uses
    // `\` on Windows, while declared include paths use `/`.
    let normalized_includes: Vec<String> =
        includes.iter().map(|i| i.path.replace('\\', "/")).collect();
    let errors: Vec<Error> = ledger
        .errors
        .iter()
        .filter(|e| {
            if e.phase != "parse"
                || !(e.message.contains("not found") || e.message.contains("does not match"))
            {
                return true;
            }
            let msg = e.message.replace('\\', "/");
            !normalized_includes.iter().any(|p| msg.contains(p))
        })
        .map(ledger_error_to_ffi)
        .collect();

    let mut options = build_ledger_options(&ledger.options, &ledger.display_context);
    let mut commodity_list: Vec<_> = commodities.into_iter().collect();
    commodity_list.sort();
    options.commodities = commodity_list;

    let plugins: Vec<Plugin> = ledger
        .plugins
        .iter()
        .map(|p| Plugin {
            name: p.name.clone(),
            config: p.config.clone(),
        })
        .collect();

    LoadResult {
        directives,
        spanned_directives: ledger.directives,
        directive_lines,
        line_lookup: lookup,
        errors,
        options,
        plugins,
        includes,
    }
}

/// Convert loader `Options` into the wire DTO `LedgerOptions`. Moved here from
/// the JSON-RPC router so both the router and the WIT component crate (#1384)
/// can build options from a file load.
///
/// `display_precision` is NOT copied from the raw options: it is the
/// ledger's RESOLVED per-currency precision, exported from the loader's
/// canonical [`rustledger_core::DisplayContext`] (inference from the
/// ledger's own amounts, overridden by `option "display_precision"`,
/// overridden by commodity `precision:` metadata). Rendering embedders
/// consume the field directly (rustfava's loader treats it as THE
/// precision map and only falls back to a local Python inference when
/// an engine predates it), so it must carry inferred currencies too —
/// a declarations-only export starves undeclared currencies (found by
/// the downstream rustfava CI job on #1808). Pre-#1766 the two load
/// paths disagreed — `load_source` overwrote the field with a local
/// `PrecisionTracker` inference re-derivation (dropping the user's
/// explicit option entirely) while `load_file` shipped the raw option
/// map (no inference, no commodity metadata).
#[must_use]
pub fn build_ledger_options(
    options: &rustledger_loader::Options,
    display: &rustledger_core::DisplayContext,
) -> LedgerOptions {
    LedgerOptions {
        title: options.title.clone(),
        operating_currency: options.operating_currency.clone(),
        name_assets: options.name_assets.clone(),
        name_liabilities: options.name_liabilities.clone(),
        name_equity: options.name_equity.clone(),
        name_income: options.name_income.clone(),
        name_expenses: options.name_expenses.clone(),
        documents: options.documents.clone(),
        commodities: Vec::new(),
        booking_method: options.booking_method.clone(),
        display_precision: display.resolved_precisions().into_iter().collect(),
        render_commas: options.render_commas,
        inferred_tolerance_default: options
            .inferred_tolerance_default
            .iter()
            .map(|(k, v)| (k.clone(), v.to_string()))
            .collect(),
        inferred_tolerance_multiplier: options.inferred_tolerance_multiplier.to_string(),
        infer_tolerance_from_cost: options.infer_tolerance_from_cost,
        account_rounding: options.account_rounding.clone(),
        account_previous_balances: options.account_previous_balances.clone(),
        account_previous_earnings: options.account_previous_earnings.clone(),
        account_previous_conversions: options.account_previous_conversions.clone(),
        account_current_earnings: options.account_current_earnings.clone(),
        account_current_conversions: options.account_current_conversions.clone(),
        account_unrealized_gains: options.account_unrealized_gains.clone(),
        conversion_currency: options.conversion_currency.clone(),
    }
}

/// Result of loading a file through the full loader (include graph resolved).
///
/// Unlike [`LoadResult`] (single-source), directives may come from several
/// files, so each carries its own line number and originating file. The
/// optional external-plugin pass is *not* run here — that is a JSON-RPC
/// handler concern gated on a request field, and the WIT surface does not
/// expose it.
pub struct FileLoad {
    pub directives: Vec<Directive>,
    pub directive_lines: Vec<u32>,
    pub directive_files: Vec<String>,
    pub errors: Vec<Error>,
    pub options: LedgerOptions,
    pub plugins: Vec<Plugin>,
    pub loaded_files: Vec<String>,
}

/// Expand `pad` directives into synthesized `Padding` transactions for
/// balance-computing consumers, preserving each directive's parallel tag
/// (line, or line+file).
///
/// Mirrors `Ledger::balance_view`, which merges via
/// [`rustledger_booking::merge_with_padding_owned`]. This cannot call that
/// directly: it carries a parallel tag per directive (line, or line+file), and
/// a synth has no source location so it takes `synth_tag`. It therefore sorts
/// the tagged pairs itself and places each synth at
/// [`rustledger_booking::pad_insertion_index`] — the shared rule, not a second
/// copy of it. An earlier copy here prepended the synths instead, and silently
/// kept doing so after the shared rule changed.
///
/// Source-faithful callers skip this; only the `load`/`load-file` consumers
/// that opt in (#1628) expand. The input must not already contain synth pad
/// transactions (it is the raw load stream).
#[must_use]
pub fn expand_pads<T: Clone>(
    directives: Vec<Directive>,
    tags: Vec<T>,
    synth_tag: &T,
) -> (Vec<Directive>, Vec<T>) {
    let pads = rustledger_booking::process_pads(&directives).padding_transactions;
    let mut pairs: Vec<(Directive, T)> = Vec::with_capacity(directives.len() + pads.len());
    pairs.extend(directives.into_iter().zip(tags));
    pairs.sort_by_key(|(d, _)| d.date());

    for txn in pads {
        let insert_at =
            rustledger_booking::pad_insertion_index(pairs.iter().map(|(d, _)| d), txn.date);
        pairs.insert(insert_at, (Directive::Transaction(txn), synth_tag.clone()));
    }

    pairs.into_iter().unzip()
}

/// Load a ledger from a file path, resolving `include` directives and booking
/// transactions. Shared by the JSON-RPC `ledger.loadFile` handler and the WIT
/// component (#1384).
///
/// # Errors
///
/// Returns the loader error string if the entry file cannot be read/parsed.
pub fn load_file(path: &std::path::Path, path_security: bool) -> Result<FileLoad, String> {
    load_file_with_fs(path, path_security, None)
}

/// Like [`load_file`], but with an optional caller-provided
/// [`FileSystem`](rustledger_loader::FileSystem).
///
/// The WASI component passes a filesystem whose `decrypt` delegates to a host
/// capability, so GPG-encrypted ledgers load in the sandbox (the guest can
/// neither spawn `gpg` nor reach the keyring) — #1667. `None` uses the default
/// on-disk filesystem (gpg via subprocess), matching the native path.
///
/// # Errors
///
/// Returns a message if loading fails.
pub fn load_file_with_fs(
    path: &std::path::Path,
    path_security: bool,
    fs: Option<Box<dyn rustledger_loader::FileSystem>>,
) -> Result<FileLoad, String> {
    // Route through the single canonical pipeline (`process::load`:
    // sort → synth → book → regular → finalize) rather than re-implementing a
    // partial loader here. This keeps the FFI surface in lock-step with the
    // native loader — crucially it runs the pre-booking SYNTH pass
    // (`auto_accounts`, `document_discovery`) that the previous hand-rolled
    // parse-and-book path silently skipped (see `tests/load_synth_plugins.rs`).
    //
    // `validate: false` preserves this surface's historical load-only error
    // contract (booking errors surface; semantic-validation errors do not, and
    // remain the concern of the `ledger.validate` endpoint); `run_plugins`
    // (default `true`) is what enables the synth pass.
    let options = rustledger_loader::LoadOptions {
        path_security,
        validate: false,
        ..Default::default()
    };
    let ledger = match fs {
        Some(fs) => rustledger_loader::load_with_fs(path, &options, fs),
        None => rustledger_loader::load(path, &options),
    }
    .map_err(|e| format!("Failed to load file: {e}"))?;

    // Directives + their line numbers / originating files (multi-file).
    // Synth-generated directives carry a `file_id` absent from the source map,
    // so they fall through to line 0 / `<unknown>` — the "generated entry"
    // fingerprint embedders key on to forbid editing synthesized directives.
    let mut directives: Vec<Directive> = Vec::new();
    let mut directive_lines: Vec<u32> = Vec::new();
    let mut directive_files: Vec<String> = Vec::new();
    for spanned in &ledger.directives {
        directives.push(spanned.value.clone());
        let file_id = spanned.file_id as usize;
        if let Some(sf) = ledger.source_map.get(file_id) {
            let (line, _col) = sf.line_col(spanned.span.start);
            directive_lines.push(line as u32);
            directive_files.push(sf.path.display().to_string());
        } else {
            directive_lines.push(0);
            directive_files.push("<unknown>".to_string());
        }
    }

    let errors: Vec<Error> = ledger.errors.iter().map(ledger_error_to_ffi).collect();
    let options = build_ledger_options(&ledger.options, &ledger.display_context);
    let plugins: Vec<Plugin> = ledger
        .plugins
        .iter()
        .map(|p| Plugin {
            name: p.name.clone(),
            config: p.config.clone(),
        })
        .collect();
    let loaded_files: Vec<String> = ledger
        .source_map
        .files()
        .iter()
        .map(|sf| sf.path.display().to_string())
        .collect();

    Ok(FileLoad {
        directives,
        directive_lines,
        directive_files,
        errors,
        options,
        plugins,
        loaded_files,
    })
}

/// Convert a loader [`rustledger_loader::LedgerError`] (produced by the
/// canonical `process::load` pipeline) into the FFI wire [`Error`], preserving
/// the message and source line. The wire `Error` distinguishes only two phases:
/// `"parse"`-phase errors keep the default `"parse"`; every other phase
/// (`"validate"`, `"plugin"`) maps to `"validate"`. The `ledger.validate`/
/// `query` handlers gate semantic validation on parse-phase errors only, so
/// non-parse diagnostics must not be reported as `"parse"`.
fn ledger_error_to_ffi(e: &rustledger_loader::LedgerError) -> Error {
    let mut err = Error::new(e.message.clone());
    if let Some(loc) = &e.location {
        err = err.with_line(loc.line as u32);
    }
    // The wire `Error` distinguishes only "parse" vs "validate". The
    // `ledger.validate`/`query` handlers gate semantic validation on
    // *parse*-phase errors only, so anything that is not a parse error
    // (booking → "validate", plugin/synth → "plugin") must NOT be reported as
    // "parse", or it would wrongly suppress validation.
    if e.phase != "parse" {
        err = err.validate_phase();
    }
    // Preserve severity: the canonical pipeline emits warnings (e.g. the
    // `unrealized` plugin's gain/loss notices) as `LedgerError`s with
    // `Warning` severity. Now that the load surface routes through the full
    // pipeline, these must surface to FFI consumers as warnings, not errors.
    if matches!(e.severity, rustledger_loader::ErrorSeverity::Warning) {
        err.severity = "warning".to_string();
    }
    err
}

/// Run the named regular (post-booking) plugins over loaded directives, shared
/// by the JSON-RPC `ledger.loadFile` handler and the WIT component (#1384).
///
/// These are *additional*, caller-requested plugins, run by name with no
/// config. The ledger's own `plugin "name" "config"` directives have already
/// run (with their config) inside the loader during `load_file`, so this is for
/// plugins a host wants beyond the ones the ledger declares. A plugin that needs
/// configuration must be declared in the ledger — the by-name request surface
/// (the WIT `plugins: list<string>` / JSON-RPC `plugins`) cannot carry config.
///
/// Returns the (possibly rewritten) directives + their line numbers/files;
/// plugin errors and unknown-plugin errors are pushed onto `errors`. No-ops if
/// `plugin_names` is empty or `errors` is already non-empty (don't run plugins
/// over a broken load).
#[must_use]
pub fn apply_plugins(
    plugin_names: &[&str],
    mut directives: Vec<Directive>,
    mut directive_lines: Vec<u32>,
    mut directive_files: Vec<String>,
    errors: &mut Vec<Error>,
    options: &LedgerOptions,
) -> (Vec<Directive>, Vec<u32>, Vec<String>) {
    use rustledger_plugin::{
        NativePluginRegistry, PluginInput, PluginOptions, directive_to_wrapper,
        wrapper_to_directive,
    };

    if plugin_names.is_empty() || !errors.is_empty() {
        return (directives, directive_lines, directive_files);
    }
    let registry = NativePluginRegistry::global();

    for plugin_name in plugin_names {
        // External API runs plugins on already-booked input — synth plugins are
        // a loader-internal concern and would re-emit Opens for already-opened
        // accounts.
        let Some(plugin) = registry.find_regular(plugin_name) else {
            errors.push(Error::new(format!("Unknown plugin: {plugin_name}")));
            continue;
        };
        let wrappers: Vec<_> = directives
            .iter()
            .enumerate()
            .map(|(i, d)| {
                let mut wrapper = directive_to_wrapper(d);
                wrapper.filename = Some(
                    directive_files
                        .get(i)
                        .cloned()
                        .unwrap_or_else(|| "<unknown>".to_string()),
                );
                wrapper.lineno = Some(directive_lines.get(i).copied().unwrap_or(0));
                wrapper
            })
            .collect();

        let input = PluginInput {
            directives: wrappers,
            options: PluginOptions {
                operating_currencies: options.operating_currency.clone(),
                title: options.title.clone(),
                // The held options carry the ledger's root renames, so pass
                // them: `..Default::default()` would hand plugins the English
                // roots and reproduce on this surface exactly the silent
                // misclassification this change fixes (#1964).
                account_types: rustledger_plugin::PluginAccountTypes {
                    assets: options.name_assets.clone(),
                    liabilities: options.name_liabilities.clone(),
                    equity: options.name_equity.clone(),
                    income: options.name_income.clone(),
                    expenses: options.name_expenses.clone(),
                },
            },
            config: None,
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);

        for err in output.errors {
            errors.push(Error::new(err.message));
        }

        // Validate the op set against the shared contract (the same coverage
        // check the loader pipeline runs). On violation, record it — naming the
        // plugin, since this surface runs a caller-supplied list — and keep the
        // directives as-is rather than materializing a malformed op set.
        if let Err(msg) = rustledger_plugin::validate_op_coverage(directives.len(), &output.ops) {
            errors.push(Error::new(format!("plugin '{plugin_name}': {msg}")));
            continue;
        }

        let mut new_directives = Vec::new();
        let mut new_lines = Vec::new();
        let mut new_files = Vec::new();
        for op in &output.ops {
            let wrapper = match op {
                rustledger_plugin::PluginOp::Keep(i) => input_dirs.get(*i).cloned(),
                rustledger_plugin::PluginOp::Modify(_, w)
                | rustledger_plugin::PluginOp::Insert(w) => Some(w.clone()),
                rustledger_plugin::PluginOp::Delete(_) => None,
            };
            if let Some(wrapper) = wrapper
                && let Ok(directive) = wrapper_to_directive(&wrapper)
            {
                new_directives.push(directive);
                new_lines.push(wrapper.lineno.unwrap_or(0));
                new_files.push(wrapper.filename.unwrap_or_else(|| "<plugin>".to_string()));
            }
        }
        directives = new_directives;
        directive_lines = new_lines;
        directive_files = new_files;
    }
    (directives, directive_lines, directive_files)
}

// The account-type taxonomy lives in `rustledger-core` (the type-owning crate)
// so every crate shares one source of truth. Re-exported here for the FFI
// call sites (`util.types`, `util.getAccountType`) that already reference
// `helpers::{ACCOUNT_TYPES, account_type}`.
pub use rustledger_core::{ACCOUNT_TYPES, account_type};

#[cfg(test)]
mod tests {
    use super::*;

    // A ledger whose balance depends on pad expansion (#1628 repro).
    const PAD_LEDGER: &str = "\
option \"operating_currency\" \"USD\"
2020-01-01 open Assets:SomeName USD
2020-01-01 open Equity:Opening-balances
2024-01-20 pad Assets:SomeName Equity:Opening-balances
2024-01-21 balance Assets:SomeName 42 USD
";

    #[test]
    fn expand_pads_materializes_padding_transaction() {
        let load = load_source(PAD_LEDGER);
        // The source-faithful load stream has no synthesized padding transaction.
        assert!(!load.directives.iter().any(|d| matches!(
            d,
            Directive::Transaction(t) if rustledger_booking::is_synthesized_pad(t)
        )));
        let raw_len = load.directives.len();

        let (expanded, lines) = expand_pads(load.directives, load.directive_lines, &0u32);
        // Exactly one synthesized Padding transaction is inserted, tags aligned.
        assert_eq!(expanded.len(), raw_len + 1);
        assert_eq!(expanded.len(), lines.len());
        let synth = expanded
            .iter()
            .filter(|d| matches!(d, Directive::Transaction(t) if rustledger_booking::is_synthesized_pad(t)))
            .count();
        assert_eq!(synth, 1, "expected exactly one synthesized Padding txn");
    }

    /// A ledger where a `pad` shares its date with an unrelated transaction.
    ///
    /// The existing tests cannot see the difference between prepending the
    /// synth to its date group and placing it at the end: both leave the
    /// stream globally date-sorted, and both synthesize exactly one Padding
    /// txn. Only the relative order WITHIN 2024-01-20 tells them apart.
    const SAME_DATE_LEDGER: &str = "\
option \"operating_currency\" \"USD\"
2020-01-01 open Assets:SomeName USD
2020-01-01 open Assets:Other USD
2020-01-01 open Equity:Opening-balances
2024-01-20 pad Assets:SomeName Equity:Opening-balances
2024-01-20 * \"unrelated\"
  Assets:Other  5 USD
  Equity:Opening-balances
2024-01-21 balance Assets:SomeName 42 USD
";

    /// A `pad` and the `balance` it targets on ONE date.
    ///
    /// `SAME_DATE_LEDGER` above shares a date between a pad and an *unrelated*
    /// transaction, with the balance a day later, so it never exercised this.
    /// #2150 was reported against the CLI and explicitly left the FFI path
    /// unverified, noting that `expand_pads` runs its own date-only sort and
    /// could diverge either way.
    const SAME_DATE_PAD_BALANCE_LEDGER: &str = "\
option \"operating_currency\" \"USD\"
2024-01-01 open Assets:A USD
2024-01-01 open Equity:Opening-balances
2024-01-05 * \"some activity\"
  Assets:A  40.00 USD
  Equity:Opening-balances
2024-06-15 pad Assets:A Equity:Opening-balances
2024-06-15 balance Assets:A 100.00 USD
";

    #[test]
    fn expand_pads_synthesizes_nothing_for_a_same_date_pad_balance() {
        // beancount checks a balance at the start of its day, so a same-date
        // pad has nothing to satisfy and is reported unused. The FFI path must
        // agree with the CLI here: before #2150 both padded, leaving the
        // account 60.00 richer than beancount reports.
        let load = load_source(SAME_DATE_PAD_BALANCE_LEDGER);
        let (expanded, _lines) = expand_pads(load.directives, load.directive_lines, &0u32);

        let synths = expanded
            .iter()
            .filter(|d| {
                matches!(d, Directive::Transaction(t) if rustledger_booking::is_synthesized_pad(t))
            })
            .count();
        assert_eq!(
            synths, 0,
            "a same-date pad+balance must synthesize nothing on the FFI path too",
        );
    }

    #[test]
    fn expand_pads_does_not_displace_unrelated_same_date_directives() {
        let load = load_source(SAME_DATE_LEDGER);
        let (expanded, lines) = expand_pads(load.directives, load.directive_lines, &0u32);

        let synth_at = expanded
            .iter()
            .position(|d| matches!(d, Directive::Transaction(t) if rustledger_booking::is_synthesized_pad(t)))
            .expect("fixture must synthesize a Padding txn");
        let unrelated_at = expanded
            .iter()
            .position(|d| matches!(d, Directive::Transaction(t) if t.narration == "unrelated"))
            .expect("fixture must keep the unrelated txn");

        assert!(
            synth_at > unrelated_at,
            "the synthesized pad must sort AFTER the unrelated same-date \
             transaction it does not concern (it went at index {synth_at}, \
             the unrelated txn at {unrelated_at}); prepending it to the date \
             group throws off every running balance from that row on",
        );

        // Tag alignment survives an INSERT, not just a sort. Placement moves
        // directives relative to their tags if the two are ever updated out of
        // step, and a wrong `filename`/`lineno` is silent — the stream still
        // looks right.
        let unrelated_line = lines[unrelated_at];
        assert_eq!(
            unrelated_line, 6,
            "the unrelated txn must keep its own source line through expansion",
        );
        assert_eq!(lines[synth_at], 0, "a synth carries the synthesized tag");
    }
}

#[cfg(test)]
mod plugin_options_tests {
    use super::*;

    /// `apply_plugins` must hand plugins the ledger's OWN root names.
    ///
    /// This surface built `PluginOptions` with `..Default::default()`, which
    /// supplies the English roots — so a plugin classifying through
    /// `account_types` still misclassified here after the native pipeline was
    /// fixed. Caught in review of #1978: the bulk edit that silenced the new
    /// field's compile errors treated this production site like a test one.
    ///
    /// Uses `check_drained`, which emits a balance assertion when a
    /// BALANCE-SHEET account is closed. `apply_plugins` hardcodes
    /// `config: None`, so a config-driven plugin like `split_expenses` is a
    /// passthrough here and cannot discriminate — the first draft of this test
    /// used it and passed with the bug reinstated.
    #[test]
    fn apply_plugins_passes_the_ledgers_account_roots() {
        let options = crate::types::output::LedgerOptions {
            name_assets: "Actifs".to_string(),
            ..crate::types::output::LedgerOptions::default()
        };

        let source = "\
2024-01-01 open Actifs:Bank
2024-01-01 open Expenses:Food

2024-02-01 * \"lunch\"
  Expenses:Food   10.00 USD
  Actifs:Bank    -10.00 USD

2024-03-01 close Actifs:Bank
";
        let parsed = rustledger_parser::parse(source);
        let directives: Vec<rustledger_core::Directive> =
            parsed.directives.iter().map(|d| (**d).clone()).collect();
        let n = directives.len();
        let before = directives.len();
        let mut errors = Vec::new();

        let (out, _, _) = apply_plugins(
            &["check_drained"],
            directives,
            vec![0; n],
            vec!["<test>".to_string(); n],
            &mut errors,
            &options,
        );

        assert!(
            out.len() > before,
            "check_drained must add a balance assertion for the closed \
             `Actifs:` account; unchanged output means the renamed root was \
             not recognized as balance-sheet, so the ledger's names never \
             reached the plugin",
        );
    }
}
