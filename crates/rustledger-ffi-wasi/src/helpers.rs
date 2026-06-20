//! Helper functions and utilities.

use std::collections::{HashMap, HashSet};

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

/// Track precision per currency: maps currency -> (`precision_counts` map)
pub struct PrecisionTracker {
    counts: HashMap<String, HashMap<u32, u32>>,
}

impl PrecisionTracker {
    pub fn new() -> Self {
        Self {
            counts: HashMap::new(),
        }
    }

    pub fn observe(&mut self, currency: &str, number: rustledger_core::Decimal) {
        let precision = number.scale();
        let currency_counts = self.counts.entry(currency.to_string()).or_default();
        *currency_counts.entry(precision).or_insert(0) += 1;
    }

    pub fn most_common_precision(&self) -> HashMap<String, u32> {
        self.counts
            .iter()
            .map(|(currency, counts)| {
                let precision = counts
                    .iter()
                    .max_by_key(|(_, count)| *count)
                    .map_or(2, |(prec, _)| *prec);
                (currency.clone(), precision)
            })
            .collect()
    }
}

impl Default for PrecisionTracker {
    fn default() -> Self {
        Self::new()
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
    for inc in &includes {
        // Empty stub: include resolution becomes a no-op, so a bare source with
        // `include` directives lists them (above) without emitting a parse-phase
        // "file not found" error that would suppress `ledger.validate`.
        vfs.add_file(inc.path.as_str(), "");
    }
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
            // but surface it rather than panicking.
            return LoadResult {
                directives: Vec::new(),
                spanned_directives: Vec::new(),
                directive_lines: Vec::new(),
                line_lookup: lookup,
                errors: vec![Error::new(e)],
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
    let mut precision_tracker = PrecisionTracker::new();
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
                        precision_tracker.observe(amt.currency.as_ref(), amt.number);
                    }
                    if let Some(price) = &p.price
                        && let Some(amt) = price.amount()
                    {
                        commodities.insert(amt.currency.to_string());
                        precision_tracker.observe(amt.currency.as_ref(), amt.number);
                    }
                }
            }
            Directive::Balance(b) => {
                commodities.insert(b.amount.currency.to_string());
                precision_tracker.observe(b.amount.currency.as_ref(), b.amount.number);
            }
            Directive::Price(p) => {
                commodities.insert(p.currency.to_string());
                commodities.insert(p.amount.currency.to_string());
                precision_tracker.observe(p.amount.currency.as_ref(), p.amount.number);
            }
            _ => {}
        }

        directives.push(spanned.value.clone());
    }

    let errors: Vec<Error> = ledger.errors.iter().map(ledger_error_to_ffi).collect();

    let mut options = build_ledger_options(&ledger.options);
    let mut commodity_list: Vec<_> = commodities.into_iter().collect();
    commodity_list.sort();
    options.commodities = commodity_list;
    options.display_precision = precision_tracker.most_common_precision();

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
#[must_use]
pub fn build_ledger_options(options: &rustledger_loader::Options) -> LedgerOptions {
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
        display_precision: options
            .display_precision
            .iter()
            .map(|(k, v)| (k.clone(), *v))
            .collect(),
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

/// Load a ledger from a file path, resolving `include` directives and booking
/// transactions. Shared by the JSON-RPC `ledger.loadFile` handler and the WIT
/// component (#1384).
///
/// # Errors
///
/// Returns the loader error string if the entry file cannot be read/parsed.
pub fn load_file(path: &std::path::Path, path_security: bool) -> Result<FileLoad, String> {
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
    let ledger =
        rustledger_loader::load(path, &options).map_err(|e| format!("Failed to load file: {e}"))?;

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
    let options = build_ledger_options(&ledger.options);
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
