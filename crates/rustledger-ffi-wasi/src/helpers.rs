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
    /// The files `spanned_directives` index into: the source, named
    /// `<string>` as beancount's `load_string` names it, so a query's
    /// `filename` / `lineno` / `location` columns resolve (#2825).
    pub source_map: rustledger_loader::SourceMap,
    pub directive_lines: Vec<u32>,
    pub line_lookup: LineLookup,
    pub errors: Vec<Error>,
    /// Parallel to `errors`: whether the error stops a query over the source
    /// from answering: a parse error or a booking failure
    /// ([`rustledger_loader::LedgerError::blocks_queries`], the rule the
    /// file-based query surfaces share, #2861, #2882), or a load that failed
    /// outright. Every other error, a plugin's among them, is reported beside
    /// the rows.
    pub error_blocks_queries: Vec<bool>,
    /// Why a query over the source refuses though no error blocks it: a
    /// rejected `booking_method`
    /// ([`rustledger_loader::Ledger::query_refusal`]). Not among `errors`;
    /// its E7002 is among [`Self::option_errors`], so a surface listing those
    /// does not list this as well.
    pub query_refusal: Option<Error>,
    /// The option diagnostics (E7001 to E7011,
    /// [`rustledger_loader::option_warnings_to_errors`]), kept apart from
    /// `errors` on purpose (#2929).
    ///
    /// `errors` is what the surfaces gate on: semantic validation is skipped
    /// over a parse-phase error, and [`apply_plugins`] skips the host's
    /// plugins over an error. An invalid option makes neither the directives
    /// nor the parse unsound, so folding these in would stop both, and
    /// `validate` would count them as parse errors. A reporting surface
    /// appends them to its `errors` last, after the plugins and validation
    /// have run. They include a rejected `booking_method`'s E7002, so a
    /// surface listing them does not list [`Self::query_refusal`] too.
    pub option_errors: Vec<Error>,
    /// What a query over the load lists of [`Self::option_errors`]: the same,
    /// with the rejected `booking_method`'s E7002 replaced by
    /// [`Self::query_refusal`]'s reason
    /// ([`rustledger_loader::Ledger::query_option_errors`], #2911, #2929).
    pub query_option_errors: Vec<Error>,
    pub options: LedgerOptions,
    /// The ledger's `tolerance_multiplier` option, for the padding
    /// [`expand_pads`] inserts (a difference within a balance's tolerance is
    /// not padded, #2901).
    pub tolerance_multiplier: rustledger_core::Decimal,
    /// The options a semantic validation of this load runs with: the ones
    /// `rledger check` builds from the ledger's options
    /// ([`rustledger_loader::validation_options_from_options`], so
    /// `tolerance_multiplier` and the rest are read), with the source map's
    /// positions for beancount's entry order (#2901).
    pub validation_options: rustledger_validate::ValidationOptions,
    pub plugins: Vec<Plugin>,
    pub includes: Vec<Include>,
}

impl LoadResult {
    /// Whether a query over this load refuses: one of its errors blocks
    /// queries (see [`Self::error_blocks_queries`]), or
    /// [`Self::query_refusal`] holds a reason.
    #[must_use]
    pub fn blocks_queries(&self) -> bool {
        self.error_blocks_queries.iter().any(|&blocks| blocks) || self.query_refusal.is_some()
    }
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
    // Named `<string>`, as beancount's `load_string` names an in-memory
    // source: the name a query's `filename` column reports (#2825).
    vfs.add_file("<string>", source);
    let load_opts = rustledger_loader::LoadOptions {
        validate: false,
        ..Default::default()
    };
    // The parse errors are taken out before `process`, to be reported one by
    // one with their code and line, as `rledger check` reports them
    // (`take_parse_errors`, `parse_errors_to_ledger_errors`); left in,
    // `process` reports them as one line-less `parse errors in <string>`.
    let mut parse_errors: Vec<rustledger_loader::LedgerError> = Vec::new();
    let ledger = match rustledger_loader::Loader::new()
        .with_filesystem(Box::new(vfs))
        .load(std::path::Path::new("<string>"))
        .map_err(|e| e.to_string())
        .and_then(|mut raw| {
            parse_errors = parse_errors_of(&mut raw);
            rustledger_loader::process(raw, &load_opts).map_err(|e| e.to_string())
        }) {
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
                source_map: rustledger_loader::SourceMap::new(),
                directive_lines: Vec::new(),
                line_lookup: lookup,
                errors: vec![Error::new(e).validate_phase()],
                // Nothing was loaded, so a query has nothing to answer from.
                error_blocks_queries: vec![true],
                query_refusal: None,
                option_errors: Vec::new(),
                query_option_errors: Vec::new(),
                options: LedgerOptions::default(),
                tolerance_multiplier: rustledger_booking::DEFAULT_TOLERANCE_MULTIPLIER,
                validation_options: rustledger_validate::ValidationOptions::default(),
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
    let (errors, error_blocks_queries): (Vec<Error>, Vec<bool>) = parse_errors
        .iter()
        .chain(&ledger.errors)
        .filter(|e| {
            if e.phase != "parse"
                || !(e.message.contains("not found") || e.message.contains("does not match"))
            {
                return true;
            }
            let msg = e.message.replace('\\', "/");
            !normalized_includes.iter().any(|p| msg.contains(p))
        })
        .map(|e| (ledger_error_to_ffi(e), e.blocks_queries()))
        .unzip();
    let query_refusal = query_refusal_error(&ledger);
    let option_errors = option_errors(&ledger);
    let query_option_errors = query_option_errors(&ledger);

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

    let validation_options = rustledger_loader::validation_options_from_options(&ledger.options)
        .with_source_lines(rustledger_loader::source_lines(&ledger.source_map));

    LoadResult {
        directives,
        spanned_directives: ledger.directives,
        source_map: ledger.source_map,
        directive_lines,
        line_lookup: lookup,
        errors,
        error_blocks_queries,
        query_refusal,
        option_errors,
        query_option_errors,
        options,
        tolerance_multiplier: ledger.options.inferred_tolerance_multiplier,
        validation_options,
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
        // The method booking used (`Options::effective_booking_method`, over
        // the loader's default), not a field read: one rule for every surface.
        booking_method: options
            .effective_booking_method(rustledger_loader::LoadOptions::default().booking_method)
            .to_string(),
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
        // LEAF names under the equity root, exactly as beancount's options
        // map holds them (#2408). Hosts join `name_equity` on, as fava does
        // (`equity + ":" + options["account_current_earnings"]`); exporting
        // full names made rustfava's balance sheet show
        // `Equity:Equity:Earnings:Current`. In-process consumers resolve
        // them with `rustledger_loader::resolve_leaf_account`.
        account_previous_balances: options.account_previous_balances.clone(),
        account_previous_earnings: options.account_previous_earnings.clone(),
        account_previous_conversions: options.account_previous_conversions.clone(),
        account_current_earnings: options.account_current_earnings.clone(),
        // Always present, beancount's default when unset: a host falling back
        // to its own default would fall back to a full name and double it.
        account_current_conversions: Some(
            options
                .account_current_conversions
                .clone()
                .unwrap_or_else(|| rustledger_loader::DEFAULT_CURRENT_CONVERSIONS.to_string()),
        ),
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
    /// The files the ledger was loaded from, keyed by the paths in
    /// `directive_files`, so a query's source columns resolve (#2825).
    pub source_map: rustledger_loader::SourceMap,
    /// Parallel to `directives`: the placeholder location (name, line) of a
    /// directive a load-time plugin created, such as `auto_accounts`'s
    /// `<auto_accounts>`, 0, which `directive_files` / `directive_lines`
    /// flatten to `<unknown>`, 0. A query reports it, as the CLI does (#2825).
    pub directive_placeholders: Vec<Option<(String, u32)>>,
    /// The load's errors: the files', booking's and the ledger's plugins'.
    /// Never a validation finding ([`Self::validation_errors`]) or an option
    /// diagnostic ([`Self::option_errors`]): these are what [`apply_plugins`]
    /// gates the host's plugins on.
    pub errors: Vec<Error>,
    /// Parallel to `errors`: whether the error stops a query over the ledger
    /// from answering: a parse error, a file that could not be read or
    /// decrypted, or a booking failure
    /// ([`rustledger_loader::LedgerError::blocks_queries`], #2861).
    pub error_blocks_queries: Vec<bool>,
    /// What the canonical pipeline's validation reported, at each finding's
    /// own file and line, as `rledger check` reports them (#2935). Empty
    /// unless [`load_file_with_fs`] was asked to validate. None of them
    /// blocks a query or stops the host's plugins: a failed `balance` leaves
    /// the booked directives sound.
    pub validation_errors: Vec<Error>,
    /// The option diagnostics (E7001 to E7011); see
    /// [`LoadResult::option_errors`] for why they are kept apart (#2929).
    pub option_errors: Vec<Error>,
    /// See [`LoadResult::query_option_errors`].
    pub query_option_errors: Vec<Error>,
    /// Why a query over the ledger refuses though no error blocks it: a
    /// rejected `booking_method`
    /// ([`rustledger_loader::Ledger::query_refusal`]). Not among `errors`, so
    /// it does not stop the session plugins [`apply_plugins`] runs; its E7002
    /// is among [`Self::option_errors`], so a surface listing those does not
    /// list this as well.
    pub query_refusal: Option<Error>,
    pub options: LedgerOptions,
    /// See [`LoadResult::tolerance_multiplier`].
    pub tolerance_multiplier: rustledger_core::Decimal,
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
/// the tagged pairs itself and places the synths with
/// [`rustledger_booking::merge_padding_into_sorted`], the shared rule, not a
/// second copy of it. An earlier copy here prepended the synths instead, and
/// silently kept doing so after the shared rule changed.
///
/// Source-faithful callers skip this; only the `load`/`load-file` consumers
/// that opt in (#1628) expand. The input must not already contain synth pad
/// transactions (it is the raw load stream).
#[must_use]
pub fn expand_pads<T: Clone>(
    directives: Vec<Directive>,
    tags: Vec<T>,
    synth_tag: &T,
    tolerance_multiplier: rustledger_core::Decimal,
) -> (Vec<Directive>, Vec<T>) {
    let pads =
        rustledger_booking::process_pads(&directives, tolerance_multiplier).padding_transactions;
    let mut pairs: Vec<(Directive, T)> = directives.into_iter().zip(tags).collect();
    pairs.sort_by_key(|(d, _)| d.date());

    let synths = pads
        .into_iter()
        .map(|txn| (Directive::Transaction(txn), synth_tag.clone()))
        .collect();
    let pairs = rustledger_booking::merge_padding_into_sorted(pairs, synths, |(d, _)| d.date());

    pairs.into_iter().unzip()
}

/// Load a ledger from a file path, resolving `include` directives and booking
/// transactions, without validating it. Shared by the JSON-RPC
/// `ledger.loadFile` handler and the WIT component (#1384).
///
/// # Errors
///
/// Returns the loader error string if the entry file cannot be read/parsed.
pub fn load_file(path: &std::path::Path, path_security: bool) -> Result<FileLoad, String> {
    load_file_with_fs(path, path_security, None, false)
}

/// Like [`load_file`], but with an optional caller-provided
/// [`FileSystem`](rustledger_loader::FileSystem), and validating when
/// `validate` is set.
///
/// The WASI component passes a filesystem whose `decrypt` delegates to a host
/// capability, so GPG-encrypted ledgers load in the sandbox (the guest can
/// neither spawn `gpg` nor reach the keyring) — #1667. `None` uses the default
/// on-disk filesystem (gpg via subprocess), matching the native path.
///
/// With `validate`, the canonical pipeline validates as `rledger check` does
/// (Early before booking, Late after the ledger's plugins, with the options
/// `build_validation_options` makes from the ledger's own), and its findings
/// come back in [`FileLoad::validation_errors`] at their own file and line
/// (#2935). The component's `load-file` and `validate-file` used to report
/// no validation errors for a ledger with includes at all.
///
/// # Errors
///
/// Returns a message if loading fails.
pub fn load_file_with_fs(
    path: &std::path::Path,
    path_security: bool,
    fs: Option<Box<dyn rustledger_loader::FileSystem>>,
    validate: bool,
) -> Result<FileLoad, String> {
    // Route through the single canonical pipeline (`process::load`:
    // sort → synth → Early → book → regular → Late → finalize) rather than
    // re-implementing a partial loader here. This keeps the FFI surface in
    // lock-step with the native loader: crucially it runs the pre-booking
    // SYNTH pass (`auto_accounts`, `document_discovery`) that the previous
    // hand-rolled parse-and-book path silently skipped (see
    // `tests/load_synth_plugins.rs`), and, when asked, the validation passes
    // exactly as `rledger check` runs them. `run_plugins` (default `true`) is
    // what enables the synth pass.
    let options = rustledger_loader::LoadOptions {
        path_security,
        validate,
        ..Default::default()
    };
    // `rustledger_loader::load` / `load_with_fs`, with the parse errors taken
    // out before `process` to be reported one by one, each at its own file,
    // line and column with its code, as `rledger check` reports them; left
    // in, `process` reports each file's as one line-less `parse errors in
    // <path>`. `process` then validates what did parse, as `check` does.
    let mut loader = rustledger_loader::Loader::new();
    if let Some(fs) = fs {
        loader = loader.with_filesystem(fs);
    }
    if path_security {
        loader = loader.with_path_security(true);
    }
    let mut raw = loader
        .load(path)
        .map_err(|e| format!("Failed to load file: {e}"))?;
    let parse_errors = parse_errors_of(&mut raw);
    let ledger = rustledger_loader::process(raw, &options)
        .map_err(|e| format!("Failed to load file: {e}"))?;

    // Directives + their line numbers / originating files (multi-file).
    // Synth-generated directives carry a `file_id` absent from the source map,
    // so they fall through to line 0 / `<unknown>` — the "generated entry"
    // fingerprint embedders key on to forbid editing synthesized directives.
    let mut directives: Vec<Directive> = Vec::new();
    let mut directive_lines: Vec<u32> = Vec::new();
    let mut directive_files: Vec<String> = Vec::new();
    let mut directive_placeholders: Vec<Option<(String, u32)>> = Vec::new();
    for spanned in &ledger.directives {
        directives.push(spanned.value.clone());
        directive_placeholders.push(
            ledger
                .source_map
                .placeholder(spanned.file_id)
                .map(|(name, line)| (name.display().to_string(), line)),
        );
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

    // The validator's findings apart from the load's own errors: these are
    // what the host's plugins are gated on, and a finding (a failed
    // `balance`) does not make the booked directives unsound.
    let (findings, load_errors): (Vec<_>, Vec<_>) = parse_errors
        .iter()
        .chain(&ledger.errors)
        .partition(|e| e.is_validation_finding());
    let errors: Vec<Error> = load_errors
        .iter()
        .copied()
        .map(ledger_error_to_ffi)
        .collect();
    let error_blocks_queries: Vec<bool> = load_errors.iter().map(|e| e.blocks_queries()).collect();
    // As `rledger check` reports them: an advisory-only code (E1004, closing
    // an account with a balance, which bean-check does not flag) is left out,
    // by the canonical predicate the CLI and the WASM query apply. A finding
    // is kept when a declared plugin was not run (E8004, E8005): `check`
    // keeps it too, so an account the plugin would have opened is an E1001
    // on both, beside the plugin error that says why.
    let validation_errors: Vec<Error> = findings
        .into_iter()
        .filter(|e| !rustledger_validate::is_advisory_only_code(&e.code))
        .map(ledger_error_to_ffi)
        .collect();
    let query_refusal = query_refusal_error(&ledger);
    let option_errors = option_errors(&ledger);
    let query_option_errors = query_option_errors(&ledger);
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
        source_map: ledger.source_map,
        directive_placeholders,
        errors,
        error_blocks_queries,
        validation_errors,
        option_errors,
        query_option_errors,
        query_refusal,
        options,
        tolerance_multiplier: ledger.options.inferred_tolerance_multiplier,
        plugins,
        loaded_files,
    })
}

/// The ledger's option diagnostics as wire errors: the loader's
/// [`rustledger_loader::option_warnings_to_errors`], the mapping the WASM
/// surface shares, so neither decides a severity, code or phase of its own
/// (#2929).
fn option_errors(ledger: &rustledger_loader::Ledger) -> Vec<Error> {
    rustledger_loader::option_warnings_to_errors(&ledger.options.warnings)
        .iter()
        .map(ledger_error_to_ffi)
        .collect()
}

/// The option diagnostics a query over `ledger` lists, as wire errors:
/// [`rustledger_loader::Ledger::query_option_errors`], so the rejected
/// `booking_method`'s E7002 is the refusal, as [`query_refusal_error`]
/// gives it (#2911, #2929).
fn query_option_errors(ledger: &rustledger_loader::Ledger) -> Vec<Error> {
    ledger
        .query_option_errors()
        .iter()
        .map(|e| {
            // The refusal crosses as `query_refusal_error` gives it.
            if e.blocks_queries() {
                refusal_to_ffi(e)
            } else {
                ledger_error_to_ffi(e)
            }
        })
        .collect()
}

/// The refusal a rejected option makes for queries over `ledger`
/// ([`rustledger_loader::Ledger::query_refusal`]: an invalid
/// `booking_method` whose ledger books another method, #2911), as a wire
/// error, or `None`.
///
/// Kept apart from the load's `errors`: it belongs to query results only.
/// The load's own errors are what `load`/`validate` list and what
/// [`apply_plugins`] gates on, and a ledger the loader booked is neither
/// broken nor a reason to skip a host's plugins.
fn query_refusal_error(ledger: &rustledger_loader::Ledger) -> Option<Error> {
    ledger.query_refusal().map(|refusal| {
        debug_assert!(refusal.blocks_queries());
        refusal_to_ffi(&refusal)
    })
}

/// A query refusal ([`rustledger_loader::Ledger::query_refusal`]) as a wire
/// error, for [`query_refusal_error`] and [`query_option_errors`] alike.
///
/// Not "parse" on the wire, though options are read at parse time: a
/// parse-phase error there stops semantic validation, and the ledger parsed.
fn refusal_to_ffi(refusal: &rustledger_loader::LedgerError) -> Error {
    ledger_error_to_ffi(refusal).validate_phase()
}

/// Take `raw`'s parse errors out ([`rustledger_loader::LoadResult::take_parse_errors`])
/// and give each as `rledger check` reports it
/// ([`rustledger_loader::parse_errors_to_ledger_errors`]): with its code,
/// file, line and column, for an included file too. Left in, `process`
/// reports each file's as one line-less `parse errors in <path>`.
fn parse_errors_of(raw: &mut rustledger_loader::LoadResult) -> Vec<rustledger_loader::LedgerError> {
    raw.take_parse_errors()
        .iter()
        .flat_map(|failure| {
            rustledger_loader::parse_errors_to_ledger_errors(failure, &raw.source_map)
        })
        .collect()
}

/// Convert a loader [`rustledger_loader::LedgerError`] (produced by the
/// canonical `process::load` pipeline) into the FFI wire [`Error`], preserving
/// the message, code and source file and line. The wire `Error` distinguishes
/// only two phases:
/// `"parse"`-phase errors keep the default `"parse"`; every other phase
/// (`"validate"`, `"plugin"`) maps to `"validate"`. The `ledger.validate`/
/// `query` handlers gate semantic validation on parse-phase errors only, so
/// non-parse diagnostics must not be reported as `"parse"`.
fn ledger_error_to_ffi(e: &rustledger_loader::LedgerError) -> Error {
    let mut err = Error::new(e.message.clone());
    if !e.code.is_empty() {
        err.code = Some(e.code.clone());
    }
    if let Some(loc) = &e.location {
        err = err.with_line(loc.line as u32);
        err.column = Some(loc.column as u32);
        err.file = Some(loc.file.display().to_string());
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
/// `plugin_names` is empty or `errors` already holds an error (don't run
/// plugins over a broken load). A warning does not count: it used to, so a
/// ledger plugin's warning silently skipped every plugin the host asked for
/// (#2929). Pass the load's own errors only, never its validation findings
/// or option diagnostics, which leave the directives sound.
///
/// A plugin's errors are mapped as the loader maps a declared plugin's
/// (`rustledger_loader::plugin_error_to_ledger_error`), its file resolved
/// through `source_map`, the load's (pass an empty one where there is none).
#[must_use]
pub fn apply_plugins(
    plugin_names: &[&str],
    mut directives: Vec<Directive>,
    mut directive_lines: Vec<u32>,
    mut directive_files: Vec<String>,
    errors: &mut Vec<Error>,
    options: &LedgerOptions,
    source_map: &rustledger_loader::SourceMap,
) -> (Vec<Directive>, Vec<u32>, Vec<String>) {
    use rustledger_plugin::{
        NativePluginRegistry, PluginInput, PluginOptions, directive_to_wrapper,
        wrapper_to_directive,
    };

    if plugin_names.is_empty() || errors.iter().any(Error::is_error) {
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
                // And the tolerance options, for the same reason (#2653).
                // Sorted: the map's order is not stable. (The input is a
                // loaded ledger, so no posting carries booking's
                // interpolation mark: the loader removed it.)
                inferred_tolerance_default: {
                    let mut defaults: Vec<(String, String)> = options
                        .inferred_tolerance_default
                        .iter()
                        .map(|(currency, number)| (currency.clone(), number.clone()))
                        .collect();
                    defaults.sort();
                    defaults
                },
                tolerance_multiplier: options.inferred_tolerance_multiplier.clone(),
                infer_tolerance_from_cost: options.infer_tolerance_from_cost,
            },
            config: None,
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);

        // As the loader records a declared plugin's errors (code `PLUGIN`,
        // its severity, its location, escaped): the one canonical mapping.
        errors.extend(output.errors.iter().map(|err| {
            ledger_error_to_ffi(&rustledger_loader::plugin_error_to_ledger_error(
                err, source_map,
            ))
        }));

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

        let (expanded, lines) = expand_pads(
            load.directives,
            load.directive_lines,
            &0u32,
            load.tolerance_multiplier,
        );
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

    /// A pad sharing its date with an UNRELATED balance, the pad's own target
    /// balance landing later. The shape #2188 was filed for: the placement
    /// rule used to return the index of the first same-date `Balance`, which
    /// put the synth at the FRONT of the whole date group.
    const UNRELATED_SAME_DATE_BALANCE_LEDGER: &str = "\
option \"operating_currency\" \"USD\"
2020-01-01 open Assets:A USD
2020-01-01 open Assets:B USD
2020-01-01 open Equity:Opening-balances
2024-06-10 pad Assets:A Equity:Opening-balances
2024-06-10 balance Assets:B 0 USD
2024-06-15 balance Assets:A 100 USD
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
        let (expanded, _lines) = expand_pads(
            load.directives,
            load.directive_lines,
            &0u32,
            load.tolerance_multiplier,
        );

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
    fn expand_pads_puts_the_synth_after_an_unrelated_same_date_balance() {
        // The FFI copy of the placement rule (#2188). `expand_pads` shares
        // `merge_padding_into_sorted` with the CLI merge, but reaches it by a
        // different route -- it carries parallel provenance tags and so cannot
        // call either merge -- and two of the three consumers were still
        // prepending the last time this rule changed. Pinned per consumer for
        // that reason.
        //
        // bean-query reports this date group as `balance pad transaction`.
        let load = load_source(UNRELATED_SAME_DATE_BALANCE_LEDGER);
        let (expanded, lines) = expand_pads(
            load.directives,
            load.directive_lines,
            &0u32,
            load.tolerance_multiplier,
        );

        let group: Vec<&str> = expanded
            .iter()
            .filter(|d| d.date() == rustledger_core::naive_date(2024, 6, 10).unwrap())
            .map(|d| match d {
                Directive::Balance(_) => "balance",
                Directive::Pad(_) => "pad",
                Directive::Transaction(_) => "transaction",
                _ => "other",
            })
            .collect();
        assert_eq!(
            group,
            vec!["balance", "pad", "transaction"],
            "the synth belongs at the END of its date group; returning the \
             index of the unrelated same-date balance put it at the front",
        );

        // Tags must still line up after the insert moved.
        let synth_at = expanded
            .iter()
            .position(|d| matches!(d, Directive::Transaction(t) if rustledger_booking::is_synthesized_pad(t)))
            .expect("fixture must synthesize a Padding txn");
        assert_eq!(lines[synth_at], 0, "a synth carries the synthesized tag");
    }

    #[test]
    fn expand_pads_does_not_displace_unrelated_same_date_directives() {
        let load = load_source(SAME_DATE_LEDGER);
        let (expanded, lines) = expand_pads(
            load.directives,
            load.directive_lines,
            &0u32,
            load.tolerance_multiplier,
        );

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
            &rustledger_loader::SourceMap::new(),
        );

        assert!(
            out.len() > before,
            "check_drained must add a balance assertion for the closed \
             `Actifs:` account; unchanged output means the renamed root was \
             not recognized as balance-sheet, so the ledger's names never \
             reached the plugin",
        );
    }

    /// `apply_plugins` must hand plugins the ledger's tolerance options too
    /// (#2653): `sellgains` passes proceeds 4 cents off under a
    /// `tolerance_multiplier` of 5 and fails them under the default 0.5, as
    /// bean-check does.
    #[test]
    fn apply_plugins_passes_the_ledgers_tolerance_options() {
        let source = "\
2024-01-01 open Assets:Cash
2024-01-01 open Assets:Stock
2024-01-01 open Income:Gains

2024-01-05 * \"off by 4 cents\"
  Assets:Stock  -2 AAA {100 USD} @ 150 USD
  Assets:Cash  300.04 USD
  Income:Gains  -100.04 USD
";
        let run = |options: &crate::types::output::LedgerOptions| {
            let parsed = rustledger_parser::parse(source);
            let directives: Vec<rustledger_core::Directive> =
                parsed.directives.iter().map(|d| (**d).clone()).collect();
            let n = directives.len();
            let mut errors = Vec::new();
            let _ = apply_plugins(
                &["sellgains"],
                directives,
                vec![0; n],
                vec!["<test>".to_string(); n],
                &mut errors,
                options,
                &rustledger_loader::SourceMap::new(),
            );
            errors.len()
        };
        assert_eq!(
            run(&crate::types::output::LedgerOptions::default()),
            1,
            "the default tolerance must report the 4 cents"
        );
        let options = crate::types::output::LedgerOptions {
            inferred_tolerance_multiplier: "5".to_string(),
            ..crate::types::output::LedgerOptions::default()
        };
        assert_eq!(
            run(&options),
            0,
            "a tolerance_multiplier of 5 allows the 4 cents; an error means \
             the ledger's option never reached the plugin"
        );
    }

    /// The host's plugins are gated by severity (#2929): a warning already in
    /// `errors` (a ledger plugin's notice) used to skip them all; an error
    /// still does.
    #[test]
    fn test_apply_plugins_runs_over_a_warning_not_over_an_error() {
        let source = "\
2024-01-01 open Assets:Bank
2024-01-01 open Expenses:Food

2024-02-01 * \"lunch\"
  Expenses:Food   10.00 USD
  Assets:Bank    -10.00 USD

2024-03-01 close Assets:Bank
";
        let run = |prior: Error| {
            let parsed = rustledger_parser::parse(source);
            let directives: Vec<rustledger_core::Directive> =
                parsed.directives.iter().map(|d| (**d).clone()).collect();
            let n = directives.len();
            let mut errors = vec![prior];
            let (out, _, _) = apply_plugins(
                &["check_drained"],
                directives,
                vec![0; n],
                vec!["<test>".to_string(); n],
                &mut errors,
                &crate::types::output::LedgerOptions::default(),
                &rustledger_loader::SourceMap::new(),
            );
            out.len() > n
        };
        let mut warning = Error::new("a ledger plugin's notice").validate_phase();
        warning.severity = "warning".to_string();
        assert!(
            run(warning),
            "a warning must not stop the host's plugins: check_drained added nothing"
        );
        assert!(
            !run(Error::new("a parse error")),
            "an error must still stop them"
        );
    }
}
