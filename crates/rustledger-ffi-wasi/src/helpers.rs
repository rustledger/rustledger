//! Helper functions and utilities.

use std::collections::{HashMap, HashSet};

use rustledger_booking::BookingEngine;
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
    let parse_result = parse_beancount(source);
    let lookup = LineLookup::new(source);

    let mut errors: Vec<Error> = parse_result
        .errors
        .iter()
        .map(|e| Error::new(e.to_string()).with_line(lookup.byte_to_line(e.span().0)))
        .collect();

    // Extract options
    let mut options = LedgerOptions::default();
    for (key, value, _span) in &parse_result.options {
        match key.as_str() {
            "title" => options.title = Some(value.clone()),
            "operating_currency" => options.operating_currency.push(value.clone()),
            "name_assets" => options.name_assets.clone_from(value),
            "name_liabilities" => options.name_liabilities.clone_from(value),
            "name_equity" => options.name_equity.clone_from(value),
            "name_income" => options.name_income.clone_from(value),
            "name_expenses" => options.name_expenses.clone_from(value),
            "documents" => options.documents.push(value.clone()),
            "booking_method" => options.booking_method.clone_from(value),
            "render_commas" => {
                options.render_commas = value.eq_ignore_ascii_case("true") || value == "1";
            }
            "inferred_tolerance_default" => {
                // Parse "CURRENCY:TOLERANCE" or "*:TOLERANCE"
                if let Some((curr, tol)) = value.split_once(':') {
                    options
                        .inferred_tolerance_default
                        .insert(curr.trim().to_string(), tol.trim().to_string());
                }
            }
            "inferred_tolerance_multiplier" | "tolerance_multiplier" => {
                options.inferred_tolerance_multiplier.clone_from(value);
            }
            "infer_tolerance_from_cost" => {
                options.infer_tolerance_from_cost =
                    value.eq_ignore_ascii_case("true") || value == "1";
            }
            "account_rounding" => options.account_rounding = Some(value.clone()),
            "account_previous_balances" => options.account_previous_balances.clone_from(value),
            "account_previous_earnings" => options.account_previous_earnings.clone_from(value),
            "account_previous_conversions" => {
                options.account_previous_conversions.clone_from(value);
            }
            "account_current_earnings" => options.account_current_earnings.clone_from(value),
            "account_current_conversions" => {
                options.account_current_conversions = Some(value.clone());
            }
            "account_unrealized_gains" => options.account_unrealized_gains = Some(value.clone()),
            "conversion_currency" => options.conversion_currency = Some(value.clone()),
            _ => {}
        }
    }

    // Collect directive line numbers, commodities, and precision
    let mut directive_lines: Vec<u32> = Vec::new();
    let mut commodities: HashSet<String> = HashSet::new();
    let mut precision_tracker = PrecisionTracker::new();

    let mut directives: Vec<Directive> = Vec::new();
    for spanned in &parse_result.directives {
        let line = lookup.byte_to_line(spanned.span.start);
        directive_lines.push(line);

        // Collect commodities and track precision
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

    // Run booking and interpolation on transactions (sequential)
    // This fills in empty cost specs via lot matching, normalizes total prices,
    // and interpolates missing amounts. Must be sequential because lot matching
    // depends on prior inventory state.
    if errors.is_empty() {
        let booking_method = options
            .booking_method
            .parse()
            .unwrap_or(rustledger_core::BookingMethod::Strict);
        let mut booking_engine = BookingEngine::with_method(booking_method);
        booking_engine.register_account_methods(directives.iter());

        for (i, directive) in directives.iter_mut().enumerate() {
            if let Directive::Transaction(txn) = directive {
                match booking_engine.book_and_interpolate(txn) {
                    Ok(result) => {
                        // Apply the booked transaction to update inventory for subsequent lot matching
                        booking_engine.apply(&result.transaction);
                        *txn = result.transaction;
                        // Normalize total prices (@@→@) for downstream consumers
                        rustledger_booking::normalize_prices(txn);
                    }
                    Err(e) => {
                        errors.push(
                            Error::new(e.to_string())
                                .with_line(directive_lines[i])
                                .validate_phase(),
                        );
                    }
                }
            }
        }
    }

    let mut commodity_list: Vec<_> = commodities.into_iter().collect();
    commodity_list.sort();
    options.commodities = commodity_list;
    options.display_precision = precision_tracker.most_common_precision();

    // Extract plugins
    let plugins: Vec<Plugin> = parse_result
        .plugins
        .iter()
        .map(|(name, config, _span)| Plugin {
            name: name.clone(),
            config: config.clone(),
        })
        .collect();

    // Extract includes
    let includes: Vec<Include> = parse_result
        .includes
        .iter()
        .map(|(path, span)| Include {
            path: path.clone(),
            lineno: lookup.byte_to_line(span.start),
        })
        .collect();

    // Clone spanned directives for validation
    let spanned_directives: Vec<Spanned<Directive>> = parse_result.directives.clone();

    LoadResult {
        directives,
        spanned_directives,
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
    let mut loader = rustledger_loader::Loader::new().with_path_security(path_security);
    let load_result = loader
        .load(path)
        .map_err(|e| format!("Failed to load file: {e}"))?;

    let mut errors: Vec<Error> = load_result
        .errors
        .iter()
        .map(|e| Error::new(e.to_string()))
        .collect();

    // Directives + their line numbers / originating files (multi-file).
    let mut directives: Vec<Directive> = Vec::new();
    let mut directive_lines: Vec<u32> = Vec::new();
    let mut directive_files: Vec<String> = Vec::new();
    for spanned in &load_result.directives {
        directives.push(spanned.value.clone());
        let file_id = spanned.file_id as usize;
        if let Some(sf) = load_result.source_map.get(file_id) {
            let (line, _col) = sf.line_col(spanned.span.start);
            directive_lines.push(line as u32);
            directive_files.push(sf.path.display().to_string());
        } else {
            directive_lines.push(0);
            directive_files.push("<unknown>".to_string());
        }
    }

    // Booking + interpolation (loader does not book).
    let booking_method = load_result
        .options
        .booking_method
        .parse()
        .unwrap_or(rustledger_core::BookingMethod::Strict);
    let mut booking_engine = BookingEngine::with_method(booking_method);
    booking_engine.register_account_methods(directives.iter());
    for (i, directive) in directives.iter_mut().enumerate() {
        if let Directive::Transaction(txn) = directive {
            match booking_engine.book_and_interpolate(txn) {
                Ok(result) => {
                    booking_engine.apply(&result.transaction);
                    *txn = result.transaction;
                    rustledger_booking::normalize_prices(txn);
                }
                Err(e) => {
                    errors.push(Error::new(e.to_string()).with_line(directive_lines[i]));
                }
            }
        }
    }

    let options = build_ledger_options(&load_result.options);
    let plugins: Vec<Plugin> = load_result
        .plugins
        .iter()
        .map(|p| Plugin {
            name: p.name.clone(),
            config: p.config.clone(),
        })
        .collect();
    let loaded_files: Vec<String> = load_result
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

/// Run the named regular (post-booking) plugins over loaded directives, shared
/// by the JSON-RPC `ledger.loadFile` handler and the WIT component (#1384).
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

/// The five account-type roots, in declaration order.
///
/// Single source of truth for `util.types`' `account_types` and
/// `util.getAccountType`, shared by both the JSON-RPC and Component-Model (WIT)
/// surfaces so they cannot drift.
pub const ACCOUNT_TYPES: [&str; 5] = ["Assets", "Liabilities", "Equity", "Income", "Expenses"];

/// The lowercased account-type root for `account` — the segment before the
/// first `:` — or `"unknown"` if it is not one of [`ACCOUNT_TYPES`].
#[must_use]
pub fn account_type(account: &str) -> &'static str {
    match account.split(':').next() {
        Some("Assets") => "assets",
        Some("Liabilities") => "liabilities",
        Some("Equity") => "equity",
        Some("Income") => "income",
        Some("Expenses") => "expenses",
        _ => "unknown",
    }
}
