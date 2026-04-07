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
