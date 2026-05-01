//! Symbol discovery from beancount files.
//!
//! Walks a loaded ledger to identify which commodities to fetch prices for.
//! The default (strict) mode is verified against upstream
//! `beanprice/price.py::find_currencies_declared`:
//!
//! - `commodity` directives carrying a `price:` metadata key drive
//!   metadata-based discovery. Format: `"<quote>:<source>/<ticker>"`,
//!   optionally chained with `,` for fallback alternatives, e.g.
//!   `"USD:yahoo/AAPL,USD:google/NASDAQ:AAPL"`.
//! - `quote_currency:` metadata supplies a per-commodity quote currency,
//!   used as the `--currency` default for that one symbol. (This is a
//!   permissive extension over bean-price, which only treats `price:` as
//!   a discovery trigger; `quote_currency:` alone is enough here.)
//! - `price: ""` (empty/whitespace) explicitly opts a commodity *out* of
//!   fetching, even if it would otherwise be picked up. Mirrors
//!   `bean-price`'s "Skipping ignored currency (with empty price)" rule.
//!
//! By default, only "active" commodities are returned: those with a non-zero
//! balance in at least one open balance-sheet account. Set `inactive: true`
//! to skip the activity filter — corresponds to `bean-price --inactive`.
//!
//! ## `undeclared` divergence
//!
//! Setting `undeclared: true` re-enables a ticker-shape heuristic for
//! `commodity` directives that lack metadata (uppercase letters / digits /
//! dashes / dots, ≤ 10 chars). This is **not** a 1:1 match for
//! `bean-price --undeclared`, which instead unions the at-cost, converted,
//! and priced currencies *seen in transactions* with no name filtering.
//! Our heuristic is a strict subset chosen deliberately so that currency
//! codes like `EUR` or `BAM` aren't auto-routed to a stock source and
//! produce wrong prices (issue #962). Closer alignment with bean-price's
//! transaction-walking semantics is tracked in the audit issue.

use crate::config::{CommodityMapping, DetailedMapping, SourceRef};
use rust_decimal::Decimal;
use rustledger_core::{Directive, MetaValue};
use rustledger_loader::Options;
use rustledger_parser::Spanned;
use std::collections::{HashMap, HashSet};

/// What the discovery pass produces for a single commodity symbol.
#[derive(Debug, Clone, Default)]
pub struct DiscoveredCommodity {
    /// Optional source/ticker mapping derived from `price:` metadata.
    /// `None` when discovery was driven by `quote_currency:` metadata
    /// alone, by the `--undeclared` ticker-shape heuristic, or by a
    /// CLI-supplied symbol — in those cases the source/ticker is
    /// resolved later from CLI args, config, or `[price.default_source]`.
    pub mapping: Option<CommodityMapping>,
    /// Optional per-commodity quote currency from `quote_currency:` metadata.
    pub quote_currency: Option<String>,
}

/// One parsed entry from a `price:` metadata string.
#[derive(Debug, Clone, PartialEq, Eq)]
struct PriceSpec {
    quote_currency: String,
    source: String,
    ticker: String,
}

/// Discover the set of commodities to fetch prices for from a loaded ledger.
///
/// Returns a map from commodity symbol to discovery info. Caller-supplied
/// CLI symbols are always included (with empty discovery info) so they
/// override or augment file-based discovery.
///
/// `inactive` corresponds to `bean-price --inactive`: when false (the
/// default), only commodities with a non-zero balance on at least one open
/// balance-sheet account are returned.
///
/// `undeclared` corresponds to `bean-price --undeclared`: when false (the
/// default), only commodities with `price:` or `quote_currency:` metadata
/// are returned. With `undeclared = true`, commodities whose name looks
/// like a ticker symbol are also picked up using configured/default
/// sources.
///
/// Takes the directive slice directly so it works with either `LoadResult`
/// (raw load) or the post-processing `Ledger` type without coupling. Reads
/// the configured account-type names from `options` so the
/// active-commodity check works on ledgers using non-English account
/// roots (e.g., `Activos:` instead of `Assets:`).
pub fn discover_symbols(
    directives: &[Spanned<Directive>],
    options: &Options,
    cli_symbols: &[String],
    inactive: bool,
    undeclared: bool,
) -> HashMap<String, DiscoveredCommodity> {
    let active = if inactive {
        None
    } else {
        Some(active_commodities(directives, options))
    };

    let mut out: HashMap<String, DiscoveredCommodity> = HashMap::new();

    for spanned in directives {
        let Directive::Commodity(comm) = &spanned.value else {
            continue;
        };
        let symbol = comm.currency.as_str();

        let classification = classify_commodity_meta(&comm.meta);

        // Warn on a non-empty `price:` value that didn't yield any usable
        // specs — almost always a typo. Matches `bean-price`, which logs
        // "Ignoring currency with invalid 'price' source" for the same
        // case. We still skip the commodity (no source to fetch from);
        // the warning surfaces the misconfiguration.
        if classification.malformed_price {
            eprintln!(
                "warning: commodity {symbol} has malformed `price:` metadata; \
                 expected `<quote>:<source>/<ticker>` (e.g. `USD:yahoo/AAPL`). Skipping."
            );
        }

        let info = match classification.decision {
            // `price: ""` (or whitespace) is an explicit opt-out, honored
            // regardless of `undeclared` so users can suppress commodities
            // that would otherwise be picked up by the heuristic.
            DiscoveryDecision::OptOut => continue,
            DiscoveryDecision::Discovered(info) => info,
            // No metadata: only include if `--undeclared` is set AND the
            // commodity name looks like a ticker symbol. This is a strict
            // subset of `bean-price --undeclared` (see module docs for the
            // rationale).
            DiscoveryDecision::Inherit => {
                if !(undeclared && looks_like_ticker(symbol)) {
                    continue;
                }
                DiscoveredCommodity::default()
            }
        };

        // Skip inactive commodities unless the user opted in.
        if let Some(ref active_set) = active
            && !active_set.contains(symbol)
        {
            continue;
        }

        out.insert(symbol.to_string(), info);
    }

    // CLI-supplied symbols always pass through with default (empty) info.
    for symbol in cli_symbols {
        out.entry(symbol.clone()).or_default();
    }

    out
}

/// Outcome of inspecting one `commodity` directive's metadata.
enum DiscoveryDecision {
    /// `price: ""` (or whitespace-only) — user explicitly opted this
    /// commodity out of fetching.
    OptOut,
    /// `price:` and/or `quote_currency:` metadata is present.
    Discovered(DiscoveredCommodity),
    /// No relevant metadata. Whether to include depends on `undeclared`
    /// and the name heuristic.
    Inherit,
}

/// Result of classifying a commodity, plus a flag for whether the
/// commodity had a non-empty `price:` value that didn't parse (typo /
/// misconfig). The caller surfaces this as a warning.
struct Classification {
    decision: DiscoveryDecision,
    malformed_price: bool,
}

/// Classify a commodity by its metadata in a single pass over the map.
fn classify_commodity_meta(meta: &rustledger_core::Metadata) -> Classification {
    let price_raw = meta.get("price").and_then(metavalue_as_str);

    // Empty or whitespace-only `price:` is the explicit opt-out marker.
    if let Some(p) = price_raw
        && p.trim().is_empty()
    {
        return Classification {
            decision: DiscoveryDecision::OptOut,
            malformed_price: false,
        };
    }

    let price_specs = price_raw.map(parse_price_metadata).unwrap_or_default();
    // A non-empty `price:` that produces zero parsed specs is malformed.
    // We still return `Inherit`/`Discovered` based on other signals; the
    // caller logs a warning.
    let malformed_price = price_raw.is_some_and(|s| !s.trim().is_empty()) && price_specs.is_empty();
    let mapping = build_mapping(&price_specs);

    let quote_currency_meta = meta.get("quote_currency").and_then(|v| match v {
        MetaValue::String(s) | MetaValue::Currency(s) => Some(s.clone()),
        _ => None,
    });

    let info = DiscoveredCommodity {
        mapping,
        // If `price:` already specified a quote currency, prefer that.
        quote_currency: price_specs
            .first()
            .map(|s| s.quote_currency.clone())
            .or(quote_currency_meta),
    };

    let decision = if info.mapping.is_some() || info.quote_currency.is_some() {
        DiscoveryDecision::Discovered(info)
    } else {
        DiscoveryDecision::Inherit
    };

    Classification {
        decision,
        malformed_price,
    }
}

/// Convert parsed `PriceSpec` entries into the existing `CommodityMapping`
/// shape so the rest of the price pipeline doesn't need new branches.
fn build_mapping(specs: &[PriceSpec]) -> Option<CommodityMapping> {
    if specs.is_empty() {
        return None;
    }
    if specs.len() == 1 {
        let s = &specs[0];
        return Some(CommodityMapping::Detailed(DetailedMapping {
            source: SourceRef::Single(s.source.clone()),
            ticker: Some(s.ticker.clone()),
            quote_currency: None,
        }));
    }
    // Multiple specs: build a fallback chain. The ticker is taken from the
    // first spec; it's the user's responsibility to ensure ticker symbols
    // are interchangeable across sources in their `price:` chain (matching
    // bean-price's contract).
    let sources: Vec<String> = specs.iter().map(|s| s.source.clone()).collect();
    Some(CommodityMapping::Detailed(DetailedMapping {
        source: SourceRef::Fallback(sources),
        ticker: Some(specs[0].ticker.clone()),
        quote_currency: None,
    }))
}

/// Parse a `price:` metadata value into one or more specs.
///
/// Format: `"<quote>:<source>/<ticker>"`, comma-separated for alternatives.
/// Malformed entries are silently skipped (matches `bean-price`'s lenient
/// parsing).
fn parse_price_metadata(raw: &str) -> Vec<PriceSpec> {
    raw.split(',')
        .filter_map(|chunk| {
            let chunk = chunk.trim();
            if chunk.is_empty() {
                return None;
            }
            let (quote, rest) = chunk.split_once(':')?;
            let (source, ticker) = rest.split_once('/')?;
            let quote = quote.trim();
            let source = source.trim();
            let ticker = ticker.trim();
            if quote.is_empty() || source.is_empty() || ticker.is_empty() {
                return None;
            }
            Some(PriceSpec {
                quote_currency: quote.to_string(),
                source: source.to_string(),
                ticker: ticker.to_string(),
            })
        })
        .collect()
}

const fn metavalue_as_str(v: &MetaValue) -> Option<&str> {
    match v {
        MetaValue::String(s) | MetaValue::Currency(s) => Some(s.as_str()),
        _ => None,
    }
}

/// Heuristic preserved for backward compat: a name is "ticker-shaped" if it's
/// uppercase ASCII letters, digits, dashes, or dots, length ≤ 10. The dot
/// allowance handles common exchange-suffixed tickers like `VECP.AS`,
/// `BRK.B`, or `7203.T` (issue #952). Beancount itself permits dots in
/// commodity names; the heuristic was previously stricter than the parser.
///
/// Intentionally permissive about the leading character (`7203.T` legitimately
/// starts with a digit). False positives like `..` are accepted because the
/// downstream price fetch will fail loudly for nonsense names — there's no
/// gain to encoding stricter validation here than the parser already does.
fn looks_like_ticker(symbol: &str) -> bool {
    !symbol.is_empty()
        && symbol.len() <= 10
        && symbol
            .chars()
            .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '-' || c == '.')
}

/// Compute the set of commodity codes that have a non-zero balance in at
/// least one open balance-sheet (Assets or Liabilities) account.
///
/// Restricting to balance-sheet accounts is the correct definition of
/// "currently held": Equity accounts (e.g. `Equity:Opening-Balances`)
/// retain inverse balances of every commodity that ever moved through the
/// ledger, so including them would mark long-closed positions as active.
/// Income and Expenses are never holdings.
///
/// The "Assets" / "Liabilities" prefix is read from `options` so ledgers
/// using translated account roots (`Activos`, `Aktiva`, etc.) work too.
fn active_commodities(directives: &[Spanned<Directive>], options: &Options) -> HashSet<String> {
    let assets_prefix = format!("{}:", options.name_assets);
    let liabilities_prefix = format!("{}:", options.name_liabilities);
    let is_balance_sheet = |account: &str| {
        account.starts_with(&assets_prefix) || account.starts_with(&liabilities_prefix)
    };

    let mut balances: HashMap<(String, String), Decimal> = HashMap::new();
    let mut closed: HashSet<String> = HashSet::new();

    for spanned in directives {
        match &spanned.value {
            Directive::Transaction(txn) => {
                for posting in &txn.postings {
                    let account = posting.account.as_str();
                    if !is_balance_sheet(account) {
                        continue;
                    }
                    if let Some(amount) = posting.amount() {
                        let key = (account.to_string(), amount.currency.to_string());
                        *balances.entry(key).or_default() += amount.number;
                    }
                }
            }
            Directive::Close(close) => {
                closed.insert(close.account.to_string());
            }
            _ => {}
        }
    }

    let mut active: HashSet<String> = HashSet::new();
    for ((account, currency), amount) in &balances {
        if !amount.is_zero() && !closed.contains(account) {
            active.insert(currency.clone());
        }
    }
    active
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;
    use rustledger_core::{Amount, Close, Commodity, NaiveDate, Open, Posting, Transaction};
    use rustledger_parser::Span;

    fn date(y: i32, m: u32, d: u32) -> NaiveDate {
        rustledger_core::naive_date(y, m, d).unwrap()
    }

    fn directives(items: Vec<Directive>) -> Vec<Spanned<Directive>> {
        items
            .into_iter()
            .map(|d| Spanned::new(d, Span::new(0, 0)))
            .collect()
    }

    #[test]
    fn parses_single_price_spec() {
        let specs = parse_price_metadata("USD:yahoo/AAPL");
        assert_eq!(
            specs,
            vec![PriceSpec {
                quote_currency: "USD".into(),
                source: "yahoo".into(),
                ticker: "AAPL".into(),
            }]
        );
    }

    #[test]
    fn parses_chained_price_specs() {
        let specs = parse_price_metadata("USD:yahoo/AAPL, USD:google/NASDAQ:AAPL");
        assert_eq!(specs.len(), 2);
        assert_eq!(specs[0].source, "yahoo");
        assert_eq!(specs[1].source, "google");
        // Ticker preserves embedded colons after the first / split.
        assert_eq!(specs[1].ticker, "NASDAQ:AAPL");
    }

    #[test]
    fn parse_price_skips_malformed_entries() {
        let specs = parse_price_metadata("USD:yahoo/AAPL,bogus,EUR:ecb/EUR.USD");
        assert_eq!(specs.len(), 2);
        assert_eq!(specs[0].quote_currency, "USD");
        assert_eq!(specs[1].quote_currency, "EUR");
    }

    #[test]
    fn ticker_heuristic_rejects_long_or_lowercase() {
        assert!(looks_like_ticker("AAPL"));
        assert!(looks_like_ticker("BTC-USD"));
        assert!(looks_like_ticker("VTI2025"));
        // Issue #952: exchange-suffixed tickers (dots) used to be silently dropped.
        assert!(looks_like_ticker("VECP.AS"));
        assert!(looks_like_ticker("BRK.B"));
        assert!(looks_like_ticker("7203.T"));
        assert!(!looks_like_ticker("usd"));
        assert!(!looks_like_ticker("Vanguard"));
        assert!(!looks_like_ticker("VERYLONGTICKER"));
        assert!(!looks_like_ticker(""));
    }

    #[test]
    fn active_filter_keeps_held_commodities() {
        // Bought 100 AAPL, never sold = active.
        // Bought and sold all BTC = inactive.
        // EUR cash held in Assets:Cash = active.
        let dirs = directives(vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Commodity(Commodity::new(date(2024, 1, 1), "AAPL")),
            Directive::Commodity(Commodity::new(date(2024, 1, 1), "BTC")),
            Directive::Commodity(Commodity::new(date(2024, 1, 1), "EUR")),
            Directive::Transaction(
                Transaction::new(date(2024, 2, 1), "Buy AAPL")
                    .with_posting(Posting::new(
                        "Assets:Brokerage",
                        Amount::new(dec!(100), "AAPL"),
                    ))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-100), "AAPL"),
                    )),
            ),
            Directive::Transaction(
                Transaction::new(date(2024, 3, 1), "Buy BTC")
                    .with_posting(Posting::new(
                        "Assets:Brokerage",
                        Amount::new(dec!(1), "BTC"),
                    ))
                    .with_posting(Posting::new("Equity:Opening", Amount::new(dec!(-1), "BTC"))),
            ),
            Directive::Transaction(
                Transaction::new(date(2024, 4, 1), "Sell BTC")
                    .with_posting(Posting::new(
                        "Assets:Brokerage",
                        Amount::new(dec!(-1), "BTC"),
                    ))
                    .with_posting(Posting::new("Equity:Opening", Amount::new(dec!(1), "BTC"))),
            ),
            Directive::Transaction(
                Transaction::new(date(2024, 5, 1), "Receive EUR")
                    .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(500), "EUR")))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-500), "EUR"),
                    )),
            ),
        ]);
        let active = active_commodities(&dirs, &Options::new());
        assert!(active.contains("AAPL"));
        assert!(active.contains("EUR"));
        assert!(
            !active.contains("BTC"),
            "BTC was fully sold, should not be active"
        );
    }

    #[test]
    fn closed_account_balance_does_not_count_as_active() {
        // A balance left over in a closed account is treated as inactive
        // (the close directive supersedes; any non-zero residual is a
        // validation problem, not an "active" signal for price fetching).
        let dirs = directives(vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Transaction(
                Transaction::new(date(2024, 2, 1), "Buy stale token")
                    .with_posting(Posting::new(
                        "Assets:Brokerage",
                        Amount::new(dec!(10), "DEFUNCT"),
                    ))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-10), "DEFUNCT"),
                    )),
            ),
            Directive::Close(Close::new(date(2024, 12, 31), "Assets:Brokerage")),
        ]);
        let active = active_commodities(&dirs, &Options::new());
        assert!(!active.contains("DEFUNCT"));
    }

    #[test]
    fn discover_picks_up_metadata_driven_commodity() {
        let mut comm = Commodity::new(date(2024, 1, 1), "Vanguard_VTI");
        comm.meta.insert(
            "price".to_string(),
            MetaValue::String("USD:yahoo/VTI".into()),
        );
        let dirs = directives(vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Commodity(comm),
            Directive::Transaction(
                Transaction::new(date(2024, 2, 1), "Buy VTI")
                    .with_posting(Posting::new(
                        "Assets:Brokerage",
                        Amount::new(dec!(10), "Vanguard_VTI"),
                    ))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-10), "Vanguard_VTI"),
                    )),
            ),
        ]);
        let discovered = discover_symbols(&dirs, &Options::new(), &[], false, false);

        // Even though "Vanguard_VTI" doesn't pass the ticker heuristic,
        // it has price: metadata, so it's discovered.
        let info = discovered
            .get("Vanguard_VTI")
            .expect("should be discovered");
        assert!(info.mapping.is_some());
        assert_eq!(info.quote_currency.as_deref(), Some("USD"));
    }

    #[test]
    fn discover_skips_inactive_by_default() {
        let mut comm = Commodity::new(date(2024, 1, 1), "OLD");
        comm.meta.insert(
            "price".to_string(),
            MetaValue::String("USD:yahoo/OLD".into()),
        );
        let dirs = directives(vec![Directive::Commodity(comm)]);

        // Default: no active postings means OLD is not discovered.
        let discovered = discover_symbols(&dirs, &Options::new(), &[], false, false);
        assert!(!discovered.contains_key("OLD"));

        // Opt-in: inactive=true brings it back.
        let discovered_all = discover_symbols(&dirs, &Options::new(), &[], true, false);
        assert!(discovered_all.contains_key("OLD"));
    }

    #[test]
    fn cli_symbols_always_included_with_default_info() {
        let dirs: Vec<Spanned<Directive>> = vec![];
        let discovered = discover_symbols(
            &dirs,
            &Options::new(),
            &["MANUAL".to_string()],
            false,
            false,
        );
        let info = discovered.get("MANUAL").unwrap();
        assert!(info.mapping.is_none());
        assert!(info.quote_currency.is_none());
    }

    /// Issue #962: a ticker-shaped commodity name without `price:`
    /// metadata must NOT be discovered by default. `bean-price -f` only
    /// fetches commodities with explicit `price:` metadata; the previous
    /// rustledger fallback to the name heuristic produced unwanted
    /// downloads (e.g., currency code `BAM` was treated as a stock).
    #[test]
    fn discover_skips_no_metadata_commodity_by_default() {
        // `BAM` looks ticker-shaped (3 uppercase letters) and has an
        // active balance, but has no `price:` metadata, so it must be
        // skipped by default.
        let dirs = directives(vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Commodity(Commodity::new(date(2024, 1, 1), "BAM")),
            Directive::Transaction(
                Transaction::new(date(2024, 2, 1), "Receive BAM")
                    .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(100), "BAM")))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-100), "BAM"),
                    )),
            ),
        ]);

        let strict = discover_symbols(&dirs, &Options::new(), &[], false, false);
        assert!(
            !strict.contains_key("BAM"),
            "BAM has no `price:` metadata, must not be discovered by default (#962)"
        );

        // `--undeclared` brings the heuristic back.
        let with_undeclared = discover_symbols(&dirs, &Options::new(), &[], false, true);
        assert!(with_undeclared.contains_key("BAM"));
    }

    /// `price: ""` is an explicit opt-out (bean-price-compatible). It
    /// must suppress discovery even with `--undeclared`, so users can
    /// override the heuristic on a per-commodity basis.
    #[test]
    fn discover_honors_empty_price_opt_out() {
        let mut comm = Commodity::new(date(2024, 1, 1), "BAM");
        comm.meta
            .insert("price".to_string(), MetaValue::String(String::new()));
        let dirs = directives(vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Commodity(comm),
            Directive::Transaction(
                Transaction::new(date(2024, 2, 1), "Receive BAM")
                    .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(100), "BAM")))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-100), "BAM"),
                    )),
            ),
        ]);

        // Even with --undeclared, the empty price: opt-out wins.
        let discovered = discover_symbols(&dirs, &Options::new(), &[], false, true);
        assert!(!discovered.contains_key("BAM"));
    }

    /// `quote_currency:` alone (no `price:`) is an explicit user opt-in
    /// for fetching with a configured/default source — it should be
    /// discovered without needing `--undeclared`.
    #[test]
    fn discover_picks_up_quote_currency_only_commodity() {
        let mut comm = Commodity::new(date(2024, 1, 1), "GOVT_EU");
        comm.meta.insert(
            "quote_currency".to_string(),
            MetaValue::String("EUR".into()),
        );
        let dirs = directives(vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Commodity(comm),
            Directive::Transaction(
                Transaction::new(date(2024, 2, 1), "Buy GOVT_EU")
                    .with_posting(Posting::new(
                        "Assets:Brokerage",
                        Amount::new(dec!(10), "GOVT_EU"),
                    ))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-10), "GOVT_EU"),
                    )),
            ),
        ]);

        let discovered = discover_symbols(&dirs, &Options::new(), &[], false, false);
        let info = discovered
            .get("GOVT_EU")
            .expect("quote_currency: alone should opt into discovery");
        assert!(info.mapping.is_none());
        assert_eq!(info.quote_currency.as_deref(), Some("EUR"));
    }

    #[test]
    fn discover_inactive_undeclared_combined_matches_legacy_all_commodities() {
        // Sanity check that --inactive=true + --undeclared=true behaves
        // like the old --all-commodities path: heuristic on, no active
        // filter. Matches the legacy discovery surface.
        let dirs = directives(vec![Directive::Commodity(Commodity::new(
            date(2024, 1, 1),
            "OLD",
        ))]);
        let discovered = discover_symbols(&dirs, &Options::new(), &[], true, true);
        assert!(discovered.contains_key("OLD"));
    }

    /// Malformed `price:` metadata (e.g. typo, wrong format) produces no
    /// parsed specs. The commodity is skipped under the strict default
    /// (no usable source), but the malformed flag is set so the caller
    /// can log a warning. This matches `bean-price`, which logs
    /// "Ignoring currency with invalid 'price' source" for the same case.
    #[test]
    fn classify_flags_malformed_price_metadata() {
        let mut meta = rustledger_core::Metadata::default();
        meta.insert(
            "price".to_string(),
            MetaValue::String("BOGUS_FORMAT".into()),
        );
        let classification = classify_commodity_meta(&meta);
        assert!(classification.malformed_price);
        assert!(matches!(
            classification.decision,
            DiscoveryDecision::Inherit
        ));
    }

    /// A malformed `price:` paired with a valid `quote_currency:` should
    /// still surface the malformed-price warning, even though the
    /// commodity is included via `quote_currency:`. The caller can then
    /// nudge the user to fix the typo.
    #[test]
    fn classify_flags_malformed_price_even_when_quote_currency_present() {
        let mut meta = rustledger_core::Metadata::default();
        meta.insert(
            "price".to_string(),
            MetaValue::String("BOGUS_FORMAT".into()),
        );
        meta.insert(
            "quote_currency".to_string(),
            MetaValue::String("EUR".into()),
        );
        let classification = classify_commodity_meta(&meta);
        assert!(classification.malformed_price);
        assert!(matches!(
            classification.decision,
            DiscoveryDecision::Discovered(_)
        ));
    }

    /// `price: ""` is an opt-out, not malformed — ensure we don't emit a
    /// false-positive warning for the explicit opt-out path.
    #[test]
    fn classify_does_not_flag_empty_price_as_malformed() {
        let mut meta = rustledger_core::Metadata::default();
        meta.insert("price".to_string(), MetaValue::String(String::new()));
        let classification = classify_commodity_meta(&meta);
        assert!(!classification.malformed_price);
        assert!(matches!(classification.decision, DiscoveryDecision::OptOut));
    }

    /// Whitespace-only `price:` is treated the same as empty — explicit
    /// opt-out — so users can write `price: "   "` and still suppress
    /// fetching consistently with `price: ""`.
    #[test]
    fn discover_honors_whitespace_only_price_opt_out() {
        let mut comm = Commodity::new(date(2024, 1, 1), "BAM");
        comm.meta
            .insert("price".to_string(), MetaValue::String("   ".into()));
        let dirs = directives(vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Cash")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Commodity(comm),
            Directive::Transaction(
                Transaction::new(date(2024, 2, 1), "Receive BAM")
                    .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(100), "BAM")))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-100), "BAM"),
                    )),
            ),
        ]);

        let discovered = discover_symbols(&dirs, &Options::new(), &[], false, true);
        assert!(!discovered.contains_key("BAM"));
    }

    #[test]
    fn active_filter_handles_explicit_amounts_on_balance_sheet_side() {
        // Simulates the post-booking shape: every posting has explicit units,
        // including the asset side. Confirms the active filter sees the
        // asset-side amount and includes the commodity. The actual
        // interpolation happens in the booking engine before this function
        // sees the directives — `price_cmd.rs` calls `process::load` with
        // booking enabled to ensure that.
        let dirs = directives(vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Brokerage")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Transaction(
                Transaction::new(date(2024, 2, 1), "Buy AAPL")
                    .with_posting(Posting::new(
                        "Assets:Brokerage",
                        Amount::new(dec!(100), "AAPL"),
                    ))
                    .with_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-100), "AAPL"),
                    )),
            ),
        ]);
        let active = active_commodities(&dirs, &Options::new());
        assert!(active.contains("AAPL"));
    }
}
