//! Symbol discovery from beancount files.
//!
//! Walks a loaded ledger to identify which commodities to fetch prices for,
//! matching the workflow `bean-price` exposes via the same metadata
//! conventions:
//!
//! - `commodity` directives carrying a `price:` metadata key drive
//!   metadata-based discovery. Format: `"<quote>:<source>/<ticker>"`,
//!   optionally chained with `,` for fallback alternatives, e.g.
//!   `"USD:yahoo/AAPL,USD:google/NASDAQ:AAPL"`.
//! - `quote_currency:` metadata supplies a per-commodity quote currency,
//!   used as the `--currency` default for that one symbol.
//! - With no metadata, ticker-shaped commodity names (uppercase + digits +
//!   dashes, ≤ 10 chars) are picked up via heuristic so existing users
//!   aren't broken (issue #948).
//!
//! By default, only "active" commodities are returned: those with a non-zero
//! balance in any open account, computed by walking transaction postings and
//! summing per-(account, currency). This matches `bean-price`'s default
//! behavior and avoids wasting API calls on commodities the user no longer
//! holds. Pass `include_inactive: true` to skip the activity filter.

use crate::config::{CommodityMapping, SourceRef};
use rust_decimal::Decimal;
use rustledger_core::{Directive, MetaValue};
use rustledger_loader::Options;
use rustledger_parser::Spanned;
use std::collections::{HashMap, HashSet};

/// What the discovery pass produces for a single commodity symbol.
#[derive(Debug, Clone, Default)]
pub struct DiscoveredCommodity {
    /// Optional source/ticker mapping derived from `price:` metadata.
    /// `None` means the symbol was found by name heuristic only.
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
/// Takes the directive slice directly so it works with either `LoadResult`
/// (raw load) or the post-processing `Ledger` type without coupling. Reads
/// the configured account-type names from `options` so the
/// active-commodity check works on ledgers using non-English account
/// roots (e.g., `Activos:` instead of `Assets:`).
pub fn discover_symbols(
    directives: &[Spanned<Directive>],
    options: &Options,
    cli_symbols: &[String],
    include_inactive: bool,
) -> HashMap<String, DiscoveredCommodity> {
    let active = if include_inactive {
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
        let info = build_discovery_info(&comm.meta);

        // Skip commodities with no metadata that don't look like a ticker —
        // preserves backward-compat with the old name-heuristic filter.
        if info.mapping.is_none() && info.quote_currency.is_none() && !looks_like_ticker(symbol) {
            continue;
        }

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

/// Build the per-commodity discovery info from its metadata map.
fn build_discovery_info(meta: &rustledger_core::Metadata) -> DiscoveredCommodity {
    let price_specs = meta
        .get("price")
        .and_then(metavalue_as_str)
        .map(parse_price_metadata)
        .unwrap_or_default();

    let quote_currency = meta.get("quote_currency").and_then(|v| match v {
        MetaValue::String(s) | MetaValue::Currency(s) => Some(s.clone()),
        _ => None,
    });

    let mapping = build_mapping(&price_specs);

    DiscoveredCommodity {
        mapping,
        // If `price:` already specified a quote currency, prefer that.
        quote_currency: price_specs
            .first()
            .map(|s| s.quote_currency.clone())
            .or(quote_currency),
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
        return Some(CommodityMapping::Detailed {
            source: SourceRef::Single(s.source.clone()),
            ticker: Some(s.ticker.clone()),
        });
    }
    // Multiple specs: build a fallback chain. The ticker is taken from the
    // first spec; it's the user's responsibility to ensure ticker symbols
    // are interchangeable across sources in their `price:` chain (matching
    // bean-price's contract).
    let sources: Vec<String> = specs.iter().map(|s| s.source.clone()).collect();
    Some(CommodityMapping::Detailed {
        source: SourceRef::Fallback(sources),
        ticker: Some(specs[0].ticker.clone()),
    })
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
/// uppercase ASCII letters / digits / dashes, length ≤ 10.
fn looks_like_ticker(symbol: &str) -> bool {
    !symbol.is_empty()
        && symbol.len() <= 10
        && symbol
            .chars()
            .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '-')
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
        let discovered = discover_symbols(&dirs, &Options::new(), &[], false);

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
        let discovered = discover_symbols(&dirs, &Options::new(), &[], false);
        assert!(!discovered.contains_key("OLD"));

        // Opt-in: include_inactive=true brings it back.
        let discovered_all = discover_symbols(&dirs, &Options::new(), &[], true);
        assert!(discovered_all.contains_key("OLD"));
    }

    #[test]
    fn cli_symbols_always_included_with_default_info() {
        let dirs: Vec<Spanned<Directive>> = vec![];
        let discovered = discover_symbols(&dirs, &Options::new(), &["MANUAL".to_string()], false);
        let info = discovered.get("MANUAL").unwrap();
        assert!(info.mapping.is_none());
        assert!(info.quote_currency.is_none());
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
