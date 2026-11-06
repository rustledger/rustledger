//! Price fetching module for rustledger.
//!
//! This module provides a pluggable price source system that supports:
//! - Built-in sources (Yahoo Finance, Coinbase, ECB, etc.)
//! - External command sources for custom integrations
//! - Configurable commodity-to-source mappings
//! - Fallback chains for reliability

pub mod cache;
pub mod discovery;
pub mod external;
pub mod sources;

use crate::config::{CommodityMapping, PriceConfig, PriceSourceConfig, SourceRef};
use anyhow::{Context, Result};
use rust_decimal::Decimal;
use rustledger_core::NaiveDate;
use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;

pub use sources::PriceSource;

/// A request to fetch a price.
#[derive(Debug, Clone)]
pub struct PriceRequest {
    /// The ticker symbol to fetch.
    pub ticker: String,
    /// The target currency for the price.
    pub currency: String,
    /// Optional specific date (None = current price).
    pub date: Option<NaiveDate>,
}

impl PriceRequest {
    /// Create a new price request.
    pub fn new(ticker: impl Into<String>, currency: impl Into<String>) -> Self {
        Self {
            ticker: ticker.into(),
            currency: currency.into(),
            date: None,
        }
    }

    /// Set the date for the request.
    #[must_use]
    pub const fn with_date(mut self, date: NaiveDate) -> Self {
        self.date = Some(date);
        self
    }
}

/// A response from a price source.
#[derive(Debug, Clone)]
pub struct PriceResponse {
    /// The fetched price.
    pub price: Decimal,
    /// The currency of the price.
    pub currency: String,
    /// The date of the price.
    pub date: NaiveDate,
    /// The source that provided the price.
    pub source: String,
}

/// Parse a price quote from a JSON value into a [`Decimal`].
///
/// Handles both shapes price APIs use:
/// - **String** quotes (`"1.2345"`) parse exactly.
/// - **Integer** numbers parse exactly.
/// - **Float** numbers are bounded by `f64` (~15–17 significant digits): a JSON
///   float has already been parsed into an `f64` by the time it reaches a
///   `serde_json::Value` (`serde_json` is built without `arbitrary_precision`), so
///   the most we can recover is its shortest round-trippable string. That is
///   exact for every human-scale quote (FX / equities / crypto) and only loses
///   precision past ~15 significant digits — far beyond any real price.
///
/// We deliberately do not enable `serde_json`'s `arbitrary_precision` feature: it
/// is global and breaks the workspace's `#[serde(untagged)]` / `flatten` enums.
/// A per-field `RawValue` rewrite of every network source was judged
/// disproportionate for the negligible gain (see #1621).
#[must_use]
pub fn price_decimal_from_json(value: &serde_json::Value) -> Option<Decimal> {
    use std::str::FromStr;
    match value {
        serde_json::Value::String(s) => Decimal::from_str(s).ok(),
        serde_json::Value::Number(n) => Decimal::from_str(&n.to_string()).ok(),
        _ => None,
    }
}

/// Registry of available price sources.
pub struct PriceSourceRegistry {
    sources: HashMap<String, Arc<dyn PriceSource>>,
    default_source: String,
    timeout: Duration,
    /// When false, a commodity with no explicit source declaration
    /// errors instead of silently using `default_source`. See #966 and
    /// `PriceConfig::use_default_source`.
    use_default_source: bool,
}

impl PriceSourceRegistry {
    /// Create a new registry with built-in sources.
    pub fn new(config: &PriceConfig) -> Self {
        let mut sources: HashMap<String, Arc<dyn PriceSource>> = HashMap::new();
        let timeout = Duration::from_secs(config.effective_timeout());

        // Register built-in sources
        sources.insert(
            "yahoo".to_string(),
            Arc::new(sources::YahooFinanceSource::new(timeout)),
        );
        sources.insert(
            "coinbase".to_string(),
            Arc::new(sources::CoinbaseSource::new(timeout)),
        );
        sources.insert(
            "coincap".to_string(),
            Arc::new(sources::CoinCapSource::new(timeout)),
        );
        let ecb: Arc<dyn PriceSource> = Arc::new(sources::EcbSource::new(timeout));
        sources.insert("ecb".to_string(), Arc::clone(&ecb));
        // beanprice calls the same ECB reference-rate source `ecbrates`,
        // so a `price: "EUR:ecbrates/GBP-EUR"` written for bean-price
        // resolves (#2866); `ecb` reads its `BASE-SYMBOL` ticker too.
        sources.insert("ecbrates".to_string(), ecb);
        sources.insert(
            "ratesapi".to_string(),
            Arc::new(sources::RatesApiSource::new(timeout)),
        );
        sources.insert(
            "tsp".to_string(),
            Arc::new(sources::TspSource::new(timeout)),
        );
        sources.insert(
            "eastmoneyfund".to_string(),
            Arc::new(sources::EastMoneyFundSource::new(timeout)),
        );

        // Register API key sources (always registered; they return clear errors if key is missing)
        sources.insert(
            "oanda".to_string(),
            Arc::new(sources::OandaSource::new(timeout)),
        );
        sources.insert(
            "alphavantage".to_string(),
            Arc::new(sources::AlphaVantageSource::new(timeout)),
        );
        sources.insert(
            "coinmarketcap".to_string(),
            Arc::new(sources::CoinMarketCapSource::new(timeout)),
        );
        sources.insert(
            "quandl".to_string(),
            Arc::new(sources::QuandlSource::new(timeout)),
        );

        // Register custom command sources from config
        for (name, source_config) in &config.sources {
            if let PriceSourceConfig::Command {
                command,
                timeout: cmd_timeout,
                env,
            } = source_config
            {
                let cmd_timeout =
                    Duration::from_secs(cmd_timeout.unwrap_or(config.effective_timeout()));
                sources.insert(
                    name.clone(),
                    Arc::new(external::ExternalCommandSource::with_name(
                        command.clone(),
                        cmd_timeout,
                        env.clone(),
                        name.clone(),
                    )),
                );
            }
        }

        Self {
            sources,
            default_source: config.effective_default_source().to_string(),
            timeout,
            use_default_source: config.effective_use_default_source(),
        }
    }

    /// Get a source by name.
    pub fn get(&self, name: &str) -> Option<Arc<dyn PriceSource>> {
        self.sources.get(name).cloned()
    }

    /// Get the default source.
    pub fn default_source(&self) -> Option<Arc<dyn PriceSource>> {
        self.get(&self.default_source)
    }

    /// Get the default source name.
    pub fn default_source_name(&self) -> &str {
        &self.default_source
    }

    /// List all registered source names.
    pub fn list_sources(&self) -> Vec<&str> {
        let mut names: Vec<&str> = self.sources.keys().map(String::as_str).collect();
        names.sort_unstable();
        names
    }

    /// Check if a source is registered.
    pub fn has_source(&self, name: &str) -> bool {
        self.sources.contains_key(name)
    }

    /// Get the configured timeout.
    pub const fn timeout(&self) -> Duration {
        self.timeout
    }

    /// Fetch a price using the configured mapping.
    ///
    /// This method resolves the commodity to the appropriate source and
    /// ticker based on the configuration, then fetches the price. When a
    /// fallback chain is in play, each entry's per-source ticker is used
    /// (issue #963).
    ///
    /// # Errors
    ///
    /// Returns an error if the commodity has no explicit source
    /// declaration (no CLI `--source`, no `[price.mapping.X]` in config,
    /// no `price:` metadata) and `[price] use_default_source = false`
    /// (the default). See issue #966.
    pub fn fetch_price(
        &self,
        commodity: &str,
        currency: &str,
        date: Option<NaiveDate>,
        mapping: &HashMap<String, CommodityMapping>,
    ) -> Result<PriceResponse> {
        let attempts = self.resolve_mapping(commodity, mapping)?;

        // Every failed attempt is kept, not just the last: in a chain
        // like [yahoo, coinbase] with --date, the trailing source's
        // "latest quote only" refusal must not mask yahoo's real
        // (possibly transient) failure (round-2 deep review of #1801).
        let mut errors: Vec<(String, anyhow::Error)> = Vec::new();
        let mut unknown_sources = Vec::new();

        for (source_name, ticker) in &attempts {
            if let Some(source) = self.get(source_name) {
                // bean-price's `^TICKER` asks for the inverse of the
                // source's rate, on every source (#2866).
                let (ticker, inverted) = match ticker.strip_prefix('^') {
                    Some(rest) => (rest, true),
                    None => (ticker.as_str(), false),
                };
                let request = PriceRequest {
                    ticker: ticker.to_string(),
                    currency: currency.to_string(),
                    date,
                };

                let result = source.fetch_price(&request).and_then(|response| {
                    if inverted {
                        invert_response(response, currency)
                    } else {
                        Ok(response)
                    }
                });
                match result {
                    Ok(response) => return Ok(response),
                    Err(e) => {
                        errors.push((source_name.clone(), e));
                        // Try next source in fallback chain
                    }
                }
            } else {
                // Track unknown sources for error reporting
                unknown_sources.push(source_name.clone());
            }
        }

        // Build an informative error message
        let err_msg = if errors.len() == 1 {
            // A single failure keeps its full error value.
            let (_, single) = errors.remove(0);
            if unknown_sources.is_empty() {
                single
            } else {
                anyhow::anyhow!(
                    "{single:#}; note: unknown sources skipped: {}",
                    unknown_sources.join(", ")
                )
            }
        } else if !errors.is_empty() {
            let attempts_report = errors
                .iter()
                .map(|(name, e)| format!("{name}: {e:#}"))
                .collect::<Vec<_>>()
                .join("; ");
            if unknown_sources.is_empty() {
                anyhow::anyhow!("all sources failed for {commodity}: {attempts_report}")
            } else {
                anyhow::anyhow!(
                    "all sources failed for {commodity}: {attempts_report}; \
                     note: unknown sources skipped: {}",
                    unknown_sources.join(", ")
                )
            }
        } else if !unknown_sources.is_empty() {
            anyhow::anyhow!(
                "No price source available for commodity {commodity}: unknown sources: {}",
                unknown_sources.join(", ")
            )
        } else {
            anyhow::anyhow!("No price source available for commodity {commodity}")
        };

        Err(err_msg)
    }

    /// Resolve a commodity to a list of `(source, ticker)` attempts to
    /// try in order. Each fallback entry can carry its own ticker so a
    /// chain like `EUR:ecbrates/GBP-EUR,EUR:ecb/GBP` queries each source
    /// with the ticker shape it expects (issue #963).
    ///
    /// # Errors
    ///
    /// Returns an error if `mapping` has no entry for `commodity` and
    /// `use_default_source` is false. The error message lists the
    /// remediation paths so users can pick whichever fits their workflow.
    fn resolve_mapping(
        &self,
        commodity: &str,
        mapping: &HashMap<String, CommodityMapping>,
    ) -> Result<Vec<(String, String)>> {
        if let Some(commodity_mapping) = mapping.get(commodity) {
            let attempts = match commodity_mapping {
                CommodityMapping::Simple(ticker) => {
                    vec![(self.default_source.clone(), ticker.clone())]
                }
                CommodityMapping::Detailed(d) => {
                    let parent_ticker = d.ticker.clone().unwrap_or_else(|| commodity.to_string());
                    match &d.source {
                        SourceRef::Single(s) => vec![(s.clone(), parent_ticker)],
                        SourceRef::Fallback(entries) => entries
                            .iter()
                            .map(|e| {
                                // Per-entry ticker wins; otherwise fall back to the
                                // parent ticker. This mirrors the metadata semantics
                                // the discovery layer encodes for chained `price:`.
                                let t = e
                                    .ticker()
                                    .map_or_else(|| parent_ticker.clone(), str::to_string);
                                (e.source_name().to_string(), t)
                            })
                            .collect(),
                    }
                }
            };
            return Ok(attempts);
        }

        // No mapping. Issue #966: silently dispatching to `default_source`
        // is the failure mode where currency codes like `BAM` get sent to
        // Yahoo and return a stock price for an unrelated ticker. Refuse
        // unless the user has opted in via `[price] use_default_source = true`.
        if self.use_default_source {
            return Ok(vec![(self.default_source.clone(), commodity.to_string())]);
        }
        Err(anyhow::anyhow!(
            "no price source configured for {commodity}. Pick one:\n  \
             - pass `--source <name>` (e.g. `--source ecb`),\n  \
             - pass `--mapping {commodity}:<TICKER>`,\n  \
             - add `[price.mapping.{commodity}]` to your rledger config,\n  \
             - annotate the commodity in your beancount file with \
             `price: \"<quote>:<source>/<ticker>\"` or `quote_currency: \"<currency>\"` \
             and load the file with `-f`,\n  \
             - or set `[price] use_default_source = true` in your config to fall back \
             to the default source ({default}) for unmapped symbols.",
            default = self.default_source,
        ))
    }
}

/// The inverse of a fetched quote, for bean-price's `^TICKER` (#2866):
/// `1 / price`, labeled with the requested quote currency, as bean-price
/// labels it (`EUR:ratesapi/^EUR-GBP` fetches GBP per EUR and writes EUR
/// per GBP).
///
/// The digits are bean-price's `ONE / price` under Python's default decimal
/// context: an exact inverse in its shortest form (`1 / 8` is `0.125`), and
/// any other rounded to 28 significant digits, half to even. One limit is
/// `rust_decimal`'s: it holds at most 28 decimal places, so an inverse
/// below 0.1 keeps fewer significant digits than Python's (`1 / 149.5` is
/// `0.0066889632107023411371237458`, where Python carries two more), the
/// "not fixable locally" precision case of AGENTS.md.
///
/// # Errors
///
/// A zero price, which has no inverse.
fn invert_response(response: PriceResponse, currency: &str) -> Result<PriceResponse> {
    let price = response.price;
    let inverse = Decimal::ONE.checked_div(price).with_context(|| {
        format!(
            "cannot invert the {} price {} {} for `^`: it has no inverse",
            response.source, response.price, response.currency
        )
    })?;
    let significant_digits = inverse.mantissa().unsigned_abs().to_string().len();
    let inverse = if significant_digits > 28 {
        inverse
            .round_sf_with_strategy(28, rust_decimal::RoundingStrategy::MidpointNearestEven)
            .context("rounding the inverted price")?
    } else {
        inverse
    };
    // Python gives an exact quotient its shortest form, and rounds only an
    // inexact one, which keeps its trailing zeros.
    let inverse = if inverse.checked_mul(price) == Some(Decimal::ONE) {
        inverse.normalize()
    } else {
        inverse
    };
    Ok(PriceResponse {
        price: inverse,
        currency: currency.to_uppercase(),
        ..response
    })
}

impl Default for PriceSourceRegistry {
    fn default() -> Self {
        Self::new(&PriceConfig::default())
    }
}

/// Convenience function to fetch a single price with default configuration.
pub fn fetch_price(
    ticker: &str,
    currency: &str,
    source_name: Option<&str>,
) -> Result<PriceResponse> {
    let config = PriceConfig::default();
    let registry = PriceSourceRegistry::new(&config);

    let source_name = source_name.unwrap_or(registry.default_source_name());
    let source = registry
        .get(source_name)
        .with_context(|| format!("Unknown price source: {source_name}"))?;

    let request = PriceRequest::new(ticker, currency);
    source.fetch_price(&request)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::{FallbackDetail, FallbackEntry};

    #[test]
    fn test_price_decimal_from_json() {
        use std::str::FromStr;
        // String quotes parse exactly, including beyond f64 precision.
        assert_eq!(
            price_decimal_from_json(&serde_json::json!("1.23456789012345678901234567")),
            Some(Decimal::from_str("1.23456789012345678901234567").unwrap())
        );
        // Integer numbers are exact.
        assert_eq!(
            price_decimal_from_json(&serde_json::json!(42)),
            Some(Decimal::from(42))
        );
        // Ordinary float quotes round-trip to the expected decimal.
        assert_eq!(
            price_decimal_from_json(&serde_json::json!(1.25)),
            Some(Decimal::from_str("1.25").unwrap())
        );
        // Non-numeric / wrong-shape values yield None.
        assert_eq!(
            price_decimal_from_json(&serde_json::json!("not-a-number")),
            None
        );
        assert_eq!(price_decimal_from_json(&serde_json::json!(true)), None);
        assert_eq!(price_decimal_from_json(&serde_json::json!(null)), None);
        assert_eq!(price_decimal_from_json(&serde_json::json!([1, 2])), None);
    }

    #[test]
    fn test_price_request_builder() {
        let request = PriceRequest::new("AAPL", "USD");
        assert_eq!(request.ticker, "AAPL");
        assert_eq!(request.currency, "USD");
        assert!(request.date.is_none());

        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();
        let request_with_date = PriceRequest::new("AAPL", "USD").with_date(date);
        assert_eq!(request_with_date.date, Some(date));
    }

    #[test]
    fn test_registry_default_sources() {
        let registry = PriceSourceRegistry::default();

        // Built-in sources should be registered (no API key required)
        assert!(registry.has_source("yahoo"));
        assert!(registry.has_source("coinbase"));
        assert!(registry.has_source("coincap"));
        assert!(registry.has_source("ecb"));
        assert!(registry.has_source("ratesapi"));
        assert!(registry.has_source("tsp"));
        assert!(registry.has_source("eastmoneyfund"));

        // API key sources should also be registered (will error if key not set)
        assert!(registry.has_source("oanda"));
        assert!(registry.has_source("alphavantage"));
        assert!(registry.has_source("coinmarketcap"));
        assert!(registry.has_source("quandl"));

        // Default source should be yahoo
        assert_eq!(registry.default_source_name(), "yahoo");
    }

    #[test]
    fn test_registry_list_sources() {
        let registry = PriceSourceRegistry::default();
        let sources = registry.list_sources();

        assert!(sources.contains(&"yahoo"));
        assert!(sources.contains(&"coinbase"));

        // List should be sorted
        let mut sorted = sources.clone();
        sorted.sort_unstable();
        assert_eq!(sources, sorted);
    }

    #[test]
    fn test_resolve_mapping_simple() {
        let registry = PriceSourceRegistry::default();
        let mut mapping = HashMap::new();
        mapping.insert(
            "BTC".to_string(),
            CommodityMapping::Simple("BTC-USD".to_string()),
        );

        let attempts = registry.resolve_mapping("BTC", &mapping).unwrap();
        assert_eq!(attempts, vec![("yahoo".to_string(), "BTC-USD".to_string())]);
    }

    #[test]
    fn test_resolve_mapping_detailed() {
        let registry = PriceSourceRegistry::default();
        let mut mapping = HashMap::new();
        mapping.insert(
            "EUR".to_string(),
            CommodityMapping::Detailed(crate::config::DetailedMapping {
                source: SourceRef::Fallback(vec![
                    FallbackEntry::Name("ecb".to_string()),
                    FallbackEntry::Name("ratesapi".to_string()),
                ]),
                ticker: None,
                quote_currency: None,
            }),
        );

        let attempts = registry.resolve_mapping("EUR", &mapping).unwrap();
        assert_eq!(
            attempts,
            vec![
                ("ecb".to_string(), "EUR".to_string()),
                ("ratesapi".to_string(), "EUR".to_string()),
            ]
        );
    }

    /// Issue #966: by default, resolving a commodity that has no
    /// mapping (and no `--source` was provided at the call site) is an
    /// error rather than a silent dispatch to `default_source`. The
    /// error message points the user at every remediation path so they
    /// don't have to guess which one applies to their workflow.
    #[test]
    fn test_resolve_mapping_no_mapping_errors_by_default() {
        let registry = PriceSourceRegistry::default();
        let mapping = HashMap::new();

        let result = registry.resolve_mapping("AAPL", &mapping);
        let err = result.expect_err("default behavior must refuse unmapped symbols");
        let msg = err.to_string();
        assert!(
            msg.contains("AAPL"),
            "error must name the offending symbol: {msg}"
        );
        // Every remediation path must be discoverable from the error so
        // the user can pick whichever one fits their workflow.
        for needle in [
            "--source",
            "--mapping",
            "[price.mapping.AAPL]",
            "price:",
            "quote_currency:",
            "-f",
            "use_default_source",
        ] {
            assert!(msg.contains(needle), "error must mention `{needle}`: {msg}");
        }
    }

    /// `[price] use_default_source = true` restores the previous
    /// behavior — unmapped symbols dispatch to `default_source`.
    #[test]
    fn test_resolve_mapping_no_mapping_uses_default_when_opted_in() {
        let config = PriceConfig {
            use_default_source: Some(true),
            ..PriceConfig::default()
        };
        let registry = PriceSourceRegistry::new(&config);
        let mapping = HashMap::new();

        let attempts = registry
            .resolve_mapping("AAPL", &mapping)
            .expect("opt-in must allow default-source dispatch");
        assert_eq!(attempts, vec![("yahoo".to_string(), "AAPL".to_string())]);
    }

    /// Issue #963: a fallback chain whose entries carry per-source
    /// tickers must query each source with that source's own ticker.
    /// Previously all sources reused the first spec's ticker.
    #[test]
    fn test_resolve_mapping_fallback_uses_per_source_tickers() {
        let registry = PriceSourceRegistry::default();
        let mut mapping = HashMap::new();
        mapping.insert(
            "GBP".to_string(),
            CommodityMapping::Detailed(crate::config::DetailedMapping {
                source: SourceRef::Fallback(vec![
                    FallbackEntry::Detailed(FallbackDetail {
                        source: "ecbrates".to_string(),
                        ticker: Some("GBP-EUR".to_string()),
                    }),
                    FallbackEntry::Detailed(FallbackDetail {
                        source: "ecb".to_string(),
                        ticker: Some("GBP".to_string()),
                    }),
                ]),
                ticker: Some("GBP-EUR".to_string()),
                quote_currency: Some("EUR".to_string()),
            }),
        );

        let attempts = registry.resolve_mapping("GBP", &mapping).unwrap();
        assert_eq!(
            attempts,
            vec![
                ("ecbrates".to_string(), "GBP-EUR".to_string()),
                ("ecb".to_string(), "GBP".to_string()),
            ],
            "each fallback source must use its own ticker (issue #963)"
        );
    }

    /// Mixed-shape fallback: a bare-string entry inherits the parent
    /// ticker, while an object entry uses its own. Verifies the
    /// `FallbackEntry::Name(_)` arm of `resolve_mapping` falls through
    /// to `parent_ticker` correctly.
    #[test]
    fn test_resolve_mapping_fallback_mixed_entries_inherit_parent_ticker() {
        let registry = PriceSourceRegistry::default();
        let mut mapping = HashMap::new();
        mapping.insert(
            "BTC".to_string(),
            CommodityMapping::Detailed(crate::config::DetailedMapping {
                source: SourceRef::Fallback(vec![
                    FallbackEntry::Name("yahoo".to_string()),
                    FallbackEntry::Detailed(FallbackDetail {
                        source: "coingecko".to_string(),
                        ticker: Some("bitcoin".to_string()),
                    }),
                ]),
                ticker: Some("BTC-USD".to_string()),
                quote_currency: None,
            }),
        );

        let attempts = registry.resolve_mapping("BTC", &mapping).unwrap();
        assert_eq!(
            attempts,
            vec![
                // Bare-string entry inherits parent ticker.
                ("yahoo".to_string(), "BTC-USD".to_string()),
                // Detailed entry uses its own ticker.
                ("coingecko".to_string(), "bitcoin".to_string()),
            ]
        );
    }

    #[test]
    fn test_custom_config() {
        let config = PriceConfig {
            default_source: Some("coinbase".to_string()),
            timeout: Some(60),
            ..Default::default()
        };

        let registry = PriceSourceRegistry::new(&config);
        assert_eq!(registry.default_source_name(), "coinbase");
        assert_eq!(registry.timeout(), Duration::from_mins(1));
    }

    /// A source that reads beanprice's `BASE-SYMBOL` ticker, like
    /// `ratesapi`, records the pair it was asked for, and answers a fixed
    /// rate in the pair's currency.
    struct PairSource {
        rate: Decimal,
        asked: std::sync::Mutex<Vec<(String, String)>>,
    }

    impl PriceSource for PairSource {
        fn name(&self) -> &'static str {
            "pairs"
        }

        fn description(&self) -> &'static str {
            "test source"
        }

        fn bean_price_pair(&self, pair: sources::PricePair) -> sources::PricePair {
            match sources::split_dash_pair(&pair.ticker) {
                Some((ticker, currency)) => sources::PricePair {
                    ticker: ticker.to_string(),
                    currency: currency.to_string(),
                },
                None => pair,
            }
        }

        fn fetch_latest(&self, pair: &sources::PricePair) -> Result<PriceResponse> {
            self.asked
                .lock()
                .expect("not poisoned")
                .push((pair.ticker.clone(), pair.currency.clone()));
            Ok(PriceResponse {
                price: self.rate,
                currency: pair.currency.clone(),
                date: rustledger_core::naive_date(2024, 1, 15).expect("valid date"),
                source: "pairs".to_string(),
            })
        }
    }

    /// A registry holding only `sources`, and a mapping of `commodity` to
    /// the chain of `(source, ticker)` entries.
    fn registry_with(
        sources: Vec<(&str, Arc<dyn PriceSource>)>,
        commodity: &str,
        chain: &[(&str, &str)],
    ) -> (PriceSourceRegistry, HashMap<String, CommodityMapping>) {
        let registry = PriceSourceRegistry {
            sources: sources
                .into_iter()
                .map(|(name, source)| (name.to_string(), source))
                .collect(),
            ..PriceSourceRegistry::default()
        };
        let entries = chain
            .iter()
            .map(|(source, ticker)| {
                FallbackEntry::Detailed(FallbackDetail {
                    source: (*source).to_string(),
                    ticker: Some((*ticker).to_string()),
                })
            })
            .collect();
        let mut mapping = HashMap::new();
        mapping.insert(
            commodity.to_string(),
            CommodityMapping::Detailed(crate::config::DetailedMapping {
                source: SourceRef::Fallback(entries),
                ticker: None,
                quote_currency: None,
            }),
        );
        (registry, mapping)
    }

    fn pair_source(rate: &str) -> Arc<PairSource> {
        use std::str::FromStr;
        Arc::new(PairSource {
            rate: Decimal::from_str(rate).expect("valid rate"),
            asked: std::sync::Mutex::new(Vec::new()),
        })
    }

    /// `EUR:pairs/^EUR-GBP` for GBP fetches EUR in GBP and writes the
    /// inverse, GBP in EUR, labeled EUR, to bean-price's 28 significant
    /// digits: `ONE / Decimal("0.83467")` in bean-price 2.1.0 is
    /// `1.198078282434974301220841770` (#2866).
    #[test]
    fn test_fetch_price_inverts_a_caret_ticker() {
        let source = pair_source("0.83467");
        let (registry, mapping) = registry_with(
            vec![("pairs", source.clone())],
            "GBP",
            &[("pairs", "^EUR-GBP")],
        );
        let response = registry
            .fetch_price("GBP", "EUR", None, &mapping)
            .expect("an inverted quote");
        assert_eq!(response.price.to_string(), "1.198078282434974301220841770");
        assert_eq!(response.currency, "EUR");
        assert_eq!(
            *source.asked.lock().expect("not poisoned"),
            vec![("EUR".to_string(), "GBP".to_string())]
        );
    }

    /// The same 28-digit rounding as Python's for quotes above and below
    /// one (values from bean-price 2.1.0's `ONE / D(x)`).
    #[test]
    fn test_invert_response_matches_python_decimal() {
        use std::str::FromStr;
        for (rate, inverse) in [
            ("1.0852", "0.9214891264283081459638776262"),
            ("3", "0.3333333333333333333333333333"),
            // Exact quotients take their shortest form, as in Python.
            ("2", "0.5"),
            ("0.25", "4"),
            ("2.50", "0.4"),
            ("8", "0.125"),
            ("0.8", "1.25"),
            // Below 0.1, rust_decimal's 28 decimal places hold two digits
            // fewer than Python's 0.006688963210702341137123745819.
            ("149.5", "0.0066889632107023411371237458"),
        ] {
            let response = PriceResponse {
                price: Decimal::from_str(rate).expect("valid rate"),
                currency: "USD".to_string(),
                date: rustledger_core::naive_date(2024, 1, 15).expect("valid date"),
                source: "pairs".to_string(),
            };
            let inverted = invert_response(response, "eur").expect("invertible");
            assert_eq!(inverted.price.to_string(), inverse, "1 / {rate}");
            assert_eq!(inverted.currency, "EUR");
        }
    }

    /// A ticker that names its pair is fetched as that pair, whatever the
    /// requested currency labels (#2866): `EUR:ratesapi/USD-EUR`.
    #[test]
    fn test_fetch_price_reads_a_pair_ticker() {
        let source = pair_source("0.88755");
        let (registry, mapping) = registry_with(
            vec![("pairs", source.clone())],
            "USD",
            &[("pairs", "USD-EUR")],
        );
        let response = registry
            .fetch_price("USD", "EUR", None, &mapping)
            .expect("a quote");
        assert_eq!(response.price.to_string(), "0.88755");
        assert_eq!(response.currency, "EUR");
        assert_eq!(
            *source.asked.lock().expect("not poisoned"),
            vec![("USD".to_string(), "EUR".to_string())]
        );
    }

    /// A zero quote has no inverse: that attempt fails, and the chain
    /// goes on to the next source.
    #[test]
    fn test_fetch_price_zero_inverse_tries_the_next_source() {
        let zero = pair_source("0");
        let good = pair_source("2");
        let (registry, mapping) = registry_with(
            vec![("zero", zero), ("good", good)],
            "GBP",
            &[("zero", "^EUR-GBP"), ("good", "^EUR-GBP")],
        );
        let response = registry
            .fetch_price("GBP", "EUR", None, &mapping)
            .expect("the second source answers");
        assert_eq!(response.price.to_string(), "0.5");

        let zero = pair_source("0");
        let (registry, mapping) =
            registry_with(vec![("zero", zero)], "GBP", &[("zero", "^EUR-GBP")]);
        let err = registry
            .fetch_price("GBP", "EUR", None, &mapping)
            .expect_err("a zero quote cannot be inverted");
        assert_eq!(
            format!("{err:#}"),
            "cannot invert the pairs price 0 GBP for `^`: it has no inverse"
        );
    }

    /// bean-price's `ecbrates` module name resolves to the ECB source.
    #[test]
    fn test_registry_has_ecbrates() {
        let registry = PriceSourceRegistry::default();
        assert_eq!(
            registry.get("ecbrates").map(|source| source.name()),
            Some("ecb")
        );
    }
}
