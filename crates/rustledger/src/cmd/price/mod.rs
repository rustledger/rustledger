//! Price fetching module for rustledger.
//!
//! This module provides a pluggable price source system that supports:
//! - Built-in sources (Yahoo Finance, Coinbase, ECB, etc.)
//! - External command sources for custom integrations
//! - Configurable commodity-to-source mappings
//! - Fallback chains for reliability

pub mod cache;
pub mod external;
pub mod sources;

use crate::config::{CommodityMapping, PriceConfig, PriceSourceConfig, SourceRef};
use anyhow::{Context, Result};
use chrono::NaiveDate;
use rust_decimal::Decimal;
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

/// Registry of available price sources.
pub struct PriceSourceRegistry {
    sources: HashMap<String, Arc<dyn PriceSource>>,
    default_source: String,
    timeout: Duration,
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
        sources.insert(
            "ecb".to_string(),
            Arc::new(sources::EcbSource::new(timeout)),
        );
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
    /// This method resolves the commodity to the appropriate source and ticker
    /// based on the configuration, then fetches the price.
    pub fn fetch_price(
        &self,
        commodity: &str,
        currency: &str,
        date: Option<NaiveDate>,
        mapping: &HashMap<String, CommodityMapping>,
    ) -> Result<PriceResponse> {
        let (source_names, ticker) = self.resolve_mapping(commodity, mapping);

        let mut last_error = None;
        let mut unknown_sources = Vec::new();

        for source_name in &source_names {
            if let Some(source) = self.get(source_name) {
                let request = PriceRequest {
                    ticker: ticker.clone(),
                    currency: currency.to_string(),
                    date,
                };

                match source.fetch_price(&request) {
                    Ok(response) => return Ok(response),
                    Err(e) => {
                        last_error = Some(e);
                        // Try next source in fallback chain
                    }
                }
            } else {
                // Track unknown sources for error reporting
                unknown_sources.push(source_name.clone());
            }
        }

        // Build an informative error message
        let err_msg = if let Some(e) = last_error {
            if unknown_sources.is_empty() {
                e
            } else {
                anyhow::anyhow!(
                    "{}; note: unknown sources skipped: {}",
                    e,
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

    /// Resolve a commodity to its source(s) and ticker.
    fn resolve_mapping(
        &self,
        commodity: &str,
        mapping: &HashMap<String, CommodityMapping>,
    ) -> (Vec<String>, String) {
        if let Some(commodity_mapping) = mapping.get(commodity) {
            match commodity_mapping {
                CommodityMapping::Simple(ticker) => {
                    (vec![self.default_source.clone()], ticker.clone())
                }
                CommodityMapping::Detailed { source, ticker } => {
                    let ticker = ticker.clone().unwrap_or_else(|| commodity.to_string());
                    let sources = match source {
                        SourceRef::Single(s) => vec![s.clone()],
                        SourceRef::Fallback(sources) => sources.clone(),
                    };
                    (sources, ticker)
                }
            }
        } else {
            // No mapping - use default source with commodity as ticker
            (vec![self.default_source.clone()], commodity.to_string())
        }
    }
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

    #[test]
    fn test_price_request_builder() {
        let request = PriceRequest::new("AAPL", "USD");
        assert_eq!(request.ticker, "AAPL");
        assert_eq!(request.currency, "USD");
        assert!(request.date.is_none());

        let date = NaiveDate::from_ymd_opt(2024, 1, 15).unwrap();
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

        let (sources, ticker) = registry.resolve_mapping("BTC", &mapping);
        assert_eq!(sources, vec!["yahoo"]);
        assert_eq!(ticker, "BTC-USD");
    }

    #[test]
    fn test_resolve_mapping_detailed() {
        let registry = PriceSourceRegistry::default();
        let mut mapping = HashMap::new();
        mapping.insert(
            "EUR".to_string(),
            CommodityMapping::Detailed {
                source: SourceRef::Fallback(vec!["ecb".to_string(), "ratesapi".to_string()]),
                ticker: None,
            },
        );

        let (sources, ticker) = registry.resolve_mapping("EUR", &mapping);
        assert_eq!(sources, vec!["ecb", "ratesapi"]);
        assert_eq!(ticker, "EUR");
    }

    #[test]
    fn test_resolve_mapping_no_mapping() {
        let registry = PriceSourceRegistry::default();
        let mapping = HashMap::new();

        let (sources, ticker) = registry.resolve_mapping("AAPL", &mapping);
        assert_eq!(sources, vec!["yahoo"]);
        assert_eq!(ticker, "AAPL");
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
}
