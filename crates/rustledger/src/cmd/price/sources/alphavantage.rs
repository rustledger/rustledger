//! Alpha Vantage price source.
//!
//! Fetches stock, forex, and crypto prices from Alpha Vantage.

use super::{PriceSource, user_agent};
use crate::cmd::price::{PriceRequest, PriceResponse};
use anyhow::{Context, Result};
use chrono::Utc;
use rust_decimal::Decimal;
use rustledger_core::NaiveDate;
use std::env;
use std::str::FromStr;
use std::time::Duration;

/// Alpha Vantage price source.
///
/// Uses Alpha Vantage's API to fetch stock quotes, forex rates, and crypto prices.
/// Requires an API key set in the `ALPHAVANTAGE_API_KEY` environment variable.
///
/// # API Key
///
/// Get a free API key at <https://www.alphavantage.co/support/#api-key>
/// Set it as: `export ALPHAVANTAGE_API_KEY=your-key-here`
///
/// # Supported Symbols
///
/// - Stocks: `AAPL`, `MSFT`, `GOOGL`
/// - Forex: Use `from_currency/to_currency` format (e.g., `EUR/USD`)
/// - Crypto: Use `CRYPTO:symbol` format (e.g., `CRYPTO:BTC`)
#[derive(Debug)]
pub struct AlphaVantageSource {}

impl AlphaVantageSource {
    /// Create a new Alpha Vantage source.
    pub const fn new(_timeout: Duration) -> Self {
        Self {}
    }

    /// Get the API key from environment.
    fn get_api_key() -> Result<String> {
        env::var("ALPHAVANTAGE_API_KEY")
            .with_context(|| "ALPHAVANTAGE_API_KEY environment variable not set")
    }

    /// Build the Alpha Vantage API URL for stocks.
    fn build_stock_url(&self, symbol: &str, api_key: &str) -> String {
        format!(
            "https://www.alphavantage.co/query?function=GLOBAL_QUOTE&symbol={symbol}&apikey={api_key}"
        )
    }

    /// Build the Alpha Vantage API URL for forex.
    fn build_forex_url(&self, from: &str, to: &str, api_key: &str) -> String {
        format!(
            "https://www.alphavantage.co/query?function=CURRENCY_EXCHANGE_RATE&from_currency={from}&to_currency={to}&apikey={api_key}"
        )
    }

    /// Build the Alpha Vantage API URL for crypto.
    fn build_crypto_url(&self, symbol: &str, market: &str, api_key: &str) -> String {
        format!(
            "https://www.alphavantage.co/query?function=CURRENCY_EXCHANGE_RATE&from_currency={symbol}&to_currency={market}&apikey={api_key}"
        )
    }

    /// Determine the type of request and fetch accordingly.
    fn fetch_internal(&self, request: &PriceRequest, api_key: &str) -> Result<PriceResponse> {
        let ticker = &request.ticker;

        // Check for crypto prefix
        if let Some(symbol) = ticker.strip_prefix("CRYPTO:") {
            return self.fetch_crypto(symbol, &request.currency, api_key);
        }

        // Check for forex format (contains /)
        if ticker.contains('/') {
            let parts: Vec<&str> = ticker.split('/').collect();
            if parts.len() == 2 {
                return self.fetch_forex(parts[0], parts[1], api_key);
            }
        }

        // Default to stock
        self.fetch_stock(ticker, &request.currency, api_key)
    }

    fn fetch_stock(&self, symbol: &str, currency: &str, api_key: &str) -> Result<PriceResponse> {
        let url = self.build_stock_url(symbol, api_key);

        let mut response = ureq::get(&url)
            .header("User-Agent", user_agent())
            .call()
            .with_context(|| format!("Failed to fetch quote for {symbol}"))?;

        let json: serde_json::Value = response
            .body_mut()
            .read_json()
            .with_context(|| "Failed to parse Alpha Vantage response")?;

        // Check for API errors
        if let Some(note) = json.get("Note") {
            let msg = note.as_str().unwrap_or("API limit reached");
            anyhow::bail!("Alpha Vantage: {msg}");
        }
        if let Some(error) = json.get("Error Message") {
            let msg = error.as_str().unwrap_or("Unknown error");
            anyhow::bail!("Alpha Vantage error: {msg}");
        }

        let quote = json
            .get("Global Quote")
            .with_context(|| "Missing Global Quote in response")?;

        let price_str = quote
            .get("05. price")
            .and_then(serde_json::Value::as_str)
            .with_context(|| "Missing price in quote")?;

        let price = Decimal::from_str(price_str)
            .with_context(|| format!("Failed to parse price: {price_str}"))?;

        let date = NaiveDate::today();

        Ok(PriceResponse {
            price,
            currency: currency.to_string(),
            date,
            source: self.name().to_string(),
        })
    }

    fn fetch_forex(&self, from: &str, to: &str, api_key: &str) -> Result<PriceResponse> {
        let url = self.build_forex_url(from, to, api_key);

        let mut response = ureq::get(&url)
            .header("User-Agent", user_agent())
            .call()
            .with_context(|| format!("Failed to fetch rate for {from}/{to}"))?;

        let json: serde_json::Value = response
            .body_mut()
            .read_json()
            .with_context(|| "Failed to parse Alpha Vantage response")?;

        let rate_data = json
            .get("Realtime Currency Exchange Rate")
            .with_context(|| "Missing exchange rate data")?;

        let price_str = rate_data
            .get("5. Exchange Rate")
            .and_then(serde_json::Value::as_str)
            .with_context(|| "Missing exchange rate")?;

        let price = Decimal::from_str(price_str)
            .with_context(|| format!("Failed to parse rate: {price_str}"))?;

        let date = NaiveDate::today();

        Ok(PriceResponse {
            price,
            currency: to.to_string(),
            date,
            source: self.name().to_string(),
        })
    }

    fn fetch_crypto(&self, symbol: &str, market: &str, api_key: &str) -> Result<PriceResponse> {
        let url = self.build_crypto_url(symbol, market, api_key);

        let mut response = ureq::get(&url)
            .header("User-Agent", user_agent())
            .call()
            .with_context(|| format!("Failed to fetch crypto price for {symbol}"))?;

        let json: serde_json::Value = response
            .body_mut()
            .read_json()
            .with_context(|| "Failed to parse Alpha Vantage response")?;

        let rate_data = json
            .get("Realtime Currency Exchange Rate")
            .with_context(|| "Missing crypto price data")?;

        let price_str = rate_data
            .get("5. Exchange Rate")
            .and_then(serde_json::Value::as_str)
            .with_context(|| "Missing crypto price")?;

        let price = Decimal::from_str(price_str)
            .with_context(|| format!("Failed to parse price: {price_str}"))?;

        let date = NaiveDate::today();

        Ok(PriceResponse {
            price,
            currency: market.to_string(),
            date,
            source: self.name().to_string(),
        })
    }
}

impl PriceSource for AlphaVantageSource {
    fn name(&self) -> &'static str {
        "alphavantage"
    }

    fn description(&self) -> &'static str {
        "Alpha Vantage - stocks, forex, crypto (requires API key)"
    }

    fn requires_api_key(&self) -> bool {
        true
    }

    fn api_key_env_var(&self) -> Option<&'static str> {
        Some("ALPHAVANTAGE_API_KEY")
    }

    fn fetch_price(&self, request: &PriceRequest) -> Result<PriceResponse> {
        let api_key = Self::get_api_key()?;
        self.fetch_internal(request, &api_key)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_build_stock_url() {
        let source = AlphaVantageSource::new(Duration::from_secs(30));
        let url = source.build_stock_url("AAPL", "demo");
        assert!(url.contains("AAPL"));
        assert!(url.contains("GLOBAL_QUOTE"));
    }

    #[test]
    fn test_build_forex_url() {
        let source = AlphaVantageSource::new(Duration::from_secs(30));
        let url = source.build_forex_url("EUR", "USD", "demo");
        assert!(url.contains("EUR"));
        assert!(url.contains("USD"));
        assert!(url.contains("CURRENCY_EXCHANGE_RATE"));
    }

    #[test]
    fn test_source_metadata() {
        let source = AlphaVantageSource::new(Duration::from_secs(30));
        assert_eq!(source.name(), "alphavantage");
        assert!(source.requires_api_key());
        assert_eq!(source.api_key_env_var(), Some("ALPHAVANTAGE_API_KEY"));
    }
}
