//! `CoinMarketCap` price source.
//!
//! Fetches cryptocurrency prices from `CoinMarketCap`.

use super::{PriceSource, user_agent};
use crate::cmd::price::{PriceRequest, PriceResponse};
use anyhow::{Context, Result};
use chrono::Utc;
use rust_decimal::Decimal;
use rustledger_core::NaiveDate;
use std::env;
use std::str::FromStr;
use std::time::Duration;

/// `CoinMarketCap` price source.
///
/// Uses `CoinMarketCap`'s API to fetch cryptocurrency prices.
/// Requires an API key set in the `CMC_API_KEY` environment variable.
///
/// # API Key
///
/// Get a free API key at <https://coinmarketcap.com/api/>
/// Set it as: `export CMC_API_KEY=your-key-here`
///
/// # Supported Symbols
///
/// All cryptocurrencies listed on `CoinMarketCap`:
/// - `BTC`, `ETH`, `SOL`, `DOGE`, etc.
#[derive(Debug)]
pub struct CoinMarketCapSource {}

impl CoinMarketCapSource {
    /// Create a new `CoinMarketCap` source.
    pub const fn new(_timeout: Duration) -> Self {
        Self {}
    }

    /// Get the API key from environment.
    fn get_api_key() -> Result<String> {
        env::var("CMC_API_KEY").with_context(|| "CMC_API_KEY environment variable not set")
    }

    /// Build the `CoinMarketCap` API URL.
    fn build_url(&self, symbol: &str, currency: &str) -> String {
        format!(
            "https://pro-api.coinmarketcap.com/v1/cryptocurrency/quotes/latest?symbol={}&convert={}",
            symbol.to_uppercase(),
            currency.to_uppercase()
        )
    }
}

impl PriceSource for CoinMarketCapSource {
    fn name(&self) -> &'static str {
        "coinmarketcap"
    }

    fn description(&self) -> &'static str {
        "CoinMarketCap - cryptocurrency prices (requires API key)"
    }

    fn requires_api_key(&self) -> bool {
        true
    }

    fn api_key_env_var(&self) -> Option<&'static str> {
        Some("CMC_API_KEY")
    }

    fn fetch_price(&self, request: &PriceRequest) -> Result<PriceResponse> {
        let api_key = Self::get_api_key()?;
        let url = self.build_url(&request.ticker, &request.currency);

        let mut response = ureq::get(&url)
            .header("User-Agent", user_agent())
            .header("X-CMC_PRO_API_KEY", &api_key)
            .header("Accept", "application/json")
            .call()
            .with_context(|| format!("Failed to fetch price for {}", request.ticker))?;

        let json: serde_json::Value = response
            .body_mut()
            .read_json()
            .with_context(|| "Failed to parse CoinMarketCap response")?;

        // Check for API errors
        let status = json
            .get("status")
            .with_context(|| "Missing status in response")?;

        if let Some(error_code) = status.get("error_code").and_then(serde_json::Value::as_i64)
            && error_code != 0
        {
            let error_message = status
                .get("error_message")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("Unknown error");
            anyhow::bail!("CoinMarketCap error: {error_message}");
        }

        let data = json
            .get("data")
            .and_then(serde_json::Value::as_object)
            .with_context(|| "Missing data in response")?;

        let symbol_upper = request.ticker.to_uppercase();
        let coin_data = data
            .get(&symbol_upper)
            .with_context(|| format!("No data for symbol: {symbol_upper}"))?;

        let quote = coin_data
            .get("quote")
            .and_then(serde_json::Value::as_object)
            .with_context(|| "Missing quote data")?;

        let currency_upper = request.currency.to_uppercase();
        let currency_quote = quote
            .get(&currency_upper)
            .with_context(|| format!("No quote for currency: {currency_upper}"))?;

        let price_value = currency_quote
            .get("price")
            .with_context(|| "Missing price in quote")?;

        let price_str = if let Some(n) = price_value.as_f64() {
            n.to_string()
        } else if let Some(s) = price_value.as_str() {
            s.to_string()
        } else {
            anyhow::bail!("Invalid price format");
        };

        let price = Decimal::from_str(&price_str)
            .with_context(|| format!("Failed to parse price: {price_str}"))?;

        let date = request.date.unwrap_or_else(|| NaiveDate::today());

        Ok(PriceResponse {
            price,
            currency: request.currency.to_uppercase(),
            date,
            source: self.name().to_string(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_build_url() {
        let source = CoinMarketCapSource::new(Duration::from_secs(30));
        let url = source.build_url("btc", "usd");
        assert!(url.contains("BTC"));
        assert!(url.contains("USD"));
        assert!(url.contains("pro-api.coinmarketcap.com"));
    }

    #[test]
    fn test_source_metadata() {
        let source = CoinMarketCapSource::new(Duration::from_secs(30));
        assert_eq!(source.name(), "coinmarketcap");
        assert!(source.requires_api_key());
        assert_eq!(source.api_key_env_var(), Some("CMC_API_KEY"));
    }
}
