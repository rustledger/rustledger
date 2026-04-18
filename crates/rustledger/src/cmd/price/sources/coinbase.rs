//! Coinbase price source.
//!
//! Fetches cryptocurrency prices from Coinbase.

use super::{PriceSource, user_agent};
use crate::cmd::price::{PriceRequest, PriceResponse};
use anyhow::{Context, Result};
use chrono::Utc;
use rust_decimal::Decimal;
use rustledger_core::NaiveDate;
use std::str::FromStr;
use std::time::Duration;

/// Coinbase price source.
///
/// Uses the Coinbase API to fetch cryptocurrency spot prices.
/// No API key required for read-only access.
///
/// # Supported Symbols
///
/// - Cryptocurrencies: `BTC`, `ETH`, `SOL`, etc.
/// - Format: Uses `{CRYPTO}-{CURRENCY}` pairs (e.g., `BTC-USD`)
#[derive(Debug)]
pub struct CoinbaseSource {}

impl CoinbaseSource {
    /// Create a new Coinbase source.
    ///
    /// The timeout parameter is accepted for API consistency but not
    /// currently applied to HTTP requests.
    pub const fn new(_timeout: Duration) -> Self {
        Self {}
    }

    /// Build the Coinbase API URL.
    fn build_url(&self, ticker: &str, currency: &str) -> String {
        // If the ticker already contains a dash, use it directly
        // Otherwise, append the currency
        let pair = if ticker.contains('-') {
            ticker.to_string()
        } else {
            format!("{ticker}-{currency}")
        };
        format!("https://api.coinbase.com/v2/prices/{pair}/spot")
    }
}

impl PriceSource for CoinbaseSource {
    fn name(&self) -> &'static str {
        "coinbase"
    }

    fn description(&self) -> &'static str {
        "Coinbase - cryptocurrency spot prices"
    }

    fn fetch_price(&self, request: &PriceRequest) -> Result<PriceResponse> {
        let url = self.build_url(&request.ticker, &request.currency);

        let mut response = ureq::get(&url)
            .header("User-Agent", user_agent())
            .call()
            .with_context(|| format!("Failed to fetch price for {}", request.ticker))?;

        let json: serde_json::Value = response
            .body_mut()
            .read_json()
            .with_context(|| format!("Failed to parse response for {}", request.ticker))?;

        // Check for errors
        if let Some(errors) = json.get("errors")
            && let Some(first_error) = errors.as_array().and_then(|arr| arr.first())
        {
            let message = first_error
                .get("message")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("Unknown error");
            anyhow::bail!("Coinbase error: {message}");
        }

        let data = json
            .get("data")
            .with_context(|| "Missing 'data' field in response")?;

        let price_str = data
            .get("amount")
            .and_then(serde_json::Value::as_str)
            .with_context(|| "Missing 'amount' field in response")?;

        let price = Decimal::from_str(price_str)
            .with_context(|| format!("Failed to parse price: {price_str}"))?;

        let currency = data
            .get("currency")
            .and_then(serde_json::Value::as_str)
            .unwrap_or(&request.currency)
            .to_string();

        let date = request.date.unwrap_or_else(|| NaiveDate::today());

        Ok(PriceResponse {
            price,
            currency,
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
        let source = CoinbaseSource::new(Duration::from_secs(30));

        let url = source.build_url("BTC", "USD");
        assert_eq!(url, "https://api.coinbase.com/v2/prices/BTC-USD/spot");

        let url = source.build_url("BTC-EUR", "USD");
        assert_eq!(url, "https://api.coinbase.com/v2/prices/BTC-EUR/spot");
    }

    #[test]
    fn test_source_metadata() {
        let source = CoinbaseSource::new(Duration::from_secs(30));
        assert_eq!(source.name(), "coinbase");
        assert!(!source.requires_api_key());
    }
}
