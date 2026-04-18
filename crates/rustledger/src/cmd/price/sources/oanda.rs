//! OANDA price source.
//!
//! Fetches forex rates from OANDA's API.

use super::{PriceSource, user_agent};
use crate::cmd::price::{PriceRequest, PriceResponse};
use anyhow::{Context, Result};
use chrono::Utc;
use rust_decimal::Decimal;
use rustledger_core::NaiveDate;
use std::env;
use std::str::FromStr;
use std::time::Duration;

/// OANDA price source.
///
/// Uses OANDA's REST API to fetch forex rates.
/// Requires an API key set in the `OANDA_API_KEY` environment variable.
///
/// # API Key
///
/// Sign up at <https://oanda.com> for an API key.
/// Set it as: `export OANDA_API_KEY=your-key-here`
///
/// # Supported Pairs
///
/// All major and minor forex pairs:
/// - `EUR_USD`, `GBP_USD`, `USD_JPY`, etc.
#[derive(Debug)]
pub struct OandaSource {}

impl OandaSource {
    /// Create a new OANDA source.
    ///
    /// The timeout parameter is accepted for API consistency but not
    /// currently applied to HTTP requests.
    pub const fn new(_timeout: Duration) -> Self {
        Self {}
    }

    /// Get the API key from environment.
    fn get_api_key() -> Result<String> {
        env::var("OANDA_API_KEY").with_context(|| "OANDA_API_KEY environment variable not set")
    }

    /// Build the OANDA API URL.
    fn build_url(&self, instrument: &str) -> String {
        format!(
            "https://api-fxpractice.oanda.com/v3/instruments/{instrument}/candles?count=1&granularity=D"
        )
    }

    /// Format currency pair for OANDA.
    fn format_instrument(ticker: &str, currency: &str) -> String {
        if ticker.contains('_') {
            ticker.to_uppercase()
        } else {
            format!("{}_{}", ticker.to_uppercase(), currency.to_uppercase())
        }
    }
}

impl PriceSource for OandaSource {
    fn name(&self) -> &'static str {
        "oanda"
    }

    fn description(&self) -> &'static str {
        "OANDA - forex rates (requires API key)"
    }

    fn requires_api_key(&self) -> bool {
        true
    }

    fn api_key_env_var(&self) -> Option<&'static str> {
        Some("OANDA_API_KEY")
    }

    fn fetch_price(&self, request: &PriceRequest) -> Result<PriceResponse> {
        let api_key = Self::get_api_key()?;
        let instrument = Self::format_instrument(&request.ticker, &request.currency);
        let url = self.build_url(&instrument);

        let mut response = ureq::get(&url)
            .header("User-Agent", user_agent())
            .header("Authorization", &format!("Bearer {api_key}"))
            .header("Accept-Datetime-Format", "RFC3339")
            .call()
            .with_context(|| format!("Failed to fetch rate for {instrument}"))?;

        let json: serde_json::Value = response
            .body_mut()
            .read_json()
            .with_context(|| "Failed to parse OANDA response")?;

        // Check for errors
        if let Some(error_message) = json.get("errorMessage") {
            let msg = error_message.as_str().unwrap_or("Unknown error");
            anyhow::bail!("OANDA error: {msg}");
        }

        let candles = json
            .get("candles")
            .and_then(serde_json::Value::as_array)
            .with_context(|| "Missing candles in response")?;

        let candle = candles
            .first()
            .with_context(|| "No candle data available")?;

        let mid = candle
            .get("mid")
            .with_context(|| "Missing mid price in candle")?;

        let close_str = mid
            .get("c")
            .and_then(serde_json::Value::as_str)
            .with_context(|| "Missing close price")?;

        let price = Decimal::from_str(close_str)
            .with_context(|| format!("Failed to parse price: {close_str}"))?;

        let date = request.date.unwrap_or_else(|| NaiveDate::today());

        let target_currency = if instrument.contains('_') {
            instrument
                .split('_')
                .next_back()
                .unwrap_or(&request.currency)
        } else {
            &request.currency
        };

        Ok(PriceResponse {
            price,
            currency: target_currency.to_string(),
            date,
            source: self.name().to_string(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_format_instrument() {
        assert_eq!(OandaSource::format_instrument("EUR", "USD"), "EUR_USD");
        assert_eq!(OandaSource::format_instrument("eur_usd", "GBP"), "EUR_USD");
        assert_eq!(OandaSource::format_instrument("GBP", "JPY"), "GBP_JPY");
    }

    #[test]
    fn test_build_url() {
        let source = OandaSource::new(Duration::from_secs(30));
        let url = source.build_url("EUR_USD");
        assert!(url.contains("EUR_USD"));
        assert!(url.contains("oanda.com"));
    }

    #[test]
    fn test_source_metadata() {
        let source = OandaSource::new(Duration::from_secs(30));
        assert_eq!(source.name(), "oanda");
        assert!(source.requires_api_key());
        assert_eq!(source.api_key_env_var(), Some("OANDA_API_KEY"));
    }
}
