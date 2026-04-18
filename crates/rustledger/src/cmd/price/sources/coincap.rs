//! `CoinCap` price source.
//!
//! Fetches cryptocurrency prices from `CoinCap`.

use super::{PriceSource, user_agent};
use crate::cmd::price::{PriceRequest, PriceResponse};
use anyhow::{Context, Result};
use chrono::Utc;
use rust_decimal::Decimal;
use rustledger_core::NaiveDate;
use std::str::FromStr;
use std::time::Duration;

/// `CoinCap` price source.
///
/// Uses the `CoinCap` API (coincap.io) to fetch cryptocurrency prices.
/// Free tier with no API key required.
///
/// # Supported Symbols
///
/// - Cryptocurrencies by ID: `bitcoin`, `ethereum`, `solana`
/// - Also supports uppercase symbols which are converted to lowercase IDs
#[derive(Debug)]
pub struct CoinCapSource {}

impl CoinCapSource {
    /// Create a new `CoinCap` source.
    pub const fn new(_timeout: Duration) -> Self {
        Self {}
    }

    /// Convert ticker to `CoinCap` asset ID.
    fn ticker_to_id(ticker: &str) -> String {
        // Common mappings from symbol to CoinCap ID
        match ticker.to_uppercase().as_str() {
            "BTC" => "bitcoin".to_string(),
            "ETH" => "ethereum".to_string(),
            "SOL" => "solana".to_string(),
            "DOGE" => "dogecoin".to_string(),
            "ADA" => "cardano".to_string(),
            "XRP" => "xrp".to_string(),
            "DOT" => "polkadot".to_string(),
            "AVAX" => "avalanche".to_string(),
            "MATIC" => "polygon".to_string(),
            "LINK" => "chainlink".to_string(),
            "UNI" => "uniswap".to_string(),
            "LTC" => "litecoin".to_string(),
            "BCH" => "bitcoin-cash".to_string(),
            "ATOM" => "cosmos".to_string(),
            "XLM" => "stellar".to_string(),
            "ALGO" => "algorand".to_string(),
            "VET" => "vechain".to_string(),
            "FIL" => "filecoin".to_string(),
            "TRX" => "tron".to_string(),
            "ETC" => "ethereum-classic".to_string(),
            _ => ticker.to_lowercase(),
        }
    }

    /// Build the `CoinCap` API URL.
    fn build_url(&self, ticker: &str) -> String {
        let id = Self::ticker_to_id(ticker);
        format!("https://api.coincap.io/v2/assets/{id}")
    }
}

impl PriceSource for CoinCapSource {
    fn name(&self) -> &'static str {
        "coincap"
    }

    fn description(&self) -> &'static str {
        "CoinCap - cryptocurrency prices"
    }

    fn fetch_price(&self, request: &PriceRequest) -> Result<PriceResponse> {
        let url = self.build_url(&request.ticker);

        let mut response = ureq::get(&url)
            .header("User-Agent", user_agent())
            .call()
            .with_context(|| format!("Failed to fetch price for {}", request.ticker))?;

        let json: serde_json::Value = response
            .body_mut()
            .read_json()
            .with_context(|| format!("Failed to parse response for {}", request.ticker))?;

        // Check for errors
        if let Some(error) = json.get("error") {
            let message = error.as_str().unwrap_or("Unknown error");
            anyhow::bail!("CoinCap error: {message}");
        }

        let data = json
            .get("data")
            .with_context(|| "Missing 'data' field in response")?;

        let price_str = data
            .get("priceUsd")
            .and_then(serde_json::Value::as_str)
            .with_context(|| "Missing 'priceUsd' field in response")?;

        let price = Decimal::from_str(price_str)
            .with_context(|| format!("Failed to parse price: {price_str}"))?;

        let date = request.date.unwrap_or_else(|| NaiveDate::today());

        // CoinCap only provides USD prices
        Ok(PriceResponse {
            price,
            currency: "USD".to_string(),
            date,
            source: self.name().to_string(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ticker_to_id() {
        assert_eq!(CoinCapSource::ticker_to_id("BTC"), "bitcoin");
        assert_eq!(CoinCapSource::ticker_to_id("btc"), "bitcoin");
        assert_eq!(CoinCapSource::ticker_to_id("ETH"), "ethereum");
        assert_eq!(CoinCapSource::ticker_to_id("unknown"), "unknown");
    }

    #[test]
    fn test_build_url() {
        let source = CoinCapSource::new(Duration::from_secs(30));
        let url = source.build_url("BTC");
        assert_eq!(url, "https://api.coincap.io/v2/assets/bitcoin");
    }

    #[test]
    fn test_source_metadata() {
        let source = CoinCapSource::new(Duration::from_secs(30));
        assert_eq!(source.name(), "coincap");
        assert!(!source.requires_api_key());
    }
}
