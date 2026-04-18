//! Yahoo Finance price source.
//!
//! Fetches stock, ETF, and cryptocurrency prices from Yahoo Finance.

use super::{PriceSource, user_agent};
use crate::cmd::price::{PriceRequest, PriceResponse};
use anyhow::{Context, Result};
use chrono::Utc;
use rust_decimal::Decimal;
use rustledger_core::NaiveDate;
use std::str::FromStr;
use std::time::Duration;

/// Yahoo Finance price source.
///
/// Uses the Yahoo Finance API to fetch prices for stocks, ETFs, mutual funds,
/// and cryptocurrencies.
///
/// # Supported Symbols
///
/// - Stocks: `AAPL`, `MSFT`, `GOOGL`
/// - ETFs: `VTI`, `SPY`, `QQQ`
/// - Cryptocurrencies: `BTC-USD`, `ETH-USD`
/// - Forex: `EURUSD=X`, `GBPUSD=X`
/// - Mutual funds: Fund symbols
#[derive(Debug)]
pub struct YahooFinanceSource {}

impl YahooFinanceSource {
    /// Create a new Yahoo Finance source.
    pub const fn new(_timeout: Duration) -> Self {
        Self {}
    }

    /// Build the Yahoo Finance API URL.
    fn build_url(&self, symbol: &str) -> String {
        format!("https://query1.finance.yahoo.com/v8/finance/chart/{symbol}?interval=1d&range=1d")
    }
}

impl PriceSource for YahooFinanceSource {
    fn name(&self) -> &'static str {
        "yahoo"
    }

    fn description(&self) -> &'static str {
        "Yahoo Finance - stocks, ETFs, crypto, forex"
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

        // Check for errors in the response
        if let Some(chart) = json.get("chart")
            && let Some(error) = chart.get("error")
            && !error.is_null()
        {
            let description = error
                .get("description")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("Unknown error");
            anyhow::bail!("Yahoo Finance error: {description}");
        }

        // Navigate to the price in the response
        let meta = json
            .get("chart")
            .and_then(|c| c.get("result"))
            .and_then(|r| r.get(0))
            .and_then(|r| r.get("meta"))
            .with_context(|| format!("Invalid response structure for {}", request.ticker))?;

        let price_value = meta
            .get("regularMarketPrice")
            .with_context(|| format!("No price found for {}", request.ticker))?;

        // Parse directly from JSON number representation to avoid f64 precision loss
        let price_str = match price_value {
            serde_json::Value::Number(n) => n.to_string(),
            serde_json::Value::String(s) => s.clone(),
            _ => anyhow::bail!("Invalid price format for {}", request.ticker),
        };

        let price = Decimal::from_str(&price_str)
            .with_context(|| format!("Failed to convert price {price_str} to decimal"))?;

        // Get the currency from the response
        let currency = meta
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
        let source = YahooFinanceSource::new(Duration::from_secs(30));
        let url = source.build_url("AAPL");
        assert!(url.contains("AAPL"));
        assert!(url.contains("query1.finance.yahoo.com"));
    }

    #[test]
    fn test_source_metadata() {
        let source = YahooFinanceSource::new(Duration::from_secs(30));
        assert_eq!(source.name(), "yahoo");
        assert!(!source.requires_api_key());
        assert!(source.description().contains("Yahoo"));
    }
}
