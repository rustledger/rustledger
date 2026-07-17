//! Quandl (Nasdaq Data Link) price source.
//!
//! Fetches financial data from Quandl/Nasdaq Data Link.

use super::{PriceSource, user_agent};
use crate::cmd::price::{PriceRequest, PriceResponse};
use anyhow::{Context, Result};
use std::env;
use std::time::Duration;

/// Quandl (Nasdaq Data Link) price source.
///
/// Uses Nasdaq Data Link's API (formerly Quandl) to fetch financial data.
/// Requires an API key set in the `QUANDL_API_KEY` environment variable.
///
/// # API Key
///
/// Get a free API key at <https://data.nasdaq.com/>
/// Set it as: `export QUANDL_API_KEY=your-key-here`
///
/// # Supported Datasets
///
/// Uses the format `DATABASE/DATASET` for tickers:
/// - `WIKI/AAPL` - Wiki EOD Stock Prices
/// - `LBMA/GOLD` - London Bullion Market Gold Price
/// - `FRED/GDP` - Federal Reserve Economic Data
/// - `CHRIS/CME_CL1` - CME Crude Oil Futures
#[derive(Debug)]
pub struct QuandlSource {}

impl QuandlSource {
    /// Create a new Quandl source.
    ///
    /// The timeout parameter is accepted for API consistency but not
    /// currently applied to HTTP requests.
    pub const fn new(_timeout: Duration) -> Self {
        Self {}
    }

    /// Get the API key from environment.
    fn get_api_key() -> Result<String> {
        env::var("QUANDL_API_KEY").with_context(|| "QUANDL_API_KEY environment variable not set")
    }

    /// Build the Quandl API URL.
    fn build_url(&self, dataset: &str, api_key: &str) -> String {
        format!(
            "https://data.nasdaq.com/api/v3/datasets/{dataset}/data.json?limit=1&api_key={api_key}"
        )
    }

    /// Parse the dataset identifier.
    fn parse_dataset(ticker: &str) -> (&str, &str) {
        if let Some(pos) = ticker.find('/') {
            (&ticker[..pos], &ticker[pos + 1..])
        } else {
            ("WIKI", ticker)
        }
    }
}

impl PriceSource for QuandlSource {
    fn name(&self) -> &'static str {
        "quandl"
    }

    fn description(&self) -> &'static str {
        "Nasdaq Data Link (Quandl) - financial datasets (requires API key)"
    }

    fn requires_api_key(&self) -> bool {
        true
    }

    fn api_key_env_var(&self) -> Option<&'static str> {
        Some("QUANDL_API_KEY")
    }

    fn fetch_price(&self, request: &PriceRequest) -> Result<PriceResponse> {
        // Latest-only source: a historical --date must refuse, not
        // mislabel the current quote (#1794).
        super::reject_historical_date(self.name(), request)?;

        let api_key = Self::get_api_key()?;
        let (database, dataset) = Self::parse_dataset(&request.ticker);
        let full_dataset = format!("{database}/{dataset}");
        let url = self.build_url(&full_dataset, &api_key);

        let mut response = ureq::get(&url)
            .header("User-Agent", user_agent())
            .call()
            .with_context(|| format!("Failed to fetch data for {}", request.ticker))?;

        let json: serde_json::Value = response
            .body_mut()
            .read_json()
            .with_context(|| "Failed to parse Quandl response")?;

        // Check for errors
        if let Some(quandl_error) = json.get("quandl_error") {
            let code = quandl_error
                .get("code")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("UNKNOWN");
            let message = quandl_error
                .get("message")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("Unknown error");
            anyhow::bail!("Quandl error {code}: {message}");
        }

        let dataset_data = json
            .get("dataset_data")
            .with_context(|| "Missing dataset_data in response")?;

        let data = dataset_data
            .get("data")
            .and_then(serde_json::Value::as_array)
            .and_then(|a| a.first())
            .and_then(serde_json::Value::as_array)
            .with_context(|| "No data available")?;

        let column_names = dataset_data
            .get("column_names")
            .and_then(serde_json::Value::as_array)
            .with_context(|| "Missing column names")?;

        // Find the date column (usually first)
        let date_idx = column_names
            .iter()
            .position(|c| {
                c.as_str()
                    .is_some_and(|s| s.to_lowercase().contains("date"))
            })
            .unwrap_or(0);

        // Find a price column (Close, Value, Price, etc.)
        let price_idx = column_names
            .iter()
            .position(|c| {
                c.as_str().is_some_and(|s| {
                    let lower = s.to_lowercase();
                    lower.contains("close")
                        || lower.contains("value")
                        || lower.contains("price")
                        || lower.contains("settle")
                })
            })
            .with_context(|| "No price column found in dataset")?;

        // The feed's own date, never the requested one (#1794; the old
        // request.date fallback was the exact mislabeling pattern this
        // PR removes — round-3 deep review).
        let date =
            super::feed_date_or_today(data.get(date_idx).and_then(serde_json::Value::as_str));

        // Extract price
        let price_value = data.get(price_idx).with_context(|| "Missing price value")?;

        let price = crate::cmd::price::price_decimal_from_json(price_value)
            .with_context(|| format!("Invalid price format: {price_value}"))?;

        Ok(PriceResponse {
            price,
            currency: request.currency.clone(),
            date,
            source: self.name().to_string(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_dataset() {
        assert_eq!(QuandlSource::parse_dataset("WIKI/AAPL"), ("WIKI", "AAPL"));
        assert_eq!(QuandlSource::parse_dataset("LBMA/GOLD"), ("LBMA", "GOLD"));
        assert_eq!(QuandlSource::parse_dataset("AAPL"), ("WIKI", "AAPL"));
    }

    #[test]
    fn test_build_url() {
        let source = QuandlSource::new(Duration::from_secs(30));
        let url = source.build_url("WIKI/AAPL", "demo");
        assert!(url.contains("WIKI/AAPL"));
        assert!(url.contains("data.nasdaq.com"));
    }

    #[test]
    fn test_source_metadata() {
        let source = QuandlSource::new(Duration::from_secs(30));
        assert_eq!(source.name(), "quandl");
        assert!(source.requires_api_key());
        assert_eq!(source.api_key_env_var(), Some("QUANDL_API_KEY"));
    }
}
