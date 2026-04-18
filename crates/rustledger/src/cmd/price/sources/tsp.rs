//! Thrift Savings Plan (TSP) price source.
//!
//! Fetches TSP fund share prices from the TSP.gov website.

use super::{PriceSource, user_agent};
use crate::cmd::price::{PriceRequest, PriceResponse};
use anyhow::{Context, Result};
use chrono::Utc;
use rust_decimal::Decimal;
use rustledger_core::NaiveDate;
use std::str::FromStr;
use std::time::Duration;

/// Thrift Savings Plan price source.
///
/// Fetches share prices for TSP funds from the official TSP.gov website.
/// No API key required.
///
/// # Supported Funds
///
/// - `LFUND` - L Funds (Lifecycle)
/// - `GFUND` - G Fund (Government Securities)
/// - `FFUND` - F Fund (Fixed Income Index)
/// - `CFUND` - C Fund (Common Stock Index)
/// - `SFUND` - S Fund (Small Cap Stock Index)
/// - `IFUND` - I Fund (International Stock Index)
#[derive(Debug)]
pub struct TspSource {}

impl TspSource {
    /// Create a new TSP source.
    ///
    /// The timeout parameter is accepted for API consistency but not
    /// currently applied to HTTP requests.
    pub const fn new(_timeout: Duration) -> Self {
        Self {}
    }

    /// Normalize TSP fund name.
    fn normalize_fund(ticker: &str) -> Option<&'static str> {
        match ticker.to_uppercase().as_str() {
            "LFUND" | "L" | "LIFECYCLE" => Some("L Fund"),
            "GFUND" | "G" => Some("G Fund"),
            "FFUND" | "F" => Some("F Fund"),
            "CFUND" | "C" => Some("C Fund"),
            "SFUND" | "S" => Some("S Fund"),
            "IFUND" | "I" => Some("I Fund"),
            "L2025" => Some("L 2025"),
            "L2030" => Some("L 2030"),
            "L2035" => Some("L 2035"),
            "L2040" => Some("L 2040"),
            "L2045" => Some("L 2045"),
            "L2050" => Some("L 2050"),
            "L2055" => Some("L 2055"),
            "L2060" => Some("L 2060"),
            "L2065" => Some("L 2065"),
            "LINCOME" | "L INCOME" => Some("L Income"),
            _ => None,
        }
    }

    /// Build the TSP API URL.
    fn build_url(&self) -> String {
        "https://www.tsp.gov/data/fund-price-history.json".to_string()
    }
}

impl PriceSource for TspSource {
    fn name(&self) -> &'static str {
        "tsp"
    }

    fn description(&self) -> &'static str {
        "Thrift Savings Plan - TSP fund share prices"
    }

    fn fetch_price(&self, request: &PriceRequest) -> Result<PriceResponse> {
        let fund_name = Self::normalize_fund(&request.ticker)
            .with_context(|| format!("Unknown TSP fund: {}", request.ticker))?;

        let url = self.build_url();

        let mut response = ureq::get(&url)
            .header("User-Agent", user_agent())
            .call()
            .with_context(|| "Failed to fetch TSP prices")?;

        let json: serde_json::Value = response
            .body_mut()
            .read_json()
            .with_context(|| "Failed to parse TSP response")?;

        // The TSP API returns an array of daily prices
        let data = json
            .as_array()
            .with_context(|| "Invalid TSP response format")?;

        // Get the most recent entry
        let latest = data.last().with_context(|| "No price data available")?;

        // Find the price for our fund
        let fund_key = fund_name.replace(' ', "");

        let price_value = latest
            .get(&fund_key)
            .or_else(|| latest.get(fund_name))
            .with_context(|| format!("Fund {fund_name} not found in TSP data"))?;

        let price_str = if let Some(n) = price_value.as_f64() {
            n.to_string()
        } else if let Some(s) = price_value.as_str() {
            s.to_string()
        } else {
            anyhow::bail!("Invalid price format for {fund_name}");
        };

        let price = Decimal::from_str(&price_str)
            .with_context(|| format!("Failed to parse price: {price_str}"))?;

        // Get the date from the response
        let date = latest
            .get("date")
            .and_then(serde_json::Value::as_str)
            .and_then(|s| NaiveDate::parse_from_str(s, "%Y-%m-%d").ok())
            .unwrap_or_else(|| request.date.unwrap_or_else(|| NaiveDate::today()));

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
    fn test_normalize_fund() {
        assert_eq!(TspSource::normalize_fund("CFUND"), Some("C Fund"));
        assert_eq!(TspSource::normalize_fund("C"), Some("C Fund"));
        assert_eq!(TspSource::normalize_fund("cfund"), Some("C Fund"));
        assert_eq!(TspSource::normalize_fund("L2030"), Some("L 2030"));
        assert_eq!(TspSource::normalize_fund("UNKNOWN"), None);
    }

    #[test]
    fn test_build_url() {
        let source = TspSource::new(Duration::from_secs(30));
        let url = source.build_url();
        assert!(url.contains("tsp.gov"));
    }

    #[test]
    fn test_source_metadata() {
        let source = TspSource::new(Duration::from_secs(30));
        assert_eq!(source.name(), "tsp");
        assert!(!source.requires_api_key());
    }
}
