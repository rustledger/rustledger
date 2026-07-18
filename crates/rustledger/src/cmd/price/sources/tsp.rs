//! Thrift Savings Plan (TSP) price source.
//!
//! Fetches TSP fund share prices from the TSP.gov website.

use super::{DateWindow, HistoricalCoverage, PricePair, PricePoint, PriceSource, user_agent};
use crate::cmd::price::PriceResponse;
use anyhow::{Context, Result};
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

    /// Fetch the full daily price-history array the endpoint serves —
    /// one JSON object per trading day, shared by the latest and
    /// window paths (#1802 source ports). There is no dated query
    /// parameter; both paths slice this same array.
    fn fetch_history(&self) -> Result<Vec<serde_json::Value>> {
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
        match json {
            serde_json::Value::Array(entries) => Ok(entries),
            _ => anyhow::bail!("Invalid TSP response format"),
        }
    }
}

impl PriceSource for TspSource {
    fn name(&self) -> &'static str {
        "tsp"
    }

    fn description(&self) -> &'static str {
        "Thrift Savings Plan - TSP fund share prices"
    }

    fn fetch_latest(&self, pair: &PricePair) -> Result<PriceResponse> {
        let fund_name = Self::normalize_fund(&pair.ticker)
            .with_context(|| format!("Unknown TSP fund: {}", pair.ticker))?;

        let data = self.fetch_history()?;

        // Get the most recent entry
        let latest = data.last().with_context(|| "No price data available")?;

        // Find the price for our fund
        let fund_key = fund_name.replace(' ', "");

        let price_value = latest
            .get(&fund_key)
            .or_else(|| latest.get(fund_name))
            .with_context(|| format!("Fund {fund_name} not found in TSP data"))?;

        let price = crate::cmd::price::price_decimal_from_json(price_value)
            .with_context(|| format!("Invalid price format for {fund_name}: {price_value}"))?;

        // The feed's own date, never the requested one (#1794; the old
        // request.date fallback was the exact mislabeling pattern this
        // PR removes — round-3 deep review).
        let date =
            super::feed_date_or_today(latest.get("date").and_then(serde_json::Value::as_str));

        Ok(PriceResponse {
            price,
            currency: "USD".to_string(),
            date,
            source: self.name().to_string(),
        })
    }

    fn historical_coverage(&self) -> HistoricalCoverage {
        // The endpoint serves its whole daily history in one payload
        // (#1802 source ports); its retention is undocumented, and
        // dates beyond it degrade to the dispatch's clean no-quote
        // error rather than a refusal.
        HistoricalCoverage::Full
    }

    fn fetch_window(&self, pair: &PricePair, window: DateWindow) -> Result<Vec<PricePoint>> {
        // Same single-payload fetch as the latest path, sliced to the
        // window here (#1802 source ports). Entries with a
        // missing/unparsable date are SKIPPED, never today-labeled — a
        // today-fallback on a historical entry would be discarded by
        // the dispatch's on-or-before selection, turning a served
        // price into a spurious no-quote error (deep review of #1803).
        let fund_name = Self::normalize_fund(&pair.ticker)
            .with_context(|| format!("Unknown TSP fund: {}", pair.ticker))?;
        let fund_key = fund_name.replace(' ', "");

        let mut points = Vec::new();
        for entry in self.fetch_history()? {
            let Some(date) =
                super::feed_date(entry.get("date").and_then(serde_json::Value::as_str))
            else {
                continue;
            };
            if date < window.start || date > window.end {
                continue;
            }
            // Skip days the fund has no entry for (funds launched at
            // different times) — absence is not an error here.
            let Some(price) = entry
                .get(&fund_key)
                .or_else(|| entry.get(fund_name))
                .and_then(crate::cmd::price::price_decimal_from_json)
            else {
                continue;
            };
            points.push(PricePoint {
                date,
                price,
                // TSP share prices are always US dollars, same as the
                // latest path's hardcoded currency.
                currency: Some("USD".to_string()),
            });
        }
        Ok(points)
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
