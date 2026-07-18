//! Quandl (Nasdaq Data Link) price source.
//!
//! Fetches financial data from Quandl/Nasdaq Data Link.

use super::{DateWindow, HistoricalCoverage, PricePair, PricePoint, PriceSource, user_agent};
use crate::cmd::price::PriceResponse;
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

    /// Build the Quandl API URL. `None` asks for the latest row
    /// (`limit=1`); a [`DateWindow`] asks for the inclusive
    /// `start_date`/`end_date` slice of the dataset (#1802 source
    /// ports).
    fn build_url(&self, dataset: &str, api_key: &str, window: Option<DateWindow>) -> String {
        match window {
            Some(w) => format!(
                "https://data.nasdaq.com/api/v3/datasets/{dataset}/data.json?start_date={}&end_date={}&api_key={api_key}",
                w.start, w.end
            ),
            None => format!(
                "https://data.nasdaq.com/api/v3/datasets/{dataset}/data.json?limit=1&api_key={api_key}"
            ),
        }
    }

    /// Parse the dataset identifier.
    fn parse_dataset(ticker: &str) -> (&str, &str) {
        if let Some(pos) = ticker.find('/') {
            (&ticker[..pos], &ticker[pos + 1..])
        } else {
            ("WIKI", ticker)
        }
    }

    /// Shared fetch + parse for the dataset endpoint (latest or
    /// windowed — same response shape): every row of
    /// `dataset_data.data` becomes a [`PricePoint`] (#1802 source
    /// ports). Rows with a missing/unparsable date or price are
    /// SKIPPED, never today-labeled — a today-fallback on a historical
    /// row would be discarded by the dispatch's on-or-before selection,
    /// turning a served rate into a spurious no-quote error (deep
    /// review of #1803).
    fn fetch_rows(
        &self,
        url: &str,
        pair: &PricePair,
        undated_fallback: Option<rustledger_core::NaiveDate>,
    ) -> Result<Vec<PricePoint>> {
        let mut response = ureq::get(url)
            .header("User-Agent", user_agent())
            .call()
            .with_context(|| format!("Failed to fetch data for {}", pair.ticker))?;

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

        let rows = dataset_data
            .get("data")
            .and_then(serde_json::Value::as_array)
            .with_context(|| "Missing data in response")?;

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

        let mut points = Vec::new();
        for row in rows {
            let Some(row) = row.as_array() else {
                continue;
            };
            // The row's OWN date, never the requested one (#1794). A
            // row with an unresolvable date takes `undated_fallback`
            // on the LATEST path (today, matching feed_date_or's rule
            // and main's behavior) and is SKIPPED on the historical
            // path (deep review of #1804 restored the latest fallback
            // this refactor had dropped).
            let raw_date = row.get(date_idx).and_then(serde_json::Value::as_str);
            let Some(date) = super::feed_date(raw_date).or(undated_fallback) else {
                continue;
            };
            let Some(price) = row
                .get(price_idx)
                .and_then(crate::cmd::price::price_decimal_from_json)
            else {
                continue;
            };
            points.push(PricePoint {
                date,
                price,
                // The dataset's quote currency is dataset-defined and
                // not reported per row; the dispatch substitutes the
                // request currency, uppercased.
                currency: None,
            });
        }
        Ok(points)
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

    fn fetch_latest(&self, pair: &PricePair) -> Result<PriceResponse> {
        let api_key = Self::get_api_key()?;
        let (database, dataset) = Self::parse_dataset(&pair.ticker);
        let full_dataset = format!("{database}/{dataset}");
        let url = self.build_url(&full_dataset, &api_key, None);

        // The row's own date, never the requested one (#1794); the
        // greatest-date pick guards against a provider that ignores
        // limit=1 (providers do not guarantee sorted series).
        let points = self.fetch_rows(&url, pair, Some(jiff::Zoned::now().date()))?;
        let point = points.into_iter().max_by_key(|p| p.date).with_context(
            || "No usable rows in the Quandl response (empty dataset or unparsable prices)",
        )?;

        Ok(PriceResponse {
            price: point.price,
            currency: pair.currency.clone(),
            date: point.date,
            source: self.name().to_string(),
        })
    }

    fn historical_coverage(&self) -> HistoricalCoverage {
        // Nasdaq Data Link datasets carry their own full history
        // (#1802 source ports); dates a given dataset lacks surface as
        // the dispatch's clean no-quote error, not a refusal.
        HistoricalCoverage::Full
    }

    fn fetch_window(&self, pair: &PricePair, window: DateWindow) -> Result<Vec<PricePoint>> {
        // Same endpoint as the latest path, sliced by the inclusive
        // start_date/end_date parameters (#1802 source ports); the
        // dispatch does on-or-before selection over the rows.
        let api_key = Self::get_api_key()?;
        let (database, dataset) = Self::parse_dataset(&pair.ticker);
        let full_dataset = format!("{database}/{dataset}");
        let url = self.build_url(&full_dataset, &api_key, Some(window));
        self.fetch_rows(&url, pair, None)
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
        let url = source.build_url("WIKI/AAPL", "demo", None);
        assert!(url.contains("WIKI/AAPL"));
        assert!(url.contains("data.nasdaq.com"));
        assert!(url.contains("limit=1"), "{url}");

        // Historical (#1802): the window replaces the limit=1 form.
        let window = DateWindow {
            start: rustledger_core::naive_date(2024, 1, 8).unwrap(),
            end: rustledger_core::naive_date(2024, 1, 15).unwrap(),
        };
        let url = source.build_url("WIKI/AAPL", "demo", Some(window));
        assert!(url.contains("start_date=2024-01-08"), "{url}");
        assert!(url.contains("end_date=2024-01-15"), "{url}");
        assert!(!url.contains("limit="), "{url}");
    }

    #[test]
    fn test_source_metadata() {
        let source = QuandlSource::new(Duration::from_secs(30));
        assert_eq!(source.name(), "quandl");
        assert!(source.requires_api_key());
        assert_eq!(source.api_key_env_var(), Some("QUANDL_API_KEY"));
    }
}
