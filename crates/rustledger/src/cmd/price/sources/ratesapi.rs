//! Rates API price source.
//!
//! Fetches currency exchange rates from exchangerate.host or similar free APIs.

use super::{DateWindow, HistoricalCoverage, PricePair, PricePoint, PriceSource, user_agent};
use crate::cmd::price::PriceResponse;
use anyhow::{Context, Result};
use rust_decimal::Decimal;
use rustledger_core::NaiveDate;
use std::time::Duration;

/// Rates API price source.
///
/// Uses a free exchange rate API to fetch currency conversion rates.
/// No API key required.
///
/// # Supported Currencies
///
/// All major world currencies:
/// - USD, EUR, GBP, JPY, CHF, CAD, AUD, CNY, INR, etc.
#[derive(Debug)]
pub struct RatesApiSource {}

impl RatesApiSource {
    /// Create a new Rates API source.
    pub const fn new(_timeout: Duration) -> Self {
        Self {}
    }

    /// Build the API URL. The date-path form serves the historical
    /// EU-reference rate for that day (#1802).
    fn build_url(&self, base: &str, target: &str, date: Option<NaiveDate>) -> String {
        match date {
            Some(d) => format!("https://api.exchangerate.host/{d}?base={base}&symbols={target}"),
            None => format!("https://api.exchangerate.host/latest?base={base}&symbols={target}"),
        }
    }

    /// Shared fetch + parse for the latest and dated endpoints (same
    /// response shape). Returns `(price, feed_date)`.
    fn fetch_rate(&self, url: &str, pair: &PricePair) -> Result<(Decimal, NaiveDate)> {
        let mut response = ureq::get(url)
            .header("User-Agent", user_agent())
            .call()
            .with_context(|| format!("Failed to fetch rate for {}", pair.ticker))?;

        let json: serde_json::Value = response
            .body_mut()
            .read_json()
            .with_context(|| format!("Failed to parse response for {}", pair.ticker))?;

        // Check for success
        let success = json
            .get("success")
            .and_then(serde_json::Value::as_bool)
            .unwrap_or(true);
        if !success {
            let error = json
                .get("error")
                .and_then(|e| e.get("info"))
                .and_then(serde_json::Value::as_str)
                .unwrap_or("Unknown error");
            anyhow::bail!("Rates API error: {error}");
        }

        let rates = json
            .get("rates")
            .and_then(serde_json::Value::as_object)
            .with_context(|| "Missing 'rates' in response")?;

        let target_currency = pair.currency.to_uppercase();
        let rate_value = rates
            .get(&target_currency)
            .with_context(|| format!("Rate for {target_currency} not found"))?;

        let price = crate::cmd::price::price_decimal_from_json(rate_value)
            .with_context(|| format!("Invalid rate format: {rate_value}"))?;

        // The feed's OWN quote date when present (exchangerate.host
        // returns a "date" field) — on weekends the latest rate belongs
        // to Friday and must say so (deep review, same rule as ECB).
        let date = super::feed_date_or_today(json.get("date").and_then(serde_json::Value::as_str));

        Ok((price, date))
    }
}

impl PriceSource for RatesApiSource {
    fn name(&self) -> &'static str {
        "ratesapi"
    }

    fn description(&self) -> &'static str {
        "Exchange Rate API - currency conversion rates"
    }

    fn fetch_latest(&self, pair: &PricePair) -> Result<PriceResponse> {
        let url = self.build_url(
            &pair.ticker.to_uppercase(),
            &pair.currency.to_uppercase(),
            None,
        );
        let (price, date) = self.fetch_rate(&url, pair)?;

        Ok(PriceResponse {
            price,
            currency: pair.currency.clone(),
            date,
            source: self.name().to_string(),
        })
    }

    fn historical_coverage(&self) -> HistoricalCoverage {
        // exchangerate.host serves the EU reference series, which
        // begins 1999-01-04 (the euro's first trading day).
        HistoricalCoverage::Since(
            rustledger_core::naive_date(1999, 1, 4).expect("static date is valid"),
        )
    }

    fn fetch_window(&self, pair: &PricePair, window: DateWindow) -> Result<Vec<PricePoint>> {
        // The dated endpoint answers any single day with the nearest
        // preceding business-day rate under the feed's OWN date, so one
        // request at the window's end covers the dispatch's on-or-before
        // selection.
        let url = self.build_url(
            &pair.ticker.to_uppercase(),
            &pair.currency.to_uppercase(),
            Some(window.end),
        );
        let (price, date) = self.fetch_rate(&url, pair)?;
        Ok(vec![PricePoint {
            date,
            price,
            currency: Some(pair.currency.clone()),
        }])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_build_url() {
        let source = RatesApiSource::new(Duration::from_secs(30));
        let url = source.build_url("EUR", "USD", None);
        assert!(url.contains("EUR"));
        assert!(url.contains("USD"));
        assert!(url.contains("/latest?"), "{url}");

        // Historical (#1802): the date replaces the /latest path.
        let d = rustledger_core::naive_date(2024, 1, 15).unwrap();
        let url = source.build_url("EUR", "USD", Some(d));
        assert!(url.contains("/2024-01-15?"), "{url}");
        assert!(!url.contains("latest"), "{url}");
    }

    #[test]
    fn test_source_metadata() {
        let source = RatesApiSource::new(Duration::from_secs(30));
        assert_eq!(source.name(), "ratesapi");
        assert!(!source.requires_api_key());
    }

    #[test]
    fn test_same_currency_returns_one() {
        // Served by the trait's canonical identity arm (#1802).
        use crate::cmd::price::PriceRequest;
        let source = RatesApiSource::new(Duration::from_secs(30));
        let request = PriceRequest::new("USD", "USD");
        let response = source.fetch_price(&request).unwrap();
        assert_eq!(response.price, Decimal::ONE);
    }
}
