//! European Central Bank (ECB) price source.
//!
//! Fetches currency exchange rates from the ECB.

use super::{PriceSource, user_agent};
use crate::cmd::price::{PriceRequest, PriceResponse};
use anyhow::{Context, Result};
use chrono::Utc;
use rust_decimal::Decimal;
use rustledger_core::NaiveDate;
use std::str::FromStr;
use std::time::Duration;

/// European Central Bank price source.
///
/// Uses the ECB Statistical Data Warehouse API to fetch exchange rates.
/// No API key required.
///
/// # Supported Currencies
///
/// All currencies in the ECB daily reference rates:
/// - EUR (base), USD, GBP, JPY, CHF, CAD, AUD, etc.
///
/// # Notes
///
/// - ECB rates are published once per day around 16:00 CET
/// - Rates are against EUR (EUR is the base currency)
/// - Weekend/holiday rates use the last available rate
#[derive(Debug)]
pub struct EcbSource {}

impl EcbSource {
    /// Create a new ECB source.
    ///
    /// The timeout parameter is accepted for API consistency but not
    /// currently applied to HTTP requests.
    pub const fn new(_timeout: Duration) -> Self {
        Self {}
    }

    /// Build the ECB API URL for a currency pair.
    fn build_url(&self, currency: &str) -> String {
        format!(
            "https://data-api.ecb.europa.eu/service/data/EXR/D.{currency}.EUR.SP00.A?lastNObservations=1&format=jsondata"
        )
    }
}

impl EcbSource {
    /// Fetch a rate from the ECB API for a currency against EUR.
    /// Returns (rate, date) where rate is "units of currency per 1 EUR".
    fn fetch_rate(&self, currency: &str) -> Result<(Decimal, NaiveDate)> {
        let url = self.build_url(&currency.to_uppercase());

        let mut response = ureq::get(&url)
            .header("User-Agent", user_agent())
            .header("Accept", "application/json")
            .call()
            .with_context(|| format!("Failed to fetch ECB rate for {currency}"))?;

        let json: serde_json::Value = response
            .body_mut()
            .read_json()
            .with_context(|| format!("Failed to parse ECB response for {currency}"))?;

        // Navigate the SDMX-JSON structure to find the rate
        let datasets = json
            .get("dataSets")
            .and_then(serde_json::Value::as_array)
            .and_then(|a| a.first())
            .with_context(|| "Missing dataSets in ECB response")?;

        let series = datasets
            .get("series")
            .and_then(serde_json::Value::as_object)
            .and_then(|o| o.values().next())
            .with_context(|| "Missing series in ECB response")?;

        let observations = series
            .get("observations")
            .and_then(serde_json::Value::as_object)
            .with_context(|| "Missing observations in ECB response")?;

        // Get the most recent observation
        let (obs_key, obs_value) = observations
            .iter()
            .next_back()
            .with_context(|| "No observations in ECB response")?;

        let rate_value = obs_value
            .as_array()
            .and_then(|a| a.first())
            .and_then(serde_json::Value::as_f64)
            .with_context(|| "Invalid rate value in ECB response")?;

        let rate = Decimal::from_str(&rate_value.to_string())
            .with_context(|| format!("Failed to parse rate: {rate_value}"))?;

        // Try to get the date from the structure
        let date = json
            .get("structure")
            .and_then(|s| s.get("dimensions"))
            .and_then(|d| d.get("observation"))
            .and_then(|o| o.as_array())
            .and_then(|a| a.first())
            .and_then(|t| t.get("values"))
            .and_then(|v| v.as_array())
            .and_then(|values| {
                let idx: usize = obs_key.parse().unwrap_or(0);
                values.get(idx)
            })
            .and_then(|v| v.get("id"))
            .and_then(serde_json::Value::as_str)
            .and_then(|s| NaiveDate::parse_from_str(s, "%Y-%m-%d").ok())
            .unwrap_or_else(|| NaiveDate::today());

        Ok((rate, date))
    }
}

impl PriceSource for EcbSource {
    fn name(&self) -> &'static str {
        "ecb"
    }

    fn description(&self) -> &'static str {
        "European Central Bank - currency exchange rates"
    }

    fn fetch_price(&self, request: &PriceRequest) -> Result<PriceResponse> {
        let ticker = request.ticker.to_uppercase();
        let currency = request.currency.to_uppercase();

        // ECB provides rates as "X per 1 EUR"
        // We need to handle three cases:
        // 1. ticker=EUR, currency=X: fetch X rate, return as-is (X per EUR)
        // 2. ticker=X, currency=EUR: fetch X rate, invert it (EUR per X)
        // 3. ticker=X, currency=Y: fetch both, compute cross-rate (Y per X)

        let date = request.date.unwrap_or_else(|| NaiveDate::today());

        if ticker == "EUR" && currency == "EUR" {
            // EUR to EUR = 1
            return Ok(PriceResponse {
                price: Decimal::ONE,
                currency,
                date,
                source: self.name().to_string(),
            });
        }

        if ticker == "EUR" {
            // EUR -> X: fetch X rate (X per EUR), return as-is
            let (rate, rate_date) = self.fetch_rate(&currency)?;
            return Ok(PriceResponse {
                price: rate,
                currency,
                date: request.date.unwrap_or(rate_date),
                source: self.name().to_string(),
            });
        }

        if currency == "EUR" {
            // X -> EUR: fetch X rate (X per EUR), invert to get EUR per X
            let (rate, rate_date) = self.fetch_rate(&ticker)?;
            if rate.is_zero() {
                anyhow::bail!("Cannot invert zero rate for {ticker}");
            }
            let inverted = Decimal::ONE / rate;
            return Ok(PriceResponse {
                price: inverted,
                currency,
                date: request.date.unwrap_or(rate_date),
                source: self.name().to_string(),
            });
        }

        // Cross-rate: X -> Y via EUR
        // X per EUR and Y per EUR => Y per X = (Y per EUR) / (X per EUR)
        let (ticker_rate, ticker_date) = self.fetch_rate(&ticker)?;
        let (currency_rate, _) = self.fetch_rate(&currency)?;

        if ticker_rate.is_zero() {
            anyhow::bail!("Cannot compute cross-rate: zero rate for {ticker}");
        }

        let cross_rate = currency_rate / ticker_rate;

        Ok(PriceResponse {
            price: cross_rate,
            currency,
            date: request.date.unwrap_or(ticker_date),
            source: self.name().to_string(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_build_url() {
        let source = EcbSource::new(Duration::from_secs(30));
        let url = source.build_url("USD");
        assert!(url.contains("USD"));
        assert!(url.contains("data-api.ecb.europa.eu"));
    }

    #[test]
    fn test_source_metadata() {
        let source = EcbSource::new(Duration::from_secs(30));
        assert_eq!(source.name(), "ecb");
        assert!(!source.requires_api_key());
    }

    #[test]
    fn test_eur_to_eur_returns_one() {
        // EUR to EUR should always return 1.0 without network access
        let source = EcbSource::new(Duration::from_secs(30));
        let request = PriceRequest::new("EUR", "EUR");
        let response = source.fetch_price(&request).unwrap();
        assert_eq!(response.price, Decimal::ONE);
        assert_eq!(response.currency, "EUR");
    }
}
