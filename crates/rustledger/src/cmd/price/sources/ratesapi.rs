//! Rates API price source.
//!
//! Fetches currency exchange rates from exchangerate.host or similar free APIs.

use super::{PriceSource, user_agent};
use crate::cmd::price::{PriceRequest, PriceResponse};
use anyhow::{Context, Result};
use chrono::Utc;
use rust_decimal::Decimal;
use rustledger_core::NaiveDate;
use std::str::FromStr;
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

    /// Build the API URL.
    fn build_url(&self, base: &str, target: &str) -> String {
        format!("https://api.exchangerate.host/latest?base={base}&symbols={target}")
    }
}

impl PriceSource for RatesApiSource {
    fn name(&self) -> &'static str {
        "ratesapi"
    }

    fn description(&self) -> &'static str {
        "Exchange Rate API - currency conversion rates"
    }

    fn fetch_price(&self, request: &PriceRequest) -> Result<PriceResponse> {
        // If ticker and currency are the same, return 1.0
        if request.ticker.to_uppercase() == request.currency.to_uppercase() {
            let date = request.date.unwrap_or_else(|| NaiveDate::today());
            return Ok(PriceResponse {
                price: Decimal::ONE,
                currency: request.currency.clone(),
                date,
                source: self.name().to_string(),
            });
        }

        let url = self.build_url(
            &request.ticker.to_uppercase(),
            &request.currency.to_uppercase(),
        );

        let mut response = ureq::get(&url)
            .header("User-Agent", user_agent())
            .call()
            .with_context(|| format!("Failed to fetch rate for {}", request.ticker))?;

        let json: serde_json::Value = response
            .body_mut()
            .read_json()
            .with_context(|| format!("Failed to parse response for {}", request.ticker))?;

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

        let target_currency = request.currency.to_uppercase();
        let rate_value = rates
            .get(&target_currency)
            .with_context(|| format!("Rate for {target_currency} not found"))?;

        let rate_str = if let Some(n) = rate_value.as_f64() {
            n.to_string()
        } else if let Some(s) = rate_value.as_str() {
            s.to_string()
        } else {
            anyhow::bail!("Invalid rate format");
        };

        let price = Decimal::from_str(&rate_str)
            .with_context(|| format!("Failed to parse rate: {rate_str}"))?;

        let date = request.date.unwrap_or_else(|| NaiveDate::today());

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
    fn test_build_url() {
        let source = RatesApiSource::new(Duration::from_secs(30));
        let url = source.build_url("EUR", "USD");
        assert!(url.contains("EUR"));
        assert!(url.contains("USD"));
    }

    #[test]
    fn test_source_metadata() {
        let source = RatesApiSource::new(Duration::from_secs(30));
        assert_eq!(source.name(), "ratesapi");
        assert!(!source.requires_api_key());
    }

    #[test]
    fn test_same_currency_returns_one() {
        let source = RatesApiSource::new(Duration::from_secs(30));
        let request = PriceRequest::new("USD", "USD");
        let response = source.fetch_price(&request).unwrap();
        assert_eq!(response.price, Decimal::ONE);
    }
}
