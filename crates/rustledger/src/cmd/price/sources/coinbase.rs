//! Coinbase price source.
//!
//! Fetches cryptocurrency prices from Coinbase.

use super::{DateWindow, HistoricalCoverage, PricePair, PricePoint, PriceSource, user_agent};
use crate::cmd::price::PriceResponse;
use anyhow::{Context, Result};
use rust_decimal::Decimal;
use std::str::FromStr;
use std::time::Duration;

/// Coinbase price source.
///
/// Uses the Coinbase API to fetch cryptocurrency spot prices.
/// No API key required for read-only access.
///
/// # Supported Symbols
///
/// - Cryptocurrencies: `BTC`, `ETH`, `SOL`, etc.
/// - Format: Uses `{CRYPTO}-{CURRENCY}` pairs (e.g., `BTC-USD`)
#[derive(Debug)]
pub struct CoinbaseSource {}

impl CoinbaseSource {
    /// Create a new Coinbase source.
    ///
    /// The timeout parameter is accepted for API consistency but not
    /// currently applied to HTTP requests.
    pub const fn new(_timeout: Duration) -> Self {
        Self {}
    }

    /// Build the Coinbase API URL. A date adds `?date=YYYY-MM-DD`,
    /// which the spot endpoint answers with that day's price.
    fn build_url(
        &self,
        ticker: &str,
        currency: &str,
        date: Option<rustledger_core::NaiveDate>,
    ) -> String {
        // If the ticker already contains a dash, use it directly
        // Otherwise, append the currency
        let pair = if ticker.contains('-') {
            ticker.to_string()
        } else {
            format!("{ticker}-{currency}")
        };
        match date {
            Some(d) => format!("https://api.coinbase.com/v2/prices/{pair}/spot?date={d}"),
            None => format!("https://api.coinbase.com/v2/prices/{pair}/spot"),
        }
    }

    /// Shared fetch + parse for the spot endpoint (dated or not).
    /// Returns `(price, currency)` — currency is `None` when the feed
    /// omits the field, so callers (and the dispatch's canonical
    /// uppercase fallback) can distinguish feed truth from the raw
    /// request value (round-5 deep review of #1803: wrapping the raw
    /// fallback in `Some` shadowed the dispatch's normalization).
    fn fetch_spot(&self, url: &str, pair: &PricePair) -> Result<(Decimal, Option<String>)> {
        let mut response = ureq::get(url)
            .header("User-Agent", user_agent())
            .call()
            .with_context(|| format!("Failed to fetch price for {}", pair.ticker))?;

        let json: serde_json::Value = response
            .body_mut()
            .read_json()
            .with_context(|| format!("Failed to parse response for {}", pair.ticker))?;

        // Check for errors
        if let Some(errors) = json.get("errors")
            && let Some(first_error) = errors.as_array().and_then(|arr| arr.first())
        {
            let message = first_error
                .get("message")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("Unknown error");
            anyhow::bail!("Coinbase error: {message}");
        }

        let data = json
            .get("data")
            .with_context(|| "Missing 'data' field in response")?;

        let price_str = data
            .get("amount")
            .and_then(serde_json::Value::as_str)
            .with_context(|| "Missing 'amount' field in response")?;

        let price = Decimal::from_str(price_str)
            .with_context(|| format!("Failed to parse price: {price_str}"))?;

        let currency = data
            .get("currency")
            .and_then(serde_json::Value::as_str)
            .map(ToString::to_string);

        Ok((price, currency))
    }
}

impl PriceSource for CoinbaseSource {
    fn name(&self) -> &'static str {
        "coinbase"
    }

    fn description(&self) -> &'static str {
        "Coinbase - cryptocurrency spot prices"
    }

    fn fetch_latest(&self, pair: &PricePair) -> Result<PriceResponse> {
        // Label read BEFORE the network fetch: the spot endpoint
        // carries no date field, and a live quote must carry the day
        // the request was made — not a day the clock rolled to during
        // network I/O (round-4 deep review of #1803: the post-fetch
        // read could poison the settled cache with a D+1-labeled
        // entry under a D key).
        let date = jiff::Zoned::now().date();
        let url = self.build_url(&pair.ticker, &pair.currency, None);
        let (price, currency) = self.fetch_spot(&url, pair)?;

        Ok(PriceResponse {
            price,
            currency: currency.unwrap_or_else(|| pair.currency.clone()),
            date,
            source: self.name().to_string(),
        })
    }

    fn historical_coverage(&self) -> HistoricalCoverage {
        // Coinbase the exchange launched in January 2015; earlier dated
        // requests get the clean capability refusal instead of a raw
        // provider error (round-2 review of #1803). Per-pair listing
        // dates vary — later-listed pairs still surface provider errors
        // for their pre-listing gap.
        HistoricalCoverage::Since(
            rustledger_core::naive_date(2015, 1, 1).expect("static date is valid"),
        )
    }

    fn fetch_window(&self, pair: &PricePair, window: DateWindow) -> Result<Vec<PricePoint>> {
        // The dispatch routes requested==today to fetch_latest before
        // the window path, so window.end here is always a COMPLETED
        // day (round-3 review of #1803 removed the per-source same-day
        // delegations along with the straddle).
        // Crypto trades every day, so the exact-date spot endpoint
        // answers for any past day: a single point at the window's end
        // satisfies the dispatch's on-or-before selection without
        // burning one request per day of the window. The dispatch
        // refuses future dates before this can run, so window.end is a
        // real, completed day.
        let url = self.build_url(&pair.ticker, &pair.currency, Some(window.end));
        let (price, currency) = self.fetch_spot(&url, pair)?;
        Ok(vec![PricePoint {
            date: window.end,
            price,
            // None when the feed omits it — the dispatch substitutes
            // the request currency, uppercased.
            currency,
        }])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_build_url() {
        let source = CoinbaseSource::new(Duration::from_secs(30));

        let url = source.build_url("BTC", "USD", None);
        assert_eq!(url, "https://api.coinbase.com/v2/prices/BTC-USD/spot");

        let url = source.build_url("BTC-EUR", "USD", None);
        assert_eq!(url, "https://api.coinbase.com/v2/prices/BTC-EUR/spot");

        // Historical (#1802): the spot endpoint takes an exact date.
        let d = rustledger_core::naive_date(2024, 1, 15).unwrap();
        let url = source.build_url("BTC", "USD", Some(d));
        assert_eq!(
            url,
            "https://api.coinbase.com/v2/prices/BTC-USD/spot?date=2024-01-15"
        );
    }

    #[test]
    fn test_source_metadata() {
        let source = CoinbaseSource::new(Duration::from_secs(30));
        assert_eq!(source.name(), "coinbase");
        assert!(!source.requires_api_key());
    }
}
