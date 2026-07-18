//! OANDA price source.
//!
//! Fetches forex rates from OANDA's API.

use super::{PricePair, PriceSource, user_agent};
use crate::cmd::price::PriceResponse;
use anyhow::{Context, Result};
use rust_decimal::Decimal;
use std::env;
use std::str::FromStr;
use std::time::Duration;

/// OANDA price source.
///
/// Uses OANDA's REST API to fetch forex rates.
/// Requires an API key set in the `OANDA_API_KEY` environment variable.
///
/// # API Key
///
/// Sign up at <https://oanda.com> for an API key.
/// Set it as: `export OANDA_API_KEY=your-key-here`
///
/// # Supported Pairs
///
/// All major and minor forex pairs:
/// - `EUR_USD`, `GBP_USD`, `USD_JPY`, etc.
#[derive(Debug)]
pub struct OandaSource {}

impl OandaSource {
    /// Create a new OANDA source.
    ///
    /// The timeout parameter is accepted for API consistency but not
    /// currently applied to HTTP requests.
    pub const fn new(_timeout: Duration) -> Self {
        Self {}
    }

    /// Get the API key from environment.
    fn get_api_key() -> Result<String> {
        env::var("OANDA_API_KEY").with_context(|| "OANDA_API_KEY environment variable not set")
    }

    /// Build the OANDA API URL.
    fn build_url(&self, instrument: &str) -> String {
        format!(
            "https://api-fxpractice.oanda.com/v3/instruments/{instrument}/candles?count=1&granularity=D"
        )
    }

    /// The trading day an OANDA D-granularity candle represents.
    ///
    /// The candle's `time` field is its OPEN, and daily candles align
    /// to the 17:00 `America/New_York` session boundary — so a candle's
    /// open timestamp falls on the civil day BEFORE the trading day it
    /// represents (Friday's candle opens Thursday 17:00 NY = 21:00Z or
    /// 22:00Z). Labeling from the raw time field dated every quote one
    /// trading day early (round-5 deep review of #1803): convert to New
    /// York time and roll forward past the session boundary instead.
    /// `None` when the timestamp or the tz database is unavailable —
    /// the caller falls back to the pre-fetch local day.
    fn candle_trading_day(time_rfc3339: &str) -> Option<rustledger_core::NaiveDate> {
        let ts: jiff::Timestamp = time_rfc3339.parse().ok()?;
        let ny = jiff::tz::TimeZone::get("America/New_York").ok()?;
        let zoned = ts.to_zoned(ny);
        if zoned.hour() >= 17 {
            zoned.date().checked_add(jiff::Span::new().days(1)).ok()
        } else {
            Some(zoned.date())
        }
    }

    /// Format currency pair for OANDA.
    fn format_instrument(ticker: &str, currency: &str) -> String {
        if ticker.contains('_') {
            ticker.to_uppercase()
        } else {
            format!("{}_{}", ticker.to_uppercase(), currency.to_uppercase())
        }
    }
}

impl PriceSource for OandaSource {
    fn name(&self) -> &'static str {
        "oanda"
    }

    fn description(&self) -> &'static str {
        "OANDA - forex rates (requires API key)"
    }

    fn requires_api_key(&self) -> bool {
        true
    }

    fn api_key_env_var(&self) -> Option<&'static str> {
        Some("OANDA_API_KEY")
    }

    fn fetch_latest(&self, pair: &PricePair) -> Result<PriceResponse> {
        // Fallback label read BEFORE the network fetch (round-5 deep
        // review of #1803: a post-fetch read can label with a day the
        // clock rolled to during I/O).
        let fallback_date = jiff::Zoned::now().date();
        let api_key = Self::get_api_key()?;
        let instrument = Self::format_instrument(&pair.ticker, &pair.currency);
        let url = self.build_url(&instrument);

        let mut response = ureq::get(&url)
            .header("User-Agent", user_agent())
            .header("Authorization", &format!("Bearer {api_key}"))
            .header("Accept-Datetime-Format", "RFC3339")
            .call()
            .with_context(|| format!("Failed to fetch rate for {instrument}"))?;

        let json: serde_json::Value = response
            .body_mut()
            .read_json()
            .with_context(|| "Failed to parse OANDA response")?;

        // Check for errors
        if let Some(error_message) = json.get("errorMessage") {
            let msg = error_message.as_str().unwrap_or("Unknown error");
            anyhow::bail!("OANDA error: {msg}");
        }

        let candles = json
            .get("candles")
            .and_then(serde_json::Value::as_array)
            .with_context(|| "Missing candles in response")?;

        let candle = candles
            .first()
            .with_context(|| "No candle data available")?;

        let mid = candle
            .get("mid")
            .with_context(|| "Missing mid price in candle")?;

        let close_str = mid
            .get("c")
            .and_then(serde_json::Value::as_str)
            .with_context(|| "Missing close price")?;

        let price = Decimal::from_str(close_str)
            .with_context(|| format!("Failed to parse price: {close_str}"))?;

        // The candle's OWN trading day, never the local fetch day
        // (rounds 4-5 deep review of #1803; the local-day label was
        // the #1794 class, and the raw time field is one day early —
        // see candle_trading_day).
        let date = candle
            .get("time")
            .and_then(serde_json::Value::as_str)
            .and_then(Self::candle_trading_day)
            .unwrap_or(fallback_date);

        let target_currency = if instrument.contains('_') {
            instrument.split('_').next_back().unwrap_or(&pair.currency)
        } else {
            &pair.currency
        };

        Ok(PriceResponse {
            price,
            currency: target_currency.to_string(),
            date,
            source: self.name().to_string(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Candle open times roll forward past the 17:00 New-York session
    /// boundary onto the trading day the candle represents — in both
    /// DST regimes — while intraday times stay on their own day
    /// (round-5 deep review of #1803: the raw open time labeled every
    /// quote one trading day early).
    #[test]
    fn candle_trading_day_rolls_past_session_open() {
        // Thu 2026-07-16 21:00Z = Thu 17:00 EDT → Friday's candle.
        assert_eq!(
            OandaSource::candle_trading_day("2026-07-16T21:00:00.000000000Z"),
            Some(rustledger_core::naive_date(2026, 7, 17).unwrap())
        );
        // Thu 2026-01-15 22:00Z = Thu 17:00 EST (winter) → Friday's.
        assert_eq!(
            OandaSource::candle_trading_day("2026-01-15T22:00:00.000000000Z"),
            Some(rustledger_core::naive_date(2026, 1, 16).unwrap())
        );
        // Fri 14:00Z = Fri 10:00 EDT (before the boundary) → Friday.
        assert_eq!(
            OandaSource::candle_trading_day("2026-07-17T14:00:00.000000000Z"),
            Some(rustledger_core::naive_date(2026, 7, 17).unwrap())
        );
        // Garbage → None (caller falls back to the pre-fetch day).
        assert_eq!(OandaSource::candle_trading_day("not-a-time"), None);
    }

    #[test]
    fn test_format_instrument() {
        assert_eq!(OandaSource::format_instrument("EUR", "USD"), "EUR_USD");
        assert_eq!(OandaSource::format_instrument("eur_usd", "GBP"), "EUR_USD");
        assert_eq!(OandaSource::format_instrument("GBP", "JPY"), "GBP_JPY");
    }

    #[test]
    fn test_build_url() {
        let source = OandaSource::new(Duration::from_secs(30));
        let url = source.build_url("EUR_USD");
        assert!(url.contains("EUR_USD"));
        assert!(url.contains("oanda.com"));
    }

    #[test]
    fn test_source_metadata() {
        let source = OandaSource::new(Duration::from_secs(30));
        assert_eq!(source.name(), "oanda");
        assert!(source.requires_api_key());
        assert_eq!(source.api_key_env_var(), Some("OANDA_API_KEY"));
    }
}
