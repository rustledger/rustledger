//! Alpha Vantage price source.
//!
//! Fetches stock, forex, and crypto prices from Alpha Vantage.

use super::{DateWindow, HistoricalCoverage, PricePair, PricePoint, PriceSource, user_agent};
use crate::cmd::price::PriceResponse;
use anyhow::{Context, Result};
use rust_decimal::Decimal;
use std::env;
use std::str::FromStr;
use std::time::Duration;

/// Alpha Vantage price source.
///
/// Uses Alpha Vantage's API to fetch stock quotes, forex rates, and crypto prices.
/// Requires an API key set in the `ALPHAVANTAGE_API_KEY` environment variable.
///
/// # API Key
///
/// Get a free API key at <https://www.alphavantage.co/support/#api-key>
/// Set it as: `export ALPHAVANTAGE_API_KEY=your-key-here`
///
/// # Supported Symbols
///
/// - Stocks: `AAPL`, `MSFT`, `GOOGL`
/// - Forex: Use `from_currency/to_currency` format (e.g., `EUR/USD`)
/// - Crypto: Use `CRYPTO:symbol` format (e.g., `CRYPTO:BTC`)
#[derive(Debug)]
pub struct AlphaVantageSource {}

impl AlphaVantageSource {
    /// Create a new Alpha Vantage source.
    pub const fn new(_timeout: Duration) -> Self {
        Self {}
    }

    /// Get the API key from environment.
    fn get_api_key() -> Result<String> {
        env::var("ALPHAVANTAGE_API_KEY")
            .with_context(|| "ALPHAVANTAGE_API_KEY environment variable not set")
    }

    /// Build the Alpha Vantage API URL for stocks.
    fn build_stock_url(&self, symbol: &str, api_key: &str) -> String {
        format!(
            "https://www.alphavantage.co/query?function=GLOBAL_QUOTE&symbol={symbol}&apikey={api_key}"
        )
    }

    /// Build the `TIME_SERIES_DAILY` URL for a stock's history (#1802
    /// source ports). `compact` returns the trailing ~100 trading days;
    /// windows ending further back need `full` (the whole listing
    /// history — a heavier payload, fetched only when required).
    fn build_daily_url(symbol: &str, api_key: &str, window: DateWindow) -> String {
        let compact_horizon = jiff::Zoned::now()
            .date()
            .checked_sub(jiff::Span::new().days(90))
            .ok();
        let outputsize = match compact_horizon {
            Some(horizon) if window.end >= horizon => "compact",
            _ => "full",
        };
        format!(
            "https://www.alphavantage.co/query?function=TIME_SERIES_DAILY&symbol={symbol}&outputsize={outputsize}&apikey={api_key}"
        )
    }

    /// Parse a `TIME_SERIES_DAILY` response: every daily close as a
    /// dated point. Factored off the HTTP fetch for hermetic fixture
    /// tests (#1802 source ports). The listing currency is not carried
    /// in the response, so points leave `currency` to the dispatch's
    /// request-currency fallback.
    fn parse_daily_series(json: &serde_json::Value) -> Result<Vec<PricePoint>> {
        // Rate-limit and error notes use the same shapes as the quote
        // endpoints.
        if let Some(note) = json.get("Note") {
            let msg = note.as_str().unwrap_or("API limit reached");
            anyhow::bail!("Alpha Vantage: {msg}");
        }
        if let Some(error) = json.get("Error Message") {
            let msg = error.as_str().unwrap_or("Unknown error");
            anyhow::bail!("Alpha Vantage error: {msg}");
        }

        let series = json
            .get("Time Series (Daily)")
            .and_then(serde_json::Value::as_object)
            .with_context(|| "Missing 'Time Series (Daily)' in response")?;

        let mut points = Vec::with_capacity(series.len());
        for (date_str, daily_bar) in series {
            let Some(date) = super::feed_date(Some(date_str)) else {
                continue;
            };
            let Some(price) = daily_bar
                .get("4. close")
                .and_then(crate::cmd::price::price_decimal_from_json)
            else {
                continue;
            };
            points.push(PricePoint {
                date,
                price,
                currency: None,
            });
        }
        Ok(points)
    }

    /// Build the Alpha Vantage API URL for forex.
    fn build_forex_url(&self, from: &str, to: &str, api_key: &str) -> String {
        format!(
            "https://www.alphavantage.co/query?function=CURRENCY_EXCHANGE_RATE&from_currency={from}&to_currency={to}&apikey={api_key}"
        )
    }

    /// Build the Alpha Vantage API URL for crypto.
    fn build_crypto_url(&self, symbol: &str, market: &str, api_key: &str) -> String {
        format!(
            "https://www.alphavantage.co/query?function=CURRENCY_EXCHANGE_RATE&from_currency={symbol}&to_currency={market}&apikey={api_key}"
        )
    }

    /// Determine the type of request and fetch accordingly.
    fn fetch_internal(&self, pair: &PricePair, api_key: &str) -> Result<PriceResponse> {
        let ticker = &pair.ticker;

        // Check for crypto prefix
        if let Some(symbol) = ticker.strip_prefix("CRYPTO:") {
            return self.fetch_crypto(symbol, &pair.currency, api_key);
        }

        // Check for forex format (contains /)
        if ticker.contains('/') {
            let parts: Vec<&str> = ticker.split('/').collect();
            if parts.len() == 2 {
                return self.fetch_forex(parts[0], parts[1], api_key);
            }
        }

        // Default to stock
        self.fetch_stock(ticker, &pair.currency, api_key)
    }

    fn fetch_stock(&self, symbol: &str, currency: &str, api_key: &str) -> Result<PriceResponse> {
        let url = self.build_stock_url(symbol, api_key);

        let mut response = ureq::get(&url)
            .header("User-Agent", user_agent())
            .call()
            .with_context(|| format!("Failed to fetch quote for {symbol}"))?;

        let json: serde_json::Value = response
            .body_mut()
            .read_json()
            .with_context(|| "Failed to parse Alpha Vantage response")?;

        // Check for API errors
        if let Some(note) = json.get("Note") {
            let msg = note.as_str().unwrap_or("API limit reached");
            anyhow::bail!("Alpha Vantage: {msg}");
        }
        if let Some(error) = json.get("Error Message") {
            let msg = error.as_str().unwrap_or("Unknown error");
            anyhow::bail!("Alpha Vantage error: {msg}");
        }

        let quote = json
            .get("Global Quote")
            .with_context(|| "Missing Global Quote in response")?;

        let price_str = quote
            .get("05. price")
            .and_then(serde_json::Value::as_str)
            .with_context(|| "Missing price in quote")?;

        let price = Decimal::from_str(price_str)
            .with_context(|| format!("Failed to parse price: {price_str}"))?;

        // The quote's OWN trading day when present — a weekend fetch must
        // date the price Friday, not today (deep review of #1801).
        let date = super::feed_date_or_today(
            quote
                .get("07. latest trading day")
                .and_then(serde_json::Value::as_str),
        );

        Ok(PriceResponse {
            price,
            currency: currency.to_string(),
            date,
            source: self.name().to_string(),
        })
    }

    fn fetch_forex(&self, from: &str, to: &str, api_key: &str) -> Result<PriceResponse> {
        let url = self.build_forex_url(from, to, api_key);
        self.fetch_exchange_rate(&url, from, to)
    }

    fn fetch_crypto(&self, symbol: &str, market: &str, api_key: &str) -> Result<PriceResponse> {
        let url = self.build_crypto_url(symbol, market, api_key);
        self.fetch_exchange_rate(&url, symbol, market)
    }

    /// Shared `CURRENCY_EXCHANGE_RATE` fetch — forex and crypto hit the
    /// same endpoint and parse the same response shape (round-2 deep
    /// review: the two copies had drifted, keeping the local-clock date
    /// label in both while the stock path was fixed).
    fn fetch_exchange_rate(&self, url: &str, from: &str, to: &str) -> Result<PriceResponse> {
        let mut response = ureq::get(url)
            .header("User-Agent", user_agent())
            .call()
            .with_context(|| format!("Failed to fetch rate for {from}/{to}"))?;

        let json: serde_json::Value = response
            .body_mut()
            .read_json()
            .with_context(|| "Failed to parse Alpha Vantage response")?;

        let rate_data = json
            .get("Realtime Currency Exchange Rate")
            .with_context(|| "Missing exchange rate data")?;

        let price_str = rate_data
            .get("5. Exchange Rate")
            .and_then(serde_json::Value::as_str)
            .with_context(|| "Missing exchange rate")?;

        let price = Decimal::from_str(price_str)
            .with_context(|| format!("Failed to parse rate: {price_str}"))?;

        // The quote's OWN refresh day when present ("6. Last Refreshed"
        // is "YYYY-MM-DD HH:MM:SS" in UTC) — a weekend FX fetch returns
        // Friday's rate and must be dated Friday, not today (#1794
        // class; round-2 deep review).
        let date = super::feed_date_or_today(
            rate_data
                .get("6. Last Refreshed")
                .and_then(serde_json::Value::as_str),
        );

        Ok(PriceResponse {
            price,
            currency: to.to_string(),
            date,
            source: self.name().to_string(),
        })
    }
}

impl PriceSource for AlphaVantageSource {
    fn name(&self) -> &'static str {
        "alphavantage"
    }

    fn description(&self) -> &'static str {
        "Alpha Vantage - stocks, forex, crypto (requires API key)"
    }

    fn requires_api_key(&self) -> bool {
        true
    }

    fn api_key_env_var(&self) -> Option<&'static str> {
        Some("ALPHAVANTAGE_API_KEY")
    }

    fn fetch_latest(&self, pair: &PricePair) -> Result<PriceResponse> {
        let api_key = Self::get_api_key()?;
        self.fetch_internal(pair, &api_key)
    }

    fn historical_coverage(&self) -> HistoricalCoverage {
        // TIME_SERIES_DAILY carries decades of STOCK history; forex and
        // crypto tickers refuse hermetically in fetch_window below —
        // coverage is per-source, per-ticker gaps error at fetch
        // (#1802 source ports).
        HistoricalCoverage::Full
    }

    fn fetch_window(&self, pair: &PricePair, window: DateWindow) -> Result<Vec<PricePoint>> {
        // Historical support covers STOCK tickers only for now: the
        // forex (`EUR/USD`) and crypto (`CRYPTO:BTC`) ticker forms use
        // different daily endpoints with different response shapes —
        // refuse BEFORE any network I/O with a pointer at the sources
        // that serve those asset classes historically (#1802).
        if pair.ticker.contains('/') || pair.ticker.starts_with("CRYPTO:") {
            anyhow::bail!(
                "alphavantage historical fetches support stock tickers only; for dated \
                 {} quotes use ratesapi (FX) or coinbase (crypto), or drop --date",
                pair.ticker
            );
        }

        let api_key = Self::get_api_key()?;
        let url = Self::build_daily_url(&pair.ticker, &api_key, window);

        let mut response = ureq::get(&url)
            .header("User-Agent", user_agent())
            .call()
            .with_context(|| format!("Failed to fetch daily series for {}", pair.ticker))?;

        let json: serde_json::Value = response
            .body_mut()
            .read_json()
            .with_context(|| "Failed to parse Alpha Vantage response")?;

        let points = Self::parse_daily_series(&json)?;
        // Drop the still-open US session's bar: TIME_SERIES_DAILY dates
        // are US/Eastern market days, and the dispatch's past-vs-today
        // split uses the LOCAL calendar — a UTC+8 user's local
        // "yesterday" can be the live US session, whose in-progress bar
        // must not be served as a settled close (deep review of #1804).
        // Completed Eastern days are settled and pass through.
        let eastern_today = Self::eastern_today();
        Ok(Self::drop_unsettled(points, eastern_today))
    }
}

impl AlphaVantageSource {
    /// The current civil day on the US/Eastern market calendar,
    /// falling back to UTC when the tz database is unavailable.
    fn eastern_today() -> rustledger_core::NaiveDate {
        jiff::tz::TimeZone::get("America/New_York").map_or_else(
            |_| {
                jiff::Timestamp::now()
                    .to_zoned(jiff::tz::TimeZone::UTC)
                    .date()
            },
            |tz| jiff::Timestamp::now().to_zoned(tz).date(),
        )
    }

    /// Keep only bars from COMPLETED Eastern market days — pure for
    /// testability (deep review of #1804).
    fn drop_unsettled(
        points: Vec<PricePoint>,
        eastern_today: rustledger_core::NaiveDate,
    ) -> Vec<PricePoint> {
        points
            .into_iter()
            .filter(|p| p.date < eastern_today)
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_build_stock_url() {
        let source = AlphaVantageSource::new(Duration::from_secs(30));
        let url = source.build_stock_url("AAPL", "demo");
        assert!(url.contains("AAPL"));
        assert!(url.contains("GLOBAL_QUOTE"));
    }

    #[test]
    fn test_build_forex_url() {
        let source = AlphaVantageSource::new(Duration::from_secs(30));
        let url = source.build_forex_url("EUR", "USD", "demo");
        assert!(url.contains("EUR"));
        assert!(url.contains("USD"));
        assert!(url.contains("CURRENCY_EXCHANGE_RATE"));
    }

    /// Forex and crypto ticker forms refuse historical fetches BEFORE
    /// any network I/O — hermetic (#1802 source ports).
    #[test]
    fn fetch_window_refuses_forex_and_crypto_tickers_hermetically() {
        let source = AlphaVantageSource::new(Duration::from_secs(30));
        let window = DateWindow {
            start: rustledger_core::naive_date(2024, 1, 8).unwrap(),
            end: rustledger_core::naive_date(2024, 1, 15).unwrap(),
        };
        for ticker in ["EUR/USD", "CRYPTO:BTC"] {
            let pair = PricePair {
                ticker: ticker.to_string(),
                currency: "USD".to_string(),
            };
            let err = source
                .fetch_window(&pair, window)
                .expect_err("must refuse before any I/O");
            assert!(err.to_string().contains("stock tickers only"), "{err}");
        }
    }

    /// The still-open Eastern session's bar is dropped; completed days
    /// pass (pure helper — deep review of #1804: a UTC+8 user's local
    /// yesterday can be the LIVE US session).
    #[test]
    fn drop_unsettled_removes_the_open_sessions_bar() {
        let d = |day| rustledger_core::naive_date(2024, 1, day).unwrap();
        let point = |day| PricePoint {
            date: d(day),
            price: Decimal::ONE,
            currency: None,
        };
        let kept = AlphaVantageSource::drop_unsettled(vec![point(11), point(12)], d(12));
        assert_eq!(kept.len(), 1);
        assert_eq!(kept[0].date, d(11), "the eastern-today bar is dropped");
    }

    /// The forex refusal holds THROUGH the canonical dispatch, not just
    /// on a direct `fetch_window` call: a dated forex fetch must fail
    /// hermetically before the API-key check or any network I/O (deep
    /// review of #1804 — the old latest-only wiring pin was removed
    /// when alphavantage became window-capable).
    #[test]
    fn dated_forex_refuses_through_the_dispatch() {
        let source = AlphaVantageSource::new(Duration::from_secs(30));
        let request = crate::cmd::price::PriceRequest {
            ticker: "EUR/USD".to_string(),
            currency: "USD".to_string(),
            date: Some(rustledger_core::naive_date(2024, 1, 10).unwrap()),
        };
        let err = source
            .fetch_price(&request)
            .expect_err("must refuse before any I/O");
        assert!(err.to_string().contains("stock tickers only"), "{err}");
    }

    /// `TIME_SERIES_DAILY` parsing: every daily close becomes a dated
    /// point; malformed entries are skipped (hermetic fixture).
    #[test]
    fn parse_daily_series_extracts_all_closes() {
        let json: serde_json::Value = serde_json::json!({
            "Time Series (Daily)": {
                "2024-01-12": { "4. close": "185.9200" },
                "2024-01-11": { "4. close": "185.5900" },
                "not-a-date": { "4. close": "1.0" },
                "2024-01-10": { "1. open": "184.00" }
            }
        });
        let mut points = AlphaVantageSource::parse_daily_series(&json).expect("parses");
        points.sort_by_key(|p| p.date);
        assert_eq!(points.len(), 2, "malformed entries are skipped");
        assert_eq!(
            points[0].date,
            rustledger_core::naive_date(2024, 1, 11).unwrap()
        );
        assert_eq!(points[1].price.to_string(), "185.9200");
    }

    /// A rate-limit Note refuses instead of parsing garbage.
    #[test]
    fn parse_daily_series_surfaces_rate_limit_note() {
        let json: serde_json::Value = serde_json::json!({
            "Note": "Thank you for using Alpha Vantage! Our standard API rate limit is 25 requests per day."
        });
        let err = AlphaVantageSource::parse_daily_series(&json).expect_err("must refuse");
        assert!(err.to_string().contains("Alpha Vantage"), "{err}");
    }

    #[test]
    fn test_source_metadata() {
        let source = AlphaVantageSource::new(Duration::from_secs(30));
        assert_eq!(source.name(), "alphavantage");
        assert!(source.requires_api_key());
        assert_eq!(source.api_key_env_var(), Some("ALPHAVANTAGE_API_KEY"));
    }
}
