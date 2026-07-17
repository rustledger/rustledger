//! Yahoo Finance price source.
//!
//! Fetches stock, ETF, and cryptocurrency prices from Yahoo Finance.

use super::{PriceSource, user_agent};
use crate::cmd::price::{PriceRequest, PriceResponse};
use anyhow::{Context, Result};
use rustledger_core::NaiveDate;
use std::time::Duration;

/// Yahoo Finance price source.
///
/// Uses the Yahoo Finance API to fetch prices for stocks, ETFs, mutual funds,
/// and cryptocurrencies.
///
/// # Supported Symbols
///
/// - Stocks: `AAPL`, `MSFT`, `GOOGL`
/// - ETFs: `VTI`, `SPY`, `QQQ`
/// - Cryptocurrencies: `BTC-USD`, `ETH-USD`
/// - Forex: `EURUSD=X`, `GBPUSD=X`
/// - Mutual funds: Fund symbols
#[derive(Debug)]
pub struct YahooFinanceSource {}

impl YahooFinanceSource {
    /// Create a new Yahoo Finance source.
    pub const fn new(_timeout: Duration) -> Self {
        Self {}
    }

    /// Build the Yahoo Finance chart-API URL.
    ///
    /// Latest quote: a one-day range. Historical (#1794): a window of the
    /// five days up to and including the requested date, via epoch
    /// `period1`/`period2` — mirroring beanprice's `get_historical_price`,
    /// which fetches `time - 5d .. time` so weekends/holidays resolve to
    /// the preceding trading day.
    fn build_url(&self, symbol: &str, date: Option<NaiveDate>) -> Result<String> {
        match date {
            Some(d) => {
                let end = d
                    .tomorrow()
                    .context("date overflow")?
                    .to_zoned(jiff::tz::TimeZone::UTC)
                    .context("date out of range")?
                    .timestamp()
                    .as_second();
                let begin = d
                    .checked_sub(jiff::Span::new().days(5))
                    .context("date underflow")?
                    .to_zoned(jiff::tz::TimeZone::UTC)
                    .context("date out of range")?
                    .timestamp()
                    .as_second();
                Ok(format!(
                    "https://query1.finance.yahoo.com/v8/finance/chart/{symbol}?interval=1d&period1={begin}&period2={end}"
                ))
            }
            None => Ok(format!(
                "https://query1.finance.yahoo.com/v8/finance/chart/{symbol}?interval=1d&range=1d"
            )),
        }
    }

    /// Extract `(price, currency, effective-date)` from a chart response.
    ///
    /// Latest mode (`requested = None`): `meta.regularMarketPrice`, dated
    /// today. Historical mode: the LAST non-null close on or before the
    /// requested date, dated by its own quote timestamp — never the
    /// requested date (#1794: a Saturday request must emit Friday's close
    /// under Friday's date). Errors when the window holds no usable quote,
    /// instead of mislabeling the latest one.
    fn parse_chart(
        json: &serde_json::Value,
        requested: Option<NaiveDate>,
        ticker: &str,
    ) -> Result<(rust_decimal::Decimal, Option<String>, NaiveDate)> {
        // Check for errors in the response
        if let Some(chart) = json.get("chart")
            && let Some(error) = chart.get("error")
            && !error.is_null()
        {
            let description = error
                .get("description")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("Unknown error");
            anyhow::bail!("Yahoo Finance error: {description}");
        }

        let result = json
            .get("chart")
            .and_then(|c| c.get("result"))
            .and_then(|r| r.get(0))
            .with_context(|| format!("Invalid response structure for {ticker}"))?;
        let currency = result
            .get("meta")
            .and_then(|m| m.get("currency"))
            .and_then(serde_json::Value::as_str)
            .map(ToString::to_string);

        let Some(requested) = requested else {
            // Latest quote.
            let price_value = result
                .get("meta")
                .and_then(|m| m.get("regularMarketPrice"))
                .with_context(|| format!("No price found for {ticker}"))?;
            let price = crate::cmd::price::price_decimal_from_json(price_value)
                .with_context(|| format!("Invalid price for {ticker}"))?;
            return Ok((price, currency, jiff::Zoned::now().date()));
        };

        // Historical: walk timestamps/closes in parallel, keep the last
        // usable close on or before the requested date.
        let timestamps = result
            .get("timestamp")
            .and_then(serde_json::Value::as_array)
            .with_context(|| format!("No quotes for {ticker} in the requested window"))?;
        let closes = result
            .get("indicators")
            .and_then(|i| i.get("quote"))
            .and_then(|q| q.get(0))
            .and_then(|q| q.get("close"))
            .and_then(serde_json::Value::as_array)
            .with_context(|| format!("No close series for {ticker}"))?;

        let mut best: Option<(rust_decimal::Decimal, NaiveDate)> = None;
        for (ts, close) in timestamps.iter().zip(closes) {
            if close.is_null() {
                continue;
            }
            let Some(secs) = ts.as_i64() else { continue };
            let Ok(stamp) = jiff::Timestamp::from_second(secs) else {
                continue;
            };
            let quote_date = stamp.to_zoned(jiff::tz::TimeZone::UTC).date();
            if quote_date > requested {
                break;
            }
            if let Some(price) = crate::cmd::price::price_decimal_from_json(close) {
                best = Some((price, quote_date));
            }
        }

        let (price, date) = best.with_context(|| {
            format!(
                "no Yahoo quote for {ticker} on or before {requested} in the \
                 fetched window; the market may not have traded that week"
            )
        })?;
        Ok((price, currency, date))
    }
}

impl PriceSource for YahooFinanceSource {
    fn name(&self) -> &'static str {
        "yahoo"
    }

    fn description(&self) -> &'static str {
        "Yahoo Finance - stocks, ETFs, crypto, forex"
    }

    fn fetch_price(&self, request: &PriceRequest) -> Result<PriceResponse> {
        let url = self.build_url(&request.ticker, request.date)?;

        let mut response = ureq::get(&url)
            .header("User-Agent", user_agent())
            .call()
            .with_context(|| format!("Failed to fetch price for {}", request.ticker))?;

        let json: serde_json::Value = response
            .body_mut()
            .read_json()
            .with_context(|| format!("Failed to parse response for {}", request.ticker))?;

        let (price, currency, date) = Self::parse_chart(&json, request.date, &request.ticker)?;

        Ok(PriceResponse {
            price,
            currency: currency.unwrap_or_else(|| request.currency.clone()),
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
        let source = YahooFinanceSource::new(Duration::from_secs(30));
        let url = source.build_url("AAPL", None).expect("latest url");
        assert!(url.contains("AAPL"));
        assert!(url.contains("query1.finance.yahoo.com"));
        assert!(url.contains("range=1d"));

        // Historical: an epoch window bracketing the requested date, no
        // range param (#1794 — range=1d was the always-latest bug).
        let d = rustledger_core::naive_date(2025, 1, 2).unwrap();
        let url = source.build_url("AAPL", Some(d)).expect("historical url");
        assert!(url.contains("period1="), "{url}");
        assert!(url.contains("period2="), "{url}");
        assert!(!url.contains("range="), "{url}");
        // period2 is the exclusive end: midnight UTC of the day after.
        assert!(url.contains("period2=1735862400"), "{url}");
    }

    /// Fixture-driven historical parsing: Sat 2025-01-04 requested, the
    /// window holds Thu/Fri closes plus a null (market holiday) — the
    /// result is FRIDAY's close under FRIDAY's date, never the requested
    /// Saturday or the latest quote (#1794).
    #[test]
    fn parse_chart_historical_picks_last_close_on_or_before_date() {
        // 2025-01-02 (Thu) 14:30 UTC, 2025-01-03 (Fri), 2025-01-06 (Mon)
        let json: serde_json::Value = serde_json::json!({
            "chart": { "result": [{
                "meta": { "currency": "USD", "regularMarketPrice": 999.99 },
                "timestamp": [1_735_828_200_i64, 1_735_914_600_i64, 1_736_173_800_i64],
                "indicators": { "quote": [{ "close": [243.85, 243.36, 245.00] }] }
            }], "error": null }
        });
        let requested = rustledger_core::naive_date(2025, 1, 4).unwrap();
        let (price, currency, date) =
            YahooFinanceSource::parse_chart(&json, Some(requested), "AAPL").expect("parses");
        assert_eq!(price.to_string(), "243.36");
        assert_eq!(currency.as_deref(), Some("USD"));
        assert_eq!(date, rustledger_core::naive_date(2025, 1, 3).unwrap());
    }

    /// Null closes (holidays) are skipped, not treated as zero.
    #[test]
    fn parse_chart_skips_null_closes() {
        let json: serde_json::Value = serde_json::json!({
            "chart": { "result": [{
                "meta": { "currency": "USD" },
                "timestamp": [1_735_828_200_i64, 1_735_914_600_i64],
                "indicators": { "quote": [{ "close": [243.85, null] }] }
            }], "error": null }
        });
        let requested = rustledger_core::naive_date(2025, 1, 3).unwrap();
        let (price, _, date) =
            YahooFinanceSource::parse_chart(&json, Some(requested), "AAPL").expect("parses");
        assert_eq!(price.to_string(), "243.85");
        assert_eq!(date, rustledger_core::naive_date(2025, 1, 2).unwrap());
    }

    /// An empty window is a hard error — never the latest quote under a
    /// historical label (the exact corruption from #1794).
    #[test]
    fn parse_chart_errors_when_no_quote_in_window() {
        let json: serde_json::Value = serde_json::json!({
            "chart": { "result": [{
                "meta": { "currency": "USD", "regularMarketPrice": 999.99 },
                "timestamp": [1_736_173_800_i64],
                "indicators": { "quote": [{ "close": [245.00] }] }
            }], "error": null }
        });
        // Requested date precedes every quote in the window.
        let requested = rustledger_core::naive_date(2025, 1, 4).unwrap();
        let err = YahooFinanceSource::parse_chart(&json, Some(requested), "AAPL")
            .expect_err("must refuse");
        assert!(err.to_string().contains("on or before"), "{err}");
    }

    /// The latest path still reads regularMarketPrice.
    #[test]
    fn parse_chart_latest_uses_regular_market_price() {
        let json: serde_json::Value = serde_json::json!({
            "chart": { "result": [{
                "meta": { "currency": "USD", "regularMarketPrice": 243.85 }
            }], "error": null }
        });
        let (price, currency, _) =
            YahooFinanceSource::parse_chart(&json, None, "AAPL").expect("parses");
        assert_eq!(price.to_string(), "243.85");
        assert_eq!(currency.as_deref(), Some("USD"));
    }

    #[test]
    fn test_source_metadata() {
        let source = YahooFinanceSource::new(Duration::from_secs(30));
        assert_eq!(source.name(), "yahoo");
        assert!(!source.requires_api_key());
        assert!(source.description().contains("Yahoo"));
    }
}
