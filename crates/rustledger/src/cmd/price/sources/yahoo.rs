//! Yahoo Finance price source.
//!
//! Fetches stock, ETF, and cryptocurrency prices from Yahoo Finance.

use super::{DateWindow, HistoricalCoverage, PricePair, PricePoint, PriceSource, user_agent};
use crate::cmd::price::PriceResponse;
use anyhow::{Context, Result};
use rustledger_core::NaiveDate;
use std::time::Duration;

/// A resolved exchange timezone (or fixed-offset fallback) for
/// classifying bar timestamps — see [`YahooFinanceSource::exchange_clock`].
struct ExchangeClock {
    tz: Option<jiff::tz::TimeZone>,
    gmtoffset: i64,
}

impl ExchangeClock {
    /// The exchange-local civil day `secs` falls on.
    fn civil_date(&self, secs: i64) -> Option<NaiveDate> {
        if let Some(tz) = &self.tz {
            return jiff::Timestamp::from_second(secs)
                .ok()
                .map(|t| t.to_zoned(tz.clone()).date());
        }
        jiff::Timestamp::from_second(secs.checked_add(self.gmtoffset)?)
            .ok()
            .map(|t| t.to_zoned(jiff::tz::TimeZone::UTC).date())
    }
}

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
    /// Latest quote (`window = None`): a one-day range. Historical
    /// (#1794): an epoch `period1`/`period2` range spanning the civil
    /// window padded a day on each side (UTC midnights) — the epoch
    /// bounds are fetch SLOP, not the classification: a bar's day is
    /// decided by the exchange-local date in `parse_points`, and the
    /// padding covers every exchange UTC offset (deep review of #1801:
    /// NZX/ASX sessions cross UTC midnight).
    fn build_url(&self, symbol: &str, window: Option<DateWindow>) -> Result<String> {
        match window {
            Some(w) => {
                let end = w
                    .end
                    .checked_add(jiff::Span::new().days(2))
                    .context("date overflow")?
                    .to_zoned(jiff::tz::TimeZone::UTC)
                    .context("date out of range")?
                    .timestamp()
                    .as_second();
                let begin = w
                    .start
                    .checked_sub(jiff::Span::new().days(1))
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
    /// Latest mode: `meta.regularMarketPrice`, labeled with the quote's
    /// own trading day.
    fn parse_latest(
        json: &serde_json::Value,
        ticker: &str,
    ) -> Result<(rust_decimal::Decimal, Option<String>, NaiveDate)> {
        let result = Self::chart_result(json, ticker)?;
        let meta = result.get("meta");
        let currency = meta
            .and_then(|m| m.get("currency"))
            .and_then(serde_json::Value::as_str)
            .map(ToString::to_string);

        // Latest quote — labeled with the QUOTE's own trading day
        // (meta.regularMarketTime) when present, not the local clock:
        // fetching on a weekend must date the price Friday (#1794).
        let price_value = meta
            .and_then(|m| m.get("regularMarketPrice"))
            .with_context(|| format!("No price found for {ticker}"))?;
        let price = crate::cmd::price::price_decimal_from_json(price_value)
            .with_context(|| format!("Invalid price for {ticker}"))?;
        // No regularMarketTime → no honest date for the quote → error,
        // never a local-clock guess: a Saturday fetch would label
        // Friday's price with Saturday (#1794-lite), and the --date
        // <today> path now routes through here too (round-4 deep
        // review of #1803). The field is present for every tradeable
        // instrument in practice.
        let clock = Self::exchange_clock(result);
        let date = meta
            .and_then(|m| m.get("regularMarketTime"))
            .and_then(serde_json::Value::as_i64)
            .and_then(|secs| clock.civil_date(secs))
            .with_context(|| {
                format!("Yahoo response for {ticker} carried no regularMarketTime; cannot date the quote")
            })?;
        Ok((price, currency, date))
    }

    /// Historical mode: every non-null daily close in the response as a
    /// raw dated point — classified by the EXCHANGE's civil day, priced
    /// by its close. Selection is NOT done here: the trait's canonical
    /// dispatch owns on-or-before selection and labeling (#1802), so
    /// this parser cannot mislabel anything.
    fn parse_points(json: &serde_json::Value, ticker: &str) -> Result<Vec<PricePoint>> {
        let result = Self::chart_result(json, ticker)?;
        let currency = result
            .get("meta")
            .and_then(|m| m.get("currency"))
            .and_then(serde_json::Value::as_str)
            .map(ToString::to_string);

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

        let clock = Self::exchange_clock(result);
        let mut points = Vec::with_capacity(timestamps.len());
        for (ts, close) in timestamps.iter().zip(closes) {
            if close.is_null() {
                continue;
            }
            let Some(secs) = ts.as_i64() else { continue };
            let Some(date) = clock.civil_date(secs) else {
                continue;
            };
            if let Some(price) = crate::cmd::price::price_decimal_from_json(close) {
                points.push(PricePoint {
                    date,
                    price,
                    currency: currency.clone(),
                });
            }
        }
        Ok(points)
    }

    /// Shared error-check + result extraction for chart responses.
    fn chart_result<'a>(
        json: &'a serde_json::Value,
        ticker: &str,
    ) -> Result<&'a serde_json::Value> {
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
        json.get("chart")
            .and_then(|c| c.get("result"))
            .and_then(|r| r.get(0))
            .with_context(|| format!("Invalid response structure for {ticker}"))
    }

    /// The exchange clock for classifying bar timestamps, resolved ONCE
    /// per response (the tz-database lookup and meta traversal are
    /// loop-invariant — deep review of #1803).
    ///
    /// Quote timestamps are exchange-session times; classified by UTC
    /// date, NZX/ASX bars shift onto the wrong day — the wrong-date
    /// class #1794 fixed. Prefer `meta.exchangeTimezoneName` (what
    /// beanprice uses): a real timezone handles a DST switch inside the
    /// fetch window, where `meta.gmtoffset` — a single response-time
    /// offset — would misclassify pre-switch midnight-anchored bars by
    /// a day. Falls back to gmtoffset when the name is absent or the tz
    /// database is unavailable (#1801 rounds 2-4).
    fn exchange_clock(result: &serde_json::Value) -> ExchangeClock {
        let meta = result.get("meta");
        let tz = meta
            .and_then(|m| m.get("exchangeTimezoneName"))
            .and_then(serde_json::Value::as_str)
            .and_then(|name| jiff::tz::TimeZone::get(name).ok());
        let gmtoffset = meta
            .and_then(|m| m.get("gmtoffset"))
            .and_then(serde_json::Value::as_i64)
            .unwrap_or(0);
        ExchangeClock { tz, gmtoffset }
    }

    /// Shared HTTP GET + JSON parse for the chart endpoint.
    fn get_chart(&self, url: &str, ticker: &str) -> Result<serde_json::Value> {
        let mut response = ureq::get(url)
            .header("User-Agent", user_agent())
            .call()
            .with_context(|| format!("Failed to fetch price for {ticker}"))?;
        response
            .body_mut()
            .read_json()
            .with_context(|| format!("Failed to parse response for {ticker}"))
    }
}

impl PriceSource for YahooFinanceSource {
    fn name(&self) -> &'static str {
        "yahoo"
    }

    fn description(&self) -> &'static str {
        "Yahoo Finance - stocks, ETFs, crypto, forex"
    }

    fn fetch_latest(&self, pair: &PricePair) -> Result<PriceResponse> {
        let url = self.build_url(&pair.ticker, None)?;
        let json = self.get_chart(&url, &pair.ticker)?;
        let (price, currency, date) = Self::parse_latest(&json, &pair.ticker)?;

        Ok(PriceResponse {
            price,
            currency: currency.unwrap_or_else(|| pair.currency.clone()),
            date,
            source: self.name().to_string(),
        })
    }

    fn historical_coverage(&self) -> HistoricalCoverage {
        HistoricalCoverage::Full
    }

    fn fetch_window(&self, pair: &PricePair, window: DateWindow) -> Result<Vec<PricePoint>> {
        let url = self.build_url(&pair.ticker, Some(window))?;
        let json = self.get_chart(&url, &pair.ticker)?;
        Self::parse_points(&json, &pair.ticker)
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

        // Historical: an epoch range bracketing the civil window, no
        // range param (#1794 -- range=1d was the always-latest bug).
        // The dispatch builds windows as `requested-6 ..= requested`;
        // build_url pads the epoch bounds a day each side for exchange
        // UTC offsets.
        let end = rustledger_core::naive_date(2025, 1, 2).unwrap();
        let start = end.checked_sub(jiff::Span::new().days(6)).unwrap();
        let url = source
            .build_url("AAPL", Some(DateWindow { start, end }))
            .expect("historical url");
        assert!(url.contains("period1="), "{url}");
        assert!(url.contains("period2="), "{url}");
        assert!(!url.contains("range="), "{url}");
        // period2: midnight UTC two days after the window end (slop).
        assert!(url.contains("period2=1735948800"), "{url}");
    }

    /// Fixture-driven historical parsing: the response holds Thu/Fri/Mon
    /// closes. `parse_points` returns ALL of them as raw dated points --
    /// selection belongs to the dispatch, which for a Saturday request
    /// picks FRIDAY's close under FRIDAY's date (#1794), exercised here
    /// through the same canonical `select_on_or_before`.
    #[test]
    fn parse_points_returns_all_bars_and_selection_picks_friday() {
        // 2025-01-02 (Thu) 14:30 UTC, 2025-01-03 (Fri), 2025-01-06 (Mon)
        let json: serde_json::Value = serde_json::json!({
            "chart": { "result": [{
                "meta": { "currency": "USD", "regularMarketPrice": 999.99 },
                "timestamp": [1_735_828_200_i64, 1_735_914_600_i64, 1_736_173_800_i64],
                "indicators": { "quote": [{ "close": [243.85, 243.36, 245.00] }] }
            }], "error": null }
        });
        let points = YahooFinanceSource::parse_points(&json, "AAPL").expect("parses");
        assert_eq!(points.len(), 3);
        assert_eq!(
            points[1].date,
            rustledger_core::naive_date(2025, 1, 3).unwrap()
        );
        assert_eq!(points[1].currency.as_deref(), Some("USD"));

        let requested = rustledger_core::naive_date(2025, 1, 4).unwrap();
        let picked = super::super::select_on_or_before(points, requested).expect("some");
        assert_eq!(picked.price.to_string(), "243.36");
        assert_eq!(
            picked.date,
            rustledger_core::naive_date(2025, 1, 3).unwrap()
        );
    }

    /// Null closes (holidays) are skipped, not treated as zero.
    #[test]
    fn parse_points_skips_null_closes() {
        let json: serde_json::Value = serde_json::json!({
            "chart": { "result": [{
                "meta": { "currency": "USD" },
                "timestamp": [1_735_828_200_i64, 1_735_914_600_i64],
                "indicators": { "quote": [{ "close": [243.85, null] }] }
            }], "error": null }
        });
        let points = YahooFinanceSource::parse_points(&json, "AAPL").expect("parses");
        assert_eq!(points.len(), 1);
        assert_eq!(
            points[0].date,
            rustledger_core::naive_date(2025, 1, 2).unwrap()
        );
    }

    /// A window whose every quote is AFTER the requested date yields no
    /// selection -- the dispatch turns that into a hard error, never the
    /// latest quote under a historical label (the exact #1794 corruption).
    #[test]
    fn selection_refuses_when_no_quote_on_or_before() {
        let json: serde_json::Value = serde_json::json!({
            "chart": { "result": [{
                "meta": { "currency": "USD", "regularMarketPrice": 999.99 },
                "timestamp": [1_736_173_800_i64],
                "indicators": { "quote": [{ "close": [245.00] }] }
            }], "error": null }
        });
        let points = YahooFinanceSource::parse_points(&json, "AAPL").expect("parses");
        let requested = rustledger_core::naive_date(2025, 1, 4).unwrap();
        assert!(super::super::select_on_or_before(points, requested).is_none());
    }

    /// Exchange-timezone classification (deep review): NZX trades at
    /// UTC+12 in July (NZST), so Tuesday's 10:00 NZST bar is Monday
    /// 22:00 UTC. Classified by UTC date it would masquerade as Monday;
    /// classified by exchange-local date (meta.gmtoffset -- no
    /// exchangeTimezoneName in this fixture, exercising the fallback)
    /// each bar lands on its own trading day.
    #[test]
    fn parse_points_classifies_by_exchange_timezone() {
        // gmtoffset +12h (43200). Monday 2026-07-13 10:00 NZST
        // = Sunday 2026-07-12 22:00 UTC = 1783893600.
        // Tuesday 2026-07-14 10:00 NZST = Monday 2026-07-13 22:00 UTC
        // = 1783980000 -- by UTC date it masquerades as Monday.
        let json: serde_json::Value = serde_json::json!({
            "chart": { "result": [{
                "meta": { "currency": "NZD", "gmtoffset": 43200 },
                "timestamp": [1_783_893_600_i64, 1_783_980_000_i64],
                "indicators": { "quote": [{ "close": [1.11, 2.22] }] }
            }], "error": null }
        });
        let points = YahooFinanceSource::parse_points(&json, "AIR.NZ").expect("parses");
        assert_eq!(
            points[0].date,
            rustledger_core::naive_date(2026, 7, 13).unwrap()
        );
        assert_eq!(
            points[1].date,
            rustledger_core::naive_date(2026, 7, 14).unwrap()
        );

        // The Monday request must get Monday's bar, not Tuesday's.
        let requested = rustledger_core::naive_date(2026, 7, 13).unwrap();
        let picked = super::super::select_on_or_before(points, requested).expect("some");
        assert_eq!(picked.price.to_string(), "1.11");
    }

    /// A DST switch inside the fetch window (round-2 deep review of
    /// #1801): meta.gmtoffset is the offset at RESPONSE time, so
    /// applying it to a bar from before the switch shifts
    /// midnight-anchored bars by an hour -- a full civil day for FX bars
    /// stamped at local 00:00. exchangeTimezoneName resolves each bar
    /// with the offset in force at ITS OWN instant.
    #[test]
    fn parse_points_handles_dst_transition_via_timezone_name() {
        // America/New_York, DST ends 2025-11-02.
        // Fri 2025-10-31 00:00 EDT (UTC-4) = 04:00 UTC = 1761883200 --
        //   post-switch gmtoffset -18000 would misdate it 2025-10-30.
        // Tue 2025-11-04 00:00 EST (UTC-5) = 05:00 UTC = 1762232400.
        let json: serde_json::Value = serde_json::json!({
            "chart": { "result": [{
                "meta": {
                    "currency": "USD",
                    "exchangeTimezoneName": "America/New_York",
                    "gmtoffset": -18000
                },
                "timestamp": [1_761_883_200_i64, 1_762_232_400_i64],
                "indicators": { "quote": [{ "close": [1.11, 2.22] }] }
            }], "error": null }
        });
        let points = YahooFinanceSource::parse_points(&json, "EURUSD=X").expect("parses");
        assert_eq!(
            points[0].date,
            rustledger_core::naive_date(2025, 10, 31).unwrap(),
            "classified by its own instant's offset"
        );
        assert_eq!(
            points[1].date,
            rustledger_core::naive_date(2025, 11, 4).unwrap()
        );
    }

    /// The latest path labels with the quote's own trading day
    /// (regularMarketTime + gmtoffset), not the local clock.
    #[test]
    fn parse_latest_uses_quote_own_date() {
        // Friday 2026-07-10 16:00 US/Eastern (UTC-4) = 20:00 UTC
        // = 1783713600; gmtoffset -14400.
        let json: serde_json::Value = serde_json::json!({
            "chart": { "result": [{
                "meta": {
                    "currency": "USD",
                    "regularMarketPrice": 243.85,
                    "regularMarketTime": 1_783_713_600_i64,
                    "gmtoffset": -14400
                }
            }], "error": null }
        });
        let (_, _, date) = YahooFinanceSource::parse_latest(&json, "AAPL").expect("parses");
        assert_eq!(date, rustledger_core::naive_date(2026, 7, 10).unwrap());
    }

    /// The latest path reads regularMarketPrice and requires the
    /// quote's own timestamp.
    #[test]
    fn parse_latest_refuses_undatable_quotes() {
        // No regularMarketTime → refuse rather than guess a local date
        // (round-4 deep review of #1803: the local-today fallback was a
        // #1794-lite residue newly reachable via --date <today>).
        let json: serde_json::Value = serde_json::json!({
            "chart": { "result": [{
                "meta": { "currency": "USD", "regularMarketPrice": 243.85 }
            }], "error": null }
        });
        let err = YahooFinanceSource::parse_latest(&json, "AAPL").expect_err("must refuse");
        assert!(err.to_string().contains("regularMarketTime"), "{err}");

        // With the timestamp present, price and currency parse as before.
        let json: serde_json::Value = serde_json::json!({
            "chart": { "result": [{
                "meta": {
                    "currency": "USD",
                    "regularMarketPrice": 243.85,
                    "regularMarketTime": 1_783_713_600_i64,
                    "gmtoffset": -14400
                }
            }], "error": null }
        });
        let (price, currency, _) = YahooFinanceSource::parse_latest(&json, "AAPL").expect("parses");
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
