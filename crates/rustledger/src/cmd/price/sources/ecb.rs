//! European Central Bank (ECB) price source.
//!
//! Fetches currency exchange rates from the ECB.

use super::{DateWindow, HistoricalCoverage, PricePair, PricePoint, PriceSource, user_agent};
use crate::cmd::price::PriceResponse;
use anyhow::{Context, Result};
use rust_decimal::Decimal;
use rustledger_core::NaiveDate;
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

    /// Build the ECB API URL for a currency's EUR-reference series:
    /// the latest observation, or every observation in a civil-date
    /// window (`startPeriod`/`endPeriod`, #1802 source ports — the SDMX
    /// data API serves the full series back to 1999, not just the
    /// 90-day XML feed).
    fn build_url(&self, currency: &str, window: Option<DateWindow>) -> String {
        let selector = match window {
            Some(w) => format!("startPeriod={}&endPeriod={}", w.start, w.end),
            None => "lastNObservations=1".to_string(),
        };
        format!(
            "https://data-api.ecb.europa.eu/service/data/EXR/D.{currency}.EUR.SP00.A?{selector}&format=jsondata"
        )
    }
}

impl EcbSource {
    /// Fetch a currency's EUR-reference series: every observation the
    /// selector matched, as `(date, rate)` with rate = "units of
    /// currency per 1 EUR". Observations with missing dates or
    /// unparsable rates are skipped.
    fn fetch_series(
        &self,
        currency: &str,
        window: Option<DateWindow>,
        undated_fallback: Option<NaiveDate>,
    ) -> Result<Vec<(NaiveDate, Decimal)>> {
        let url = self.build_url(&currency.to_uppercase(), window);

        let mut response = match ureq::get(&url)
            .header("User-Agent", user_agent())
            .header("Accept", "application/json")
            .call()
        {
            Ok(response) => response,
            // The SDMX API answers an EMPTY selection with HTTP 404
            // ("No results found") — that is the fetch_window
            // contract's "no observations here" (a clean no-quote at
            // the dispatch), not a transport failure (deep review of
            // #1804: a frozen HRK window read as a network error).
            Err(ureq::Error::StatusCode(404)) => return Ok(Vec::new()),
            Err(e) => {
                return Err(e).with_context(|| format!("Failed to fetch ECB rate for {currency}"));
            }
        };

        let json: serde_json::Value = response
            .body_mut()
            .read_json()
            .with_context(|| format!("Failed to parse ECB response for {currency}"))?;

        Self::parse_series(&json, undated_fallback)
    }

    /// Parse an SDMX-JSON EXR response into dated observations.
    /// Factored off the HTTP fetch so fixtures can exercise it without
    /// a network (#1802 source ports).
    ///
    /// An observation whose date cannot be resolved takes
    /// `undated_fallback` when given (the LATEST-fetch convention:
    /// today), and is SKIPPED when `None` (the historical convention —
    /// deep review of #1804: dropping the latest fallback turned rates
    /// main served into "No observations" errors).
    fn parse_series(
        json: &serde_json::Value,
        undated_fallback: Option<NaiveDate>,
    ) -> Result<Vec<(NaiveDate, Decimal)>> {
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

        // Observation keys index into the date dimension's value list.
        let date_values = json
            .get("structure")
            .and_then(|s| s.get("dimensions"))
            .and_then(|d| d.get("observation"))
            .and_then(|o| o.as_array())
            .and_then(|a| a.first())
            .and_then(|t| t.get("values"))
            .and_then(|v| v.as_array());

        let mut points = Vec::with_capacity(observations.len());
        for (obs_key, obs_value) in observations {
            let Some(rate) = obs_value
                .as_array()
                .and_then(|a| a.first())
                .and_then(crate::cmd::price::price_decimal_from_json)
            else {
                continue;
            };
            let resolved = date_values
                .and_then(|values| {
                    let idx: usize = obs_key.parse().ok()?;
                    values.get(idx)
                })
                .and_then(|v| v.get("id"))
                .and_then(serde_json::Value::as_str);
            let Some(date) = super::feed_date(resolved).or(undated_fallback) else {
                continue;
            };
            points.push((date, rate));
        }
        Ok(points)
    }

    /// Latest single rate for a currency: the greatest-dated
    /// observation of a `lastNObservations=1` fetch.
    fn fetch_rate(&self, currency: &str) -> Result<(Decimal, NaiveDate)> {
        // Latest convention: an observation with an unresolvable date
        // is today-labeled, matching feed_date_or's LATEST rule (deep
        // review of #1804 restored this after the series refactor
        // dropped it).
        let series = self.fetch_series(currency, None, Some(jiff::Zoned::now().date()))?;
        let (date, rate) = series
            .into_iter()
            .max_by_key(|(date, _)| *date)
            .with_context(|| "No observations in ECB response")?;
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

    fn fetch_latest(&self, pair: &PricePair) -> Result<PriceResponse> {
        let ticker = pair.ticker.to_uppercase();
        let currency = pair.currency.to_uppercase();

        // ECB provides rates as "X per 1 EUR"
        // We need to handle three cases (identity pairs and dated
        // requests never reach here — the trait's canonical dispatch
        // handles both, #1802):
        // 1. ticker=EUR, currency=X: fetch X rate, return as-is (X per EUR)
        // 2. ticker=X, currency=EUR: fetch X rate, invert it (EUR per X)
        // 3. ticker=X, currency=Y: fetch both, compute cross-rate (Y per X)

        if ticker == "EUR" {
            // EUR -> X: fetch X rate (X per EUR), return as-is
            let (rate, rate_date) = self.fetch_rate(&currency)?;
            return Ok(PriceResponse {
                price: rate,
                currency,
                // The ECB feed's OWN reference date — never the requested one:
                // on weekends/holidays the latest rate is Friday's and must
                // be labeled as such (#1794).
                date: rate_date,
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
                // The ECB feed's OWN reference date — never the requested one:
                // on weekends/holidays the latest rate is Friday's and must
                // be labeled as such (#1794).
                date: rate_date,
                source: self.name().to_string(),
            });
        }

        // Cross-rate: X -> Y via EUR
        // X per EUR and Y per EUR => Y per X = (Y per EUR) / (X per EUR)
        let (ticker_rate, ticker_date) = self.fetch_rate(&ticker)?;
        let (currency_rate, currency_date) = self.fetch_rate(&currency)?;

        // The two legs are separate fetches of a once-daily feed; if they
        // reference different days, dividing a Monday rate by a Friday
        // rate yields a number that is not a valid rate for ANY date.
        // Refuse rather than emit a silently corrupted directive
        // (round-2 deep review — min() labeling was not sound). Two
        // causes: a transient publication straddle (gap of a day or a
        // weekend) and a permanently frozen series — the ECB stops
        // publishing discontinued currencies (HRK, RUB) but keeps
        // serving their final observation, so a large gap gets the
        // permanent diagnosis instead of useless "retry" advice
        // (rounds 3-4 deep review).
        if ticker_date != currency_date {
            let (older_date, older_ccy) = if ticker_date < currency_date {
                (ticker_date, &ticker)
            } else {
                (currency_date, &currency)
            };
            let gap_days = (ticker_date - currency_date).get_days().abs();
            if gap_days > 5 {
                anyhow::bail!(
                    "ECB's {older_ccy} series is frozen at {older_date} — the ECB \
                     no longer publishes it (discontinued currency); use a \
                     different price source for {older_ccy}"
                );
            }
            anyhow::bail!(
                "ECB returned different reference dates for the two legs of \
                 {ticker}/{currency} ({ticker_date} vs {currency_date}) — the \
                 fetches likely straddled the daily ~16:00 CET publication; \
                 retry shortly"
            );
        }

        if ticker_rate.is_zero() {
            anyhow::bail!("Cannot compute cross-rate: zero rate for {ticker}");
        }

        let cross_rate = currency_rate / ticker_rate;

        Ok(PriceResponse {
            price: cross_rate,
            currency,
            // Same rule as the direct branches: the feed's own reference
            // date (both legs agree — checked above).
            date: ticker_date,
            source: self.name().to_string(),
        })
    }

    fn historical_coverage(&self) -> HistoricalCoverage {
        // The SDMX data API serves the EU reference series from the
        // euro's first trading day (#1802 source ports).
        HistoricalCoverage::Since(
            rustledger_core::naive_date(1999, 1, 4).expect("static date is valid"),
        )
    }

    fn fetch_window(&self, pair: &PricePair, window: DateWindow) -> Result<Vec<PricePoint>> {
        let ticker = pair.ticker.to_uppercase();
        let currency = pair.currency.to_uppercase();

        // Same three shapes as fetch_latest, but over the window's full
        // series (#1802 source ports). Every point carries the feed's
        // own reference date.
        if ticker == "EUR" {
            // EUR -> X: the series as-is (X per EUR).
            let series = self.fetch_series(&currency, Some(window), None)?;
            return Ok(series
                .into_iter()
                .map(|(date, rate)| PricePoint {
                    date,
                    price: rate,
                    currency: Some(currency.clone()),
                })
                .collect());
        }

        if currency == "EUR" {
            // X -> EUR: invert each observation (EUR per X). Zero rates
            // are skipped rather than erroring the whole window.
            let series = self.fetch_series(&ticker, Some(window), None)?;
            return Ok(series
                .into_iter()
                .filter(|(_, rate)| !rate.is_zero())
                .map(|(date, rate)| PricePoint {
                    date,
                    price: Decimal::ONE / rate,
                    currency: Some(currency.clone()),
                })
                .collect());
        }

        // Cross-rate: X -> Y via EUR, joined PER REFERENCE DAY. The
        // per-date join replaces fetch_latest's leg-date-mismatch bail
        // for the historical path: days where only one leg published
        // (or a leg is frozen — HRK, RUB) simply produce no point, and
        // the dispatch's on-or-before selection works with what joined.
        let ticker_series = self.fetch_series(&ticker, Some(window), None)?;
        let currency_series = self.fetch_series(&currency, Some(window), None)?;
        let by_date: std::collections::HashMap<NaiveDate, Decimal> =
            ticker_series.into_iter().collect();
        Ok(currency_series
            .into_iter()
            .filter_map(|(date, currency_rate)| {
                let ticker_rate = by_date.get(&date)?;
                if ticker_rate.is_zero() {
                    return None;
                }
                Some(PricePoint {
                    date,
                    price: currency_rate / *ticker_rate,
                    currency: Some(currency.clone()),
                })
            })
            .collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_build_url() {
        let source = EcbSource::new(Duration::from_secs(30));
        let url = source.build_url("USD", None);
        assert!(url.contains("USD"));
        assert!(url.contains("data-api.ecb.europa.eu"));
        assert!(url.contains("lastNObservations=1"), "{url}");

        // Historical (#1802): the window selects a startPeriod/endPeriod
        // range instead of the latest observation.
        let window = DateWindow {
            start: rustledger_core::naive_date(2024, 1, 8).unwrap(),
            end: rustledger_core::naive_date(2024, 1, 15).unwrap(),
        };
        let url = source.build_url("USD", Some(window));
        assert!(url.contains("startPeriod=2024-01-08"), "{url}");
        assert!(url.contains("endPeriod=2024-01-15"), "{url}");
        assert!(!url.contains("lastNObservations"), "{url}");
    }

    /// SDMX-JSON parsing: every observation becomes a dated point via
    /// the structure's date dimension; malformed entries are skipped
    /// (#1802 source ports — hermetic, no network).
    #[test]
    fn parse_series_extracts_all_dated_observations() {
        let json: serde_json::Value = serde_json::json!({
            "dataSets": [{ "series": { "0:0:0:0:0": { "observations": {
                "0": [1.0876],
                "1": [1.0921],
                "2": [null]
            }}}}],
            "structure": { "dimensions": { "observation": [{ "values": [
                { "id": "2024-01-11" },
                { "id": "2024-01-12" },
                { "id": "2024-01-15" }
            ]}]}}
        });
        let mut series = EcbSource::parse_series(&json, None).expect("parses");
        series.sort_by_key(|(date, _)| *date);
        assert_eq!(series.len(), 2, "the null observation is skipped");
        assert_eq!(
            series[0].0,
            rustledger_core::naive_date(2024, 1, 11).unwrap()
        );
        assert_eq!(series[0].1.to_string(), "1.0876");
        assert_eq!(
            series[1].0,
            rustledger_core::naive_date(2024, 1, 12).unwrap()
        );
    }

    #[test]
    fn test_source_metadata() {
        let source = EcbSource::new(Duration::from_secs(30));
        assert_eq!(source.name(), "ecb");
        assert!(!source.requires_api_key());
    }

    #[test]
    fn test_eur_to_eur_returns_one() {
        // EUR to EUR should always return 1.0 without network access —
        // served by the trait's canonical identity arm (#1802).
        use crate::cmd::price::PriceRequest;
        let source = EcbSource::new(Duration::from_secs(30));
        let request = PriceRequest::new("EUR", "EUR");
        let response = source.fetch_price(&request).unwrap();
        assert_eq!(response.price, Decimal::ONE);
        assert_eq!(response.currency, "EUR");
    }

    /// Any identity pair — not just EUR/EUR — answers 1.0 for any
    /// requested date without network access. The pre-#1801 cross-rate
    /// path gave dated USD/USD = 1 too; the dispatch must keep that
    /// (round-2 deep review, hoisted into the trait in #1802).
    #[test]
    fn dated_non_eur_identity_returns_one() {
        use crate::cmd::price::PriceRequest;
        let source = EcbSource::new(Duration::from_secs(30));
        let date = rustledger_core::naive_date(2024, 6, 30).unwrap();
        let mut request = PriceRequest::new("USD", "USD");
        request.date = Some(date);
        let response = source.fetch_price(&request).unwrap();
        assert_eq!(response.price, Decimal::ONE);
        assert_eq!(response.date, date);
    }
}
