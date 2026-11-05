//! Rates API price source.
//!
//! Fetches currency exchange rates from Frankfurter
//! (<https://api.frankfurter.dev>), the open-source keyless API serving the
//! ECB reference rates, as beanprice's `ratesapi` source does.

use super::{DateWindow, HistoricalCoverage, PricePair, PricePoint, PriceSource, user_agent};
use crate::cmd::price::PriceResponse;
use anyhow::{Context, Result};
use rust_decimal::Decimal;
use rustledger_core::NaiveDate;
use std::time::Duration;

/// Frankfurter's API root.
const FRANKFURTER: &str = "https://api.frankfurter.dev/v1";

/// Rates API price source.
///
/// Fetches ECB reference rates from Frankfurter, as beanprice's `ratesapi`
/// does. No API key required. It used exchangerate.host, which now refuses
/// every request without a key.
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
            Some(d) => format!("{FRANKFURTER}/{d}?base={base}&symbols={target}"),
            None => format!("{FRANKFURTER}/latest?base={base}&symbols={target}"),
        }
    }

    /// Shared fetch + parse for the latest and dated endpoints (same
    /// response shape). Returns `(price, feed_date)`; a missing/broken
    /// `date` field falls back to `date_fallback` — today for a latest
    /// fetch, the requested day for a dated one (a today-fallback on a
    /// historical response would be discarded by the dispatch's
    /// on-or-before selection, deep review of #1803).
    fn fetch_rate(
        &self,
        url: &str,
        pair: &PricePair,
        date_fallback: NaiveDate,
    ) -> Result<(Decimal, NaiveDate)> {
        let mut response = match ureq::get(url).header("User-Agent", user_agent()).call() {
            Ok(response) => response,
            // Frankfurter answers an unknown currency with 404 `not found`.
            Err(ureq::Error::StatusCode(code)) => anyhow::bail!(
                "Rates API (Frankfurter) returned HTTP {code} for {}-{}; \
                 the currency pair may be unsupported (it serves the ECB reference currencies)",
                pair.ticker.to_uppercase(),
                pair.currency.to_uppercase()
            ),
            Err(e) => {
                return Err(e).with_context(|| format!("Failed to fetch rate for {}", pair.ticker));
            }
        };

        let body = response
            .body_mut()
            .read_to_string()
            .with_context(|| format!("Failed to read response for {}", pair.ticker))?;
        Self::parse_response(&body, pair, date_fallback)
    }

    /// Parse a Frankfurter response (`{"amount","base","date","rates"}`) into
    /// `(price, feed_date)`. Split from [`Self::fetch_rate`] so it is tested
    /// without the network.
    fn parse_response(
        body: &str,
        pair: &PricePair,
        date_fallback: NaiveDate,
    ) -> Result<(Decimal, NaiveDate)> {
        let json: serde_json::Value = serde_json::from_str(body)
            .with_context(|| format!("Failed to parse response for {}", pair.ticker))?;

        // An error body: Frankfurter's `{"message": ...}`, or the
        // `{"success": false, "error": {...}}` shape keyed services use.
        if json.get("rates").is_none() {
            let error = json
                .get("message")
                .and_then(serde_json::Value::as_str)
                .or_else(|| {
                    json.get("error")
                        .and_then(|e| e.get("info").or_else(|| e.get("type")))
                        .and_then(serde_json::Value::as_str)
                })
                .unwrap_or("no rates in the response");
            anyhow::bail!("Rates API error for {}: {error}", pair.ticker);
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

        // The feed's OWN quote date when present (Frankfurter
        // returns a "date" field) — on weekends the latest rate belongs
        // to Friday and must say so (deep review, same rule as ECB).
        let date = super::feed_date_or(
            json.get("date").and_then(serde_json::Value::as_str),
            date_fallback,
        );

        Ok((price, date))
    }

    /// The EU reference series publishes on WEEKDAYS only: a
    /// weekend-dated label can only be the provider echoing the
    /// requested URL date over Friday's rate, so clamp it back to the
    /// preceding Friday instead of writing a rate for a day the ECB
    /// published nothing (deep review of #1803). Weekday holidays are
    /// not detectable this way and pass through — a residual trust in
    /// the feed's labeling.
    ///
    /// Deliberate trade-off (round-2 review): some provider variants
    /// serve weekend-computed blended rates, which this clamp would
    /// relabel Friday. Spot FX does not reprice over the weekend — a
    /// "Saturday rate" is a carried-forward Friday rate — and this
    /// source models the EU reference series specifically; users who
    /// want weekend-marked data should use a source that has it
    /// natively (coinbase, yahoo).
    fn eu_reference_label(date: NaiveDate) -> NaiveDate {
        match date.weekday() {
            jiff::civil::Weekday::Saturday => {
                date.checked_sub(jiff::Span::new().days(1)).unwrap_or(date)
            }
            jiff::civil::Weekday::Sunday => {
                date.checked_sub(jiff::Span::new().days(2)).unwrap_or(date)
            }
            _ => date,
        }
    }
}

impl PriceSource for RatesApiSource {
    fn name(&self) -> &'static str {
        "ratesapi"
    }

    fn description(&self) -> &'static str {
        "Frankfurter - ECB reference exchange rates"
    }

    fn fetch_latest(&self, pair: &PricePair) -> Result<PriceResponse> {
        let url = self.build_url(
            &pair.ticker.to_uppercase(),
            &pair.currency.to_uppercase(),
            None,
        );
        let (price, date) = self.fetch_rate(&url, pair, jiff::Zoned::now().date())?;

        Ok(PriceResponse {
            price,
            currency: pair.currency.clone(),
            // The weekend clamp applies to the LATEST path too: a
            // Saturday-echoed /latest date over Friday's carried-forward
            // rate must say Friday, exactly as the window path does
            // (round-4 deep review of #1803 — the clamp existed on only
            // one of the two paths).
            date: Self::eu_reference_label(date),
            source: self.name().to_string(),
        })
    }

    fn historical_coverage(&self) -> HistoricalCoverage {
        // Frankfurter serves the EU reference series, which
        // begins 1999-01-04 (the euro's first trading day).
        HistoricalCoverage::Since(
            rustledger_core::naive_date(1999, 1, 4).expect("static date is valid"),
        )
    }

    fn fetch_window(&self, pair: &PricePair, window: DateWindow) -> Result<Vec<PricePoint>> {
        // The dispatch routes requested==today to fetch_latest before
        // the window path, so window.end here is always a COMPLETED
        // day (round-3 review of #1803 removed the per-source same-day
        // delegations along with the straddle).
        // The dated endpoint answers a single day; one request at the
        // window's end covers the dispatch's on-or-before selection.
        // The feed's date label is trusted EXCEPT when it echoes a
        // weekend day — see eu_reference_label.
        let url = self.build_url(
            &pair.ticker.to_uppercase(),
            &pair.currency.to_uppercase(),
            Some(window.end),
        );
        let (price, date) = self.fetch_rate(&url, pair, window.end)?;
        Ok(vec![PricePoint {
            date: Self::eu_reference_label(date),
            price,
            // The feed reports no currency; the dispatch substitutes
            // the request's (carrying a copy here would shadow that
            // canonical fallback — deep review of #1803).
            currency: None,
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

    /// Weekend-dated labels can only be the provider echoing the URL
    /// date over Friday's rate — the EU reference series publishes on
    /// weekdays only, so the label clamps to the preceding Friday
    /// (deep review of #1803).
    #[test]
    fn eu_reference_label_clamps_weekends_to_friday() {
        let fri = rustledger_core::naive_date(2024, 1, 12).unwrap();
        let sat = rustledger_core::naive_date(2024, 1, 13).unwrap();
        let sun = rustledger_core::naive_date(2024, 1, 14).unwrap();
        let mon = rustledger_core::naive_date(2024, 1, 15).unwrap();
        assert_eq!(RatesApiSource::eu_reference_label(sat), fri);
        assert_eq!(RatesApiSource::eu_reference_label(sun), fri);
        assert_eq!(RatesApiSource::eu_reference_label(fri), fri);
        assert_eq!(RatesApiSource::eu_reference_label(mon), mon);
    }

    fn usd_eur() -> PricePair {
        PricePair {
            ticker: "USD".to_string(),
            currency: "EUR".to_string(),
        }
    }

    fn day(y: i32, m: u32, d: u32) -> NaiveDate {
        rustledger_core::naive_date(y, m, d).unwrap()
    }

    #[test]
    fn test_build_url_uses_frankfurter() {
        let source = RatesApiSource::new(Duration::from_secs(30));
        assert_eq!(
            source.build_url("USD", "EUR", None),
            "https://api.frankfurter.dev/v1/latest?base=USD&symbols=EUR"
        );
        assert_eq!(
            source.build_url("USD", "EUR", Some(day(2026, 10, 30))),
            "https://api.frankfurter.dev/v1/2026-10-30?base=USD&symbols=EUR"
        );
    }

    /// Canned Frankfurter bodies, as `curl` returned them.
    #[test]
    fn test_parse_response_latest_and_historical() {
        let latest = r#"{"amount":1.0,"base":"USD","date":"2026-11-04","rates":{"EUR":0.88755}}"#;
        let (price, date) =
            RatesApiSource::parse_response(latest, &usd_eur(), day(2026, 11, 5)).unwrap();
        assert_eq!(price.to_string(), "0.88755");
        assert_eq!(date, day(2026, 11, 4));

        let historical =
            r#"{"amount":1.0,"base":"USD","date":"2026-10-30","rates":{"EUR":0.89509}}"#;
        let (price, date) =
            RatesApiSource::parse_response(historical, &usd_eur(), day(2026, 10, 30)).unwrap();
        assert_eq!(price.to_string(), "0.89509");
        assert_eq!(date, day(2026, 10, 30));
    }

    /// A weekend request (2026-11-01, a Sunday) answers with the previous
    /// business day's rate and date; the label keeps the feed's date.
    #[test]
    fn test_parse_response_weekend_request_keeps_the_business_day() {
        let body = r#"{"amount":1.0,"base":"USD","date":"2026-10-30","rates":{"EUR":0.89509}}"#;
        let (_, date) = RatesApiSource::parse_response(body, &usd_eur(), day(2026, 11, 1)).unwrap();
        assert_eq!(RatesApiSource::eu_reference_label(date), day(2026, 10, 30));
    }

    #[test]
    fn test_parse_response_reports_error_bodies() {
        let pair = usd_eur();
        let today = day(2026, 11, 4);
        // Frankfurter, unknown currency.
        let err = RatesApiSource::parse_response(r#"{"message":"not found"}"#, &pair, today)
            .unwrap_err()
            .to_string();
        assert!(err.contains("not found"), "{err}");
        // A keyed service refusing a keyless request.
        let keyed = r#"{"success":false,"error":{"code":101,"type":"missing_access_key","info":"You have not supplied an API Access Key."}}"#;
        let err = RatesApiSource::parse_response(keyed, &pair, today)
            .unwrap_err()
            .to_string();
        assert!(err.contains("API Access Key"), "{err}");
        // Not JSON at all.
        let err = format!(
            "{:#}",
            RatesApiSource::parse_response("<html>502 Bad Gateway</html>", &pair, today)
                .unwrap_err()
        );
        assert!(err.contains("Failed to parse response"), "{err}");
        // The pair is missing from the rates.
        let err = RatesApiSource::parse_response(
            r#"{"amount":1.0,"base":"USD","date":"2026-11-04","rates":{"GBP":0.7}}"#,
            &pair,
            today,
        )
        .unwrap_err()
        .to_string();
        assert!(err.contains("EUR"), "{err}");
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
