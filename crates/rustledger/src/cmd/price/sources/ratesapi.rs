//! Rates API price source.
//!
//! Fetches currency exchange rates from Frankfurter
//! (<https://api.frankfurter.dev>), the open-source keyless API serving the
//! ECB reference rates, the provider beanprice's `ratesapi` source uses.

use super::{
    DateWindow, HistoricalCoverage, PricePair, PricePoint, PriceSource, http_get, split_dash_pair,
};
use crate::cmd::price::PriceResponse;
use anyhow::{Context, Result};
use rust_decimal::Decimal;
use rustledger_core::NaiveDate;
use std::time::Duration;

/// Frankfurter's API root.
const FRANKFURTER: &str = "https://api.frankfurter.dev/v1";

/// Rates API price source.
///
/// Fetches ECB reference rates from Frankfurter, the provider beanprice's
/// `ratesapi` uses. The ticker is beanprice's `BASE-SYMBOL` (`EUR-USD`, the
/// rate of EUR in USD), or the base currency alone (`EUR`, quoted in the
/// request's currency). No API key required. It used exchangerate.host,
/// which now refuses every request without a key.
///
/// # Supported Currencies
///
/// All major world currencies:
/// - USD, EUR, GBP, JPY, CHF, CAD, AUD, CNY, INR, etc.
#[derive(Debug)]
pub struct RatesApiSource {
    /// Whole-request timeout, applied to each request.
    timeout: Duration,
}

impl RatesApiSource {
    /// Create a new Rates API source.
    pub const fn new(timeout: Duration) -> Self {
        Self { timeout }
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
        // A 4xx/5xx is read as a response, not turned into a bare
        // `StatusCode` error, so Frankfurter's `{"message": ...}` reaches
        // the user.
        let reply = http_get(url, self.timeout, &[])
            .with_context(|| format!("Failed to fetch rate for {}", pair.ticker))?;
        Self::handle_response(reply.status, &reply.body, pair, date_fallback)
    }

    /// Turn an HTTP status and body into `(price, feed_date)`, the step after
    /// the request on every fetch. A non-2xx status is an error naming the
    /// pair and the provider's message (Frankfurter answers 404 `not found`
    /// for an unknown currency, an out-of-range date or a malformed code). Split from
    /// [`Self::fetch_rate`] so it is tested without the network.
    fn handle_response(
        status: u16,
        body: &str,
        pair: &PricePair,
        date_fallback: NaiveDate,
    ) -> Result<(Decimal, NaiveDate)> {
        if !(200..300).contains(&status) {
            let message = serde_json::from_str::<serde_json::Value>(body)
                .ok()
                .and_then(|json| {
                    json.get("message")
                        .and_then(serde_json::Value::as_str)
                        .map(str::to_string)
                });
            let pair_name = format!(
                "{}-{}",
                pair.ticker.to_uppercase(),
                pair.currency.to_uppercase()
            );
            match message {
                Some(message) => anyhow::bail!(
                    "Rates API (Frankfurter) returned HTTP {status} for {pair_name}: {message}"
                ),
                None if (400..500).contains(&status) => anyhow::bail!(
                    "Rates API (Frankfurter) returned HTTP {status} for {pair_name}; \
                     the currency pair may be unsupported (it serves the ECB reference currencies)"
                ),
                None => anyhow::bail!(
                    "Rates API (Frankfurter) returned HTTP {status} for {pair_name}; \
                     the service may be unavailable, try again later"
                ),
            }
        }
        Self::parse_response(body, pair, date_fallback)
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

    /// beanprice's `ratesapi` ticker `BASE-SYMBOL` (`USD-EUR`) is the
    /// rate of BASE in SYMBOL (#2866); rledger's own form, the base alone
    /// (`USD`, quoted in the requested currency), still works.
    fn bean_price_pair(&self, pair: PricePair) -> PricePair {
        match split_dash_pair(&pair.ticker) {
            Some((ticker, currency)) => PricePair {
                ticker: ticker.to_string(),
                currency: currency.to_string(),
            },
            None => pair,
        }
    }

    /// `BASE-SYMBOL` names its pair, based in BASE (#2866).
    fn pair_base(&self, ticker: &str) -> Option<String> {
        split_dash_pair(ticker).map(|(base, _)| base.to_string())
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

    /// The base of the pair a ticker names, which a `^` inversion must
    /// be declared in (#2866).
    #[test]
    fn test_pair_base() {
        let source = RatesApiSource::new(Duration::from_secs(30));
        assert_eq!(
            source.pair_base("USD-EUR").as_deref(),
            Some("USD"),
            "USD-EUR"
        );
        assert_eq!(source.pair_base("EUR"), None, "EUR");
    }

    fn pair(ticker: &str, currency: &str) -> PricePair {
        PricePair {
            ticker: ticker.to_string(),
            currency: currency.to_string(),
        }
    }

    fn read(source: &dyn PriceSource, ticker: &str, currency: &str) -> (String, String) {
        let pair = source.bean_price_pair(pair(ticker, currency));
        (pair.ticker, pair.currency)
    }

    /// beanprice's `ratesapi` `BASE-SYMBOL` names the pair; rledger's bare
    /// base keeps the requested currency (#2866).
    #[test]
    fn test_bean_price_pair() {
        let source = RatesApiSource::new(Duration::from_secs(30));
        assert_eq!(
            read(&source, "USD-EUR", "EUR"),
            ("USD".to_string(), "EUR".to_string())
        );
        assert_eq!(
            read(&source, "EUR-GBP", "EUR"),
            ("EUR".to_string(), "GBP".to_string())
        );
        assert_eq!(
            read(&source, "USD", "EUR"),
            ("USD".to_string(), "EUR".to_string())
        );
        // Not beanprice's `^(\w+)-(\w+)$`: left as it is.
        assert_eq!(
            read(&source, "USD-EUR-X", "EUR"),
            ("USD-EUR-X".to_string(), "EUR".to_string())
        );
        assert_eq!(
            read(&source, "-EUR", "EUR"),
            ("-EUR".to_string(), "EUR".to_string())
        );
    }

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

    /// HTTP errors go through the same step as a live response: the status
    /// and body, as Frankfurter sent them (`curl`), reach the user.
    #[test]
    fn test_handle_response_reports_frankfurter_http_errors() {
        let today = day(2026, 11, 4);
        for (status, body, pair, want) in [
            (
                404,
                r#"{"message":"not found"}"#,
                ("USD", "XXX"),
                "HTTP 404 for USD-XXX: not found",
            ),
            (
                422,
                r#"{"message":"bad currency pair"}"#,
                ("EUR", "EUR"),
                "HTTP 422 for EUR-EUR: bad currency pair",
            ),
            (
                422,
                r#"{"message":"invalid date"}"#,
                ("USD", "EUR"),
                "HTTP 422 for USD-EUR: invalid date",
            ),
        ] {
            let pair = PricePair {
                ticker: pair.0.to_string(),
                currency: pair.1.to_string(),
            };
            let err = RatesApiSource::handle_response(status, body, &pair, today)
                .unwrap_err()
                .to_string();
            assert!(err.contains(want), "{err}");
        }
        // No JSON message: a 5xx says the service may be down, a 4xx that the
        // pair may be unsupported.
        let err =
            RatesApiSource::handle_response(502, "<html>Bad Gateway</html>", &usd_eur(), today)
                .unwrap_err()
                .to_string();
        assert!(err.contains("HTTP 502 for USD-EUR"), "{err}");
        assert!(err.contains("may be unavailable"), "{err}");
        let err = RatesApiSource::handle_response(404, "<html>Not Found</html>", &usd_eur(), today)
            .unwrap_err()
            .to_string();
        assert!(err.contains("may be unsupported"), "{err}");
        // A 2xx body is parsed as a rate.
        let ok = r#"{"amount":1.0,"base":"USD","date":"2026-11-04","rates":{"EUR":0.88755}}"#;
        let (price, _) = RatesApiSource::handle_response(200, ok, &usd_eur(), today).unwrap();
        assert_eq!(price.to_string(), "0.88755");
    }

    #[test]
    fn test_new_keeps_the_timeout() {
        let source = RatesApiSource::new(Duration::from_secs(7));
        assert_eq!(source.timeout, Duration::from_secs(7));
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
