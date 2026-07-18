//! East Money Fund price source.
//!
//! Fetches Chinese mutual fund prices from East Money (天天基金).

use super::{DateWindow, HistoricalCoverage, PricePair, PricePoint, PriceSource, user_agent};
use crate::cmd::price::PriceResponse;
use anyhow::{Context, Result};
use rust_decimal::Decimal;
use std::str::FromStr;
use std::time::Duration;

/// East Money Fund price source.
///
/// Fetches net asset values (NAV) for Chinese mutual funds from
/// East Money (天天基金网, fundgz.1234567.com.cn).
/// No API key required.
///
/// # Supported Funds
///
/// Chinese mutual fund codes, typically 6 digits:
/// - `000001` - 华夏成长
/// - `110011` - 易方达中小盘
/// - etc.
#[derive(Debug)]
pub struct EastMoneyFundSource {}

impl EastMoneyFundSource {
    /// Create a new East Money Fund source.
    pub const fn new(_timeout: Duration) -> Self {
        Self {}
    }

    /// Build the East Money API URL.
    fn build_url(&self, code: &str) -> String {
        format!("https://fundgz.1234567.com.cn/js/{code}.js")
    }

    /// Parse JSONP response to extract JSON.
    fn parse_jsonp(&self, response: &str) -> Result<serde_json::Value> {
        let start = response
            .find('(')
            .with_context(|| "Invalid JSONP format: missing '('")?;
        let end = response
            .rfind(')')
            .with_context(|| "Invalid JSONP format: missing ')'")?;

        if start >= end {
            anyhow::bail!("Invalid JSONP format");
        }

        let json_str = &response[start + 1..end];
        serde_json::from_str(json_str).with_context(|| "Failed to parse JSON from JSONP")
    }

    /// Build the historical-NAV (`lsjz`, 历史净值) API URL for an
    /// inclusive [`DateWindow`] (#1802 source ports). `pageSize=49`
    /// comfortably covers the dispatch's trailing look-back window on
    /// the first page.
    fn build_history_url(fund_code: &str, window: DateWindow) -> String {
        format!(
            "https://api.fund.eastmoney.com/f10/lsjz?fundCode={fund_code}&pageIndex=1&pageSize=49&startDate={}&endDate={}",
            window.start, window.end
        )
    }

    /// Parse an `lsjz` response body into [`PricePoint`]s — an
    /// associated fn over the parsed [`serde_json::Value`] so it is
    /// unit-testable without HTTP (#1802 source ports).
    ///
    /// Each `Data.LSJZList` item carries `FSRQ` (the NAV's own civil
    /// date) and `DWJZ` (unit NAV, a string that can be empty). Items
    /// with a missing/unparsable date or NAV are SKIPPED, never
    /// today-labeled — a today-fallback on a historical item would be
    /// discarded by the dispatch's on-or-before selection, turning a
    /// served NAV into a spurious no-quote error (deep review of
    /// #1803).
    ///
    /// # Errors
    ///
    /// Errors when the response carries a non-zero `ErrCode` (the
    /// message is the feed's `ErrMsg`) or when `Data.LSJZList` is
    /// missing.
    fn parse_history(json: &serde_json::Value) -> Result<Vec<PricePoint>> {
        // Check for errors
        // ErrCode arrives as a number today; tolerate a string-typed
        // code too so a feed change cannot silently skip the check
        // (deep review of #1804).
        let err_code = json.get("ErrCode").and_then(|v| {
            v.as_i64()
                .or_else(|| v.as_str().and_then(|s| s.parse().ok()))
        });
        if let Some(code) = err_code
            && code != 0
        {
            let message = json
                .get("ErrMsg")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("Unknown error");
            anyhow::bail!("East Money error {code}: {message}");
        }

        let items = json
            .get("Data")
            .and_then(|d| d.get("LSJZList"))
            .and_then(serde_json::Value::as_array)
            .with_context(|| "Missing Data.LSJZList in response")?;

        let mut points = Vec::new();
        for item in items {
            let Some(date) = super::feed_date(item.get("FSRQ").and_then(serde_json::Value::as_str))
            else {
                continue;
            };
            // DWJZ is "" on days without a published NAV — skip, don't
            // error. The canonical JSON-price parser tolerates both
            // string and number shapes, like every sibling parser
            // (deep review of #1804).
            let Some(price) = item
                .get("DWJZ")
                .and_then(crate::cmd::price::price_decimal_from_json)
            else {
                continue;
            };
            points.push(PricePoint {
                date,
                price,
                // This source only serves CNY NAVs, same as the latest
                // path's hardcoded currency.
                currency: Some("CNY".to_string()),
            });
        }
        Ok(points)
    }
}

impl PriceSource for EastMoneyFundSource {
    fn name(&self) -> &'static str {
        "eastmoneyfund"
    }

    fn description(&self) -> &'static str {
        "East Money Fund - Chinese mutual fund NAVs (天天基金)"
    }

    fn fetch_latest(&self, pair: &PricePair) -> Result<PriceResponse> {
        let url = self.build_url(&pair.ticker);

        let mut response = ureq::get(&url)
            .header("User-Agent", user_agent())
            .header("Referer", "https://fund.eastmoney.com/")
            .call()
            .with_context(|| format!("Failed to fetch fund {}", pair.ticker))?;

        let body = response
            .body_mut()
            .read_to_string()
            .with_context(|| "Failed to read response")?;

        let json = self.parse_jsonp(&body)?;

        // Extract the estimated NAV (gsz) or actual NAV (dwjz)
        let price_str = json
            .get("gsz")
            .or_else(|| json.get("dwjz"))
            .and_then(serde_json::Value::as_str)
            .with_context(|| "Missing NAV in response")?;

        let price = Decimal::from_str(price_str)
            .with_context(|| format!("Failed to parse NAV: {price_str}"))?;

        // Get the date from gztime (估算时间) or jzrq (净值日期) — the
        // feed's own date, never the requested one (#1794; the inline
        // parse with a request.date fallback was the last un-canonical
        // copy of this extraction — round-4 deep review).
        let date = super::feed_date_or_today(
            json.get("gztime")
                .or_else(|| json.get("jzrq"))
                .and_then(serde_json::Value::as_str),
        );

        Ok(PriceResponse {
            price,
            currency: "CNY".to_string(),
            date,
            source: self.name().to_string(),
        })
    }

    fn historical_coverage(&self) -> HistoricalCoverage {
        // The lsjz endpoint serves each fund's NAV series back to its
        // inception (#1802 source ports); pre-inception dates surface
        // as the dispatch's clean no-quote error, not a refusal.
        HistoricalCoverage::Full
    }

    fn fetch_window(&self, pair: &PricePair, window: DateWindow) -> Result<Vec<PricePoint>> {
        // One page of 49 NAVs covers the dispatch's 7-day windows many
        // times over, but a wider window from a library caller would be
        // SILENTLY truncated to the newest page — refuse it explicitly
        // instead (deep review of #1804; paging support can come with a
        // real consumer).
        let span_days = (window.end - window.start).get_days().abs() + 1;
        if span_days > 49 {
            anyhow::bail!(
                "eastmoneyfund history fetches are limited to 49 days per request                  (window spans {span_days} days); narrow the window"
            );
        }
        let url = Self::build_history_url(&pair.ticker, window);

        // The lsjz API rejects requests without an eastmoney Referer,
        // so send the fund-detail origin alongside the shared
        // User-Agent (#1802 source ports).
        let mut response = ureq::get(&url)
            .header("User-Agent", user_agent())
            .header("Referer", "https://fundf10.eastmoney.com/")
            .call()
            .with_context(|| format!("Failed to fetch history for fund {}", pair.ticker))?;

        let json: serde_json::Value = response
            .body_mut()
            .read_json()
            .with_context(|| "Failed to parse East Money history response")?;

        Self::parse_history(&json)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_build_url() {
        let source = EastMoneyFundSource::new(Duration::from_secs(30));
        let url = source.build_url("000001");
        assert_eq!(url, "https://fundgz.1234567.com.cn/js/000001.js");
    }

    #[test]
    fn test_parse_jsonp() {
        let source = EastMoneyFundSource::new(Duration::from_secs(30));

        let jsonp = r#"jsonpgz({"fundcode":"000001","name":"Test Fund","gsz":"1.234"});"#;
        let json = source.parse_jsonp(jsonp).unwrap();

        assert_eq!(
            json.get("fundcode").and_then(serde_json::Value::as_str),
            Some("000001")
        );
        assert_eq!(
            json.get("gsz").and_then(serde_json::Value::as_str),
            Some("1.234")
        );
    }

    #[test]
    fn test_source_metadata() {
        let source = EastMoneyFundSource::new(Duration::from_secs(30));
        assert_eq!(source.name(), "eastmoneyfund");
        assert!(!source.requires_api_key());
    }

    #[test]
    fn test_build_history_url() {
        let window = DateWindow {
            start: rustledger_core::naive_date(2024, 1, 8).unwrap(),
            end: rustledger_core::naive_date(2024, 1, 15).unwrap(),
        };
        assert_eq!(
            EastMoneyFundSource::build_history_url("000001", window),
            "https://api.fund.eastmoney.com/f10/lsjz?fundCode=000001&pageIndex=1&pageSize=49\
             &startDate=2024-01-08&endDate=2024-01-15"
        );
    }

    /// Historical parsing (#1802 source ports): each `LSJZList` item's
    /// `FSRQ`/`DWJZ` becomes a CNY point; an empty `DWJZ` (a day with
    /// no published NAV) is skipped, not an error.
    #[test]
    fn test_parse_history() {
        let json = serde_json::json!({
            "Data": {
                "LSJZList": [
                    {"FSRQ": "2024-01-15", "DWJZ": "1.2345"},
                    {"FSRQ": "2024-01-12", "DWJZ": ""},
                    {"FSRQ": "2024-01-11", "DWJZ": "1.2000"},
                ]
            },
            "ErrCode": 0,
        });
        let points = EastMoneyFundSource::parse_history(&json).unwrap();
        assert_eq!(points.len(), 2, "the empty-DWJZ item is skipped");
        assert_eq!(
            points[0].date,
            rustledger_core::naive_date(2024, 1, 15).unwrap()
        );
        assert_eq!(points[0].price.to_string(), "1.2345");
        assert_eq!(points[0].currency.as_deref(), Some("CNY"));
        assert_eq!(
            points[1].date,
            rustledger_core::naive_date(2024, 1, 11).unwrap()
        );
        assert_eq!(points[1].price.to_string(), "1.2000");
    }

    /// A non-zero `ErrCode` bails with the feed's `ErrMsg`.
    #[test]
    fn test_parse_history_error_code() {
        let json = serde_json::json!({"ErrCode": 500, "ErrMsg": "no such fund"});
        let err = EastMoneyFundSource::parse_history(&json).expect_err("must bail");
        assert!(err.to_string().contains("no such fund"), "{err}");
    }
}
