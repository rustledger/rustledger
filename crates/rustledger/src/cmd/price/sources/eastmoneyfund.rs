//! East Money Fund price source.
//!
//! Fetches Chinese mutual fund prices from East Money (天天基金).

use super::{PriceSource, user_agent};
use crate::cmd::price::{PriceRequest, PriceResponse};
use anyhow::{Context, Result};
use chrono::Utc;
use rust_decimal::Decimal;
use rustledger_core::NaiveDate;
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
}

impl PriceSource for EastMoneyFundSource {
    fn name(&self) -> &'static str {
        "eastmoneyfund"
    }

    fn description(&self) -> &'static str {
        "East Money Fund - Chinese mutual fund NAVs (天天基金)"
    }

    fn fetch_price(&self, request: &PriceRequest) -> Result<PriceResponse> {
        let url = self.build_url(&request.ticker);

        let mut response = ureq::get(&url)
            .header("User-Agent", user_agent())
            .header("Referer", "https://fund.eastmoney.com/")
            .call()
            .with_context(|| format!("Failed to fetch fund {}", request.ticker))?;

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

        // Get the date from gztime (估算时间) or jzrq (净值日期)
        let date = json
            .get("gztime")
            .or_else(|| json.get("jzrq"))
            .and_then(serde_json::Value::as_str)
            .and_then(|s| {
                // Try different date formats
                NaiveDate::parse_from_str(s, "%Y-%m-%d")
                    .or_else(|_| {
                        // Try parsing just the date portion (first 10 chars)
                        // Use char_indices for UTF-8 safety
                        if let Some((idx, _)) = s.char_indices().nth(10) {
                            NaiveDate::parse_from_str(&s[..idx], "%Y-%m-%d")
                        } else if s.len() >= 10 && s.is_char_boundary(10) {
                            NaiveDate::parse_from_str(&s[..10], "%Y-%m-%d")
                        } else {
                            // Return an error that will be converted to None by and_then
                            NaiveDate::parse_from_str("", "%Y-%m-%d")
                        }
                    })
                    .ok()
            })
            .unwrap_or_else(|| request.date.unwrap_or_else(|| NaiveDate::today()));

        Ok(PriceResponse {
            price,
            currency: "CNY".to_string(),
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
}
