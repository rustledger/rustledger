//! `CoinCap` price source.
//!
//! Fetches cryptocurrency prices from `CoinCap`.

use super::{PricePair, PriceSource, http_get_json};
use crate::cmd::price::PriceResponse;
use anyhow::{Context, Result};
use rust_decimal::Decimal;
use std::str::FromStr;
use std::time::Duration;

/// `CoinCap` price source.
///
/// Uses the `CoinCap` API (coincap.io) to fetch cryptocurrency prices.
/// Free tier with no API key required.
///
/// # Supported Symbols
///
/// - Cryptocurrencies by ID: `bitcoin`, `ethereum`, `solana`
/// - Upper-case symbols (`BTC`, `SHIB`): common ones from a built-in table,
///   others looked up in `CoinCap`'s asset list, as beanprice's `coincap`
///   looks up every upper-case symbol
#[derive(Debug)]
pub struct CoinCapSource {
    /// Whole-request timeout, applied to each request.
    timeout: Duration,
}

impl CoinCapSource {
    /// Create a new `CoinCap` source.
    pub const fn new(timeout: Duration) -> Self {
        Self { timeout }
    }

    /// Convert ticker to `CoinCap` asset ID, when that needs no request:
    /// a common symbol from this table, or an asset ID (`bitcoin`). `None`
    /// is any other upper-case symbol, which beanprice's `coincap` resolves
    /// by searching `CoinCap`'s asset list (#2866): see
    /// [`Self::id_from_asset_list`].
    fn ticker_to_id(ticker: &str) -> Option<String> {
        // Common mappings from symbol to CoinCap ID
        match ticker.to_uppercase().as_str() {
            "BTC" => Some("bitcoin".to_string()),
            "ETH" => Some("ethereum".to_string()),
            "SOL" => Some("solana".to_string()),
            "DOGE" => Some("dogecoin".to_string()),
            "ADA" => Some("cardano".to_string()),
            "XRP" => Some("xrp".to_string()),
            "DOT" => Some("polkadot".to_string()),
            "AVAX" => Some("avalanche".to_string()),
            "MATIC" => Some("polygon".to_string()),
            "LINK" => Some("chainlink".to_string()),
            "UNI" => Some("uniswap".to_string()),
            "LTC" => Some("litecoin".to_string()),
            "BCH" => Some("bitcoin-cash".to_string()),
            "ATOM" => Some("cosmos".to_string()),
            "XLM" => Some("stellar".to_string()),
            "ALGO" => Some("algorand".to_string()),
            "VET" => Some("vechain".to_string()),
            "FIL" => Some("filecoin".to_string()),
            "TRX" => Some("tron".to_string()),
            "ETC" => Some("ethereum-classic".to_string()),
            // beanprice reads a ticker as a symbol when Python's
            // `str.isupper()` holds: it has a letter and no lower-case one.
            _ if ticker.chars().any(|c| c.is_ascii_uppercase())
                && !ticker.chars().any(|c| c.is_ascii_lowercase()) =>
            {
                None
            }
            _ => Some(ticker.to_lowercase()),
        }
    }

    /// The asset ID for `symbol` in a `CoinCap` asset list, which is
    /// ordered by market cap: the first asset with that symbol (#2866).
    /// beanprice's `coincap` takes the first match the same way, but scans
    /// the unfiltered `/assets/` list, its first page of 100; rledger asks
    /// `/assets?search=SYMBOL`, which also finds a coin ranked below 100.
    ///
    /// The ID goes into a URL path, so one the provider returns is used
    /// only when it has the shape of a `CoinCap` ID: lower-case letters,
    /// digits and `-`.
    fn id_from_asset_list(json: &serde_json::Value, symbol: &str) -> Option<String> {
        let id = json
            .get("data")?
            .as_array()?
            .iter()
            .find(|asset| asset.get("symbol").and_then(serde_json::Value::as_str) == Some(symbol))?
            .get("id")?
            .as_str()?;
        let valid = !id.is_empty()
            && id
                .chars()
                .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-');
        valid.then(|| id.to_string())
    }

    /// The asset ID for `ticker`, searching the asset list when the table
    /// does not have it (see [`Self::ticker_to_id`]).
    ///
    /// # Errors
    ///
    /// The lookup failing, or no asset with a valid ID having the symbol.
    fn resolve_id(&self, ticker: &str) -> Result<String> {
        if let Some(id) = Self::ticker_to_id(ticker) {
            return Ok(id);
        }
        let json = http_get_json(
            &format!("{API}/assets?search={ticker}"),
            self.timeout,
            &[],
            &[],
            &format!("Failed to look up the CoinCap asset for {ticker}"),
        )?;
        Self::id_from_asset_list(&json, ticker)
            .with_context(|| format!("Could not find currency id with ticker '{ticker}'"))
    }

    /// Build the `CoinCap` API URL for an asset ID.
    fn build_url(id: &str) -> String {
        format!("{API}/assets/{id}")
    }
}

/// `CoinCap`'s API root.
const API: &str = "https://api.coincap.io/v2";

impl PriceSource for CoinCapSource {
    fn name(&self) -> &'static str {
        "coincap"
    }

    fn description(&self) -> &'static str {
        "CoinCap - cryptocurrency prices"
    }

    /// `CoinCap` quotes every asset in USD (#2866), so the ticker, upper-case,
    /// is the base of what is fetched: `BTC` is `BTC`. An asset ID such as
    /// `bitcoin` is its own base, `BITCOIN`, which no declared currency
    /// matches, so its inversion is refused.
    fn pair_base(&self, ticker: &str) -> Option<String> {
        Some(ticker.to_uppercase())
    }

    fn fetch_latest(&self, pair: &PricePair) -> Result<PriceResponse> {
        // Label read BEFORE the network fetch: a quote labeled with the
        // local day must carry the day the request was made, not a day
        // the clock rolled to during network I/O (round-4 deep review
        // of #1803 — the post-fetch read could poison the settled cache
        // with a D+1-labeled entry under a D key; round-5 review: the
        // round-4 edit had moved only this comment, not the read).
        let date = jiff::Zoned::now().date();
        let url = Self::build_url(&self.resolve_id(&pair.ticker)?);

        let json = http_get_json(
            &url,
            self.timeout,
            &[],
            &[],
            &format!("Failed to fetch price for {}", pair.ticker),
        )?;

        // Check for errors
        if let Some(error) = json.get("error") {
            let message = error.as_str().unwrap_or("Unknown error");
            anyhow::bail!("CoinCap error: {message}");
        }

        let data = json
            .get("data")
            .with_context(|| "Missing 'data' field in response")?;

        let price_str = data
            .get("priceUsd")
            .and_then(serde_json::Value::as_str)
            .with_context(|| "Missing 'priceUsd' field in response")?;

        let price = Decimal::from_str(price_str)
            .with_context(|| format!("Failed to parse price: {price_str}"))?;

        // CoinCap only provides USD prices
        Ok(PriceResponse {
            price,
            currency: "USD".to_string(),
            date,
            source: self.name().to_string(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every `CoinCap` quote is in USD, so the ticker is the base an
    /// inversion must be declared in (#2866).
    #[test]
    fn test_pair_base() {
        let source = CoinCapSource::new(Duration::from_secs(30));
        for (ticker, base) in [("BTC", "BTC"), ("btc", "BTC"), ("bitcoin", "BITCOIN")] {
            assert_eq!(source.pair_base(ticker).as_deref(), Some(base), "{ticker}");
        }
    }

    #[test]
    fn test_ticker_to_id() {
        let id = CoinCapSource::ticker_to_id;
        assert_eq!(id("BTC").as_deref(), Some("bitcoin"));
        assert_eq!(id("btc").as_deref(), Some("bitcoin"));
        assert_eq!(id("ETH").as_deref(), Some("ethereum"));
        assert_eq!(id("unknown").as_deref(), Some("unknown"));
        assert_eq!(id("shiba-inu").as_deref(), Some("shiba-inu"));
        // An upper-case symbol the table lacks is looked up, as
        // beanprice's `coincap` looks up every upper-case ticker (#2866).
        assert_eq!(id("SHIB"), None);
        assert_eq!(id("1INCH"), None);
    }

    /// The first asset with the symbol wins: the list is ordered by
    /// market cap, and beanprice takes the first match (#2866).
    #[test]
    fn test_id_from_asset_list() {
        let json = serde_json::json!({"data": [
            {"id": "shiba-inu", "symbol": "SHIB"},
            {"id": "shib-copy", "symbol": "SHIB"},
            {"id": "bitcoin", "symbol": "BTC"},
        ]});
        assert_eq!(
            CoinCapSource::id_from_asset_list(&json, "SHIB").as_deref(),
            Some("shiba-inu")
        );
        assert_eq!(CoinCapSource::id_from_asset_list(&json, "DOGE"), None);
        // A provider-returned ID goes into the URL path: one that is not
        // the shape of a CoinCap ID is not used.
        for id in ["../../admin", "a?b=c", "Bitcoin", ""] {
            let json = serde_json::json!({"data": [{"id": id, "symbol": "BAD"}]});
            assert_eq!(
                CoinCapSource::id_from_asset_list(&json, "BAD"),
                None,
                "{id:?}"
            );
        }
        assert_eq!(
            CoinCapSource::id_from_asset_list(&serde_json::json!({}), "SHIB"),
            None
        );
    }

    #[test]
    fn test_build_url() {
        let url = CoinCapSource::build_url("bitcoin");
        assert_eq!(url, "https://api.coincap.io/v2/assets/bitcoin");
    }

    #[test]
    fn test_source_metadata() {
        let source = CoinCapSource::new(Duration::from_secs(30));
        assert_eq!(source.name(), "coincap");
        assert!(!source.requires_api_key());
    }
}
