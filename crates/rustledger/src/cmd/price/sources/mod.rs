//! Price source implementations.
//!
//! This module contains all built-in price source implementations and the
//! `PriceSource` trait that defines the interface for all sources.

mod alphavantage;
mod coinbase;
mod coincap;
mod coinmarketcap;
mod eastmoneyfund;
mod ecb;
mod oanda;
mod quandl;
mod ratesapi;
mod tsp;
mod yahoo;

pub use alphavantage::AlphaVantageSource;
pub use coinbase::CoinbaseSource;
pub use coincap::CoinCapSource;
pub use coinmarketcap::CoinMarketCapSource;
pub use eastmoneyfund::EastMoneyFundSource;
pub use ecb::EcbSource;
pub use oanda::OandaSource;
pub use quandl::QuandlSource;
pub use ratesapi::RatesApiSource;
pub use tsp::TspSource;
pub use yahoo::YahooFinanceSource;

use super::{PriceRequest, PriceResponse};
use anyhow::Result;

/// Reject a historical `--date` on a source that can only fetch the
/// LATEST quote.
///
/// Labeling the latest price with an arbitrary historical date silently
/// corrupts price archives (#1794 — Yahoo emitted the live quote under
/// `--date 2000-01-03`). A latest-only source must refuse instead.
/// Today's date is allowed: the latest quote genuinely belongs to today.
///
/// # Errors
/// Errors when `request.date` names a day other than today.
pub(super) fn reject_historical_date(
    source: &str,
    request: &crate::cmd::price::PriceRequest,
) -> anyhow::Result<()> {
    if let Some(date) = request.date
        && date != jiff::Zoned::now().date()
    {
        anyhow::bail!(
            "the '{source}' source only provides the latest quote and cannot fetch {} \
             for {date}; drop --date, or use a source with historical support \
             (e.g. yahoo)",
            request.ticker
        );
    }
    Ok(())
}

/// Trait for price data sources.
///
/// All price sources must implement this trait. The trait is object-safe
/// to allow dynamic dispatch through `Arc<dyn PriceSource>`.
///
/// # Implementation Notes
///
/// Source implementations store a `timeout` field for future use. Currently,
/// ureq 3.x doesn't support timeout on individual requests (only on the Agent).
/// A future enhancement could use `ureq::Agent` with timeout configuration.
pub trait PriceSource: Send + Sync {
    /// Returns the unique name of this source.
    fn name(&self) -> &'static str;

    /// Returns a human-readable description of this source.
    fn description(&self) -> &'static str;

    /// Indicates if this source requires an API key.
    fn requires_api_key(&self) -> bool {
        false
    }

    /// Returns the environment variable name for the API key, if required.
    fn api_key_env_var(&self) -> Option<&'static str> {
        None
    }

    /// Fetch a price for the given request.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The network request fails
    /// - The response cannot be parsed
    /// - The ticker is not found
    /// - The API key is missing (for sources that require it)
    fn fetch_price(&self, request: &PriceRequest) -> Result<PriceResponse>;
}

/// Helper function to build a User-Agent header for HTTP requests.
pub(crate) const fn user_agent() -> &'static str {
    "Mozilla/5.0 (compatible; rustledger/1.0; +https://github.com/rustledger/rustledger)"
}

#[cfg(test)]
mod guard_tests {
    use crate::cmd::price::PriceRequest;

    fn request(date: Option<rustledger_core::NaiveDate>) -> PriceRequest {
        PriceRequest {
            ticker: "AAPL".to_string(),
            currency: "USD".to_string(),
            date,
        }
    }

    /// Latest-only sources refuse a historical --date instead of
    /// mislabeling the current quote (#1794).
    #[test]
    fn historical_date_is_rejected() {
        let yesterday = jiff::Zoned::now()
            .date()
            .yesterday()
            .expect("valid yesterday");
        let err = super::reject_historical_date("coinbase", &request(Some(yesterday)))
            .expect_err("must refuse");
        assert!(err.to_string().contains("latest quote"), "{err}");
        assert!(err.to_string().contains("coinbase"), "{err}");
    }

    /// Today's date is allowed — the latest quote genuinely belongs to
    /// today — and no date always passes.
    #[test]
    fn today_and_absent_date_pass() {
        let today = jiff::Zoned::now().date();
        assert!(super::reject_historical_date("coinbase", &request(Some(today))).is_ok());
        assert!(super::reject_historical_date("coinbase", &request(None)).is_ok());
    }
}
