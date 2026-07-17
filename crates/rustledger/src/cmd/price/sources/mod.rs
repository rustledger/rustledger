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

/// Reject a past or future `--date` on a source that can only fetch the
/// LATEST quote.
///
/// Labeling the latest price with an arbitrary historical date silently
/// corrupts price archives (#1794 — Yahoo emitted the live quote under
/// `--date 2000-01-03`). Matching beanprice, a dated fetch requires a
/// source with real historical support — with one exception: `--date
/// <today>` is allowed, because the latest quote IS a valid answer for
/// today and the emitted directive carries the response's own date
/// anyway (round-2 deep review: nightly `--date $(date +%F)` runs
/// worked on every source before #1801 and must keep working).
/// Date-independent identity branches (e.g. USD→USD = 1.0) early-return
/// BEFORE this guard.
///
/// # Errors
/// Errors whenever `request.date` is set to any day other than today.
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

    /// Latest-only sources refuse any past or future --date instead of
    /// mislabeling the current quote (#1794). Today's date is the one
    /// exception: the latest quote is a valid answer for today, and
    /// pre-#1801 nightly `--date $(date +%F)` runs must keep working
    /// (round-2 deep review).
    #[test]
    fn past_and_future_dates_are_rejected_today_passes() {
        let past = rustledger_core::naive_date(2000, 1, 3).expect("valid date");
        let err = super::reject_historical_date("coinbase", &request(Some(past)))
            .expect_err("must refuse");
        assert!(err.to_string().contains("latest quote"), "{err}");
        assert!(err.to_string().contains("coinbase"), "{err}");

        let today = jiff::Zoned::now().date();
        let future = today
            .checked_add(jiff::Span::new().days(7))
            .expect("valid date");
        assert!(
            super::reject_historical_date("coinbase", &request(Some(future))).is_err(),
            "a future date must be refused — the latest quote is not a quote for next week"
        );

        assert!(
            super::reject_historical_date("coinbase", &request(Some(today))).is_ok(),
            "--date <today> is a valid request for the latest quote"
        );
    }

    /// No date always passes.
    #[test]
    fn absent_date_passes() {
        assert!(super::reject_historical_date("coinbase", &request(None)).is_ok());
    }
}

#[cfg(test)]
mod guard_wiring_tests {
    use crate::cmd::price::{PriceConfig, PriceRequest, PriceSourceRegistry};

    /// Drift guard (deep review of #1801): every latest-only builtin must
    /// actually CALL `reject_historical_date` from `fetch_price`. The
    /// guard fires before any network I/O, so a hermetic dated fetch must
    /// fail with the guard's message — a source that forgot the guard
    /// would instead surface a network/parse error (or worse, succeed).
    /// `yahoo` (real historical support) and `external` (forwards the
    /// date to the user's command) are exempt by design.
    #[test]
    fn every_latest_only_source_rejects_dated_fetches() {
        let registry = PriceSourceRegistry::new(&PriceConfig::default());
        let past = rustledger_core::naive_date(2000, 1, 3).expect("valid date");
        for name in [
            "alphavantage",
            "coinbase",
            "coincap",
            "coinmarketcap",
            "eastmoneyfund",
            "ecb",
            "oanda",
            "quandl",
            "ratesapi",
            "tsp",
        ] {
            let source = registry
                .get(name)
                .unwrap_or_else(|| panic!("builtin source '{name}' must exist"));
            let request = PriceRequest {
                ticker: "AAPL".to_string(),
                currency: "USD".to_string(),
                date: Some(past),
            };
            let err = source
                .fetch_price(&request)
                .expect_err("dated fetch must be refused before any I/O");
            assert!(
                err.to_string().contains("latest quote"),
                "source '{name}' did not fire the historical-date guard: {err}"
            );
        }
    }
}
