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

/// The civil day of this process's FIRST guarded fetch.
///
/// Used only to widen the guard by one day across a midnight straddle —
/// see [`latest_date_window_ok`]. It deliberately does NOT replace the
/// live clock (round-4 deep review: an unconditional process-wide latch
/// froze "today" forever for long-lived library embedders, refusing
/// every fetch after the first midnight).
static FIRST_FETCH_DAY: std::sync::OnceLock<rustledger_core::NaiveDate> =
    std::sync::OnceLock::new();

/// Pure decision for the latest-only guard: `date` is fetchable when it
/// IS `today`, or when the run started on `date` and midnight has since
/// passed (`date` is yesterday AND equals the first-fetch day). The
/// second arm keeps a `--date $(date +%F)` batch working to its end
/// when it straddles midnight (round-3 review), without letting a
/// long-lived embedder replay its start day weeks later — the window
/// never widens past one day (round-4 review).
fn latest_date_window_ok(
    date: rustledger_core::NaiveDate,
    today: rustledger_core::NaiveDate,
    first_fetch_day: rustledger_core::NaiveDate,
) -> bool {
    date == today
        || (date == first_fetch_day
            && today.checked_sub(jiff::Span::new().days(1)).ok() == Some(date))
}

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
/// worked on every source before #1801 and must keep working). A batch
/// that straddles midnight stays accepted — see
/// [`latest_date_window_ok`].
/// Date-independent identity branches (e.g. USD→USD = 1.0) early-return
/// BEFORE this guard but refuse future labels via
/// [`identity_label_date`].
///
/// # Errors
/// Errors whenever `request.date` is outside the accepted window.
pub(super) fn reject_historical_date(
    source: &str,
    request: &crate::cmd::price::PriceRequest,
) -> anyhow::Result<()> {
    if let Some(date) = request.date {
        let today = jiff::Zoned::now().date();
        let first_fetch_day = *FIRST_FETCH_DAY.get_or_init(|| today);
        if !latest_date_window_ok(date, today, first_fetch_day) {
            anyhow::bail!(
                "the '{source}' source only provides the latest quote and cannot fetch {} \
                 for {date}; drop --date, or use a source with historical support \
                 (e.g. yahoo)",
                request.ticker
            );
        }
    }
    Ok(())
}

/// Date label for a date-independent identity answer (X→X = 1.0).
///
/// Identity is numerically correct for any PAST day, which is why the
/// identity branches sit ABOVE [`reject_historical_date`] — but a
/// FUTURE label would fabricate a directive for a day that hasn't
/// happened, which every guarded path refuses; refuse it here too
/// (round-4 deep review: `--date 2030-01-01` on an ecb/ratesapi
/// identity pair emitted `2030-01-01 price USD 1 USD` and cached it).
///
/// # Errors
/// Errors when `request.date` is after today.
pub(super) fn identity_label_date(
    source: &str,
    request: &crate::cmd::price::PriceRequest,
) -> anyhow::Result<rustledger_core::NaiveDate> {
    let today = jiff::Zoned::now().date();
    match request.date {
        Some(date) if date > today => anyhow::bail!(
            "the '{source}' source cannot label a price with the future date {date}; \
             use a date on or before today"
        ),
        Some(date) => Ok(date),
        None => Ok(today),
    }
}

/// Parse a feed-supplied date label — either a bare `YYYY-MM-DD` or the
/// date prefix of a `YYYY-MM-DD HH:MM:SS` timestamp — falling back to
/// the local today when the field is absent or malformed.
///
/// Canonical helper for the "quote's OWN date" rule (#1794): a source
/// labels its response with the feed's reference date, never the
/// requested date and never the local clock when the feed says
/// otherwise. Round-3 deep review: the per-source copies of this
/// extraction had already drifted once (alphavantage forex/crypto kept
/// the local-clock label while the stock path was fixed), so the
/// parsing lives here and the sources pass in the raw field.
pub(super) fn feed_date_or_today(raw: Option<&str>) -> rustledger_core::NaiveDate {
    raw.and_then(|s| s.get(..10))
        .and_then(|s| s.parse::<rustledger_core::NaiveDate>().ok())
        .unwrap_or_else(|| jiff::Zoned::now().date())
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

    /// The acceptance window: today always; yesterday ONLY when the
    /// run's first fetch happened on it (a genuine midnight straddle).
    /// A long-lived process can never replay its start day later than
    /// that, and future dates never pass (round-4 deep review).
    #[test]
    fn window_accepts_midnight_straddle_only() {
        let d = rustledger_core::naive_date(2026, 7, 16).unwrap();
        let next = d.checked_add(jiff::Span::new().days(1)).unwrap();
        let much_later = d.checked_add(jiff::Span::new().days(30)).unwrap();

        assert!(super::latest_date_window_ok(d, d, d), "same day");
        assert!(
            super::latest_date_window_ok(d, next, d),
            "midnight straddle: run started on d, clock now d+1"
        );
        assert!(
            !super::latest_date_window_ok(d, much_later, d),
            "a daemon must not replay its start day weeks later"
        );
        assert!(
            !super::latest_date_window_ok(d, next, next),
            "yesterday is refused when the run did NOT start on it"
        );
        assert!(
            !super::latest_date_window_ok(much_later, d, d),
            "future dates never pass"
        );
    }

    /// Identity answers accept any past-or-today label but refuse a
    /// future one — identity bypasses the main guard, so this is its
    /// own fence (round-4 deep review).
    #[test]
    fn identity_label_refuses_future_dates() {
        let today = jiff::Zoned::now().date();
        let past = rustledger_core::naive_date(2020, 1, 1).unwrap();
        let future = today.checked_add(jiff::Span::new().days(7)).unwrap();

        assert_eq!(
            super::identity_label_date("ecb", &request(Some(past))).unwrap(),
            past
        );
        assert_eq!(
            super::identity_label_date("ecb", &request(None)).unwrap(),
            today
        );
        let err = super::identity_label_date("ecb", &request(Some(future)))
            .expect_err("future labels are fabrication");
        assert!(err.to_string().contains("future"), "{err}");
    }
}

#[cfg(test)]
mod feed_date_tests {
    use super::feed_date_or_today;

    #[test]
    fn parses_bare_date_and_timestamp_prefix() {
        let expected = rustledger_core::naive_date(2024, 1, 15).unwrap();
        assert_eq!(feed_date_or_today(Some("2024-01-15")), expected);
        // Alpha Vantage "6. Last Refreshed" shape.
        assert_eq!(feed_date_or_today(Some("2024-01-15 10:30:00")), expected);
    }

    /// Absent, short, or malformed fields fall back to today instead of
    /// erroring — the date label degrades, the price still flows.
    #[test]
    fn falls_back_to_today_on_missing_or_malformed() {
        let today = jiff::Zoned::now().date();
        assert_eq!(feed_date_or_today(None), today);
        assert_eq!(feed_date_or_today(Some("")), today);
        assert_eq!(feed_date_or_today(Some("2024")), today);
        assert_eq!(feed_date_or_today(Some("not-a-date-at-all")), today);
        // Multibyte content at the 10-byte boundary must not panic.
        assert_eq!(feed_date_or_today(Some("2024-01-1é 10:30:00")), today);
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
