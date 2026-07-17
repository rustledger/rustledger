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
use anyhow::{Context, Result};
use rust_decimal::Decimal;
use rustledger_core::NaiveDate;

/// A `(ticker, quote-currency)` pair — the date-free fetch target.
///
/// Sources take this instead of [`PriceRequest`] so an implementation
/// cannot even see a requested date, let alone label a quote with it
/// (#1794): all date handling lives in the provided
/// [`PriceSource::fetch_price`] dispatch.
#[derive(Debug, Clone)]
pub struct PricePair {
    /// Ticker symbol.
    pub ticker: String,
    /// Quote currency.
    pub currency: String,
}

/// One dated quote from a source's historical series.
#[derive(Debug, Clone)]
pub struct PricePoint {
    /// The quote's OWN civil date (exchange-local where applicable).
    pub date: NaiveDate,
    /// The settled price for that date.
    pub price: Decimal,
    /// Quote currency when the feed reports one; the request's currency
    /// is used otherwise.
    pub currency: Option<String>,
}

/// An inclusive civil-date range for a historical window fetch.
#[derive(Debug, Clone, Copy)]
pub struct DateWindow {
    /// First day (inclusive).
    pub start: NaiveDate,
    /// Last day (inclusive).
    pub end: NaiveDate,
}

/// How far back a source can serve dated quotes.
///
/// Declared as DATA rather than probed via errors — the ccxt
/// `has`-dictionary / pricehist `types()`+`start()` pattern: the
/// dispatch refuses an uncoverable dated request before any network
/// I/O, and callers can inspect capability up front. beanprice's
/// `None`-return signaling is the documented counterexample (its own
/// `TODO(blais)` calls the capability/failure conflation a flaw).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HistoricalCoverage {
    /// Latest quote only — dated fetches (other than today's) refuse.
    None,
    /// Dated quotes available from this day onward.
    Since(NaiveDate),
    /// Full history, as far back as the provider goes.
    Full,
}

impl HistoricalCoverage {
    /// Whether a quote for `date` can be requested under this coverage.
    #[must_use]
    pub fn covers(self, date: NaiveDate) -> bool {
        match self {
            Self::None => false,
            Self::Since(start) => date >= start,
            Self::Full => true,
        }
    }
}

/// Days of look-back slop when turning a point request into a window:
/// the window `requested - LOOKBACK ..= requested` spans weekends plus
/// multi-day market holidays (beanprice uses a 5-day window for the
/// same purpose; ours matches the pre-existing yahoo behavior).
const HISTORICAL_LOOKBACK_DAYS: i64 = 6;

/// Canonical on-or-before selection over a fetched window: the point
/// with the greatest date `<= requested`.
///
/// Ownership sits HERE — in the dispatch, not in each source — so the
/// #1794 invariant (a dated answer is labeled with the quote's own
/// date, never the requested one) is enforced in exactly one place.
/// Input order is irrelevant; providers do not guarantee sorted series.
fn select_on_or_before(points: Vec<PricePoint>, requested: NaiveDate) -> Option<PricePoint> {
    points
        .into_iter()
        .filter(|p| p.date <= requested)
        .max_by_key(|p| p.date)
}

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

/// Date label for a date-independent identity answer (X→X = 1.0).
///
/// Identity is numerically correct for any PAST day, which is why the
/// identity arm sits at the top of the [`PriceSource::fetch_price`]
/// dispatch — but a FUTURE label would fabricate a directive for a day
/// that hasn't happened, which every other dated path refuses; refuse
/// it here too (round-4 deep review of #1801: `--date 2030-01-01` on an
/// identity pair emitted `2030-01-01 price USD 1 USD` and cached it).
///
/// # Errors
/// Errors when `request.date` is after today.
fn identity_label_date(
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
/// # Architecture (#1802)
///
/// Sources implement the date-free [`Self::fetch_latest`] and, when the
/// provider has a history API, [`Self::fetch_window`] plus a
/// [`Self::historical_coverage`] declaration. All date SEMANTICS —
/// identity pairs, refusing uncoverable dates, on-or-before selection,
/// and labeling the answer with the quote's own date — live in the
/// provided [`Self::fetch_price`] dispatch, so they cannot drift per
/// source (every defect in #1801's four review rounds was a per-source
/// date-labeling mistake). Grounded in a survey of beanprice (split
/// point methods, capability signaled by an ambiguous `None` its author
/// flags as a flaw), pricehist (a single series primitive subsuming the
/// point protocols, capability as data), and ccxt (`has` capability
/// dictionary); see issue #1802.
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

    /// Fetch the LATEST quote for a pair. Every provider has a latest
    /// endpoint, so this is the one mandatory fetch method.
    ///
    /// The response's `date` must be the quote's own trading day
    /// (`feed_date_or_today` is the canonical extraction helper) — a
    /// caller-chosen date is inexpressible here by design.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The network request fails
    /// - The response cannot be parsed
    /// - The ticker is not found
    /// - The API key is missing (for sources that require it)
    fn fetch_latest(&self, pair: &PricePair) -> Result<PriceResponse>;

    /// How far back this source can serve dated quotes. Latest-only
    /// sources keep the default.
    fn historical_coverage(&self) -> HistoricalCoverage {
        HistoricalCoverage::None
    }

    /// Fetch the daily points the provider has in (or near) `window` —
    /// the single historical primitive (the pricehist model).
    ///
    /// Sources return RAW dated points; on-or-before selection and
    /// response labeling happen in the provided [`Self::fetch_price`]
    /// dispatch. Points outside the window are permitted (timezone
    /// slop, single-point providers) — the dispatch filters. An EMPTY
    /// vec means "the provider has no quotes there" and becomes the
    /// dispatch's no-quote error. Implementations must be consistent
    /// with [`Self::historical_coverage`].
    ///
    /// # Errors
    ///
    /// The default refuses (latest-only source); implementations error
    /// on network/parse/auth failures.
    fn fetch_window(&self, pair: &PricePair, window: DateWindow) -> Result<Vec<PricePoint>> {
        let _ = window;
        anyhow::bail!(
            "the '{}' source only provides the latest quote and has no historical window \
             fetch for {}",
            self.name(),
            pair.ticker
        )
    }

    /// Fetch a price — the canonical dispatch.
    ///
    /// Do NOT override this: implement [`Self::fetch_latest`] /
    /// [`Self::fetch_window`] instead, so the date semantics stay in
    /// one place. The single sanctioned override is
    /// `ExternalCommandSource`, whose trust-contract divergence is
    /// documented at both sites.
    ///
    /// Dispatch order:
    /// 1. Identity pair (X→X = 1.0 for any past-or-today date).
    /// 2. No date → [`Self::fetch_latest`].
    /// 3. Date covered by [`Self::historical_coverage`] →
    ///    [`Self::fetch_window`] over the trailing look-back window,
    ///    then canonical on-or-before selection, labeled with the
    ///    point's own date (#1794).
    /// 4. Uncovered date that is today (or a midnight straddle, see
    ///    `latest_date_window_ok`) → [`Self::fetch_latest`].
    /// 5. Anything else → refusal naming the source and its coverage.
    ///
    /// # Errors
    ///
    /// Fetch failures from the underlying methods; a refusal for dated
    /// requests the source cannot serve; "no quote on or before" when
    /// the fetched window is empty.
    fn fetch_price(&self, request: &PriceRequest) -> Result<PriceResponse> {
        // 1. Identity: X priced in X is 1.0 on any past-or-today date,
        // source-independent (hoisted out of per-source branches by the
        // #1801 reviews; future labels refuse).
        if request.ticker.eq_ignore_ascii_case(&request.currency) {
            return Ok(PriceResponse {
                price: Decimal::ONE,
                currency: request.currency.clone(),
                date: identity_label_date(self.name(), request)?,
                source: self.name().to_string(),
            });
        }

        let pair = PricePair {
            ticker: request.ticker.clone(),
            currency: request.currency.clone(),
        };

        // 2. Undated → latest.
        let Some(requested) = request.date else {
            return self.fetch_latest(&pair);
        };

        // 3. Covered date → window + canonical selection. Today is
        // routed here too for window-capable sources (a same-day
        // request returns the freshest daily bar — yahoo's
        // pre-existing behavior).
        let coverage = self.historical_coverage();
        if coverage.covers(requested) {
            let start = requested
                .checked_sub(jiff::Span::new().days(HISTORICAL_LOOKBACK_DAYS))
                .context("date underflow")?;
            let window = DateWindow {
                start,
                end: requested,
            };
            let points = self.fetch_window(&pair, window)?;
            let point = select_on_or_before(points, requested).with_context(|| {
                format!(
                    "no {} quote for {} on or before {requested} in the fetched window; \
                     the market may not have traded that week",
                    self.name(),
                    pair.ticker
                )
            })?;
            return Ok(PriceResponse {
                price: point.price,
                currency: point.currency.unwrap_or_else(|| pair.currency.clone()),
                date: point.date,
                source: self.name().to_string(),
            });
        }

        // 4. Uncovered date, but it is today (or a midnight straddle):
        // the latest quote IS a valid answer for today, and the
        // response carries the quote's own date anyway (#1801).
        let today = jiff::Zoned::now().date();
        let first_fetch_day = *FIRST_FETCH_DAY.get_or_init(|| today);
        if latest_date_window_ok(requested, today, first_fetch_day) {
            return self.fetch_latest(&pair);
        }

        // 5. Refuse: mislabeling the latest quote with this date is the
        // #1794 corruption.
        let coverage_note = match coverage {
            HistoricalCoverage::Since(s) => format!(" (its history begins {s})"),
            _ => String::new(),
        };
        anyhow::bail!(
            "the '{}' source only provides the latest quote{coverage_note} and cannot \
             fetch {} for {requested}; drop --date, or use a source with historical \
             support (e.g. yahoo)",
            self.name(),
            request.ticker
        );
    }
}

/// Helper function to build a User-Agent header for HTTP requests.
pub(crate) const fn user_agent() -> &'static str {
    "Mozilla/5.0 (compatible; rustledger/1.0; +https://github.com/rustledger/rustledger)"
}

#[cfg(test)]
mod dispatch_tests {
    use super::{
        DateWindow, HistoricalCoverage, PricePair, PricePoint, PriceSource, select_on_or_before,
    };
    use crate::cmd::price::{PriceRequest, PriceResponse};
    use anyhow::Result;
    use rust_decimal::Decimal;
    use rustledger_core::NaiveDate;

    fn request(date: Option<NaiveDate>) -> PriceRequest {
        PriceRequest {
            ticker: "AAPL".to_string(),
            currency: "USD".to_string(),
            date,
        }
    }

    /// A latest-only source whose feed labels its quote with a fixed
    /// (non-today) trading day, as a weekend feed would.
    struct LatestOnly;
    const FEED_DAY: (i32, u32, u32) = (2026, 7, 10);
    impl PriceSource for LatestOnly {
        fn name(&self) -> &'static str {
            "mock-latest"
        }
        fn description(&self) -> &'static str {
            "latest-only mock"
        }
        fn fetch_latest(&self, pair: &PricePair) -> Result<PriceResponse> {
            Ok(PriceResponse {
                price: Decimal::new(4200, 2),
                currency: pair.currency.clone(),
                date: rustledger_core::naive_date(FEED_DAY.0, FEED_DAY.1, FEED_DAY.2).unwrap(),
                source: self.name().to_string(),
            })
        }
    }

    /// A window-capable source returning a fixed unsorted series,
    /// including a point AFTER any plausible requested date.
    struct Windowed;
    impl PriceSource for Windowed {
        fn name(&self) -> &'static str {
            "mock-window"
        }
        fn description(&self) -> &'static str {
            "window mock"
        }
        fn fetch_latest(&self, _pair: &PricePair) -> Result<PriceResponse> {
            panic!("dated dispatch on a covered date must use fetch_window");
        }
        fn historical_coverage(&self) -> HistoricalCoverage {
            HistoricalCoverage::Full
        }
        fn fetch_window(&self, _pair: &PricePair, _window: DateWindow) -> Result<Vec<PricePoint>> {
            let d = |y, m, day| rustledger_core::naive_date(y, m, day).unwrap();
            Ok(vec![
                PricePoint {
                    date: d(2026, 7, 6),
                    price: Decimal::new(300, 2),
                    currency: Some("USD".to_string()),
                },
                // Deliberately after the tested request date: selection
                // must skip it (unsorted input, no early break).
                PricePoint {
                    date: d(2026, 7, 13),
                    price: Decimal::new(999, 2),
                    currency: Some("USD".to_string()),
                },
                PricePoint {
                    date: d(2026, 7, 10),
                    price: Decimal::new(500, 2),
                    currency: Some("USD".to_string()),
                },
            ])
        }
    }

    /// A source that panics on ANY fetch — proves identity answers
    /// never touch the network.
    struct NeverFetch;
    impl PriceSource for NeverFetch {
        fn name(&self) -> &'static str {
            "mock-never"
        }
        fn description(&self) -> &'static str {
            "panics on fetch"
        }
        fn fetch_latest(&self, _pair: &PricePair) -> Result<PriceResponse> {
            panic!("identity must not fetch");
        }
    }

    /// Latest-only: past and future dates refuse with the latest-quote
    /// message; today routes to `fetch_latest`, and the answer carries
    /// the FEED's day, not the requested one (#1794/#1801 semantics,
    /// now enforced by the shared dispatch instead of per-source
    /// guards).
    #[test]
    fn latest_only_refuses_past_and_future_but_serves_today() {
        let src = LatestOnly;
        let past = rustledger_core::naive_date(2000, 1, 3).unwrap();
        let err = src.fetch_price(&request(Some(past))).expect_err("refuse");
        assert!(err.to_string().contains("latest quote"), "{err}");
        assert!(err.to_string().contains("mock-latest"), "{err}");

        let today = jiff::Zoned::now().date();
        let future = today.checked_add(jiff::Span::new().days(7)).unwrap();
        assert!(src.fetch_price(&request(Some(future))).is_err());

        let response = src.fetch_price(&request(Some(today))).expect("today ok");
        assert_eq!(
            response.date,
            rustledger_core::naive_date(FEED_DAY.0, FEED_DAY.1, FEED_DAY.2).unwrap(),
            "the response carries the feed's own day, not the requested one"
        );

        assert!(src.fetch_price(&request(None)).is_ok(), "undated passes");
    }

    /// Covered dates go through the window primitive: the dispatch
    /// selects the greatest point `<= requested` from unsorted input
    /// and labels the response with THAT point's date.
    #[test]
    fn covered_date_selects_on_or_before_and_labels_with_point_date() {
        let src = Windowed;
        let requested = rustledger_core::naive_date(2026, 7, 12).unwrap();
        let response = src.fetch_price(&request(Some(requested))).expect("fetch");
        assert_eq!(response.price.to_string(), "5.00", "Friday's close");
        assert_eq!(
            response.date,
            rustledger_core::naive_date(2026, 7, 10).unwrap(),
            "labeled with the point's own date, never the requested one"
        );
    }

    /// An empty window is a hard error, never a mislabeled latest quote.
    #[test]
    fn empty_window_is_a_no_quote_error() {
        struct Empty;
        impl PriceSource for Empty {
            fn name(&self) -> &'static str {
                "mock-empty"
            }
            fn description(&self) -> &'static str {
                "empty window"
            }
            fn fetch_latest(&self, _p: &PricePair) -> Result<PriceResponse> {
                panic!("must not fall back to latest");
            }
            fn historical_coverage(&self) -> HistoricalCoverage {
                HistoricalCoverage::Full
            }
            fn fetch_window(&self, _p: &PricePair, _w: DateWindow) -> Result<Vec<PricePoint>> {
                Ok(vec![])
            }
        }
        let requested = rustledger_core::naive_date(2026, 7, 12).unwrap();
        let err = Empty
            .fetch_price(&request(Some(requested)))
            .expect_err("must refuse");
        assert!(err.to_string().contains("on or before"), "{err}");
    }

    /// `Since` coverage: a date before the epoch refuses and the
    /// message names where history begins.
    #[test]
    fn since_coverage_refuses_earlier_dates_with_epoch_in_message() {
        struct SinceSource;
        impl PriceSource for SinceSource {
            fn name(&self) -> &'static str {
                "mock-since"
            }
            fn description(&self) -> &'static str {
                "since mock"
            }
            fn fetch_latest(&self, _p: &PricePair) -> Result<PriceResponse> {
                panic!("uncovered past date must refuse, not fetch latest");
            }
            fn historical_coverage(&self) -> HistoricalCoverage {
                HistoricalCoverage::Since(rustledger_core::naive_date(1999, 1, 4).unwrap())
            }
            fn fetch_window(&self, _p: &PricePair, _w: DateWindow) -> Result<Vec<PricePoint>> {
                panic!("uncovered date must not reach fetch_window");
            }
        }
        let too_early = rustledger_core::naive_date(1980, 1, 1).unwrap();
        let err = SinceSource
            .fetch_price(&request(Some(too_early)))
            .expect_err("refuse");
        assert!(err.to_string().contains("1999-01-04"), "{err}");
        assert!(err.to_string().contains("latest quote"), "{err}");
    }

    /// Identity pairs answer 1.0 for any past-or-today date without any
    /// fetch, on EVERY source; future identity labels refuse.
    #[test]
    fn identity_answers_without_fetching_and_refuses_future() {
        let src = NeverFetch;
        let past = rustledger_core::naive_date(2024, 6, 30).unwrap();
        let mut req = PriceRequest::new("USD", "USD");
        req.date = Some(past);
        let response = src.fetch_price(&req).expect("identity");
        assert_eq!(response.price, Decimal::ONE);
        assert_eq!(response.date, past);

        let today = jiff::Zoned::now().date();
        let future = today.checked_add(jiff::Span::new().days(7)).unwrap();
        req.date = Some(future);
        let err = src.fetch_price(&req).expect_err("future identity refuses");
        assert!(err.to_string().contains("future"), "{err}");
    }

    /// The selection helper itself: greatest date <= requested, order
    /// independent, currency carried through.
    #[test]
    fn select_on_or_before_picks_max_not_first() {
        let d = |day| rustledger_core::naive_date(2026, 7, day).unwrap();
        let point = |day, cents| PricePoint {
            date: d(day),
            price: Decimal::new(cents, 2),
            currency: None,
        };
        let picked =
            select_on_or_before(vec![point(10, 500), point(6, 300), point(13, 999)], d(12))
                .expect("some");
        assert_eq!(picked.date, d(10));
        assert!(select_on_or_before(vec![point(13, 999)], d(12)).is_none());
        assert!(select_on_or_before(vec![], d(12)).is_none());
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
mod capability_wiring_tests {
    use super::HistoricalCoverage;
    use crate::cmd::price::{PriceConfig, PriceRequest, PriceSourceRegistry};

    /// Drift guard (#1801 reviews, rearchitected in #1802): every
    /// builtin that declares NO historical coverage must refuse a dated
    /// fetch through the shared dispatch, before any network I/O — a
    /// hermetic dated fetch fails with the refusal message. A source
    /// that wrongly declared coverage would instead surface a
    /// network/parse error here.
    #[test]
    fn latest_only_builtins_refuse_dated_fetches() {
        let registry = PriceSourceRegistry::new(&PriceConfig::default());
        let past = rustledger_core::naive_date(2000, 1, 3).expect("valid date");
        for name in [
            "alphavantage",
            "coincap",
            "coinmarketcap",
            "eastmoneyfund",
            "ecb",
            "oanda",
            "quandl",
            "tsp",
        ] {
            let source = registry
                .get(name)
                .unwrap_or_else(|| panic!("builtin source '{name}' must exist"));
            assert_eq!(
                source.historical_coverage(),
                HistoricalCoverage::None,
                "'{name}' is expected to be latest-only; if it grew historical \
                 support, move it to the capable list below"
            );
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
                "source '{name}' did not refuse through the dispatch: {err}"
            );
        }
    }

    /// The capable builtins declare their coverage as data — the
    /// introspection callers (dry-run validation, fallback-chain
    /// skipping) rely on these declarations being truthful.
    #[test]
    fn historical_capable_builtins_declare_coverage() {
        let registry = PriceSourceRegistry::new(&PriceConfig::default());
        let coverage = |name: &str| registry.get(name).expect(name).historical_coverage();
        assert_eq!(coverage("yahoo"), HistoricalCoverage::Full);
        assert_eq!(coverage("coinbase"), HistoricalCoverage::Full);
        // exchangerate.host serves EU-reference history from 1999-01-04.
        assert_eq!(
            coverage("ratesapi"),
            HistoricalCoverage::Since(rustledger_core::naive_date(1999, 1, 4).unwrap())
        );
    }
}
