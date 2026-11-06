//! Price fetching module for rustledger.
//!
//! This module provides a pluggable price source system that supports:
//! - Built-in sources (Yahoo Finance, Coinbase, ECB, etc.)
//! - External command sources for custom integrations
//! - Configurable commodity-to-source mappings
//! - Fallback chains for reliability

pub mod cache;
pub mod discovery;
pub mod external;
pub mod sources;

use crate::config::{CommodityMapping, PriceConfig, PriceSourceConfig, SourceRef};
use anyhow::{Context, Result};
use rust_decimal::Decimal;
use rustledger_core::NaiveDate;
use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;

pub use sources::PriceSource;

/// A request to fetch a price.
#[derive(Debug, Clone)]
pub struct PriceRequest {
    /// The ticker symbol to fetch.
    pub ticker: String,
    /// The target currency for the price.
    pub currency: String,
    /// Optional specific date (None = current price).
    pub date: Option<NaiveDate>,
}

impl PriceRequest {
    /// Create a new price request.
    pub fn new(ticker: impl Into<String>, currency: impl Into<String>) -> Self {
        Self {
            ticker: ticker.into(),
            currency: currency.into(),
            date: None,
        }
    }

    /// Set the date for the request.
    #[must_use]
    pub const fn with_date(mut self, date: NaiveDate) -> Self {
        self.date = Some(date);
        self
    }
}

/// A response from a price source.
#[derive(Debug, Clone)]
pub struct PriceResponse {
    /// The fetched price.
    pub price: Decimal,
    /// The currency of the price.
    pub currency: String,
    /// The date of the price.
    pub date: NaiveDate,
    /// The source that provided the price.
    pub source: String,
}

/// Parse a price quote from a JSON value into a [`Decimal`].
///
/// Handles both shapes price APIs use:
/// - **String** quotes (`"1.2345"`) parse exactly.
/// - **Integer** numbers parse exactly.
/// - **Float** numbers are bounded by `f64` (~15–17 significant digits): a JSON
///   float has already been parsed into an `f64` by the time it reaches a
///   `serde_json::Value` (`serde_json` is built without `arbitrary_precision`), so
///   the most we can recover is its shortest round-trippable string. That is
///   exact for every human-scale quote (FX / equities / crypto) and only loses
///   precision past ~15 significant digits — far beyond any real price.
///
/// We deliberately do not enable `serde_json`'s `arbitrary_precision` feature: it
/// is global and breaks the workspace's `#[serde(untagged)]` / `flatten` enums.
/// A per-field `RawValue` rewrite of every network source was judged
/// disproportionate for the negligible gain (see #1621).
#[must_use]
pub fn price_decimal_from_json(value: &serde_json::Value) -> Option<Decimal> {
    use std::str::FromStr;
    match value {
        serde_json::Value::String(s) => Decimal::from_str(s).ok(),
        serde_json::Value::Number(n) => Decimal::from_str(&n.to_string()).ok(),
        _ => None,
    }
}

/// Registry of available price sources.
pub struct PriceSourceRegistry {
    sources: HashMap<String, Arc<dyn PriceSource>>,
    default_source: String,
    timeout: Duration,
    /// When false, a commodity with no explicit source declaration
    /// errors instead of silently using `default_source`. See #966 and
    /// `PriceConfig::use_default_source`.
    use_default_source: bool,
}

impl PriceSourceRegistry {
    /// Create a new registry with built-in sources.
    pub fn new(config: &PriceConfig) -> Self {
        let mut sources: HashMap<String, Arc<dyn PriceSource>> = HashMap::new();
        let timeout = Duration::from_secs(config.effective_timeout());

        // Register built-in sources
        sources.insert(
            "yahoo".to_string(),
            Arc::new(sources::YahooFinanceSource::new(timeout)),
        );
        sources.insert(
            "coinbase".to_string(),
            Arc::new(sources::CoinbaseSource::new(timeout)),
        );
        sources.insert(
            "coincap".to_string(),
            Arc::new(sources::CoinCapSource::new(timeout)),
        );
        let ecb: Arc<dyn PriceSource> = Arc::new(sources::EcbSource::new(timeout));
        sources.insert("ecb".to_string(), Arc::clone(&ecb));
        // beanprice calls the same ECB reference-rate source `ecbrates`,
        // so a `price: "EUR:ecbrates/GBP-EUR"` written for bean-price
        // resolves (#2866); `ecb` reads its `BASE-SYMBOL` ticker too.
        sources.insert("ecbrates".to_string(), ecb);
        sources.insert(
            "ratesapi".to_string(),
            Arc::new(sources::RatesApiSource::new(timeout)),
        );
        sources.insert(
            "tsp".to_string(),
            Arc::new(sources::TspSource::new(timeout)),
        );
        sources.insert(
            "eastmoneyfund".to_string(),
            Arc::new(sources::EastMoneyFundSource::new(timeout)),
        );

        // Register API key sources (always registered; they return clear errors if key is missing)
        sources.insert(
            "oanda".to_string(),
            Arc::new(sources::OandaSource::new(timeout)),
        );
        sources.insert(
            "alphavantage".to_string(),
            Arc::new(sources::AlphaVantageSource::new(timeout)),
        );
        sources.insert(
            "coinmarketcap".to_string(),
            Arc::new(sources::CoinMarketCapSource::new(timeout)),
        );
        sources.insert(
            "quandl".to_string(),
            Arc::new(sources::QuandlSource::new(timeout)),
        );

        // Register custom command sources from config
        for (name, source_config) in &config.sources {
            if let PriceSourceConfig::Command {
                command,
                timeout: cmd_timeout,
                env,
            } = source_config
            {
                let cmd_timeout =
                    Duration::from_secs(cmd_timeout.unwrap_or(config.effective_timeout()));
                sources.insert(
                    name.clone(),
                    Arc::new(external::ExternalCommandSource::with_name(
                        command.clone(),
                        cmd_timeout,
                        env.clone(),
                        name.clone(),
                    )),
                );
            }
        }

        Self {
            sources,
            default_source: config.effective_default_source().to_string(),
            timeout,
            use_default_source: config.effective_use_default_source(),
        }
    }

    /// Get a source by name.
    pub fn get(&self, name: &str) -> Option<Arc<dyn PriceSource>> {
        self.sources.get(name).cloned()
    }

    /// Get the default source.
    pub fn default_source(&self) -> Option<Arc<dyn PriceSource>> {
        self.get(&self.default_source)
    }

    /// Get the default source name.
    pub fn default_source_name(&self) -> &str {
        &self.default_source
    }

    /// List all registered source names.
    pub fn list_sources(&self) -> Vec<&str> {
        let mut names: Vec<&str> = self.sources.keys().map(String::as_str).collect();
        names.sort_unstable();
        names
    }

    /// Check if a source is registered.
    pub fn has_source(&self, name: &str) -> bool {
        self.sources.contains_key(name)
    }

    /// Get the configured timeout.
    pub const fn timeout(&self) -> Duration {
        self.timeout
    }

    /// Fetch a price using the configured mapping.
    ///
    /// This method resolves the commodity to the appropriate source and
    /// ticker based on the configuration, then fetches the price. When a
    /// fallback chain is in play, each entry's per-source ticker is used
    /// (issue #963).
    ///
    /// # Errors
    ///
    /// Returns an error if the commodity has no explicit source
    /// declaration (no CLI `--source`, no `[price.mapping.X]` in config,
    /// no `price:` metadata) and `[price] use_default_source = false`
    /// (the default). See issue #966.
    ///
    /// Every ticker is sent as it is written: a leading `^` is part of it
    /// (Yahoo's `^GSPC`). For a mapping read from `price:` metadata, where
    /// `^` is bean-price's inversion, use [`Self::fetch_price_for_spec`].
    pub fn fetch_price(
        &self,
        commodity: &str,
        currency: &str,
        date: Option<NaiveDate>,
        mapping: &HashMap<String, CommodityMapping>,
    ) -> Result<PriceResponse> {
        self.fetch_attempts(commodity, currency, date, mapping, TickerSyntax::Verbatim)
    }

    /// [`Self::fetch_price`] for a mapping read from a commodity's `price:`
    /// metadata, bean-price's source-spec grammar
    /// `CURRENCY:module/[^]TICKER` (#2866): a leading `^` asks for the
    /// inverse of the source's quote. Config mappings, `--mapping` and
    /// `--source` keep their tickers verbatim, as bean-price's grammar does
    /// not apply to them (Yahoo index tickers such as `^GSPC` start with
    /// `^`).
    ///
    /// # Errors
    ///
    /// As [`Self::fetch_price`]. An inverted attempt also fails when the
    /// ticker has a second `^`, when the quote is not a price of
    /// `commodity` or (for a ticker naming its pair, `^EUR-GBP`) not of a
    /// pair based in `currency`, and when the quote has no writable
    /// inverse (zero, or an inverse too small for 28 decimal places).
    pub fn fetch_price_for_spec(
        &self,
        commodity: &str,
        currency: &str,
        date: Option<NaiveDate>,
        mapping: &HashMap<String, CommodityMapping>,
    ) -> Result<PriceResponse> {
        self.fetch_attempts(
            commodity,
            currency,
            date,
            mapping,
            TickerSyntax::BeanPriceSpec,
        )
    }

    /// The fallback chain behind [`Self::fetch_price`] and
    /// [`Self::fetch_price_for_spec`].
    fn fetch_attempts(
        &self,
        commodity: &str,
        currency: &str,
        date: Option<NaiveDate>,
        mapping: &HashMap<String, CommodityMapping>,
        syntax: TickerSyntax,
    ) -> Result<PriceResponse> {
        let attempts = self.resolve_mapping(commodity, mapping)?;

        // Every failed attempt is kept, not just the last: in a chain
        // like [yahoo, coinbase] with --date, the trailing source's
        // "latest quote only" refusal must not mask yahoo's real
        // (possibly transient) failure (round-2 deep review of #1801).
        let mut errors: Vec<(String, anyhow::Error)> = Vec::new();
        let mut unknown_sources = Vec::new();
        // Whether an attempt read a `^` as bean-price's inversion: a failed
        // fetch then says so, once (#2866).
        let mut inverted_any = false;

        for (source_name, ticker) in &attempts {
            if let Some(source) = self.get(source_name) {
                inverted_any |= syntax == TickerSyntax::BeanPriceSpec && ticker.starts_with('^');
                let result = match syntax.inverted_ticker(ticker) {
                    Ok(Some(rest)) => {
                        Self::fetch_inverse(&*source, commodity, rest, currency, date)
                    }
                    Ok(None) => source.fetch_price(&PriceRequest {
                        ticker: ticker.clone(),
                        currency: currency.to_string(),
                        date,
                    }),
                    Err(e) => Err(e),
                };
                // A failed attempt, a zero quote among them, moves on to
                // the next source in the chain. bean-price aborts the job
                // with DivisionByZero instead.
                match result {
                    Ok(response) => return Ok(response),
                    Err(e) => {
                        errors.push((source_name.clone(), e));
                        // Try next source in fallback chain
                    }
                }
            } else {
                // Track unknown sources for error reporting
                unknown_sources.push(source_name.clone());
            }
        }

        // Build an informative error message
        let err_msg = if errors.len() == 1 {
            // A single failure keeps its full error value.
            let (_, single) = errors.remove(0);
            if unknown_sources.is_empty() {
                single
            } else {
                anyhow::anyhow!(
                    "{single:#}; note: unknown sources skipped: {}",
                    unknown_sources.join(", ")
                )
            }
        } else if !errors.is_empty() {
            let attempts_report = errors
                .iter()
                .map(|(name, e)| format!("{name}: {e:#}"))
                .collect::<Vec<_>>()
                .join("; ");
            if unknown_sources.is_empty() {
                anyhow::anyhow!("all sources failed for {commodity}: {attempts_report}")
            } else {
                anyhow::anyhow!(
                    "all sources failed for {commodity}: {attempts_report}; \
                     note: unknown sources skipped: {}",
                    unknown_sources.join(", ")
                )
            }
        } else if !unknown_sources.is_empty() {
            anyhow::anyhow!(
                "No price source available for commodity {commodity}: unknown sources: {}",
                unknown_sources.join(", ")
            )
        } else {
            anyhow::anyhow!("No price source available for commodity {commodity}")
        };

        if inverted_any {
            return Err(anyhow::anyhow!("{err_msg:#} ({INVERSION_NOTE})"));
        }
        Err(err_msg)
    }

    /// Resolve a commodity to a list of `(source, ticker)` attempts to
    /// try in order. Each fallback entry can carry its own ticker so a
    /// chain like `EUR:ecbrates/GBP-EUR,EUR:ecb/GBP` queries each source
    /// with the ticker shape it expects (issue #963).
    ///
    /// # Errors
    ///
    /// Returns an error if `mapping` has no entry for `commodity` and
    /// `use_default_source` is false. The error message lists the
    /// remediation paths so users can pick whichever fits their workflow.
    fn resolve_mapping(
        &self,
        commodity: &str,
        mapping: &HashMap<String, CommodityMapping>,
    ) -> Result<Vec<(String, String)>> {
        if let Some(commodity_mapping) = mapping.get(commodity) {
            let attempts = match commodity_mapping {
                CommodityMapping::Simple(ticker) => {
                    vec![(self.default_source.clone(), ticker.clone())]
                }
                CommodityMapping::Detailed(d) => {
                    let parent_ticker = d.ticker.clone().unwrap_or_else(|| commodity.to_string());
                    match &d.source {
                        SourceRef::Single(s) => vec![(s.clone(), parent_ticker)],
                        SourceRef::Fallback(entries) => entries
                            .iter()
                            .map(|e| {
                                // Per-entry ticker wins; otherwise fall back to the
                                // parent ticker. This mirrors the metadata semantics
                                // the discovery layer encodes for chained `price:`.
                                let t = e
                                    .ticker()
                                    .map_or_else(|| parent_ticker.clone(), str::to_string);
                                (e.source_name().to_string(), t)
                            })
                            .collect(),
                    }
                }
            };
            return Ok(attempts);
        }

        // No mapping. Issue #966: silently dispatching to `default_source`
        // is the failure mode where currency codes like `BAM` get sent to
        // Yahoo and return a stock price for an unrelated ticker. Refuse
        // unless the user has opted in via `[price] use_default_source = true`.
        if self.use_default_source {
            return Ok(vec![(self.default_source.clone(), commodity.to_string())]);
        }
        Err(anyhow::anyhow!(
            "no price source configured for {commodity}. Pick one:\n  \
             - pass `--source <name>` (e.g. `--source ecb`),\n  \
             - pass `--mapping {commodity}:<TICKER>`,\n  \
             - add `[price.mapping.{commodity}]` to your rledger config,\n  \
             - annotate the commodity in your beancount file with \
             `price: \"<quote>:<source>/<ticker>\"` or `quote_currency: \"<currency>\"` \
             and load the file with `-f`,\n  \
             - or set `[price] use_default_source = true` in your config to fall back \
             to the default source ({default}) for unmapped symbols.",
            default = self.default_source,
        ))
    }
}

/// The note a failed fetch carries when an attempt read a `^` as
/// bean-price's inversion (#2866): a `price:` spec written for rledger
/// before #2866 (`USD:yahoo/^GSPC`) now means the inverse of `GSPC`.
const INVERSION_NOTE: &str = "note: in a `price:` spec, a leading `^` is bean-price's \
     inversion: the rest of the ticker is fetched and its inverse written; a ticker that \
     itself starts with `^`, such as Yahoo's `^GSPC`, is kept literal in `[price.mapping]` \
     or `--mapping SYMBOL:^TICKER`";

/// How [`PriceSourceRegistry`] reads a mapping's tickers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TickerSyntax {
    /// As written: a config mapping, `--mapping` or `--source` ticker. A
    /// leading `^` is part of the ticker (Yahoo's `^GSPC`).
    Verbatim,
    /// bean-price's source spec, from `price:` metadata (#2866): a leading
    /// `^` asks for the inverse of the quote.
    BeanPriceSpec,
}

impl TickerSyntax {
    /// The ticker to fetch and invert, when `ticker` asks for an inverse.
    ///
    /// # Errors
    ///
    /// A spec ticker with nothing after its `^`, or a second `^`, which
    /// bean-price's grammar (`/(\^?)([a-zA-Z0-9:=_\-\.\(\)]+)$`) rejects.
    fn inverted_ticker(self, ticker: &str) -> Result<Option<&str>> {
        if self == Self::Verbatim {
            return Ok(None);
        }
        match ticker.strip_prefix('^') {
            None => Ok(None),
            Some(rest) if rest.is_empty() || rest.starts_with('^') => anyhow::bail!(
                "invalid source ticker `{ticker}`: a bean-price spec inverts with one `^` \
                 before the ticker"
            ),
            Some(rest) => Ok(Some(rest)),
        }
    }
}

impl PriceSourceRegistry {
    /// Fetch `ticker` from `source` and invert it, for bean-price's
    /// `^TICKER` (#2866): `EUR:ratesapi/^EUR-GBP` on GBP fetches the
    /// EUR-GBP rate (GBP per EUR) and writes its inverse, the GBP price in
    /// EUR, labeled `currency` as bean-price labels it.
    ///
    /// The inverse of a price of B in Q is a price of Q in B. It is written
    /// only when both hold:
    ///
    /// - the currency of the quote the source returns (Q) is `commodity`;
    /// - when the source reports the base of what it fetches for the ticker
    ///   ([`PriceSource::pair_base`], read by the same code the fetch uses:
    ///   `EUR` for `EUR-GBP`, `EUR_CHF`, `EURCHF=X` or `fx:EUR:CHF`), that
    ///   base (B) is `currency`.
    ///
    /// Otherwise the label would claim a pair the number is not, a relabel
    /// past the #2731 mismatch check that judges an uninverted quote. The
    /// refusal applies with or without `-b`. Stricter than Python:
    /// bean-price writes any such inverse, labeled the declared currency.
    ///
    /// A failed fetch that tried an inversion carries [`INVERSION_NOTE`],
    /// once, from [`Self::fetch_attempts`].
    ///
    /// # Errors
    ///
    /// The fetch failing, a quote that is not of `commodity`, a pair not
    /// based in `currency`, or a quote with no writable inverse (see
    /// [`invert_price`]).
    fn fetch_inverse(
        source: &dyn PriceSource,
        commodity: &str,
        ticker: &str,
        currency: &str,
        date: Option<NaiveDate>,
    ) -> Result<PriceResponse> {
        if let Some(base) = source.pair_base(ticker)
            && !base.eq_ignore_ascii_case(currency)
        {
            let base = base.to_uppercase();
            let currency = currency.to_uppercase();
            anyhow::bail!(
                "`^{ticker}` inverts a price of {base}, which is a price in {base}, not \
                 in {currency}; refusing to write it as a {currency} price"
            );
        }
        let response = source.fetch_price(&PriceRequest {
            ticker: ticker.to_string(),
            currency: currency.to_string(),
            date,
        })?;
        let quote = response.currency.to_uppercase();
        if !quote.eq_ignore_ascii_case(commodity) {
            anyhow::bail!(
                "`^{ticker}` inverts a price in {quote}, which is a price of {quote}, not of \
                 {commodity}; refusing to write it as a {commodity} price"
            );
        }
        let price = invert_price(response.price).with_context(|| {
            format!(
                "cannot invert the {} price {} {} for `^{ticker}`",
                response.source, response.price, response.currency
            )
        })?;
        Ok(PriceResponse {
            price,
            currency: currency.to_uppercase(),
            ..response
        })
    }
}

/// The significant digits [`invert_price`] keeps: Python's default decimal
/// context, under which bean-price computes `ONE / price`.
const INVERSE_DIGITS: i64 = 28;

/// The most decimal places a `rust_decimal` value holds.
const MAX_SCALE: i64 = 28;

/// `1 / price` with bean-price's digits (#2866): `ONE / price` under
/// Python's default decimal context. An exact quotient takes its shortest
/// form (`1 / 8` is `0.125`), and any other is rounded once, half to even,
/// to 28 significant digits (`1 / 4.538` is `0.2203613926840017628911414720`,
/// trailing zero kept). The division is exact integer arithmetic, so that
/// one rounding is the only one.
///
/// One limit is `rust_decimal`'s: it holds at most 28 decimal places, so an
/// inverse near 10^-k keeps k - 1 fewer significant digits than Python's,
/// rounded once at the 28th decimal place (`1 / 149.5` is
/// `0.0066889632107023411371237458`, where Python carries
/// `0.006688963210702341137123745819`). This is the "not fixable locally"
/// precision case of AGENTS.md.
///
/// bean-price's `ecbrates` writes fewer digits than 28: it sets the global
/// decimal precision to its rate legs' (`getcontext().prec = max(5, ...)`)
/// and leaves it set, so the `ONE / price` that follows is rounded to about
/// six digits. Stricter than Python: that is a context leak in beanprice's
/// `ecbrates.py`, not a precision anyone chose, so rledger keeps 28 digits
/// for every source.
///
/// # Errors
///
/// A zero price, which has no inverse, and an inverse that rounds to zero
/// at 28 decimal places (a price at or above 2 * 10^28), which would be written
/// as `0`.
fn invert_price(price: Decimal) -> Result<Decimal> {
    use bigdecimal::num_bigint::BigInt;

    if price.is_zero() {
        anyhow::bail!("a zero price has no inverse");
    }
    let zero = BigInt::from(0);
    // price = coef / 10^exp10, so 1 / price = 10^exp10 / coef, and value =
    // 10^(exp10 + shift) / coef is it scaled by 10^shift.
    let coef = BigInt::from(price.mantissa().unsigned_abs());
    let exp10 = i64::from(price.scale());
    let pow10 = |n: i64| BigInt::from(10).pow(u32::try_from(n).expect("a small exponent"));
    let digits = |n: &BigInt| i64::try_from(n.to_string().len()).expect("a short number");
    let quotient = |shift: i64| {
        let (num, den) = if exp10 + shift >= 0 {
            (pow10(exp10 + shift), coef.clone())
        } else {
            (BigInt::from(1), &coef * pow10(-(exp10 + shift)))
        };
        (&num / &den, &num % &den, den)
    };
    // Pick shift so the integer part of value holds 28 digits, within the 28
    // decimal places rust_decimal holds.
    let mut shift = INVERSE_DIGITS + digits(&coef) - exp10;
    while shift > MAX_SCALE || digits(&quotient(shift).0) > INVERSE_DIGITS {
        shift -= 1;
    }
    let (mut value, rem, den) = quotient(shift);
    // One rounding, half to even, on the exact remainder.
    let exact = rem == zero;
    let twice = &rem * 2;
    if twice > den || (twice == den && &value % 2 != zero) {
        value += 1;
    }
    if digits(&value) > INVERSE_DIGITS {
        // Rounded up to 10^28: drop the zero it gained.
        value /= 10;
        shift -= 1;
    }
    if exact {
        // Python's shortest form for an exact quotient: no trailing zeros.
        while shift > 0 && &value % 10 == zero {
            value /= 10;
            shift -= 1;
        }
    }
    if value == zero {
        anyhow::bail!("its inverse is below the smallest writable price (28 decimal places)");
    }
    while shift < 0 {
        value *= 10;
        shift += 1;
    }
    let mantissa = i128::try_from(&value).context("the inverse is too large to write")?;
    let mantissa = if price.is_sign_negative() {
        -mantissa
    } else {
        mantissa
    };
    let scale = u32::try_from(shift).expect("a scale within 0..=28");
    Decimal::try_from_i128_with_scale(mantissa, scale).context("the inverse is too large to write")
}

impl Default for PriceSourceRegistry {
    fn default() -> Self {
        Self::new(&PriceConfig::default())
    }
}

/// Convenience function to fetch a single price with default configuration.
pub fn fetch_price(
    ticker: &str,
    currency: &str,
    source_name: Option<&str>,
) -> Result<PriceResponse> {
    let config = PriceConfig::default();
    let registry = PriceSourceRegistry::new(&config);

    let source_name = source_name.unwrap_or(registry.default_source_name());
    let source = registry
        .get(source_name)
        .with_context(|| format!("Unknown price source: {source_name}"))?;

    let request = PriceRequest::new(ticker, currency);
    source.fetch_price(&request)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::{FallbackDetail, FallbackEntry};

    #[test]
    fn test_price_decimal_from_json() {
        use std::str::FromStr;
        // String quotes parse exactly, including beyond f64 precision.
        assert_eq!(
            price_decimal_from_json(&serde_json::json!("1.23456789012345678901234567")),
            Some(Decimal::from_str("1.23456789012345678901234567").unwrap())
        );
        // Integer numbers are exact.
        assert_eq!(
            price_decimal_from_json(&serde_json::json!(42)),
            Some(Decimal::from(42))
        );
        // Ordinary float quotes round-trip to the expected decimal.
        assert_eq!(
            price_decimal_from_json(&serde_json::json!(1.25)),
            Some(Decimal::from_str("1.25").unwrap())
        );
        // Non-numeric / wrong-shape values yield None.
        assert_eq!(
            price_decimal_from_json(&serde_json::json!("not-a-number")),
            None
        );
        assert_eq!(price_decimal_from_json(&serde_json::json!(true)), None);
        assert_eq!(price_decimal_from_json(&serde_json::json!(null)), None);
        assert_eq!(price_decimal_from_json(&serde_json::json!([1, 2])), None);
    }

    #[test]
    fn test_price_request_builder() {
        let request = PriceRequest::new("AAPL", "USD");
        assert_eq!(request.ticker, "AAPL");
        assert_eq!(request.currency, "USD");
        assert!(request.date.is_none());

        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();
        let request_with_date = PriceRequest::new("AAPL", "USD").with_date(date);
        assert_eq!(request_with_date.date, Some(date));
    }

    #[test]
    fn test_registry_default_sources() {
        let registry = PriceSourceRegistry::default();

        // Built-in sources should be registered (no API key required)
        assert!(registry.has_source("yahoo"));
        assert!(registry.has_source("coinbase"));
        assert!(registry.has_source("coincap"));
        assert!(registry.has_source("ecb"));
        assert!(registry.has_source("ratesapi"));
        assert!(registry.has_source("tsp"));
        assert!(registry.has_source("eastmoneyfund"));

        // API key sources should also be registered (will error if key not set)
        assert!(registry.has_source("oanda"));
        assert!(registry.has_source("alphavantage"));
        assert!(registry.has_source("coinmarketcap"));
        assert!(registry.has_source("quandl"));

        // Default source should be yahoo
        assert_eq!(registry.default_source_name(), "yahoo");
    }

    #[test]
    fn test_registry_list_sources() {
        let registry = PriceSourceRegistry::default();
        let sources = registry.list_sources();

        assert!(sources.contains(&"yahoo"));
        assert!(sources.contains(&"coinbase"));

        // List should be sorted
        let mut sorted = sources.clone();
        sorted.sort_unstable();
        assert_eq!(sources, sorted);
    }

    #[test]
    fn test_resolve_mapping_simple() {
        let registry = PriceSourceRegistry::default();
        let mut mapping = HashMap::new();
        mapping.insert(
            "BTC".to_string(),
            CommodityMapping::Simple("BTC-USD".to_string()),
        );

        let attempts = registry.resolve_mapping("BTC", &mapping).unwrap();
        assert_eq!(attempts, vec![("yahoo".to_string(), "BTC-USD".to_string())]);
    }

    #[test]
    fn test_resolve_mapping_detailed() {
        let registry = PriceSourceRegistry::default();
        let mut mapping = HashMap::new();
        mapping.insert(
            "EUR".to_string(),
            CommodityMapping::Detailed(crate::config::DetailedMapping {
                source: SourceRef::Fallback(vec![
                    FallbackEntry::Name("ecb".to_string()),
                    FallbackEntry::Name("ratesapi".to_string()),
                ]),
                ticker: None,
                quote_currency: None,
            }),
        );

        let attempts = registry.resolve_mapping("EUR", &mapping).unwrap();
        assert_eq!(
            attempts,
            vec![
                ("ecb".to_string(), "EUR".to_string()),
                ("ratesapi".to_string(), "EUR".to_string()),
            ]
        );
    }

    /// Issue #966: by default, resolving a commodity that has no
    /// mapping (and no `--source` was provided at the call site) is an
    /// error rather than a silent dispatch to `default_source`. The
    /// error message points the user at every remediation path so they
    /// don't have to guess which one applies to their workflow.
    #[test]
    fn test_resolve_mapping_no_mapping_errors_by_default() {
        let registry = PriceSourceRegistry::default();
        let mapping = HashMap::new();

        let result = registry.resolve_mapping("AAPL", &mapping);
        let err = result.expect_err("default behavior must refuse unmapped symbols");
        let msg = err.to_string();
        assert!(
            msg.contains("AAPL"),
            "error must name the offending symbol: {msg}"
        );
        // Every remediation path must be discoverable from the error so
        // the user can pick whichever one fits their workflow.
        for needle in [
            "--source",
            "--mapping",
            "[price.mapping.AAPL]",
            "price:",
            "quote_currency:",
            "-f",
            "use_default_source",
        ] {
            assert!(msg.contains(needle), "error must mention `{needle}`: {msg}");
        }
    }

    /// `[price] use_default_source = true` restores the previous
    /// behavior — unmapped symbols dispatch to `default_source`.
    #[test]
    fn test_resolve_mapping_no_mapping_uses_default_when_opted_in() {
        let config = PriceConfig {
            use_default_source: Some(true),
            ..PriceConfig::default()
        };
        let registry = PriceSourceRegistry::new(&config);
        let mapping = HashMap::new();

        let attempts = registry
            .resolve_mapping("AAPL", &mapping)
            .expect("opt-in must allow default-source dispatch");
        assert_eq!(attempts, vec![("yahoo".to_string(), "AAPL".to_string())]);
    }

    /// Issue #963: a fallback chain whose entries carry per-source
    /// tickers must query each source with that source's own ticker.
    /// Previously all sources reused the first spec's ticker.
    #[test]
    fn test_resolve_mapping_fallback_uses_per_source_tickers() {
        let registry = PriceSourceRegistry::default();
        let mut mapping = HashMap::new();
        mapping.insert(
            "GBP".to_string(),
            CommodityMapping::Detailed(crate::config::DetailedMapping {
                source: SourceRef::Fallback(vec![
                    FallbackEntry::Detailed(FallbackDetail {
                        source: "ecbrates".to_string(),
                        ticker: Some("GBP-EUR".to_string()),
                    }),
                    FallbackEntry::Detailed(FallbackDetail {
                        source: "ecb".to_string(),
                        ticker: Some("GBP".to_string()),
                    }),
                ]),
                ticker: Some("GBP-EUR".to_string()),
                quote_currency: Some("EUR".to_string()),
            }),
        );

        let attempts = registry.resolve_mapping("GBP", &mapping).unwrap();
        assert_eq!(
            attempts,
            vec![
                ("ecbrates".to_string(), "GBP-EUR".to_string()),
                ("ecb".to_string(), "GBP".to_string()),
            ],
            "each fallback source must use its own ticker (issue #963)"
        );
    }

    /// Mixed-shape fallback: a bare-string entry inherits the parent
    /// ticker, while an object entry uses its own. Verifies the
    /// `FallbackEntry::Name(_)` arm of `resolve_mapping` falls through
    /// to `parent_ticker` correctly.
    #[test]
    fn test_resolve_mapping_fallback_mixed_entries_inherit_parent_ticker() {
        let registry = PriceSourceRegistry::default();
        let mut mapping = HashMap::new();
        mapping.insert(
            "BTC".to_string(),
            CommodityMapping::Detailed(crate::config::DetailedMapping {
                source: SourceRef::Fallback(vec![
                    FallbackEntry::Name("yahoo".to_string()),
                    FallbackEntry::Detailed(FallbackDetail {
                        source: "coingecko".to_string(),
                        ticker: Some("bitcoin".to_string()),
                    }),
                ]),
                ticker: Some("BTC-USD".to_string()),
                quote_currency: None,
            }),
        );

        let attempts = registry.resolve_mapping("BTC", &mapping).unwrap();
        assert_eq!(
            attempts,
            vec![
                // Bare-string entry inherits parent ticker.
                ("yahoo".to_string(), "BTC-USD".to_string()),
                // Detailed entry uses its own ticker.
                ("coingecko".to_string(), "bitcoin".to_string()),
            ]
        );
    }

    #[test]
    fn test_custom_config() {
        let config = PriceConfig {
            default_source: Some("coinbase".to_string()),
            timeout: Some(60),
            ..Default::default()
        };

        let registry = PriceSourceRegistry::new(&config);
        assert_eq!(registry.default_source_name(), "coinbase");
        assert_eq!(registry.timeout(), Duration::from_mins(1));
    }

    /// A source that reads beanprice's `BASE-SYMBOL` ticker, like
    /// `ratesapi`, records the pair it was asked for, and answers a fixed
    /// rate in the pair's currency.
    struct PairSource {
        rate: Decimal,
        asked: std::sync::Mutex<Vec<(String, String)>>,
    }

    impl PriceSource for PairSource {
        fn name(&self) -> &'static str {
            "pairs"
        }

        fn description(&self) -> &'static str {
            "test source"
        }

        fn bean_price_pair(&self, pair: sources::PricePair) -> sources::PricePair {
            match sources::split_dash_pair(&pair.ticker) {
                Some((ticker, currency)) => sources::PricePair {
                    ticker: ticker.to_string(),
                    currency: currency.to_string(),
                },
                None => pair,
            }
        }

        fn pair_base(&self, ticker: &str) -> Option<String> {
            sources::split_dash_pair(ticker).map(|(base, _)| base.to_string())
        }

        fn fetch_latest(&self, pair: &sources::PricePair) -> Result<PriceResponse> {
            self.asked
                .lock()
                .expect("not poisoned")
                .push((pair.ticker.clone(), pair.currency.clone()));
            Ok(PriceResponse {
                price: self.rate,
                currency: pair.currency.clone(),
                date: rustledger_core::naive_date(2024, 1, 15).expect("valid date"),
                source: "pairs".to_string(),
            })
        }
    }

    /// A registry holding only `sources`, and a mapping of `commodity` to
    /// the chain of `(source, ticker)` entries.
    fn registry_with(
        sources: Vec<(&str, Arc<dyn PriceSource>)>,
        commodity: &str,
        chain: &[(&str, &str)],
    ) -> (PriceSourceRegistry, HashMap<String, CommodityMapping>) {
        let registry = PriceSourceRegistry {
            sources: sources
                .into_iter()
                .map(|(name, source)| (name.to_string(), source))
                .collect(),
            ..PriceSourceRegistry::default()
        };
        let entries = chain
            .iter()
            .map(|(source, ticker)| {
                FallbackEntry::Detailed(FallbackDetail {
                    source: (*source).to_string(),
                    ticker: Some((*ticker).to_string()),
                })
            })
            .collect();
        let mut mapping = HashMap::new();
        mapping.insert(
            commodity.to_string(),
            CommodityMapping::Detailed(crate::config::DetailedMapping {
                source: SourceRef::Fallback(entries),
                ticker: None,
                quote_currency: None,
            }),
        );
        (registry, mapping)
    }

    fn pair_source(rate: &str) -> Arc<PairSource> {
        use std::str::FromStr;
        Arc::new(PairSource {
            rate: Decimal::from_str(rate).expect("valid rate"),
            asked: std::sync::Mutex::new(Vec::new()),
        })
    }

    /// `EUR:pairs/^EUR-GBP` for GBP fetches EUR in GBP and writes the
    /// inverse, GBP in EUR, labeled EUR, with bean-price's digits:
    /// `ONE / Decimal("0.83467")` in bean-price 2.1.0 is
    /// `1.198078282434974301220841770` (#2866).
    #[test]
    fn test_fetch_price_for_spec_inverts_a_caret_ticker() {
        let source = pair_source("0.83467");
        let (registry, mapping) = registry_with(
            vec![("pairs", source.clone())],
            "GBP",
            &[("pairs", "^EUR-GBP")],
        );
        let response = registry
            .fetch_price_for_spec("GBP", "EUR", None, &mapping)
            .expect("an inverted quote");
        assert_eq!(response.price.to_string(), "1.198078282434974301220841770");
        assert_eq!(response.currency, "EUR");
        assert_eq!(
            *source.asked.lock().expect("not poisoned"),
            vec![("EUR".to_string(), "GBP".to_string())]
        );
    }

    /// Outside `price:` metadata a `^` is part of the ticker, as on main:
    /// Yahoo's index tickers (`^GSPC`) start with one. A config mapping
    /// and `--mapping` reach the registry through `fetch_price`.
    #[test]
    fn test_fetch_price_keeps_a_caret_ticker_verbatim() {
        let source = pair_source("5000.12");
        let (registry, mapping) = registry_with(
            vec![("pairs", source.clone())],
            "SPX",
            &[("pairs", "^GSPC")],
        );
        let response = registry
            .fetch_price("SPX", "USD", None, &mapping)
            .expect("an uninverted quote");
        assert_eq!(response.price.to_string(), "5000.12");
        assert_eq!(
            *source.asked.lock().expect("not poisoned"),
            vec![("^GSPC".to_string(), "USD".to_string())]
        );
    }

    /// The inverse of a price of B in Q is a price of Q in B: it is refused
    /// when the quote is not in the commodity, or when the pair the ticker
    /// names is not based in the declared currency. Without `^`, the #2731
    /// label check refuses the same mismatches.
    #[test]
    fn test_fetch_price_for_spec_refuses_an_inverse_of_another_pair() {
        // CHF with `GBP:pairs/^EURUSD`, a ticker naming no pair the source
        // reads: the quote is in GBP, not CHF.
        let (registry, mapping) = registry_with(
            vec![("pairs", pair_source("1.08"))],
            "CHF",
            &[("pairs", "^EURUSD")],
        );
        let err = registry
            .fetch_price_for_spec("CHF", "GBP", None, &mapping)
            .expect_err("a GBP quote inverted is not a CHF price");
        assert_eq!(
            format!("{err:#}"),
            noted(
                "`^EURUSD` inverts a price in GBP, which is a price of GBP, not of CHF; \
                 refusing to write it as a CHF price",
            )
        );

        // GBP with `USD:pairs/^EUR-GBP`: the pair is based in EUR, not USD.
        let (registry, mapping) = registry_with(
            vec![("pairs", pair_source("0.83"))],
            "GBP",
            &[("pairs", "^EUR-GBP")],
        );
        let err = registry
            .fetch_price_for_spec("GBP", "USD", None, &mapping)
            .expect_err("an EUR-based pair inverted is not a USD price");
        assert_eq!(
            format!("{err:#}"),
            noted(
                "`^EUR-GBP` inverts a price of EUR, which is a price in EUR, not in USD; \
                 refusing to write it as a USD price",
            )
        );
    }

    /// bean-price's grammar takes one `^` before the ticker; `^^X` and a
    /// bare `^` are refused, not sent upstream.
    #[test]
    fn test_fetch_price_for_spec_refuses_a_malformed_caret() {
        for ticker in ["^^EUR-GBP", "^"] {
            let source = pair_source("0.83");
            let (registry, mapping) =
                registry_with(vec![("pairs", source.clone())], "GBP", &[("pairs", ticker)]);
            let err = registry
                .fetch_price_for_spec("GBP", "EUR", None, &mapping)
                .expect_err("a malformed `^`");
            assert_eq!(
                format!("{err:#}"),
                noted(&format!(
                    "invalid source ticker `{ticker}`: a bean-price spec inverts with one `^` \
                     before the ticker"
                ))
            );
            assert!(source.asked.lock().expect("not poisoned").is_empty());
        }
    }

    /// One half-even rounding to 28 significant digits, as Python's
    /// `ONE / D(x)` (values from bean-price 2.1.0's beancount). The first
    /// four were rounded twice before: `rust_decimal`'s division rounds to
    /// about 29 digits on its own.
    #[test]
    fn test_invert_price_matches_python_decimal() {
        use std::str::FromStr;
        for (rate, inverse) in [
            ("0.00000198", "505050.5050505050505050505051"),
            ("0.006550", "152.6717557251908396946564885"),
            ("0.051", "19.60784313725490196078431373"),
            ("4.538", "0.2203613926840017628911414720"),
            ("0.83467", "1.198078282434974301220841770"),
            ("1.0852", "0.9214891264283081459638776262"),
            ("3", "0.3333333333333333333333333333"),
            ("-4", "-0.25"),
            // Exact quotients take their shortest form, as in Python.
            ("2", "0.5"),
            ("0.25", "4"),
            ("2.50", "0.4"),
            ("8", "0.125"),
            ("0.8", "1.25"),
            // Python's `1E+28` and `1E+2`, written out.
            (
                "0.0000000000000000000000000001",
                "10000000000000000000000000000",
            ),
            ("0.01", "100"),
            // Below 0.1, rust_decimal's 28 decimal places hold k - 1
            // digits fewer near 10^-k: Python has
            // 0.006688963210702341137123745819 and
            // 1.262177448353618888658765705E-28.
            ("149.5", "0.0066889632107023411371237458"),
            (
                "7922816251426433759354395033",
                "0.0000000000000000000000000001",
            ),
        ] {
            let price = Decimal::from_str(rate).expect("valid rate");
            let inverse_of = invert_price(price).expect("invertible");
            assert_eq!(inverse_of.to_string(), inverse, "1 / {rate}");
        }
    }

    /// Stricter than Python: bean-price's `ecbrates` leaves the global
    /// decimal precision at its legs' (`getcontext().prec = max(5, ...)`),
    /// so its `ONE / price` writes `0.0890115` for `1 / 11.2345`. rledger
    /// keeps the 28 digits of Python's default context, on `ecbrates` as on
    /// every source.
    #[test]
    fn test_fetch_price_for_spec_ecbrates_inverse_keeps_28_digits() {
        let source = pair_source("11.2345");
        let (registry, mapping) = registry_with(
            vec![("ecbrates", source)],
            "SEK",
            &[("ecbrates", "^EUR-SEK")],
        );
        let response = registry
            .fetch_price_for_spec("SEK", "EUR", None, &mapping)
            .expect("an inverted quote");
        assert_eq!(response.price.to_string(), "0.0890115269927455605500912368");
    }

    /// No writable inverse: a zero price, and one so large its inverse
    /// rounds to zero at 28 decimal places (it would be written `0`).
    #[test]
    fn test_invert_price_refuses_zero() {
        let err = invert_price(Decimal::ZERO).expect_err("no inverse");
        assert_eq!(err.to_string(), "a zero price has no inverse");
        let err = invert_price(Decimal::MAX).expect_err("an inverse below 1e-28");
        assert_eq!(
            err.to_string(),
            "its inverse is below the smallest writable price (28 decimal places)"
        );
    }

    /// A ticker that names its pair is fetched as that pair, whatever the
    /// requested currency labels (#2866): `EUR:ratesapi/USD-EUR`.
    #[test]
    fn test_fetch_price_reads_a_pair_ticker() {
        let source = pair_source("0.88755");
        let (registry, mapping) = registry_with(
            vec![("pairs", source.clone())],
            "USD",
            &[("pairs", "USD-EUR")],
        );
        let response = registry
            .fetch_price_for_spec("USD", "EUR", None, &mapping)
            .expect("a quote");
        assert_eq!(response.price.to_string(), "0.88755");
        assert_eq!(response.currency, "EUR");
        assert_eq!(
            *source.asked.lock().expect("not poisoned"),
            vec![("USD".to_string(), "EUR".to_string())]
        );
    }

    /// A zero quote has no inverse: that attempt fails, and the chain goes
    /// on to the next source, where bean-price aborts the job with
    /// `DivisionByZero`.
    #[test]
    fn test_fetch_price_for_spec_zero_inverse_tries_the_next_source() {
        let (registry, mapping) = registry_with(
            vec![("zero", pair_source("0")), ("good", pair_source("2"))],
            "GBP",
            &[("zero", "^EUR-GBP"), ("good", "^EUR-GBP")],
        );
        let response = registry
            .fetch_price_for_spec("GBP", "EUR", None, &mapping)
            .expect("the second source answers");
        assert_eq!(response.price.to_string(), "0.5");

        let (registry, mapping) = registry_with(
            vec![("zero", pair_source("0"))],
            "GBP",
            &[("zero", "^EUR-GBP")],
        );
        let err = registry
            .fetch_price_for_spec("GBP", "EUR", None, &mapping)
            .expect_err("a zero quote cannot be inverted");
        assert_eq!(
            format!("{err:#}"),
            noted(
                "cannot invert the pairs price 0 GBP for `^EUR-GBP`: a zero price has no inverse",
            )
        );
    }

    /// bean-price's `ecbrates` module name resolves to the ECB source.
    #[test]
    fn test_registry_has_ecbrates() {
        let registry = PriceSourceRegistry::default();
        assert_eq!(
            registry.get("ecbrates").map(|source| source.name()),
            Some("ecb")
        );
    }

    /// `message` with the note every failed `^` inversion carries.
    fn noted(message: &str) -> String {
        format!("{message} ({INVERSION_NOTE})")
    }

    /// A source that reads its pair base as `reader` does (a real source,
    /// for the ticker forms), and answers a fixed rate in `currency`.
    struct BaseOf {
        reader: Arc<dyn PriceSource>,
        rate: Decimal,
        currency: &'static str,
    }

    impl PriceSource for BaseOf {
        fn name(&self) -> &'static str {
            self.reader.name()
        }

        fn description(&self) -> &'static str {
            "test source"
        }

        fn pair_base(&self, ticker: &str) -> Option<String> {
            self.reader.pair_base(ticker)
        }

        fn fetch_latest(&self, _pair: &sources::PricePair) -> Result<PriceResponse> {
            Ok(PriceResponse {
                price: self.rate,
                currency: self.currency.to_string(),
                date: rustledger_core::naive_date(2024, 1, 15).expect("valid date"),
                source: self.reader.name().to_string(),
            })
        }
    }

    /// `price: "<currency>:<source>/^<ticker>"` on `commodity`, against
    /// `reader`'s ticker forms and a quote of `rate` in `quoted`.
    fn spec_inverse(
        reader: Arc<dyn PriceSource>,
        ticker: &str,
        commodity: &str,
        currency: &str,
        rate: &str,
        quoted: &'static str,
    ) -> Result<PriceResponse> {
        use std::str::FromStr;
        let name = reader.name();
        let source = Arc::new(BaseOf {
            reader,
            rate: Decimal::from_str(rate).expect("valid rate"),
            currency: quoted,
        });
        let (registry, mapping) = registry_with(vec![(name, source)], commodity, &[(name, ticker)]);
        registry.fetch_price_for_spec(commodity, currency, None, &mapping)
    }

    /// oanda, coinbase and yahoo read their own pair from the ticker
    /// (`EUR_CHF`, `BTC-USD`, `EURCHF=X`): an inverse is written only in
    /// the pair's base (#2866).
    #[test]
    fn test_fetch_price_for_spec_checks_the_base_of_every_pair_ticker() {
        let timeout = std::time::Duration::from_secs(1);
        let oanda = || -> Arc<dyn PriceSource> { Arc::new(sources::OandaSource::new(timeout)) };
        let coinbase =
            || -> Arc<dyn PriceSource> { Arc::new(sources::CoinbaseSource::new(timeout)) };
        let yahoo =
            || -> Arc<dyn PriceSource> { Arc::new(sources::YahooFinanceSource::new(timeout)) };

        // CHF with `USD:oanda/^EUR_CHF`: an EUR-based pair, not USD.
        let err = spec_inverse(oanda(), "^EUR_CHF", "CHF", "USD", "0.94", "CHF")
            .expect_err("EUR per CHF is not a USD price");
        assert_eq!(
            format!("{err:#}"),
            noted(
                "`^EUR_CHF` inverts a price of EUR, which is a price in EUR, not in USD; \
                 refusing to write it as a USD price",
            )
        );
        // CHF with `EUR:oanda/^EUR_CHF`: the CHF price in EUR.
        let response = spec_inverse(oanda(), "^EUR_CHF", "CHF", "EUR", "0.8", "CHF")
            .expect("CHF per EUR inverted");
        assert_eq!(
            (response.price.to_string(), response.currency),
            ("1.25".to_string(), "EUR".to_string())
        );

        // USD with `EUR:coinbase/^BTC-USD`: a BTC-based pair, not EUR.
        let err = spec_inverse(coinbase(), "^BTC-USD", "USD", "EUR", "50000", "USD")
            .expect_err("BTC per USD is not an EUR price");
        assert_eq!(
            format!("{err:#}"),
            noted(
                "`^BTC-USD` inverts a price of BTC, which is a price in BTC, not in EUR; \
                 refusing to write it as a EUR price",
            )
        );
        // USD with `BTC:coinbase/^BTC-USD`: the USD price in BTC.
        let response = spec_inverse(coinbase(), "^BTC-USD", "USD", "BTC", "50000", "USD")
            .expect("USD per BTC inverted");
        assert_eq!(
            (response.price.to_string(), response.currency),
            ("0.00002".to_string(), "BTC".to_string())
        );

        // CHF with `USD:yahoo/^EURCHF=X`: an EUR-based pair, not USD; and
        // with `EUR:yahoo/^EURCHF=X`, the CHF price in EUR.
        let err = spec_inverse(yahoo(), "^EURCHF=X", "CHF", "USD", "0.8", "CHF")
            .expect_err("EUR per CHF is not a USD price");
        assert!(
            format!("{err:#}").starts_with("`^EURCHF=X` inverts a price of EUR"),
            "{err:#}"
        );
        let response = spec_inverse(yahoo(), "^EURCHF=X", "CHF", "EUR", "0.8", "CHF")
            .expect("CHF per EUR inverted");
        assert_eq!(response.price.to_string(), "1.25");
    }

    /// Round 3 of #2883: oanda CFDs and Yahoo's `XXX=X` are pairs too, a
    /// lower-case ticker is read as the source reads it, and alphavantage's
    /// `price:IBM:USD` inverts only into IBM.
    #[test]
    fn test_fetch_price_for_spec_checks_cfd_usd_and_stock_bases() {
        let timeout = std::time::Duration::from_secs(1);
        let oanda = || -> Arc<dyn PriceSource> { Arc::new(sources::OandaSource::new(timeout)) };
        let yahoo =
            || -> Arc<dyn PriceSource> { Arc::new(sources::YahooFinanceSource::new(timeout)) };
        let alphavantage =
            || -> Arc<dyn PriceSource> { Arc::new(sources::AlphaVantageSource::new(timeout)) };

        // USD with `EUR:oanda/^NAS100_USD`: an NAS100-based CFD, not EUR.
        let err = spec_inverse(oanda(), "^NAS100_USD", "USD", "EUR", "18000", "USD")
            .expect_err("NAS100 per USD is not an EUR price");
        assert_eq!(
            format!("{err:#}"),
            noted(
                "`^NAS100_USD` inverts a price of NAS100, which is a price in NAS100, not in \
                 EUR; refusing to write it as a EUR price"
            )
        );

        // JPY with `EUR:yahoo/^JPY=X`: Yahoo's `JPY=X` is USD-based. With
        // `USD:yahoo/^JPY=X`, the JPY price in USD.
        let err = spec_inverse(yahoo(), "^JPY=X", "JPY", "EUR", "150", "JPY")
            .expect_err("USD per JPY is not an EUR price");
        assert!(
            format!("{err:#}").starts_with("`^JPY=X` inverts a price of USD"),
            "{err:#}"
        );
        let response = spec_inverse(yahoo(), "^JPY=X", "JPY", "USD", "160", "JPY")
            .expect("JPY per USD inverted");
        assert_eq!(response.price.to_string(), "0.00625");

        // A lower-case ticker is checked, and the base printed upper-case.
        let err = spec_inverse(yahoo(), "^eurchf=x", "CHF", "usd", "0.94", "CHF")
            .expect_err("EUR per CHF is not a USD price");
        assert!(
            format!("{err:#}").starts_with(
                "`^eurchf=x` inverts a price of EUR, which is a price in EUR, not in USD"
            ),
            "{err:#}"
        );

        // USD with `price: "IBM:alphavantage/^price:IBM:USD"`: the USD price
        // in IBM shares; with `EUR:`, refused.
        let response = spec_inverse(alphavantage(), "^price:IBM:USD", "USD", "IBM", "250", "USD")
            .expect("USD per IBM inverted");
        assert_eq!(
            (response.price.to_string(), response.currency),
            ("0.004".to_string(), "IBM".to_string())
        );
        let err = spec_inverse(alphavantage(), "^price:IBM:USD", "USD", "EUR", "250", "USD")
            .expect_err("IBM per USD is not an EUR price");
        assert!(
            format!("{err:#}").starts_with("`^price:IBM:USD` inverts a price of IBM"),
            "{err:#}"
        );
    }

    /// The inversion note is attached once per fetch, after the attempts,
    /// with a separator of its own.
    #[test]
    fn test_fetch_price_for_spec_notes_inversion_once() {
        let (registry, mapping) = registry_with(
            vec![("a", pair_source("0")), ("b", pair_source("0"))],
            "GBP",
            &[("a", "^EUR-GBP"), ("b", "^EUR-GBP")],
        );
        let err = registry
            .fetch_price_for_spec("GBP", "EUR", None, &mapping)
            .expect_err("both quotes are zero");
        let text = format!("{err:#}");
        assert_eq!(text.matches(INVERSION_NOTE).count(), 1, "{text}");
        assert!(text.ends_with(&format!(" ({INVERSION_NOTE})")), "{text}");
    }

    /// `CoinCap` quotes in USD, so `^BTC` inverts into BTC only, and
    /// `EUR:coincap/^BTC` is refused (#2883 round 4). (`BTC:coincap/^BTC`
    /// asks for BTC in BTC, the dispatch's identity pair.)
    #[test]
    fn test_fetch_price_for_spec_checks_the_coincap_base() {
        let coincap = || -> Arc<dyn PriceSource> {
            Arc::new(sources::CoinCapSource::new(std::time::Duration::from_secs(
                1,
            )))
        };
        let err = spec_inverse(coincap(), "^BTC", "USD", "EUR", "50000", "USD")
            .expect_err("BTC per USD is not an EUR price");
        assert_eq!(
            format!("{err:#}"),
            noted(
                "`^BTC` inverts a price of BTC, which is a price in BTC, not in EUR; refusing \
                 to write it as a EUR price"
            )
        );
    }
}
