//! Quandl (Nasdaq Data Link) price source.
//!
//! Fetches financial data from Quandl/Nasdaq Data Link.

use super::{DateWindow, HistoricalCoverage, PricePair, PricePoint, PriceSource, http_get_json};
use crate::cmd::price::PriceResponse;
use anyhow::{Context, Result};
use std::env;
use std::time::Duration;

/// Quandl (Nasdaq Data Link) price source.
///
/// Uses Nasdaq Data Link's API (formerly Quandl) to fetch financial data.
/// Requires an API key set in the `QUANDL_API_KEY` environment variable.
///
/// # API Key
///
/// Get a free API key at <https://data.nasdaq.com/>
/// Set it as: `export QUANDL_API_KEY=your-key-here`
///
/// # Supported Datasets
///
/// Uses the format `DATABASE/DATASET` for tickers, or beanprice's
/// `DATABASE:DATASET[:COLUMN]` (e.g. `WIKI:AAPL`, `WIKI:AAPL:Adj._Close`):
/// - `WIKI/AAPL` - Wiki EOD Stock Prices
/// - `LBMA/GOLD` - London Bullion Market Gold Price
/// - `FRED/GDP` - Federal Reserve Economic Data
/// - `CHRIS/CME_CL1` - CME Crude Oil Futures
#[derive(Debug)]
pub struct QuandlSource {
    /// Whole-request timeout, applied to each request.
    timeout: Duration,
}

/// How a Quandl ticker picks the dataset column that holds the price.
#[derive(Debug, Clone, PartialEq, Eq)]
enum PriceColumn {
    /// rledger's `DATABASE/DATASET` form: the first column whose name
    /// contains `close`, `value`, `price` or `settle`.
    Heuristic,
    /// beanprice's `DATABASE:DATASET` form: `Adj. Close`, else `Close`,
    /// as beanprice's `quandl` picks it.
    BeanPriceDefault,
    /// beanprice's `DATABASE:DATASET:COLUMN` form: the column named.
    Named(String),
}

impl PriceColumn {
    /// The index of the price column among `column_names`.
    fn index(&self, column_names: &[serde_json::Value]) -> Result<usize> {
        let position = |name: &str| column_names.iter().position(|c| c.as_str() == Some(name));
        match self {
            Self::Heuristic => column_names
                .iter()
                .position(|c| {
                    c.as_str().is_some_and(|s| {
                        let lower = s.to_lowercase();
                        lower.contains("close")
                            || lower.contains("value")
                            || lower.contains("price")
                            || lower.contains("settle")
                    })
                })
                .with_context(|| "No price column found in dataset"),
            Self::BeanPriceDefault => position("Adj. Close")
                .or_else(|| position("Close"))
                .with_context(|| "No 'Adj. Close' or 'Close' column in the dataset"),
            Self::Named(name) => {
                position(name).with_context(|| format!("No '{name}' column in the dataset"))
            }
        }
    }
}

impl QuandlSource {
    /// Create a new Quandl source.
    pub const fn new(timeout: Duration) -> Self {
        Self { timeout }
    }

    /// Get the API key from environment.
    fn get_api_key() -> Result<String> {
        env::var("QUANDL_API_KEY").with_context(|| "QUANDL_API_KEY environment variable not set")
    }

    /// Build the Quandl API URL. `None` asks for the latest row
    /// (`limit=1`); a [`DateWindow`] asks for the inclusive
    /// `start_date`/`end_date` slice of the dataset (#1802 source
    /// ports).
    fn build_url(&self, dataset: &str, api_key: &str, window: Option<DateWindow>) -> String {
        match window {
            Some(w) => format!(
                "https://data.nasdaq.com/api/v3/datasets/{dataset}/data.json?start_date={}&end_date={}&api_key={api_key}",
                w.start, w.end
            ),
            None => format!(
                "https://data.nasdaq.com/api/v3/datasets/{dataset}/data.json?limit=1&api_key={api_key}"
            ),
        }
    }

    /// Parse a ticker into the dataset and the way its price column is
    /// picked.
    ///
    /// beanprice's form (#2866) is `DATABASE:DATASET[:COLUMN]`, matched
    /// as beanprice's `quandl` matches it, `[A-Z0-9]+:[A-Z0-9]+(:[^:; ]+)?$`,
    /// with `_` in COLUMN read as a space (`WIKI:AAPL:Adj._Close`).
    /// rledger's own forms, `DATABASE/DATASET` and a bare `DATASET` (in
    /// `WIKI`), still work.
    fn parse_dataset(ticker: &str) -> (&str, &str, PriceColumn) {
        let code = |s: &str| {
            !s.is_empty()
                && s.chars()
                    .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit())
        };
        let mut parts = ticker.splitn(3, ':');
        if let (Some(database), Some(dataset)) = (parts.next(), parts.next())
            && code(database)
            && code(dataset)
        {
            match parts.next() {
                None => return (database, dataset, PriceColumn::BeanPriceDefault),
                Some(column) if !column.is_empty() && !column.contains([':', ';', ' ']) => {
                    return (
                        database,
                        dataset,
                        PriceColumn::Named(column.replace('_', " ")),
                    );
                }
                Some(_) => {}
            }
        }
        if let Some(pos) = ticker.find('/') {
            (&ticker[..pos], &ticker[pos + 1..], PriceColumn::Heuristic)
        } else {
            ("WIKI", ticker, PriceColumn::Heuristic)
        }
    }

    /// Shared fetch + parse for the dataset endpoint (latest or
    /// windowed — same response shape): every row of
    /// `dataset_data.data` becomes a [`PricePoint`] (#1802 source
    /// ports). Rows with a missing/unparsable date or price are
    /// SKIPPED, never today-labeled — a today-fallback on a historical
    /// row would be discarded by the dispatch's on-or-before selection,
    /// turning a served rate into a spurious no-quote error (deep
    /// review of #1803).
    fn fetch_rows(
        &self,
        url: &str,
        api_key: &str,
        pair: &PricePair,
        column: &PriceColumn,
        undated_fallback: Option<rustledger_core::NaiveDate>,
    ) -> Result<Vec<PricePoint>> {
        let json = http_get_json(
            url,
            self.timeout,
            &[],
            &[api_key],
            &format!("Failed to fetch data for {}", pair.ticker),
        )?;

        // Check for errors
        if let Some(quandl_error) = json.get("quandl_error") {
            let code = quandl_error
                .get("code")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("UNKNOWN");
            let message = quandl_error
                .get("message")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("Unknown error");
            anyhow::bail!("Quandl error {code}: {message}");
        }

        let dataset_data = json
            .get("dataset_data")
            .with_context(|| "Missing dataset_data in response")?;

        let rows = dataset_data
            .get("data")
            .and_then(serde_json::Value::as_array)
            .with_context(|| "Missing data in response")?;

        let column_names = dataset_data
            .get("column_names")
            .and_then(serde_json::Value::as_array)
            .with_context(|| "Missing column names")?;

        // Find the date column (usually first)
        let date_idx = column_names
            .iter()
            .position(|c| {
                c.as_str()
                    .is_some_and(|s| s.to_lowercase().contains("date"))
            })
            .unwrap_or(0);

        let price_idx = column.index(column_names)?;

        let mut points = Vec::new();
        for row in rows {
            let Some(row) = row.as_array() else {
                continue;
            };
            // The row's OWN date, never the requested one (#1794). A
            // row with an unresolvable date takes `undated_fallback`
            // on the LATEST path (today, matching feed_date_or's rule
            // and main's behavior) and is SKIPPED on the historical
            // path (deep review of #1804 restored the latest fallback
            // this refactor had dropped).
            let raw_date = row.get(date_idx).and_then(serde_json::Value::as_str);
            let Some(date) = super::feed_date(raw_date).or(undated_fallback) else {
                continue;
            };
            let Some(price) = row
                .get(price_idx)
                .and_then(crate::cmd::price::price_decimal_from_json)
            else {
                continue;
            };
            points.push(PricePoint {
                date,
                price,
                // The dataset's quote currency is dataset-defined and
                // not reported per row; the dispatch substitutes the
                // request currency, uppercased.
                currency: None,
            });
        }
        Ok(points)
    }
}

impl PriceSource for QuandlSource {
    fn name(&self) -> &'static str {
        "quandl"
    }

    fn description(&self) -> &'static str {
        "Nasdaq Data Link (Quandl) - financial datasets (requires API key)"
    }

    fn requires_api_key(&self) -> bool {
        true
    }

    fn api_key_env_var(&self) -> Option<&'static str> {
        Some("QUANDL_API_KEY")
    }

    fn fetch_latest(&self, pair: &PricePair) -> Result<PriceResponse> {
        let api_key = Self::get_api_key()?;
        let (database, dataset, column) = Self::parse_dataset(&pair.ticker);
        let full_dataset = format!("{database}/{dataset}");
        let url = self.build_url(&full_dataset, &api_key, None);

        // The row's own date, never the requested one (#1794); the
        // greatest-date pick guards against a provider that ignores
        // limit=1 (providers do not guarantee sorted series).
        let points = self.fetch_rows(
            &url,
            &api_key,
            pair,
            &column,
            Some(jiff::Zoned::now().date()),
        )?;
        let point = points.into_iter().max_by_key(|p| p.date).with_context(
            || "No usable rows in the Quandl response (empty dataset or unparsable prices)",
        )?;

        Ok(PriceResponse {
            price: point.price,
            currency: pair.currency.clone(),
            date: point.date,
            source: self.name().to_string(),
        })
    }

    fn historical_coverage(&self) -> HistoricalCoverage {
        // Nasdaq Data Link datasets carry their own full history
        // (#1802 source ports); dates a given dataset lacks surface as
        // the dispatch's clean no-quote error, not a refusal.
        HistoricalCoverage::Full
    }

    fn fetch_window(&self, pair: &PricePair, window: DateWindow) -> Result<Vec<PricePoint>> {
        // Same endpoint as the latest path, sliced by the inclusive
        // start_date/end_date parameters (#1802 source ports); the
        // dispatch does on-or-before selection over the rows.
        let api_key = Self::get_api_key()?;
        let (database, dataset, column) = Self::parse_dataset(&pair.ticker);
        let full_dataset = format!("{database}/{dataset}");
        let url = self.build_url(&full_dataset, &api_key, Some(window));
        self.fetch_rows(&url, &api_key, pair, &column, None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_dataset() {
        use PriceColumn::{BeanPriceDefault, Heuristic, Named};
        assert_eq!(
            QuandlSource::parse_dataset("WIKI/AAPL"),
            ("WIKI", "AAPL", Heuristic)
        );
        assert_eq!(
            QuandlSource::parse_dataset("LBMA/GOLD"),
            ("LBMA", "GOLD", Heuristic)
        );
        assert_eq!(
            QuandlSource::parse_dataset("AAPL"),
            ("WIKI", "AAPL", Heuristic)
        );
        // beanprice's form, with the cases of beanprice's own
        // quandl_test.py `test_parse_ticker` (#2866).
        assert_eq!(
            QuandlSource::parse_dataset("WIKI:FB"),
            ("WIKI", "FB", BeanPriceDefault)
        );
        assert_eq!(
            QuandlSource::parse_dataset("LBMA:GOLD:USD_(PM)"),
            ("LBMA", "GOLD", Named("USD (PM)".to_string()))
        );
        // Not beanprice's form: read as rledger's, as before.
        assert_eq!(
            QuandlSource::parse_dataset("LBMA:GOLD:col:umn"),
            ("WIKI", "LBMA:GOLD:col:umn", Heuristic)
        );
        assert_eq!(
            QuandlSource::parse_dataset("wiki:FB"),
            ("WIKI", "wiki:FB", Heuristic)
        );
    }

    /// The price column each ticker form picks (#2866): beanprice's form
    /// takes `Adj. Close`, else `Close`, or the column it names; rledger's
    /// takes the first close/value/price/settle column, as before.
    #[test]
    fn test_price_column_index() {
        let wiki: Vec<serde_json::Value> = ["Date", "Open", "Close", "Volume", "Adj. Close"]
            .into_iter()
            .map(serde_json::Value::from)
            .collect();
        assert_eq!(PriceColumn::Heuristic.index(&wiki).unwrap(), 2);
        assert_eq!(PriceColumn::BeanPriceDefault.index(&wiki).unwrap(), 4);
        assert_eq!(
            PriceColumn::Named("Open".to_string()).index(&wiki).unwrap(),
            1
        );
        let no_adj: Vec<serde_json::Value> = ["Date", "Close"]
            .into_iter()
            .map(serde_json::Value::from)
            .collect();
        assert_eq!(PriceColumn::BeanPriceDefault.index(&no_adj).unwrap(), 1);
        let err = PriceColumn::Named("USD (PM)".to_string())
            .index(&no_adj)
            .unwrap_err();
        assert_eq!(err.to_string(), "No 'USD (PM)' column in the dataset");
    }

    #[test]
    fn test_build_url() {
        let source = QuandlSource::new(Duration::from_secs(30));
        let url = source.build_url("WIKI/AAPL", "demo", None);
        assert!(url.contains("WIKI/AAPL"));
        assert!(url.contains("data.nasdaq.com"));
        assert!(url.contains("limit=1"), "{url}");

        // Historical (#1802): the window replaces the limit=1 form.
        let window = DateWindow {
            start: rustledger_core::naive_date(2024, 1, 8).unwrap(),
            end: rustledger_core::naive_date(2024, 1, 15).unwrap(),
        };
        let url = source.build_url("WIKI/AAPL", "demo", Some(window));
        assert!(url.contains("start_date=2024-01-08"), "{url}");
        assert!(url.contains("end_date=2024-01-15"), "{url}");
        assert!(!url.contains("limit="), "{url}");
    }

    #[test]
    fn test_source_metadata() {
        let source = QuandlSource::new(Duration::from_secs(30));
        assert_eq!(source.name(), "quandl");
        assert!(source.requires_api_key());
        assert_eq!(source.api_key_env_var(), Some("QUANDL_API_KEY"));
    }
}
