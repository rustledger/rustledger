//! Price fetching command for rustledger.
//!
//! Fetches current prices for commodities from online sources like Yahoo Finance.

use crate::cmd::completions::ShellType;
use anyhow::{Context, Result};
use chrono::{NaiveDate, Utc};
use clap::Parser;
use rust_decimal::Decimal;
use rustledger_loader::Loader;
use std::collections::HashMap;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;
use std::str::FromStr;

/// Fetch current prices for commodities.
#[derive(Parser, Debug)]
#[command(name = "price", about = "Fetch current prices for commodities")]
pub struct Args {
    /// Generate shell completions for the specified shell.
    #[arg(long, value_name = "SHELL")]
    generate_completions: Option<ShellType>,

    #[command(flatten)]
    price_args: PriceArgs,
}

/// Price-specific arguments.
#[derive(Parser, Debug)]
pub struct PriceArgs {
    /// Beancount file to read commodities from (optional).
    #[arg(short, long)]
    file: Option<PathBuf>,

    /// Specific commodity symbols to fetch (e.g., AAPL, MSFT).
    #[arg(value_name = "SYMBOL")]
    symbols: Vec<String>,

    /// Base currency for price quotes.
    #[arg(short = 'c', long, default_value = "USD")]
    currency: String,

    /// Date for prices (YYYY-MM-DD, defaults to today).
    #[arg(short, long)]
    date: Option<String>,

    /// Output as beancount price directives.
    #[arg(short = 'b', long)]
    beancount: bool,

    /// Show verbose output.
    #[arg(short, long)]
    verbose: bool,

    /// Yahoo Finance symbol mapping (e.g., VTI:VTI,BTC:BTC-USD).
    #[arg(short = 'm', long, value_delimiter = ',')]
    mapping: Vec<String>,
}

/// Price source trait for different data providers.
pub trait PriceSource {
    /// Fetch price for a symbol.
    fn fetch_price(&self, symbol: &str) -> Result<Option<Decimal>>;

    /// Fetch prices for multiple symbols.
    fn fetch_prices(&self, symbols: &[String]) -> HashMap<String, Result<Decimal>>;

    /// Source name.
    fn name(&self) -> &'static str;
}

/// Yahoo Finance price source.
pub struct YahooFinance {
    #[allow(dead_code)]
    currency: String,
}

impl YahooFinance {
    /// Create a new Yahoo Finance price source.
    pub fn new(currency: impl Into<String>) -> Self {
        Self {
            currency: currency.into(),
        }
    }

    /// Build the Yahoo Finance API URL.
    fn build_url(&self, symbol: &str) -> String {
        format!("https://query1.finance.yahoo.com/v8/finance/chart/{symbol}?interval=1d&range=1d")
    }
}

impl PriceSource for YahooFinance {
    fn fetch_price(&self, symbol: &str) -> Result<Option<Decimal>> {
        let url = self.build_url(symbol);

        let response = ureq::get(&url)
            .set("User-Agent", "Mozilla/5.0 (compatible; rustledger/1.0)")
            .call()
            .with_context(|| format!("Failed to fetch price for {symbol}"))?;

        let json: serde_json::Value = response
            .into_json()
            .with_context(|| format!("Failed to parse response for {symbol}"))?;

        // Navigate to the price in the response
        let price = json
            .get("chart")
            .and_then(|c| c.get("result"))
            .and_then(|r| r.get(0))
            .and_then(|r| r.get("meta"))
            .and_then(|m| m.get("regularMarketPrice"))
            .and_then(|p| p.as_f64());

        match price {
            Some(p) => {
                let decimal = Decimal::from_str(&format!("{p:.4}"))
                    .with_context(|| format!("Failed to convert price {p} to decimal"))?;
                Ok(Some(decimal))
            }
            None => Ok(None),
        }
    }

    fn fetch_prices(&self, symbols: &[String]) -> HashMap<String, Result<Decimal>> {
        let mut results = HashMap::new();

        for symbol in symbols {
            let result = self
                .fetch_price(symbol)
                .and_then(|opt| opt.ok_or_else(|| anyhow::anyhow!("No price found for {symbol}")));
            results.insert(symbol.clone(), result);
        }

        results
    }

    fn name(&self) -> &'static str {
        "yahoo"
    }
}

/// Main entry point for the price command.
pub fn main() -> ExitCode {
    main_with_name("rledger-price")
}

/// Main entry point with custom binary name (for bean-price compatibility).
pub fn main_with_name(bin_name: &str) -> ExitCode {
    let args = Args::parse();

    // Handle shell completion generation
    if let Some(shell) = args.generate_completions {
        crate::cmd::completions::generate_completions::<Args>(shell, bin_name);
        return ExitCode::SUCCESS;
    }

    match run(&args.price_args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e:#}");
            ExitCode::from(1)
        }
    }
}

/// Run the price command.
pub fn run(args: &PriceArgs) -> Result<()> {
    let mut symbols_to_fetch: Vec<String> = args.symbols.clone();

    // Build symbol mapping
    let mut symbol_mapping: HashMap<String, String> = HashMap::new();
    for mapping in &args.mapping {
        if let Some((from, to)) = mapping.split_once(':') {
            symbol_mapping.insert(from.to_string(), to.to_string());
        }
    }

    // If a file is provided, extract commodity symbols
    if let Some(ref file) = args.file {
        let mut loader = Loader::new();
        let ledger = loader.load(file)?;

        // Get commodities that might have ticker symbols
        for spanned in &ledger.directives {
            if let rustledger_core::Directive::Commodity(comm) = &spanned.value {
                let symbol = comm.currency.as_str();
                // Check if it looks like a ticker symbol (uppercase letters)
                if symbol
                    .chars()
                    .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '-')
                    && symbol.len() <= 10
                    && !symbols_to_fetch.contains(&symbol.to_string())
                {
                    symbols_to_fetch.push(symbol.to_string());
                }
            }
        }
    }

    if symbols_to_fetch.is_empty() {
        eprintln!(
            "No symbols to fetch. Provide symbols as arguments or use -f with a beancount file."
        );
        return Ok(());
    }

    // Map symbols to Yahoo Finance symbols
    let yahoo_symbols: Vec<String> = symbols_to_fetch
        .iter()
        .map(|s| symbol_mapping.get(s).cloned().unwrap_or_else(|| s.clone()))
        .collect();

    if args.verbose {
        eprintln!("Fetching prices for: {yahoo_symbols:?}");
    }

    // Create price source and fetch
    let source = YahooFinance::new(&args.currency);
    let prices = source.fetch_prices(&yahoo_symbols);

    // Parse target date
    let date = if let Some(ref d) = args.date {
        NaiveDate::parse_from_str(d, "%Y-%m-%d").with_context(|| format!("Invalid date: {d}"))?
    } else {
        Utc::now().date_naive()
    };

    let stdout = io::stdout();
    let mut handle = stdout.lock();

    // Output results
    for (i, original_symbol) in symbols_to_fetch.iter().enumerate() {
        let yahoo_symbol = &yahoo_symbols[i];

        match prices.get(yahoo_symbol) {
            Some(Ok(price)) => {
                if args.beancount {
                    // Output as beancount price directive
                    let date_str = date.format("%Y-%m-%d");
                    let currency = &args.currency;
                    writeln!(
                        handle,
                        "{date_str} price {original_symbol} {price} {currency}"
                    )?;
                } else {
                    let currency = &args.currency;
                    writeln!(handle, "{original_symbol}: {price} {currency}")?;
                }
            }
            Some(Err(e)) => {
                if args.verbose {
                    eprintln!("Error fetching {original_symbol}: {e}");
                } else {
                    eprintln!("; Failed to fetch {original_symbol}: {e}");
                }
            }
            None => {
                eprintln!("; No result for {original_symbol}");
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_price_args_parsing() {
        let args = Args::parse_from(["price", "AAPL", "MSFT"]);
        assert_eq!(args.price_args.symbols, vec!["AAPL", "MSFT"]);
        assert_eq!(args.price_args.currency, "USD");
        assert!(!args.price_args.beancount);
    }

    #[test]
    fn test_price_args_with_options() {
        let args = Args::parse_from([
            "price",
            "-c",
            "EUR",
            "-b",
            "-m",
            "BTC:BTC-USD,ETH:ETH-USD",
            "BTC",
            "ETH",
        ]);
        assert_eq!(args.price_args.symbols, vec!["BTC", "ETH"]);
        assert_eq!(args.price_args.currency, "EUR");
        assert!(args.price_args.beancount);
        assert_eq!(args.price_args.mapping.len(), 2);
    }
}
