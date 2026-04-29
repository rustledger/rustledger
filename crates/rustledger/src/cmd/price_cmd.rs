//! Price fetching command for rustledger.
//!
//! Fetches current prices for commodities from configurable online sources.

use crate::cmd::completions::ShellType;
use crate::cmd::price::discovery::{DiscoveredCommodity, discover_symbols};
use crate::cmd::price::sources::PriceSource;
use crate::cmd::price::{PriceRequest, PriceSourceRegistry};
use crate::config::{CommodityMapping, PriceConfig};
use anyhow::{Context, Result};
use clap::Parser;
use rustledger_core::NaiveDate;
use rustledger_loader::LoadOptions;
use std::collections::HashMap;
use std::io::{self, Write};
use std::path::PathBuf;
use std::time::Duration;

/// Fetch current prices for commodities.
#[derive(Parser, Debug)]
#[command(name = "price", about = "Fetch current prices for commodities")]
pub struct Args {
    /// Generate shell completions for the specified shell.
    #[arg(long, value_name = "SHELL")]
    generate_completions: Option<ShellType>,

    /// Price command arguments.
    #[command(flatten)]
    pub price_args: PriceArgs,
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

    /// Symbol mapping (e.g., VTI:VTI,BTC:BTC-USD).
    /// Maps commodity names to ticker symbols.
    #[arg(short = 'm', long, value_delimiter = ',')]
    mapping: Vec<String>,

    /// Use specific source (overrides mapping).
    #[arg(short = 's', long)]
    source: Option<String>,

    /// Use ad-hoc external command as source.
    /// The command receives the ticker as the first argument.
    #[arg(long, value_name = "CMD")]
    source_cmd: Option<String>,

    /// List configured sources and exit.
    #[arg(long)]
    list_sources: bool,

    /// Disable the price cache for this run.
    #[arg(long)]
    no_cache: bool,

    /// Clear the price cache before fetching.
    #[arg(long)]
    clear_cache: bool,

    /// When discovering symbols from `-f`, include commodities that aren't
    /// currently held (zero balance across all open accounts). The default
    /// matches `bean-price`: only fetch prices for commodities you actually
    /// hold.
    #[arg(long)]
    all_commodities: bool,
}

/// Run the price command.
pub fn run(args: &PriceArgs, price_config: &PriceConfig) -> Result<()> {
    use crate::cmd::price::cache::{PriceCache, cache_key};

    // Create the registry with config
    let registry = PriceSourceRegistry::new(price_config);

    // Handle --clear-cache (works even with --no-cache or cache_ttl=0)
    let cache_ttl = price_config.effective_cache_ttl();
    if args.clear_cache {
        let mut c = PriceCache::load(cache_ttl);
        c.clear();
        if args.verbose {
            eprintln!("Price cache cleared");
        }
    }

    // Initialize cache (if enabled)
    let cache_enabled = cache_ttl > 0 && !args.no_cache;
    let mut cache = if cache_enabled {
        Some(PriceCache::load(cache_ttl))
    } else {
        None
    };

    // Handle --list-sources
    if args.list_sources {
        return list_sources(&registry);
    }

    // Build symbol mapping from CLI args
    let mut cli_mapping: HashMap<String, CommodityMapping> = HashMap::new();
    for mapping in &args.mapping {
        if let Some((from, to)) = mapping.split_once(':') {
            cli_mapping.insert(from.to_string(), CommodityMapping::Simple(to.to_string()));
        }
    }

    // Discover symbols from the ledger (if -f given) plus any CLI symbols.
    // The discovery layer handles `price:` / `quote_currency:` metadata and
    // the active-commodity filter (issue #948).
    let discovered: HashMap<String, DiscoveredCommodity> = if let Some(ref file) = args.file {
        // Load with booking so interpolated postings (units missing in source,
        // filled in by the booking engine) get explicit amounts. Without this,
        // the active-commodity check at `discovery::active_commodities` would
        // miss the held side of any auto-balanced posting and could mark
        // currently-held commodities as inactive.
        let opts = LoadOptions {
            // Skip plugins / validation here: discovery only cares about
            // booked postings, and plugin/validation failures shouldn't
            // block fetching prices on an otherwise-loadable file.
            run_plugins: false,
            validate: false,
            ..LoadOptions::default()
        };
        let ledger = rustledger_loader::load(file, &opts)
            .with_context(|| format!("failed to load {} for symbol discovery", file.display()))?;
        discover_symbols(
            &ledger.directives,
            &ledger.options,
            &args.symbols,
            args.all_commodities,
        )
    } else {
        let mut out = HashMap::new();
        for s in &args.symbols {
            out.insert(s.clone(), DiscoveredCommodity::default());
        }
        out
    };

    // Stable order: alphabetical by symbol so output is deterministic across
    // runs (the underlying discovery uses a HashMap).
    let mut symbols_to_fetch: Vec<String> = discovered.keys().cloned().collect();
    symbols_to_fetch.sort();

    if symbols_to_fetch.is_empty() {
        eprintln!(
            "No symbols to fetch. Provide symbols as arguments or use -f with a beancount file."
        );
        if !args.all_commodities && args.file.is_some() {
            eprintln!(
                "Hint: only commodities currently held are fetched by default. \
                 Pass --all-commodities to include inactive ones."
            );
        }
        return Ok(());
    }

    if args.verbose {
        eprintln!("Fetching prices for: {symbols_to_fetch:?}");
    }

    // Parse target date
    let date = if let Some(ref d) = args.date {
        Some(
            d.parse::<NaiveDate>()
                .with_context(|| format!("Invalid date: {d}"))?,
        )
    } else {
        None
    };

    // Handle --source-cmd (ad-hoc external command)
    // This is placed after symbol discovery so -f flag works with --source-cmd
    if let Some(cmd) = &args.source_cmd {
        return run_with_external_command(
            args,
            cmd,
            &symbols_to_fetch,
            date,
            price_config,
            &discovered,
        );
    }

    // Merge mappings in increasing precedence (later inserts override earlier
    // ones via `HashMap::insert`). The effective high-to-low order is:
    //   1. CLI --mapping (last to insert, wins)
    //   2. Discovered `price:` metadata from commodity directives (#948)
    //   3. Config [price.mapping] (first to insert, lowest precedence)
    let mut combined_mapping = price_config.mapping.clone();
    for (symbol, info) in &discovered {
        if let Some(m) = &info.mapping {
            combined_mapping.insert(symbol.clone(), m.clone());
        }
    }
    for (k, v) in cli_mapping {
        combined_mapping.insert(k, v);
    }

    let stdout = io::stdout();
    let mut handle = stdout.lock();

    // Fetch prices
    let source_name_for_cache = args
        .source
        .as_deref()
        .unwrap_or(price_config.effective_default_source());

    for symbol in &symbols_to_fetch {
        // Per-commodity quote currency from `quote_currency:` (or first
        // `price:` entry) overrides the global --currency for this symbol.
        let effective_currency = discovered
            .get(symbol)
            .and_then(|d| d.quote_currency.as_deref())
            .unwrap_or(&args.currency);

        // Check cache first
        let key = cache_key(source_name_for_cache, symbol, effective_currency, date);
        if let Some(ref c) = cache
            && let Some(cached) = c.get(&key)
        {
            if args.verbose {
                eprintln!("{symbol}: cached (source: {})", cached.source);
            }
            write_price(&mut handle, symbol, &cached, args.beancount)?;
            continue;
        }

        // Fetch from network
        let result = if let Some(source_name) = &args.source {
            fetch_with_source(&registry, source_name, symbol, effective_currency, date)
        } else {
            registry.fetch_price(symbol, effective_currency, date, &combined_mapping)
        };

        match result {
            Ok(response) => {
                if let Some(ref mut c) = cache {
                    // Use the actual source that responded (may differ from
                    // default due to fallback chains)
                    let actual_key = cache_key(&response.source, symbol, effective_currency, date);
                    c.insert(&actual_key, &response);
                    // Also store under the default source key for fast lookup
                    if actual_key != key {
                        c.insert(&key, &response);
                    }
                }
                write_price(&mut handle, symbol, &response, args.beancount)?;
            }
            Err(e) => {
                if args.verbose {
                    eprintln!("Error fetching {symbol}: {e}");
                } else {
                    eprintln!("; Failed to fetch {symbol}: {e}");
                }
            }
        }
    }

    // Save cache to disk
    if let Some(ref mut c) = cache {
        c.save();
    }

    Ok(())
}

/// Fetch a price using a specific source.
fn fetch_with_source(
    registry: &PriceSourceRegistry,
    source_name: &str,
    ticker: &str,
    currency: &str,
    date: Option<NaiveDate>,
) -> Result<crate::cmd::price::PriceResponse> {
    let source = registry
        .get(source_name)
        .with_context(|| format!("Unknown source: {source_name}"))?;

    let request = PriceRequest {
        ticker: ticker.to_string(),
        currency: currency.to_string(),
        date,
    };

    source.fetch_price(&request)
}

/// Write a price response to the output.
fn write_price(
    handle: &mut impl Write,
    symbol: &str,
    response: &crate::cmd::price::PriceResponse,
    beancount: bool,
) -> Result<()> {
    if beancount {
        let date_str = response.date.to_string();
        writeln!(
            handle,
            "{date_str} price {symbol} {} {}",
            response.price, response.currency
        )?;
    } else {
        writeln!(handle, "{symbol}: {} {}", response.price, response.currency)?;
    }
    Ok(())
}

/// Run with an ad-hoc external command.
fn run_with_external_command(
    args: &PriceArgs,
    cmd: &str,
    symbols: &[String],
    date: Option<NaiveDate>,
    price_config: &PriceConfig,
    discovered: &HashMap<String, DiscoveredCommodity>,
) -> Result<()> {
    use crate::cmd::price::external::ExternalCommandSource;

    // Parse the command string into parts
    let command_parts: Vec<String> =
        shell_words::split(cmd).with_context(|| format!("Failed to parse command: {cmd}"))?;

    if command_parts.is_empty() {
        anyhow::bail!("Empty command provided");
    }

    // Use config timeout instead of hardcoded value
    let timeout = Duration::from_secs(price_config.effective_timeout());
    let source = ExternalCommandSource::new(command_parts, timeout, HashMap::new());

    let stdout = io::stdout();
    let mut handle = stdout.lock();

    for symbol in symbols {
        // Honor per-commodity quote_currency / price: metadata for --source-cmd
        // too, matching the network-fetch path.
        let effective_currency = discovered
            .get(symbol)
            .and_then(|d| d.quote_currency.as_deref())
            .unwrap_or(&args.currency);
        let request = PriceRequest {
            ticker: symbol.clone(),
            currency: effective_currency.to_string(),
            date,
        };

        match source.fetch_price(&request) {
            Ok(response) => {
                if args.beancount {
                    let date_str = response.date.to_string();
                    writeln!(
                        handle,
                        "{date_str} price {symbol} {} {}",
                        response.price, response.currency
                    )?;
                } else {
                    writeln!(handle, "{symbol}: {} {}", response.price, response.currency)?;
                }
            }
            Err(e) => {
                if args.verbose {
                    eprintln!("Error fetching {symbol}: {e}");
                } else {
                    eprintln!("; Failed to fetch {symbol}: {e}");
                }
            }
        }
    }

    Ok(())
}

/// List all configured sources.
fn list_sources(registry: &PriceSourceRegistry) -> Result<()> {
    println!("Available price sources:");
    println!();

    let sources = registry.list_sources();
    let default_source = registry.default_source_name();

    for name in sources {
        if let Some(source) = registry.get(name) {
            let default_marker = if name == default_source {
                " (default)"
            } else {
                ""
            };
            let api_key_note = if source.requires_api_key() {
                if let Some(env_var) = source.api_key_env_var() {
                    if std::env::var(env_var).is_ok() {
                        " [API key set]"
                    } else {
                        " [API key required]"
                    }
                } else {
                    " [API key required]"
                }
            } else {
                ""
            };
            println!("  {name}{default_marker}{api_key_note}");
            println!("    {}", source.description());
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

    #[test]
    fn test_price_args_with_source() {
        let args = Args::parse_from(["price", "-s", "coinbase", "BTC"]);
        assert_eq!(args.price_args.source, Some("coinbase".to_string()));
        assert_eq!(args.price_args.symbols, vec!["BTC"]);
    }

    #[test]
    fn test_price_args_with_source_cmd() {
        let args = Args::parse_from(["price", "--source-cmd", "echo 150.00 USD", "AAPL"]);
        assert_eq!(
            args.price_args.source_cmd,
            Some("echo 150.00 USD".to_string())
        );
    }

    #[test]
    fn test_price_args_list_sources() {
        let args = Args::parse_from(["price", "--list-sources"]);
        assert!(args.price_args.list_sources);
    }

    #[test]
    fn test_price_args_no_cache() {
        let args = Args::parse_from(["price", "--no-cache", "AAPL"]);
        assert!(args.price_args.no_cache);
        assert!(!args.price_args.clear_cache);
    }

    #[test]
    fn test_price_args_clear_cache() {
        let args = Args::parse_from(["price", "--clear-cache", "AAPL"]);
        assert!(args.price_args.clear_cache);
        assert!(!args.price_args.no_cache);
    }

    #[test]
    fn test_price_args_clear_and_no_cache_together() {
        let args = Args::parse_from(["price", "--clear-cache", "--no-cache", "AAPL"]);
        assert!(args.price_args.clear_cache);
        assert!(args.price_args.no_cache);
    }

    #[test]
    fn test_price_args_all_commodities_default_off() {
        let args = Args::parse_from(["price", "AAPL"]);
        assert!(!args.price_args.all_commodities);
    }

    #[test]
    fn test_price_args_all_commodities_flag() {
        let args = Args::parse_from(["price", "--all-commodities", "-f", "ledger.beancount"]);
        assert!(args.price_args.all_commodities);
    }
}
