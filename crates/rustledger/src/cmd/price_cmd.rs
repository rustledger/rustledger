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
use std::collections::{HashMap, HashSet};
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

    /// Include commodities that aren't currently held (zero balance across
    /// all open balance-sheet accounts). Matches `bean-price --inactive`.
    /// Only meaningful with `-f`; ignored otherwise.
    #[arg(long, requires = "file")]
    inactive: bool,

    /// Also discover commodities that lack `price:`/`quote_currency:`
    /// metadata if their name looks like a ticker symbol (uppercase ASCII,
    /// digits, dashes, dots; ≤ 10 chars). Off by default — the strict
    /// default avoids spurious downloads for currency codes like `BAM`
    /// that happen to collide with stock tickers (issue #962). Note: not
    /// a 1:1 match for `bean-price --undeclared`, which walks transactions
    /// instead of `commodity` directives.
    /// Only meaningful with `-f`; ignored otherwise.
    #[arg(long, requires = "file")]
    undeclared: bool,

    /// Deprecated alias for `--inactive --undeclared`. Will be removed in
    /// a future release; prefer the granular flags. Hidden from help.
    #[arg(long, requires = "file", hide = true)]
    all_commodities: bool,

    /// Print the list of symbols and resolved (source, ticker, currency)
    /// tuples that would be fetched, then exit. No network calls.
    /// Matches `bean-price --dry-run`.
    #[arg(short = 'n', long)]
    dry_run: bool,

    /// Overwrite prices already present in the input file rather than
    /// skipping them. Matches `bean-price --clobber`. Only meaningful
    /// with `-f`; ignored otherwise.
    #[arg(short = 'C', long, requires = "file")]
    clobber: bool,
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
    // the active-commodity filter, matching `bean-price` semantics
    // (issues #948, #962).
    if args.all_commodities {
        eprintln!(
            "warning: `--all-commodities` is deprecated; use `--inactive --undeclared` instead. \
             It will be removed in a future release."
        );
    }
    let effective_inactive = args.inactive || args.all_commodities;
    let effective_undeclared = args.undeclared || args.all_commodities;

    // Parse `--date` early so it can be threaded into discovery. Without
    // this, `--date 2020-01-01 -f file` would still use today's balances
    // for the active-commodity filter — wrong for historical fetches and
    // diverges from `bean-price`, which walks the file as-of `--date`.
    let date: Option<NaiveDate> = if let Some(ref d) = args.date {
        Some(
            d.parse::<NaiveDate>()
                .with_context(|| format!("Invalid date: {d}"))?,
        )
    } else {
        None
    };

    // Tuple keys for `--clobber`: every existing `price` directive in the file
    // identifies a (symbol, quote_currency, date) we should skip fetching for
    // unless `--clobber` is set. Built alongside discovery to avoid loading
    // the ledger twice.
    let (discovered, existing_prices): (
        HashMap<String, DiscoveredCommodity>,
        HashSet<(String, String, NaiveDate)>,
    ) = if let Some(ref file) = args.file {
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
        let discovered = discover_symbols(
            &ledger.directives,
            &ledger.options,
            effective_inactive,
            effective_undeclared,
            date,
        );
        let mut existing = HashSet::new();
        for spanned in &ledger.directives {
            if let rustledger_core::Directive::Price(p) = &spanned.value {
                existing.insert((
                    p.currency.as_str().to_string(),
                    p.amount.currency.as_str().to_string(),
                    p.date,
                ));
            }
        }
        (discovered, existing)
    } else {
        (HashMap::new(), HashSet::new())
    };

    // Stable order: alphabetical by symbol so output is deterministic across
    // runs (the underlying discovery uses a HashMap). Symbols come from
    // both file-based discovery and explicit CLI args; we union them, but
    // remember which set each symbol belongs to so the explicit-fetch
    // path (#966) only fires for CLI-only symbols (file-discovered
    // commodities have already passed through metadata- or `--undeclared`-
    // based opt-in checks).
    let mut symbols_to_fetch: Vec<String> = discovered.keys().cloned().collect();
    for s in &args.symbols {
        if !discovered.contains_key(s) {
            symbols_to_fetch.push(s.clone());
        }
    }
    symbols_to_fetch.sort();
    // Dedup repeated CLI args (e.g. `rledger price AAPL AAPL`) so we
    // don't fetch the same symbol twice.
    symbols_to_fetch.dedup();

    if symbols_to_fetch.is_empty() {
        eprintln!(
            "No symbols to fetch. Provide symbols as arguments or use -f with a beancount file."
        );
        if args.file.is_some() {
            if !effective_undeclared {
                eprintln!(
                    "Hint: only commodities with `price:` or `quote_currency:` metadata are \
                     fetched by default. Pass --undeclared to also include ticker-shaped names."
                );
            }
            if !effective_inactive {
                eprintln!(
                    "Hint: only commodities currently held are fetched by default. \
                     Pass --inactive to include those with zero balance."
                );
            }
        }
        return Ok(());
    }

    if args.verbose {
        eprintln!("Fetching prices for: {symbols_to_fetch:?}");
    }

    let combined_mapping = build_combined_mapping(&price_config.mapping, &discovered, &cli_mapping);

    if args.dry_run {
        return dump_fetch_plan(
            args,
            &symbols_to_fetch,
            &discovered,
            &price_config.mapping,
            &combined_mapping,
            &existing_prices,
            price_config.effective_default_source(),
            price_config.effective_use_default_source(),
            date,
        );
    }

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
            &existing_prices,
        );
    }

    let stdout = io::stdout();
    let mut handle = stdout.lock();

    // Fetch prices
    let source_name_for_cache = args
        .source
        .as_deref()
        .unwrap_or(price_config.effective_default_source());

    for symbol in &symbols_to_fetch {
        // Resolve quote currency against `price_config.mapping`, not the
        // merged `combined_mapping`. CLI `--mapping AUD:NEW-TICKER` creates
        // a `Simple` entry that overwrites a config-file `Detailed` entry
        // for the same symbol — using `combined_mapping` here would silently
        // drop the config's `quote_currency` even though the user only
        // intended to override the ticker. Source/ticker lookup still uses
        // the merged map below; only currency resolution stays config-only.
        let effective_currency =
            resolve_quote_currency(symbol, &discovered, &price_config.mapping, &args.currency);

        // --clobber: skip fetch when an explicit `price` directive for
        // (symbol, effective_currency, fetch_date) already exists in the file.
        // Match bean-price's semantics: existing prices are kept unless
        // --clobber is set.
        //
        // Limitation: this checks the REQUESTED date (`--date` or today). Some
        // sources return a different effective date for "latest" — ECB, for
        // instance, returns the last published business day on weekends. An
        // existing directive dated to the source's actual quote date will not
        // be matched here, so a duplicate may still be emitted. Fixing this
        // requires a post-fetch re-check; tracked as a follow-up.
        if !args.clobber {
            let fetch_date = date.unwrap_or_else(|| jiff::Zoned::now().date());
            if existing_prices.contains(&(symbol.clone(), effective_currency.clone(), fetch_date)) {
                if args.verbose {
                    eprintln!(
                        "{symbol}: skipped (existing price for {fetch_date} {effective_currency}; pass --clobber to refetch)"
                    );
                }
                continue;
            }
        }

        // Check cache first
        let key = cache_key(source_name_for_cache, symbol, &effective_currency, date);
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
            fetch_with_source(&registry, source_name, symbol, &effective_currency, date)
        } else {
            registry.fetch_price(symbol, &effective_currency, date, &combined_mapping)
        };

        match result {
            Ok(response) => {
                if let Some(ref mut c) = cache {
                    // Use the actual source that responded (may differ from
                    // default due to fallback chains)
                    let actual_key = cache_key(&response.source, symbol, &effective_currency, date);
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

/// Build the merged commodity-to-source mapping used during fetch.
///
/// Precedence (high to low):
/// 1. CLI `--mapping <SYMBOL>:<TICKER>` (always wins).
/// 2. Discovered `price:` metadata on a commodity directive.
/// 3. Config-file `[price.mapping.X]` entries (preserved when discovery
///    found the same commodity but only via `quote_currency:` /
///    `--undeclared` — i.e. `info.mapping = None`).
/// 4. Synthesized `Simple(symbol)` for file-discovered commodities that
///    opt in via `quote_currency:` only or matched `--undeclared` and
///    have no config entry. Without this, `resolve_mapping` would fire
///    the #966 explicit-source-required error and break those flows.
///
/// CLI-only symbols (in `args.symbols` but not in `discovered`) are
/// intentionally NOT auto-mapped — they hit `resolve_mapping`'s error
/// path unless the user passed `--source`, `--mapping`, or set
/// `[price] use_default_source = true`. That's the #966 fix.
fn build_combined_mapping(
    config_mapping: &HashMap<String, CommodityMapping>,
    discovered: &HashMap<String, DiscoveredCommodity>,
    cli_mapping: &HashMap<String, CommodityMapping>,
) -> HashMap<String, CommodityMapping> {
    let mut combined = config_mapping.clone();
    for (symbol, info) in discovered {
        if let Some(m) = &info.mapping {
            // Discovered metadata explicitly named a source — overrides
            // any config entry for the same symbol.
            combined.insert(symbol.clone(), m.clone());
        } else {
            // No source spec from metadata. Synthesize a default-source
            // mapping ONLY if the config doesn't already cover this
            // symbol — otherwise we'd silently overwrite a deliberate
            // `[price.mapping.X]` block with a Simple default-source
            // dispatch.
            combined
                .entry(symbol.clone())
                .or_insert_with(|| CommodityMapping::Simple(symbol.clone()));
        }
    }
    for (k, v) in cli_mapping {
        combined.insert(k.clone(), v.clone());
    }
    combined
}

/// Resolve the effective quote currency for a single symbol.
///
/// Precedence (high to low), per issue #952:
/// 1. `quote_currency:` metadata on the commodity directive (or the first
///    `price:` entry's quote currency), captured by `discovery` at load time
/// 2. `quote_currency = "..."` in the `[price.mapping.X]` config-file block
/// 3. The global `--currency` flag default
fn resolve_quote_currency(
    symbol: &str,
    discovered: &HashMap<String, DiscoveredCommodity>,
    mapping: &HashMap<String, CommodityMapping>,
    default_currency: &str,
) -> String {
    if let Some(c) = discovered
        .get(symbol)
        .and_then(|d| d.quote_currency.as_deref())
    {
        return c.to_string();
    }
    if let Some(CommodityMapping::Detailed(d)) = mapping.get(symbol)
        && let Some(c) = &d.quote_currency
    {
        return c.clone();
    }
    default_currency.to_string()
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

/// Print the resolved fetch plan for `--dry-run`. One line per symbol:
///   `<symbol> /<currency> @ <date> <source>(<ticker>)[, <source>(<ticker>)...]`
/// Symbols whose `(symbol, currency, date)` is already in `existing_prices`
/// are annotated `skip: existing` (matching the real run's `--clobber` gate)
/// unless `--clobber` is set.
#[allow(clippy::too_many_arguments)]
fn dump_fetch_plan(
    args: &PriceArgs,
    symbols: &[String],
    discovered: &HashMap<String, DiscoveredCommodity>,
    config_mapping: &HashMap<String, CommodityMapping>,
    combined_mapping: &HashMap<String, CommodityMapping>,
    existing_prices: &HashSet<(String, String, NaiveDate)>,
    default_source: &str,
    use_default_source: bool,
    date: Option<NaiveDate>,
) -> Result<()> {
    let stdout = io::stdout();
    let mut handle = stdout.lock();
    let date_str = date.map_or_else(|| "today".to_string(), |d| d.to_string());
    let fetch_date = date.unwrap_or_else(|| jiff::Zoned::now().date());

    for symbol in symbols {
        let currency = resolve_quote_currency(symbol, discovered, config_mapping, &args.currency);

        // --source and --source-cmd bypass the mapping entirely.
        let mut attempts: Vec<(String, String)> = if args.source_cmd.is_some() {
            vec![("source-cmd".to_string(), symbol.clone())]
        } else if let Some(s) = &args.source {
            vec![(s.clone(), symbol.clone())]
        } else {
            describe_attempts(symbol, combined_mapping, default_source)
        };
        // Mirror the runtime fallback: with `use_default_source = true`, a
        // CLI-only symbol that isn't in any mapping still goes to
        // `default_source` rather than erroring. Without this, dry-run
        // disagrees with the actual fetch plan for users who opted back
        // into default-source dispatch.
        if attempts.is_empty()
            && use_default_source
            && args.source_cmd.is_none()
            && args.source.is_none()
        {
            attempts.push((default_source.to_string(), symbol.clone()));
        }

        let attempts_str = if attempts.is_empty() {
            "<unmapped>".to_string()
        } else {
            attempts
                .iter()
                .map(|(s, t)| format!("{s}({t})"))
                .collect::<Vec<_>>()
                .join(", ")
        };

        let skipped = !args.clobber
            && existing_prices.contains(&(symbol.clone(), currency.clone(), fetch_date));
        let suffix = if skipped {
            "  [skip: existing price]"
        } else {
            ""
        };

        writeln!(
            handle,
            "{symbol} /{currency} @ {date_str} {attempts_str}{suffix}"
        )?;
    }
    Ok(())
}

/// Walk a `CommodityMapping` into the ordered list of (source, ticker) pairs
/// the registry would attempt. Used by `dump_fetch_plan`. `Simple` mappings
/// resolve their source name to the configured default (e.g. `yahoo`) so the
/// dump shows what will actually run, not the placeholder string `default`.
fn describe_attempts(
    symbol: &str,
    combined_mapping: &HashMap<String, CommodityMapping>,
    default_source: &str,
) -> Vec<(String, String)> {
    use crate::config::SourceRef;
    let Some(m) = combined_mapping.get(symbol) else {
        return Vec::new();
    };
    match m {
        CommodityMapping::Simple(ticker) => {
            vec![(default_source.to_string(), ticker.clone())]
        }
        CommodityMapping::Detailed(d) => {
            let parent_ticker = d.ticker.as_deref().unwrap_or(symbol);
            match &d.source {
                SourceRef::Single(s) => vec![(s.clone(), parent_ticker.to_string())],
                SourceRef::Fallback(entries) => entries
                    .iter()
                    .map(|e| match e {
                        crate::config::FallbackEntry::Name(s) => {
                            (s.clone(), parent_ticker.to_string())
                        }
                        crate::config::FallbackEntry::Detailed(fd) => (
                            fd.source.clone(),
                            fd.ticker
                                .clone()
                                .unwrap_or_else(|| parent_ticker.to_string()),
                        ),
                    })
                    .collect(),
            }
        }
    }
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
    existing_prices: &HashSet<(String, String, NaiveDate)>,
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
        // Same currency-resolution discipline as the network path: use the
        // raw config mapping so a CLI `--mapping` Simple override can't
        // silently wipe out a config-file `Detailed.quote_currency`.
        let effective_currency =
            resolve_quote_currency(symbol, discovered, &price_config.mapping, &args.currency);

        // --clobber: skip when an existing price for this (symbol, currency, date)
        // is already in the file. Same rule as the network fetch path.
        if !args.clobber {
            let fetch_date = date.unwrap_or_else(|| jiff::Zoned::now().date());
            if existing_prices.contains(&(symbol.clone(), effective_currency.clone(), fetch_date)) {
                if args.verbose {
                    eprintln!(
                        "{symbol}: skipped (existing price for {fetch_date} {effective_currency}; pass --clobber to refetch)"
                    );
                }
                continue;
            }
        }

        let request = PriceRequest {
            ticker: symbol.clone(),
            currency: effective_currency.clone(),
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
    fn test_price_args_discovery_flags_default_off() {
        let args = Args::parse_from(["price", "AAPL"]);
        assert!(!args.price_args.inactive);
        assert!(!args.price_args.undeclared);
    }

    #[test]
    fn test_price_args_inactive_flag() {
        let args = Args::parse_from(["price", "--inactive", "-f", "ledger.beancount"]);
        assert!(args.price_args.inactive);
        assert!(!args.price_args.undeclared);
    }

    #[test]
    fn test_price_args_undeclared_flag() {
        let args = Args::parse_from(["price", "--undeclared", "-f", "ledger.beancount"]);
        assert!(args.price_args.undeclared);
        assert!(!args.price_args.inactive);
    }

    #[test]
    fn test_price_args_inactive_and_undeclared_combined() {
        // The legacy `--all-commodities` semantics — both relaxations on.
        let args = Args::parse_from([
            "price",
            "--inactive",
            "--undeclared",
            "-f",
            "ledger.beancount",
        ]);
        assert!(args.price_args.inactive);
        assert!(args.price_args.undeclared);
    }

    /// Issue #962 follow-up (Copilot review on PR #965): keep
    /// `--all-commodities` accepted as a deprecated, hidden alias for
    /// `--inactive --undeclared` so user scripts from 0.14.1 don't break.
    #[test]
    fn test_price_args_all_commodities_deprecated_alias_still_parses() {
        let args = Args::parse_from(["price", "--all-commodities", "-f", "ledger.beancount"]);
        assert!(args.price_args.all_commodities);
        // The deprecated flag doesn't auto-set the new flags at parse
        // time; the run function maps it to effective_inactive /
        // effective_undeclared so the user still sees a deprecation
        // warning printed exactly once at run time.
        assert!(!args.price_args.inactive);
        assert!(!args.price_args.undeclared);
    }

    #[test]
    fn test_resolve_quote_currency_prefers_discovered_metadata() {
        // Discovered metadata (from `quote_currency:` or `price:` on a commodity
        // directive) wins over the config-file mapping.
        let mut discovered = HashMap::new();
        discovered.insert(
            "AAPL".to_string(),
            DiscoveredCommodity {
                quote_currency: Some("EUR".to_string()),
                ..DiscoveredCommodity::default()
            },
        );
        let mut mapping = HashMap::new();
        mapping.insert(
            "AAPL".to_string(),
            CommodityMapping::Detailed(crate::config::DetailedMapping {
                source: crate::config::SourceRef::Single("yahoo".into()),
                ticker: None,
                quote_currency: Some("GBP".into()),
            }),
        );

        assert_eq!(
            resolve_quote_currency("AAPL", &discovered, &mapping, "USD"),
            "EUR"
        );
    }

    #[test]
    fn test_resolve_quote_currency_falls_back_to_config_mapping() {
        // Issue #952: the AUD config-file `quote_currency` should override
        // the global default when no discovery info is present.
        let discovered = HashMap::new();
        let mut mapping = HashMap::new();
        mapping.insert(
            "AUD".to_string(),
            CommodityMapping::Detailed(crate::config::DetailedMapping {
                source: crate::config::SourceRef::Single("ecb".into()),
                ticker: None,
                quote_currency: Some("EUR".into()),
            }),
        );

        assert_eq!(
            resolve_quote_currency("AUD", &discovered, &mapping, "USD"),
            "EUR"
        );
    }

    #[test]
    fn test_resolve_quote_currency_uses_default_when_unset() {
        let discovered = HashMap::new();
        let mapping = HashMap::new();
        assert_eq!(
            resolve_quote_currency("AAPL", &discovered, &mapping, "USD"),
            "USD"
        );
    }

    #[test]
    fn test_resolve_quote_currency_simple_mapping_does_not_set_currency() {
        // `CommodityMapping::Simple("VTI")` carries no quote currency, so
        // the global default applies.
        let discovered = HashMap::new();
        let mut mapping = HashMap::new();
        mapping.insert("VTI".to_string(), CommodityMapping::Simple("VTI".into()));
        assert_eq!(
            resolve_quote_currency("VTI", &discovered, &mapping, "USD"),
            "USD"
        );
    }

    #[test]
    fn test_resolve_quote_currency_uses_raw_config_not_merged_mapping() {
        // Regression for Copilot review on PR #953: a CLI `--mapping
        // AUD:NEW-TICKER` overwrites the config-file `Detailed` entry with
        // `Simple` in the merged map. If we resolved currency against the
        // merged map, the config's `quote_currency` would be silently
        // dropped. The fix is to resolve against the raw config map; the
        // CLI override only affects ticker/source, not currency.
        //
        // This test simulates that exact precondition: `mapping` (the raw
        // config) has the Detailed entry the user wrote; the merged
        // combined_mapping (not passed to `resolve_quote_currency`) would
        // have it overwritten with Simple. resolve_quote_currency must
        // surface the config's "EUR".
        let discovered = HashMap::new();
        let mut mapping = HashMap::new();
        mapping.insert(
            "AUD".to_string(),
            CommodityMapping::Detailed(crate::config::DetailedMapping {
                source: crate::config::SourceRef::Single("ecb".into()),
                ticker: None,
                quote_currency: Some("EUR".into()),
            }),
        );
        // Note: we deliberately do NOT pass a merged map that has
        // CommodityMapping::Simple("AUD-EUR") for AUD here. `price_cmd::run`
        // is responsible for passing `&price_config.mapping`, not the merged
        // one. This unit test asserts the helper behaves correctly when
        // given the raw config map; the call-site comment in `run`
        // documents the contract.
        assert_eq!(
            resolve_quote_currency("AUD", &discovered, &mapping, "USD"),
            "EUR"
        );
    }

    #[test]
    fn test_resolve_quote_currency_detailed_without_quote_currency_uses_default() {
        // The common case: a config with `[price.mapping.X] source = "..."`
        // and no `quote_currency` should fall through to the global default,
        // not surface an empty string or panic.
        let discovered = HashMap::new();
        let mut mapping = HashMap::new();
        mapping.insert(
            "AAPL".to_string(),
            CommodityMapping::Detailed(crate::config::DetailedMapping {
                source: crate::config::SourceRef::Single("yahoo".into()),
                ticker: None,
                quote_currency: None,
            }),
        );
        assert_eq!(
            resolve_quote_currency("AAPL", &discovered, &mapping, "USD"),
            "USD"
        );
    }

    /// Regression for self-review on PR #971: when discovery returns an
    /// `info.mapping = None` for a symbol that ALSO has a config-level
    /// `[price.mapping.X]` entry, the synthesized `Simple` default-source
    /// mapping must NOT overwrite the user's deliberate config block.
    #[test]
    fn build_combined_mapping_preserves_config_for_quote_currency_only_commodity() {
        // Config: BTC dispatches to coinbase.
        let mut config_mapping = HashMap::new();
        config_mapping.insert(
            "BTC".to_string(),
            CommodityMapping::Detailed(crate::config::DetailedMapping {
                source: crate::config::SourceRef::Single("coinbase".to_string()),
                ticker: Some("BTC-USD".to_string()),
                quote_currency: None,
            }),
        );

        // Discovery: BTC has `quote_currency: "USD"` only, no `price:`.
        // -> `info.mapping = None`.
        let mut discovered = HashMap::new();
        discovered.insert(
            "BTC".to_string(),
            DiscoveredCommodity {
                mapping: None,
                quote_currency: Some("USD".to_string()),
            },
        );

        let combined = build_combined_mapping(&config_mapping, &discovered, &HashMap::new());

        let entry = combined.get("BTC").expect("BTC must remain in mapping");
        match entry {
            CommodityMapping::Detailed(d) => {
                match &d.source {
                    crate::config::SourceRef::Single(s) => assert_eq!(
                        s, "coinbase",
                        "config-level coinbase mapping must survive discovery synthesis"
                    ),
                    crate::config::SourceRef::Fallback(_) => {
                        panic!("expected Single source, got Fallback")
                    }
                }
                assert_eq!(d.ticker.as_deref(), Some("BTC-USD"));
            }
            CommodityMapping::Simple(_) => {
                panic!("expected Detailed mapping; synthesis silently overwrote config");
            }
        }
    }

    /// `quote_currency:`-only / `--undeclared` symbols WITHOUT a config
    /// entry must be synthesized to `Simple(symbol)` so they dispatch
    /// through the default source rather than tripping the #966
    /// explicit-source-required guard.
    #[test]
    fn build_combined_mapping_synthesizes_simple_for_unmapped_discovered_symbol() {
        let config_mapping = HashMap::new();
        let mut discovered = HashMap::new();
        discovered.insert(
            "GOVT_EU".to_string(),
            DiscoveredCommodity {
                mapping: None,
                quote_currency: Some("EUR".to_string()),
            },
        );

        let combined = build_combined_mapping(&config_mapping, &discovered, &HashMap::new());

        match combined.get("GOVT_EU") {
            Some(CommodityMapping::Simple(s)) => assert_eq!(s, "GOVT_EU"),
            other => panic!("expected synthesized Simple(\"GOVT_EU\"), got {other:?}"),
        }
    }

    /// Discovered metadata with a real source/ticker overrides any
    /// config entry for that symbol (existing precedence rule from
    /// #948/#951; pinned here so the synthesis refactor doesn't break it).
    #[test]
    fn build_combined_mapping_discovered_metadata_overrides_config() {
        let mut config_mapping = HashMap::new();
        config_mapping.insert(
            "AAPL".to_string(),
            CommodityMapping::Simple("AAPL-OLD".to_string()),
        );
        let mut discovered = HashMap::new();
        discovered.insert(
            "AAPL".to_string(),
            DiscoveredCommodity {
                mapping: Some(CommodityMapping::Detailed(crate::config::DetailedMapping {
                    source: crate::config::SourceRef::Single("yahoo".to_string()),
                    ticker: Some("AAPL".to_string()),
                    quote_currency: None,
                })),
                quote_currency: None,
            },
        );

        let combined = build_combined_mapping(&config_mapping, &discovered, &HashMap::new());
        match combined.get("AAPL") {
            Some(CommodityMapping::Detailed(d)) => match &d.source {
                crate::config::SourceRef::Single(s) => assert_eq!(s, "yahoo"),
                crate::config::SourceRef::Fallback(_) => {
                    panic!("expected Single source, got Fallback")
                }
            },
            other => panic!("expected metadata to override config, got {other:?}"),
        }
    }

    /// CLI `--mapping` always wins, even over discovered metadata.
    #[test]
    fn build_combined_mapping_cli_mapping_wins_over_discovery() {
        let config_mapping = HashMap::new();
        let mut discovered = HashMap::new();
        discovered.insert(
            "AAPL".to_string(),
            DiscoveredCommodity {
                mapping: Some(CommodityMapping::Simple("AAPL-DISCOVERED".to_string())),
                quote_currency: None,
            },
        );
        let mut cli_mapping = HashMap::new();
        cli_mapping.insert(
            "AAPL".to_string(),
            CommodityMapping::Simple("AAPL-CLI".to_string()),
        );

        let combined = build_combined_mapping(&config_mapping, &discovered, &cli_mapping);
        match combined.get("AAPL") {
            Some(CommodityMapping::Simple(s)) => assert_eq!(s, "AAPL-CLI"),
            other => panic!("CLI must win, got {other:?}"),
        }
    }

    // ========== --dry-run / describe_attempts ==========

    #[test]
    fn describe_attempts_simple_mapping_uses_configured_default() {
        // Simple mappings should resolve to the actual configured default source,
        // not the placeholder "default" — otherwise the dry-run dump is useless
        // for confirming what will run.
        let mut combined = HashMap::new();
        combined.insert(
            "AAPL".to_string(),
            CommodityMapping::Simple("AAPL".to_string()),
        );
        let attempts = describe_attempts("AAPL", &combined, "yahoo");
        assert_eq!(attempts, vec![("yahoo".to_string(), "AAPL".to_string())]);
    }

    #[test]
    fn describe_attempts_walks_fallback_chain_with_per_source_tickers() {
        // Regression for #963: each fallback entry's own ticker must show up,
        // not the parent's, so the dry-run accurately previews chained behavior.
        use crate::config::{DetailedMapping, FallbackDetail, FallbackEntry, SourceRef};
        let mut combined = HashMap::new();
        combined.insert(
            "GBP".to_string(),
            CommodityMapping::Detailed(DetailedMapping {
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
                ticker: Some("GBP".to_string()),
                quote_currency: Some("EUR".to_string()),
            }),
        );
        let attempts = describe_attempts("GBP", &combined, "yahoo");
        assert_eq!(
            attempts,
            vec![
                ("ecbrates".to_string(), "GBP-EUR".to_string()),
                ("ecb".to_string(), "GBP".to_string()),
            ]
        );
    }

    #[test]
    fn describe_attempts_unmapped_returns_empty() {
        // Unmapped symbols (CLI-only, no metadata, no config, no --source) should
        // produce zero attempts so the dry-run prints `<unmapped>`.
        let attempts = describe_attempts("AAPL", &HashMap::new(), "yahoo");
        assert!(attempts.is_empty());
    }

    // ========== --clobber / -C parsing ==========

    #[test]
    fn test_price_args_clobber_flag() {
        // --clobber requires -f, so test with -f present.
        let args = Args::parse_from(["price", "-f", "ledger.beancount", "--clobber"]);
        assert!(args.price_args.clobber);

        // Short form -C also works.
        let args = Args::parse_from(["price", "-f", "ledger.beancount", "-C"]);
        assert!(args.price_args.clobber);

        // Default is false.
        let args = Args::parse_from(["price", "AAPL"]);
        assert!(!args.price_args.clobber);
    }

    #[test]
    fn test_price_args_clobber_requires_file() {
        // --clobber without -f should error (declared `requires = "file"`).
        let result = Args::try_parse_from(["price", "AAPL", "--clobber"]);
        assert!(result.is_err(), "--clobber without -f must be rejected");
    }

    // ========== --dry-run parsing ==========

    #[test]
    fn test_price_args_dry_run_flag() {
        let args = Args::parse_from(["price", "AAPL", "--dry-run"]);
        assert!(args.price_args.dry_run);

        // Short form -n.
        let args = Args::parse_from(["price", "AAPL", "-n"]);
        assert!(args.price_args.dry_run);

        // dry-run does not require -f (works with explicit symbols).
        let args = Args::try_parse_from(["price", "AAPL", "-n"]);
        assert!(args.is_ok());
    }
}
