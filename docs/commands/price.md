______________________________________________________________________

## title: rledger price description: Fetch commodity prices

# rledger price

Fetch current and historical commodity prices from online sources.

## Usage

```bash
rledger price [OPTIONS] [SYMBOL]...
```

## Arguments

| Argument | Description |
|----------|-------------|
| `SYMBOL...` | One or more commodity symbols (e.g., AAPL, BTC, EUR) |

## Options

| Option | Description |
|--------|-------------|
| `-f, --file <FILE>` | Beancount file to discover commodities from |
| `-c, --currency <CURRENCY>` | Base currency for price quotes [default: USD] |
| `-d, --date <DATE>` | Date for prices (YYYY-MM-DD, defaults to today) |
| `-b, --beancount` | Output as beancount price directives |
| `-s, --source <SOURCE>` | Use specific source (overrides mapping) |
| `--source-cmd <CMD>` | Use ad-hoc external command as source |
| `-m, --mapping <MAPPING>` | Symbol mapping (e.g., `VTI:VTI,BTC:BTC-USD`) |
| `--inactive` | Include commodities not currently held (matches `bean-price --inactive`). Requires `-f`. |
| `--undeclared` | Also discover ticker-shaped commodities lacking `price:`/`quote_currency:` metadata. Approximate analogue of `bean-price --undeclared` (see note below). Requires `-f`. |
| `--list-sources` | List configured sources and exit |
| `--no-cache` | Disable the price cache for this run |
| `--clear-cache` | Clear the price cache before fetching |
| `-v, --verbose` | Show verbose output |

## Discovering Symbols from a Ledger

`-f / --file` extracts the list of commodities to fetch from a beancount file, so you don't have to maintain a separate symbol list. The default matches `bean-price`'s strict semantics: only commodities you've explicitly tagged with `price:` or `quote_currency:` metadata are discovered, and only if you currently hold them. The matching logic is verified against upstream `beanprice/price.py::find_currencies_declared`.

### 1. `price:` metadata on `commodity` directives

Annotate a commodity with how to fetch its price. The format is `<quote-currency>:<source>/<ticker>`, optionally chained with `,` for fallback:

```beancount
2024-01-01 commodity AAPL
  price: "USD:yahoo/AAPL"

2024-01-01 commodity Vanguard_VTI
  price: "USD:yahoo/VTI,USD:google/NYSEARCA:VTI"

2024-01-01 commodity AUD
  price: "EUR:ecb/AUD-EUR"
```

The first source in the chain is tried first; subsequent ones act as fallbacks. **Each spec carries its own ticker** — so `EUR:ecbrates/GBP-EUR,EUR:ecb/GBP` queries `ecbrates` with ticker `GBP-EUR` and, on failure, queries `ecb` with ticker `GBP`. (Issue #963: prior to this fix, all sources reused the first spec's ticker, which broke chains where sources expect different ticker shapes for the same underlying.)

The quote currency in the metadata overrides the global `--currency` for that one symbol, so you can mix USD-quoted stocks and EUR-quoted bonds in the same run.

`price: ""` (empty string, or whitespace-only) is an explicit **opt-out from `-f / --file` discovery**: the commodity is never picked up from the ledger, even with `--undeclared`. Useful for currency codes that happen to collide with stock tickers (e.g. `BAM`, `UKW`) — see issue #962. Note: a symbol passed *explicitly* on the command line (e.g. `rledger price BAM`) is always fetched regardless of the opt-out, since CLI args are explicit user intent.

### 2. `quote_currency:` metadata

If you don't use `price:` but want a per-commodity quote currency:

```beancount
2024-01-01 commodity GOVT_EU
  quote_currency: "EUR"
```

This sets the quote currency for `GOVT_EU` only, falling back to `--currency` for everything else. The presence of `quote_currency:` alone is enough to opt the commodity into discovery; the source comes from `[price.default_source]` or `--source`.

### 3. Active-only filtering

By default, only commodities you currently **hold** are fetched. A commodity is considered active if at least one open *balance-sheet* account (Assets or Liabilities, using the configured `name_assets` / `name_liabilities` options for non-English ledgers) ends with a non-zero balance in that currency. Equity, Income, and Expenses accounts are excluded from the check; including them would mark every commodity that ever moved through `Equity:Opening-Balances` as active even after the position was fully closed. Closed accounts (those with a `close` directive) are also excluded.

Pass `--inactive` to disable the filter and fetch prices for every declared commodity, regardless of current balance.

### 4. Discovering commodities without metadata (`--undeclared`)

If you have a ledger without `price:` annotations and want rustledger to guess based on commodity name, pass `--undeclared`. This re-enables a name heuristic: ticker-shaped names (uppercase letters, digits, dashes, dots; ≤ 10 chars) are picked up using the configured `[price.default_source]`.

> **Divergence note**: This is *not* a 1:1 match for `bean-price --undeclared`. The Python flag walks **transactions** and unions the at-cost, converted, and priced currencies — with no name filter. Our `--undeclared` walks `commodity` directives and applies a ticker-shape filter, deliberately keeping currency codes like `EUR` or `BAM` out of stock sources by default. Closer alignment with bean-price's transaction-walking semantics is tracked as a follow-up.

```bash
# Default: strict — only commodities with price:/quote_currency: metadata
# that you currently hold
rledger price -f main.beancount

# Include declared-but-unheld commodities
rledger price -f main.beancount --inactive

# Discover ticker-shaped commodities even without metadata
rledger price -f main.beancount --undeclared

# Legacy "fetch everything that looks fetchable" (pre-strict-default behavior)
rledger price -f main.beancount --inactive --undeclared
```

### Precedence for source/ticker resolution

When multiple configurations apply to the same symbol, the order from highest to lowest precedence is:

1. CLI `--mapping` (per-symbol overrides on the command line)
2. CLI `--source` (forces source for every symbol in the run)
3. `price:` metadata on the commodity directive
4. Config-file `[price.mapping]` entries
5. Default source from `[price.default_source]` (or `yahoo`)

### Quote currency resolution

The currency a price is quoted in is resolved separately, since a single source mapping can be queried in different currencies. From highest to lowest precedence:

1. `quote_currency:` metadata on the commodity directive (or the first quote currency listed in a chained `price:` value)
2. `quote_currency = "..."` in the `[price.mapping.X]` config-file block
3. The global `--currency` flag (or its default, `USD`)

Note that `[price.mapping.X]` blocks reject unknown keys: a typo like `currency = "EUR"` (vs the supported `quote_currency`) will fail config load with a clear error rather than being silently dropped.

## Price Caching

Prices are cached to disk to reduce API calls. By default, cached prices expire after **30 minutes** (matching Python `bean-price` behavior).

- **Latest prices** (no `--date`) expire after the configured TTL
- **Historical prices** (with `--date`) don't expire via TTL, but are pruned after 7 days of inactivity
- Cache file location: platform cache directory (e.g., `~/.cache/rledger/prices.json` on Linux)

### Configuration

```toml
[price]
cache_ttl = 1800  # 30 minutes (default)
# cache_ttl = 0   # disable caching
```

### Cache Control

```bash
# Skip cache for this run (always fetch fresh)
rledger price AAPL --no-cache

# Clear all cached prices, then fetch fresh
rledger price AAPL --clear-cache

# Clear cache without fetching
rledger price --clear-cache
```

## Price Sources

Rustledger supports 11 built-in price sources and external commands.

### Built-in Sources (No API Key)

| Source | Description |
|--------|-------------|
| `yahoo` (default) | Yahoo Finance — stocks, ETFs, crypto, forex |
| `coinbase` | Coinbase — cryptocurrency spot prices |
| `coincap` | CoinCap — cryptocurrency market data |
| `ecb` | European Central Bank — EUR exchange rates |
| `ratesapi` | Rates API — forex rates |
| `tsp` | US Thrift Savings Plan fund prices |
| `eastmoneyfund` | East Money Fund — Chinese fund prices |

### Built-in Sources (API Key Required)

| Source | Environment Variable |
|--------|---------------------|
| `oanda` | `OANDA_API_KEY` |
| `alphavantage` | `ALPHAVANTAGE_API_KEY` |
| `coinmarketcap` | `CMC_API_KEY` |
| `quandl` | `QUANDL_API_KEY` |

### Using a Specific Source

```bash
# Fetch from Coinbase instead of default (Yahoo)
rledger price BTC -s coinbase

# List all available sources
rledger price --list-sources
```

### External Command Source

Use any external script or program as a price source:

```bash
rledger price AAPL --source-cmd "my-price-fetcher"
```

The command receives the ticker as the first argument, plus `--currency <CURRENCY>` and (when provided) `--date <YYYY-MM-DD>` flags. It should output in one of:

- Simple format: `150.00 USD`
- Beancount format: `2024-01-15 price AAPL 150.00 USD`
- JSON format: `{"price": "150.00", "currency": "USD"}`

### Source Configuration

Configure sources, mappings, and fallback chains in config:

```toml
[price]
default_source = "yahoo"
timeout = 30
cache_ttl = 1800

[price.mapping]
# Simple ticker mapping
BTC = "BTC-USD"

# Source-specific mapping
[price.mapping.ETH]
source = "coinbase"
ticker = "ETH"

# Per-commodity quote currency override (issue #952)
[price.mapping.AUD]
source = "ecb"
quote_currency = "EUR"  # quote AUD in EUR even when --currency is USD

# Fallback chain (bare source names — all use the parent ticker)
[price.mapping.VTI]
source = ["yahoo", "alphavantage"]

# Fallback chain with per-source tickers (issue #963).
# Use this when sources expect different ticker shapes for the same
# underlying instrument — e.g. ratesapi-style `GBP-EUR` vs ecb-style `GBP`.
[price.mapping.GBP]
source = [
  { source = "ecbrates", ticker = "GBP-EUR" },
  { source = "ecb", ticker = "GBP" },
]
quote_currency = "EUR"

# Custom external command source
[price.sources.mybank]
type = "command"
command = ["python3", "/path/to/mybank-prices.py"]
```

## Examples

### Fetch Single Price

```bash
rledger price AAPL
```

### Historical Price

```bash
rledger price AAPL -d 2024-01-15
```

### Different Currency

```bash
rledger price EUR -c USD
```

### Cryptocurrency

```bash
rledger price BTC -s coinbase
# or with Yahoo mapping
rledger price BTC -m "BTC:BTC-USD"
```

### All Commodities from Ledger

```bash
rledger price -f ledger.beancount -b
```

### Append to Price File

```bash
rledger price -f ledger.beancount -b >> prices.beancount
```

### Daily Price Update Script

```bash
#!/bin/bash
rledger price -f ledger.beancount -b >> prices.beancount
```

Run with cron:

```cron
0 18 * * 1-5 /path/to/update-prices.sh
```

## See Also

- [Common Queries](../guides/common-queries.md) - Querying prices
