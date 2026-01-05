# rustledger

A pure Rust implementation of [Beancount](https://beancount.github.io/), the double-entry bookkeeping language.

[![Crates.io](https://img.shields.io/crates/v/rustledger.svg)](https://crates.io/crates/rustledger)
[![Documentation](https://docs.rs/rustledger/badge.svg)](https://docs.rs/rustledger)
[![License](https://img.shields.io/crates/l/rustledger.svg)](LICENSE)

## Features

- **Pure Rust** - No Python dependencies, compiles to native and WebAssembly
- **Full Beancount Syntax** - Parses all directive types with error recovery
- **Drop-in Replacement** - Compatible CLI commands for Python beancount users
- **7 Booking Methods** - STRICT, FIFO, LIFO, HIFO, AVERAGE, and more
- **14 Built-in Plugins** - implicit_prices, auto_accounts, pedantic, etc.
- **BQL Query Engine** - SQL-like queries on your ledger
- **Fast** - 10x faster than Python beancount

## Installation

### CLI Tools

```bash
# Install with bean-* compatibility aliases (default)
cargo install rustledger

# Install only rledger-* commands (no bean-* aliases)
cargo install rustledger --no-default-features
```

### As a Library

```bash
cargo add rustledger-core rustledger-parser rustledger-loader
```

## CLI Usage

```bash
# Validate a ledger file
rledger-check ledger.beancount

# Format a ledger file
rledger-format ledger.beancount
rledger-format --in-place ledger.beancount

# Run a BQL query (one-shot or interactive)
rledger-query ledger.beancount "SELECT account, SUM(position) GROUP BY account"
rledger-query ledger.beancount   # Interactive shell with readline/history

# Generate reports
rledger-report ledger.beancount balances
rledger-report ledger.beancount accounts
rledger-report ledger.beancount stats

# Debugging tools
rledger-doctor ledger.beancount context 42        # Show context around line 42
rledger-doctor ledger.beancount linked ^link-name # Find linked transactions
rledger-doctor ledger.beancount missing           # Find missing Open directives
rledger-doctor ledger.beancount stats             # Ledger statistics

# Use plugins
rledger-check --native-plugin auto_accounts ledger.beancount
rledger-check --native-plugin pedantic ledger.beancount
```

### Python Beancount Compatibility

For users migrating from Python beancount, the `bean-*` commands are also available:

```bash
bean-check ledger.beancount
bean-format ledger.beancount
bean-query ledger.beancount "SELECT ..."
bean-report ledger.beancount balances
bean-doctor ledger.beancount context 42
```

## Library Usage

```rust
use rustledger_loader::load;

fn main() -> anyhow::Result<()> {
    let result = load("ledger.beancount")?;

    println!("Loaded {} directives", result.directives.len());

    for error in &result.errors {
        eprintln!("{}", error);
    }

    Ok(())
}
```

## Crates

| Crate | Description |
|-------|-------------|
| [`rustledger-core`](crates/rustledger-core) | Core types: Amount, Position, Inventory, Directives |
| [`rustledger-parser`](crates/rustledger-parser) | Lexer and parser with error recovery |
| [`rustledger-loader`](crates/rustledger-loader) | File loading, includes, options |
| [`rustledger-booking`](crates/rustledger-booking) | Interpolation and booking engine |
| [`rustledger-validate`](crates/rustledger-validate) | 30 validation error codes |
| [`rustledger-query`](crates/rustledger-query) | BQL query engine |
| [`rustledger-plugin`](crates/rustledger-plugin) | Native and WASM plugin system |
| [`rustledger`](crates/rustledger) | Command-line tools |
| [`rustledger-wasm`](crates/rustledger-wasm) | WebAssembly library target |

## Supported Features

### Parser

- All 12 directive types (transaction, balance, open, close, etc.)
- Cost specifications: `{100 USD}`, `{{100 USD}}`, `{100 # 5 USD}`, `{*}`
- Price annotations: `@ 100 USD`, `@@ 1000 USD`
- Arithmetic expressions: `(40.00/3 + 5) USD`
- Multi-line strings: `"""..."""`
- All transaction flags: `* ! P S T C U R M`
- Metadata with 6 value types
- Error recovery (continues parsing after errors)

### Booking Methods

- `STRICT` - Lots must match exactly (with total match exception)
- `STRICT_WITH_SIZE` - Exact-size matches accept oldest lot
- `FIFO` - First in, first out
- `LIFO` - Last in, first out
- `HIFO` - Highest cost first
- `AVERAGE` - Average cost basis
- `NONE` - No cost tracking

### Built-in Plugins

| Plugin | Description |
|--------|-------------|
| `implicit_prices` | Generate price entries from costs |
| `check_commodity` | Validate commodity declarations |
| `auto_accounts` | Auto-generate Open directives |
| `leafonly` | Error on non-leaf postings |
| `noduplicates` | Hash-based duplicate detection |
| `onecommodity` | Single commodity per account |
| `unique_prices` | One price per day per pair |
| `check_closing` | Zero balance assertion on closing |
| `close_tree` | Close descendant accounts |
| `coherent_cost` | Enforce cost OR price consistency |
| `sellgains` | Cross-check gains against sales |
| `pedantic` | Enable all strict validations |
| `unrealized` | Calculate unrealized gains |

### Options (28 supported)

- Account prefixes (`name_assets`, `name_liabilities`, etc.)
- Equity accounts (`account_previous_balances`, etc.)
- Tolerance settings (`inferred_tolerance_default` with wildcards)
- Booking method, documents directories, and more

## Compatibility

rustledger is compatible with Python beancount. It can parse and validate any valid beancount file. The `bean-*` command aliases are included by default for easy migration.

## Performance

Benchmarks show rustledger is approximately 10x faster than Python beancount for parsing and validation.

## License

This project is licensed under the GNU General Public License v3.0 - see the [LICENSE](LICENSE) file for details.

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request.
