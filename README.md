<div align="center">

# rustledger

**A blazing-fast Rust implementation of [Beancount](https://beancount.github.io/)**

Parse and validate your ledger faster than Python beancount.

[![CI](https://github.com/rustledger/rustledger/actions/workflows/ci.yml/badge.svg)](https://github.com/rustledger/rustledger/actions/workflows/ci.yml)
[![Compatibility](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/rustledger/rustledger/compatibility/.github/badges/compat-badge.json)](https://github.com/rustledger/rustledger/actions/workflows/compat.yml)
[![docs.rs](https://img.shields.io/docsrs/rustledger-core)](https://docs.rs/rustledger-core)
[![GitHub Release](https://img.shields.io/github/v/release/rustledger/rustledger)](https://github.com/rustledger/rustledger/releases)
[![License: GPL v3](https://img.shields.io/badge/License-GPLv3-blue.svg)](LICENSE)
[![Liberapay](https://img.shields.io/liberapay/gives/rustledger.svg?logo=liberapay)](https://liberapay.com/rustledger)

</div>

---

## Why rustledger?

| | |
|---|---|
| **10-30x faster** | Parse and validate large ledgers in milliseconds ([see benchmarks](#performance)) |
| **No dependencies** | No Python runtime, no libraries to install |
| **Drop-in replacement** | Compatible `bean-*` CLI commands for easy migration |
| **Full compatibility** | Parses any valid beancount file |
| **Editor support** | LSP server for VS Code, Neovim, Helix, and more |
| **AI-ready** | MCP server for Claude, Cursor, and other AI assistants |
| **Runs anywhere** | WebAssembly support for browser and Node.js |
| **Better errors** | Detailed error messages with source locations |
| **20 built-in plugins** | Plus Python plugin compatibility via WASI sandbox |

<details>
<summary><strong>Comparison with other tools</strong></summary>

| Feature | rustledger | Python beancount | hledger | ledger-cli |
|---------|------------|------------------|---------|------------|
| **Language** | Rust | Python | Haskell | C++ |
| **Speed** | Very fast | Slow | Fast | Fast |
| **Beancount syntax** | Native | Native | Via conversion | No |
| **Query language** | BQL (100% compat) | BQL | Custom | Custom |
| **LSP server** | Built-in | No | Via plugin | No |
| **WASM support** | Yes | No | Partial | No |
| **Plugin system** | Native + Python | Python | Haskell | Custom |
| **Active development** | Yes | Maintenance | Yes | Limited |

**When to use rustledger:**
- You use Beancount syntax and want speed
- You want a single binary with no runtime dependencies
- You need LSP editor integration
- You want to use existing Python plugins

**When to use Python beancount:**
- You need Fava web interface (until rustledger integration)
- You have complex Python plugins with C extensions

**When to use hledger:**
- You prefer hledger's syntax and reports
- You need time-tracking features

</details>

## Install

| Platform | Command |
|----------|---------|
| **macOS** | `brew install rustledger/rustledger/rustledger` |
| **Arch Linux** | `yay -S rustledger-bin` or `yay -S rustledger` (from source) |
| **Windows** | `scoop bucket add rustledger https://github.com/rustledger/scoop-rustledger && scoop install rustledger` |
| **Cargo** | `cargo binstall rustledger` or `cargo install rustledger` |
| **Fedora/RHEL** | `sudo dnf copr enable robcohen/rustledger && sudo dnf install rustledger` |
| **Nix** | `nix run github:rustledger/rustledger` |
| **Docker** | `docker run --rm -v "$PWD:/data" ghcr.io/rustledger/rustledger /data/ledger.beancount` |
| **Binaries** | [GitHub Releases](https://github.com/rustledger/rustledger/releases) |
| **npm (WASM)** | `npm install @rustledger/wasm` |
| **npm (MCP)** | `npx @rustledger/mcp-server` ([Model Context Protocol](https://modelcontextprotocol.io) server) |

<sub>Missing your platform? [Open an issue](https://github.com/rustledger/rustledger/issues/new) to request it.</sub>

**Coming from Python beancount?** See the [Migration Guide](docs/MIGRATION.md) for command equivalents and plugin mapping.

## Quick Start

```bash
rledger check ledger.beancount
rledger query ledger.beancount "SELECT account, SUM(position) GROUP BY account"
```

## CLI Commands

| Command | Description |
|---------|-------------|
| `rledger check` | Validate ledger files with detailed error messages |
| `rledger query` | Run BQL queries (interactive shell or one-shot) |
| `rledger format` | Auto-format beancount files |
| `rledger report` | Generate balance, account, and statistics reports |
| `rledger doctor` | Debugging tools for ledger issues |
| `rledger extract` | Import transactions from CSV/OFX bank statements |
| `rledger price` | Fetch commodity prices from online sources |
| `rledger-lsp` | Language Server Protocol for editor integration |

Python beancount users can also use `bean-check`, `bean-query`, etc.

<details>
<summary><strong>Report subcommands</strong></summary>

| Subcommand | Alias | Description |
|------------|-------|-------------|
| `balances` | | All account balances |
| `balsheet` | `bal` | Balance sheet report |
| `income` | `is` | Income statement |
| `journal` | `register` | Transaction register |
| `holdings` | | Investment holdings |
| `networth` | | Net worth over time |
| `accounts` | | List all accounts |
| `commodities` | | List all commodities |
| `prices` | | Price entries |
| `stats` | | Ledger statistics |

</details>

<details>
<summary><strong>Doctor subcommands</strong></summary>

Debugging and diagnostic tools:

| Subcommand | Description |
|------------|-------------|
| `lex` | Dump lexer tokens (alias: `dump-lexer`) |
| `parse` | Parse and show directives |
| `context` | Show transaction context at a line number |
| `linked` | Find transactions by link (`^link`) or tag (`#tag`) |
| `missing-open` | Generate missing Open directives |
| `list-options` | List all available beancount options |
| `print-options` | Print options parsed from a file |
| `stats` | Display ledger statistics |
| `display-context` | Show inferred decimal precision context |
| `roundtrip` | Round-trip parse/format test |
| `directories` | Validate directory hierarchy against accounts |
| `region` | Print transactions in a line range with balances |
| `generate-synthetic` | Generate synthetic test files |

```bash
# Debug a parsing issue at line 42
rledger doctor context ledger.beancount 42

# Find all transactions with a link
rledger doctor linked ledger.beancount ^trip-2024

# Generate Open directives for accounts missing them
rledger doctor missing-open ledger.beancount >> ledger.beancount
```

</details>

<sub>Run `rledger <command> --help` for all options.</sub>

<details>
<summary><strong>CLI examples</strong></summary>

```bash
# Validate with plugins
rledger check --native-plugin auto_accounts ledger.beancount

# Interactive query shell
rledger query ledger.beancount

# One-shot query
rledger query ledger.beancount "SELECT date, narration WHERE account ~ 'Expenses:Food'"

# Reports
rledger report ledger.beancount balances
rledger report ledger.beancount stats

# Format in place
rledger format --in-place ledger.beancount
```

</details>

## Crates

| Crate | Description |
|-------|-------------|
| `rustledger` | CLI tool (`rledger check`, `rledger query`, etc.) |
| `rustledger-core` | Core types: Amount, Position, Inventory |
| `rustledger-parser` | Lexer and parser with error recovery |
| `rustledger-loader` | File loading and includes |
| `rustledger-booking` | Interpolation and 7 booking methods |
| `rustledger-validate` | 27 validation error codes |
| `rustledger-query` | BQL query engine |
| `rustledger-plugin` | 20 built-in plugins + Python plugin support |
| `rustledger-importer` | CSV/OFX import framework |
| `rustledger-lsp` | Language Server Protocol for editor integration |
| `rustledger-wasm` | WebAssembly bindings for JavaScript/TypeScript |

<details>
<summary><strong>Booking methods (7)</strong></summary>

| Method | Description |
|--------|-------------|
| `STRICT` | Lots must match exactly (default) |
| `STRICT_WITH_SIZE` | Exact-size matches accept oldest lot |
| `FIFO` | First in, first out |
| `LIFO` | Last in, first out |
| `HIFO` | Highest cost first |
| `AVERAGE` | Average cost basis |
| `NONE` | No cost tracking |

</details>

<details>
<summary><strong>Built-in plugins (20)</strong></summary>

| Plugin | Description |
|--------|-------------|
| `auto_accounts` | Auto-generate Open directives |
| `auto_tag` | Automatically tag transactions |
| `check_average_cost` | Validate average cost bookings |
| `check_closing` | Zero balance assertion on account close |
| `check_commodity` | Validate commodity declarations |
| `check_drained` | Ensure accounts are drained before close |
| `close_tree` | Close descendant accounts |
| `coherent_cost` | Enforce cost OR price (not both) |
| `commodity_attr` | Validate commodity attributes |
| `currency_accounts` | Enforce currency constraints on accounts |
| `document_discovery` | Auto-discover document files |
| `implicit_prices` | Generate price entries from transaction costs |
| `leafonly` | Error on postings to non-leaf accounts |
| `noduplicates` | Hash-based duplicate transaction detection |
| `nounused` | Warn on unused accounts |
| `onecommodity` | Single commodity per account |
| `pedantic` | Enable all strict validations |
| `sellgains` | Cross-check capital gains against sales |
| `unique_prices` | One price per day per commodity pair |
| `unrealized` | Calculate unrealized gains |

**Python plugins**: Run existing Python beancount plugins via CPython-WASI sandbox.

</details>

<details>
<summary><strong>Python plugin support</strong></summary>

rustledger can execute your existing Python beancount plugins via a secure WebAssembly sandbox:

```bash
# Run with a Python plugin
rledger check --plugin beancount.plugins.auto_accounts ledger.beancount

# Multiple plugins
rledger check --plugin my_plugin --plugin another_plugin ledger.beancount
```

**How it works:**
- Plugins run in a sandboxed CPython interpreter compiled to WebAssembly (WASI)
- No system Python installation required
- Plugins cannot access the filesystem or network (sandbox isolation)
- Compatible with most pure-Python beancount plugins

**Limitations:**
- Plugins with C extensions won't work (numpy, pandas, etc.)
- No network access (price fetching plugins need alternatives)
- First plugin load has ~1s startup overhead

</details>

## Editor Integration

rustledger includes a full-featured Language Server (`rledger-lsp`) for IDE support:

- Real-time diagnostics
- Autocompletion (accounts, currencies, payees)
- Go to definition / find references
- Hover information with account balances
- Rename refactoring
- Document formatting

See [LSP setup guide](crates/rustledger-lsp/README.md) for VS Code, Neovim, Helix, Zed, and Emacs.

## Performance

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="https://raw.githubusercontent.com/rustledger/rustledger/benchmarks/.github/badges/validation-chart.svg">
  <source media="(prefers-color-scheme: light)" srcset="https://raw.githubusercontent.com/rustledger/rustledger/benchmarks/.github/badges/validation-chart.svg">
  <img alt="Validation Benchmark" src="https://raw.githubusercontent.com/rustledger/rustledger/benchmarks/.github/badges/validation-chart.png" width="100%">
</picture>

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="https://raw.githubusercontent.com/rustledger/rustledger/benchmarks/.github/badges/balance-chart.svg">
  <source media="(prefers-color-scheme: light)" srcset="https://raw.githubusercontent.com/rustledger/rustledger/benchmarks/.github/badges/balance-chart.svg">
  <img alt="Balance Report Benchmark" src="https://raw.githubusercontent.com/rustledger/rustledger/benchmarks/.github/badges/balance-chart.png" width="100%">
</picture>

<sub>Benchmarks run nightly on 10K transaction ledgers. [View workflow →](https://github.com/rustledger/rustledger/actions/workflows/bench.yml)</sub>

<details>
<summary><strong>Benchmark details</strong></summary>

**What's measured:**
- **Validation**: Parse ledger + validate (balance assertions, account opens, etc.)
- **Balance Report**: Parse + compute all account balances

**Memory efficiency:**
rustledger typically uses 3-5x less memory than Python beancount thanks to Rust's zero-cost abstractions and efficient data structures.

**Run locally:**
```bash
# Quick comparison (requires nix)
nix develop .#bench
./scripts/bench.sh

# Criterion micro-benchmarks
cargo bench -p rustledger-core
cargo bench -p rustledger-parser
```

See [BENCHMARKING.md](docs/BENCHMARKING.md) for detailed benchmark documentation.

</details>

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for development setup and guidelines.

**Documentation:**
- [Architecture](docs/ARCHITECTURE.md) - Crate structure and data flow
- [BQL Reference](docs/BQL_REFERENCE.md) - Query language guide
- [Importing](docs/IMPORTING.md) - CSV/OFX bank import tutorial
- [Validation errors](docs/VALIDATION_ERRORS.md) - Error code reference
- [API docs](https://docs.rs/rustledger-core) - Rust API documentation

By submitting a pull request, you agree to the [Contributor License Agreement](CLA.md).

## License

[GPL-3.0](LICENSE)

**Commercial licensing available** - [contact us](https://rustledger.github.io/#contact) for proprietary license options.

## Funding

rustledger is free and open source. If you find it useful, consider supporting development:

[![Support on Liberapay](https://img.shields.io/badge/Support%20on-Liberapay-F6C915?logo=liberapay)](https://liberapay.com/rustledger)
