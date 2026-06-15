______________________________________________________________________

## title: rustledger Documentation description: A blazing-fast Rust implementation of Beancount

# rustledger Documentation

Welcome to rustledger, a high-performance Rust implementation of [Beancount](https://beancount.github.io/) double-entry bookkeeping.

## Why rustledger?

- **10-30x faster** than Python beancount
- **Drop-in replacement** - your existing beancount files work unchanged
- **No dependencies** - single binary, no Python runtime needed
- **Full BQL support** - 100% query language compatibility
- **LSP support** - IDE integration for VS Code, Neovim, Helix
- **31 built-in plugins** - plus Python plugin compatibility

## Quick Start

```bash
# Install
brew install rustledger  # macOS/Linux
scoop install rustledger # Windows

# Validate your ledger
rledger check ledger.beancount

# Run a query
rledger query ledger.beancount "SELECT account, sum(position) GROUP BY account"

# Generate reports
rledger report ledger.beancount balances
```

## Documentation Sections

### [Getting Started](getting-started/index.md)

Installation, configuration, and your first steps with rustledger.

### [Commands](commands/index.md)

Complete CLI reference for all rustledger commands.

### [Guides](guides/index.md)

Practical guides for common workflows and advanced usage.

### [Migration](migration/index.md)

Moving to rustledger from Python beancount, ledger-cli, or hledger.

### [Reference](reference/index.md)

BQL query language, plugins, error codes, and options.

### [Development](development/index.md)

Contributing to rustledger - testing, benchmarking, and roadmaps.

## Getting Help

- [GitHub Issues](https://github.com/rustledger/rustledger/issues) - Bug reports
- [GitHub Discussions](https://github.com/rustledger/rustledger/discussions) - Questions & ideas
- `rledger --help` - Built-in CLI help
