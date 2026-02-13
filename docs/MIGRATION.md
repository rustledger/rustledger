# Migrating from Python Beancount

This guide helps you transition from Python beancount to rustledger.

## Quick Start

rustledger is a drop-in replacement. Your existing `.beancount` files work without modification:

```bash
# Instead of:
bean-check ledger.beancount
bean-query ledger.beancount "SELECT ..."

# Use:
rledger check ledger.beancount
rledger query ledger.beancount "SELECT ..."

# Or use the bean-* aliases (installed by default):
bean-check ledger.beancount  # → calls rledger check
```

## Command Mapping

| Python beancount | rustledger | Notes |
|-----------------|------------|-------|
| `bean-check` | `rledger check` | Identical behavior |
| `bean-query` | `rledger query` | 100% BQL compatible |
| `bean-format` | `rledger format` | Same formatting rules |
| `bean-doctor` | `rledger doctor` | Most subcommands supported |
| `bean-extract` | `rledger extract` | CSV/OFX import |
| `bean-price` | `rledger price` | Yahoo Finance support |
| `bean-report` | `rledger report` | Different subcommand names |

### Report Command Differences

| Python | rustledger | Description |
|--------|------------|-------------|
| `bean-report balances` | `rledger report balances` | Same |
| `bean-report balsheet` | `rledger report balsheet` | Same (alias: `bal`) |
| `bean-report income` | `rledger report income` | Same (alias: `is`) |
| `bean-report journal` | `rledger report journal` | Same (alias: `register`) |
| `bean-report holdings` | `rledger report holdings` | Same |
| `bean-report networth` | `rledger report networth` | Same |

## Plugin Migration

### Native Plugins (Recommended)

rustledger has 20 built-in plugins that match Python beancount behavior:

```beancount
; Python beancount:
plugin "beancount.plugins.auto_accounts"

; rustledger (use --native-plugin flag):
; rledger check --native-plugin auto_accounts ledger.beancount
```

Or enable via command line:
```bash
rledger check --native-plugin auto_accounts --native-plugin implicit_prices ledger.beancount
```

### Python Plugin Compatibility

rustledger can run your existing Python plugins via a WASM sandbox:

```bash
# Run with Python plugin
rledger check --plugin beancount.plugins.auto_accounts ledger.beancount

# Custom plugin
rledger check --plugin my_custom_plugin ledger.beancount
```

**Limitations:**
- Plugins with C extensions (numpy, pandas) won't work
- No network access from plugins
- ~1s startup overhead for first plugin load

### Plugin Equivalents

| Python Plugin | rustledger Native | Notes |
|--------------|-------------------|-------|
| `beancount.plugins.auto_accounts` | `auto_accounts` | Identical |
| `beancount.plugins.check_commodity` | `check_commodity` | Identical |
| `beancount.plugins.coherent_cost` | `coherent_cost` | Identical |
| `beancount.plugins.implicit_prices` | `implicit_prices` | Identical |
| `beancount.plugins.leafonly` | `leafonly` | Identical |
| `beancount.plugins.noduplicates` | `noduplicates` | Identical |
| `beancount.plugins.nounused` | `nounused` | Identical |
| `beancount.plugins.onecommodity` | `onecommodity` | Identical |
| `beancount.plugins.pedantic` | `pedantic` | Identical |
| `beancount.plugins.sellgains` | `sellgains` | Identical |
| `beancount.plugins.unrealized` | `unrealized` | Identical |

## BQL Query Compatibility

rustledger has **100% BQL compatibility** with Python beancount. All queries work identically:

```sql
-- These all work the same way:
SELECT account, SUM(position) GROUP BY account
SELECT date, narration WHERE account ~ 'Expenses:Food'
BALANCES FROM year = 2024
JOURNAL 'Assets:Bank'
```

### Output Format Differences

rustledger supports additional output formats:

```bash
# Text (default, same as Python)
rledger query ledger.beancount "BALANCES" -f text

# CSV export
rledger query ledger.beancount "BALANCES" -f csv

# JSON export
rledger query ledger.beancount "BALANCES" -f json

# Beancount format (for piping to other tools)
rledger query ledger.beancount "SELECT *" -f beancount
```

## Error Message Differences

rustledger provides more detailed error messages with error codes:

```
# Python beancount:
ledger.beancount:42: Transaction does not balance

# rustledger:
error[E0201]: Transaction does not balance
  --> ledger.beancount:42:1
   |
42 | 2024-01-15 * "Coffee shop"
   | ^^^^^^^^^^^^^^^^^^^^^^^^^
   = help: Expenses:Food has 5.00 USD, Assets:Bank has -4.99 USD
   = note: residual: 0.01 USD
```

See [VALIDATION_ERRORS.md](VALIDATION_ERRORS.md) for all error codes.

## Performance Comparison

Typical speedups on real-world ledgers:

| Operation | Python | rustledger | Speedup |
|-----------|--------|------------|---------|
| Parse 10K transactions | 2.5s | 0.08s | **31x** |
| Validate | 3.2s | 0.15s | **21x** |
| Balance query | 3.5s | 0.20s | **17x** |

Memory usage is typically 3-5x lower.

## Fava Integration

rustledger works with [Fava](https://github.com/beancount/fava) for web-based viewing:

```bash
# Fava still uses Python beancount by default
# rustledger can be used for faster validation alongside:
rledger check ledger.beancount && fava ledger.beancount
```

Full Fava backend integration is planned for a future release.

## Breaking Differences

### Decimal Precision

rustledger uses 28-digit precision (vs Python's arbitrary precision). This only matters for extreme edge cases:

```beancount
; This works in Python but may lose precision in rustledger:
2024-01-01 * "Extreme precision"
  Assets:Bank  0.0000000000000000000000000001 USD
  Equity:Opening
```

**Practical impact:** None for real-world ledgers.

### Unsupported Features

These Python beancount features are not yet supported:

| Feature | Status | Workaround |
|---------|--------|------------|
| `bean-web` | Not planned | Use Fava |
| `bean-bake` | Not planned | Use static site generators |
| Custom importers (Python) | Partial | Use `rledger extract` for CSV/OFX |

## Gradual Migration

You can use both tools during migration:

```bash
# Validate with rustledger (fast feedback)
rledger check ledger.beancount

# Use Python for features not yet in rustledger
bean-web ledger.beancount
```

## Getting Help

- [GitHub Issues](https://github.com/rustledger/rustledger/issues) - Bug reports and feature requests
- [Discussions](https://github.com/rustledger/rustledger/discussions) - Questions and community help
- Run `rledger --help` or `rledger <command> --help` for CLI documentation
