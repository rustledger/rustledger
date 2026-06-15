______________________________________________________________________

## title: Migrating from Python Beancount description: Switch from Python beancount to rustledger

# Migrating from Python Beancount

rustledger is designed as a drop-in replacement for Python beancount with 10-30x better performance.

## Quick Start

Your existing beancount files work as-is:

```bash
# Validate with rustledger
rledger check ledger.beancount

# Run queries
rledger query ledger.beancount "SELECT account, sum(position) GROUP BY account"
```

## Compatibility

### Fully Compatible

- All beancount syntax
- All directive types (transaction, balance, open, close, etc.)
- All booking methods (FIFO, LIFO, STRICT, etc.)
- BQL query language
- Include directives
- Options
- Metadata

### Plugin Compatibility

| Plugin | Status | Notes |
|--------|--------|-------|
| `auto_accounts` | ✅ Native | Faster implementation |
| `implicit_prices` | ✅ Native | Faster implementation |
| `check_commodity` | ✅ Native | |
| `coherent_cost` | ✅ Native | |
| `leafonly` | ✅ Native | |
| `noduplicates` | ✅ Native | |
| `onecommodity` | ✅ Native | |
| `sellgains` | ✅ Native | |
| `unique_prices` | ✅ Native | |
| Custom Python plugins | ⚠️ WASM | Requires compilation |

See [Plugins Reference](../reference/plugins.md) for full list.

### Known Differences

1. **Decimal precision**: rustledger uses 28-digit precision vs Python's arbitrary precision. This only affects extreme edge cases (28+ decimal places).

1. **Error messages**: Format differs but contains same information.

1. **Plugin loading**: Python plugins require WASM compilation.

## Migration Steps

### 1. Install rustledger

```bash
cargo install rustledger
```

### 2. Validate Your Ledger

```bash
rledger check ledger.beancount
```

Compare output with Python beancount:

```bash
bean-check ledger.beancount
```

### 3. Test Reports

```bash
# Balance report
rledger report ledger.beancount balances

# Compare with
bean-report ledger.beancount balances
```

### 4. Test Queries

```bash
rledger query ledger.beancount "SELECT account, sum(position) GROUP BY account"
```

### 5. Update Your Workflow

Replace beancount commands:

| Python Beancount | rustledger |
|------------------|------------|
| `bean-check` | `rledger check` |
| `bean-query` | `rledger query` |
| `bean-report` | `rledger report` |
| `bean-format` | `rledger format` |
| `bean-price` | `rledger price` |
| `bean-extract` | `rledger extract` |

Or install wrapper scripts so existing scripts work without changes:

```bash
rledger compat install
```

### 6. Update Editor

If using VS Code or other editors with Python beancount LSP, switch to rustledger LSP for better performance.

## Plugin Migration

### Python Plugins to WASM

For custom Python plugins, you have options:

1. **Rewrite in Rust**: Add to `rustledger-plugin/src/native/`
1. **Compile to WASM**: Use [py2wasm](https://pywasm.org) (experimental)
1. **Use pre/post hooks**: For simple transformations

### Check Plugin Equivalents

Many Python plugins have native Rust equivalents:

```beancount
; Before (Python)
plugin "beancount.plugins.auto_accounts"

; After (rustledger) - same syntax, native implementation
plugin "beancount.plugins.auto_accounts"
```

## Performance Comparison

Typical speedups on real ledgers:

| Ledger Size | Python | rustledger | Speedup |
|-------------|--------|------------|---------|
| 1,000 txns | 2.5s | 0.1s | 25x |
| 10,000 txns | 8s | 0.3s | 27x |
| 50,000 txns | 35s | 1.2s | 29x |

## Troubleshooting

### "Unknown plugin" Error

The plugin may not be implemented yet. Check [Plugins Reference](../reference/plugins.md) or open an issue.

### Different Balance

Check for precision differences:

```bash
# Python
bean-query ledger.beancount "SELECT sum(position) WHERE account ~ 'Assets'"

# rustledger
rledger query ledger.beancount "SELECT sum(position) WHERE account ~ 'Assets'"
```

If amounts differ by tiny fractions (e.g., 1e-20), it's a precision difference and can be ignored.

### Query Syntax Differences

BQL is compatible, but check:

- Date literals: Use `2024-01-15` not `"2024-01-15"`
- Regex: Use `account ~ "pattern"` for regex matching

## See Also

- [Installation](../getting-started/installation.md) - Install rustledger
- [Commands](../commands/index.md) - Command reference
- [Plugins](../reference/plugins.md) - Plugin compatibility
