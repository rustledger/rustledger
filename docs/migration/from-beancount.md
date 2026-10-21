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

1. **Decimal precision**: both keep 28 significant digits. Python beancount's `decimal` context has `prec = 28`, and rustledger's `Decimal` holds 28–29. So an amount, a running balance or a merged lot is exact to 28 significant digits in both, and the last digit rounds the same way. For example, a lot of `1e20` units merged with `1e-15` units on the same date keeps `1e20`, a relative difference below 1e-28.
   The difference is **magnitude**: Python's context reaches about 1e999999, while `Decimal` tops out near 7.9e28. Where a result can't be represented, rustledger escalates to exact arithmetic or reports an overflow error. It never stores a clamped number.
   A per-unit cost or price derived from a total (a total cost, a compound cost, a total price `@@`) is divided as Python divides it, so it has the same digits and scale: 10 USD over 4 units is `2.5`, over 3 units `3.333333333333333333333333333`. Two shapes can't be held by `Decimal`, which has at most 28 decimal places and no exponent. A quotient Python writes below `1e-28` (any inexact one under 0.1, like 1/11) is rounded to 28 places, so it has fewer digits than Python's (one fewer for 1/11). And Python's exponent form (`2E+1` for 10 over 0.5 units) is written plainly (`20`), the same value.
   A per-unit rounded to 28 places still books: the lot keeps its exact total beside it, and the total is what weighs the posting and its sales. So a total cost of 1 USD over 30000000000 units balances against `-1 USD` exactly, where bean-check reports `(-1E-28 USD)` from its own per-unit times the units. A per-unit below `1e-28`, which `Decimal` can't hold at all, is refused with a `BOOK` error that says so.

1. **Error messages**: Format differs but contains same information.

1. **Plugin loading**: Python plugins require WASM compilation.

1. **Repeated same-day lots** (no longer a difference since v0.23.0):
   buying the same holding more than once on one day at the same cost and
   label creates **one** lot in both engines, as Python beancount always
   has. Earlier rustledger releases kept one lot per purchase. When a lot at
   another cost was bought between two such purchases, FIFO and LIFO then
   consumed the lots in a different order from Python, so cost basis and
   realized gains could differ, or a later reduction naming an explicit cost
   could fail on one engine only. If you compared figures with an older
   release and saw that kind of difference on a holding bought several times
   in one day, upgrade. Use distinct labels (`{10.00 USD, "morning"}`) to
   keep same-day purchases apart. Fixed in
   [#2118](https://github.com/rustledger/rustledger/issues/2118).

1. **Adding to one side of a long-and-short holding**: if an account holds a
   commodity both long and short, a posting whose cost names a lot of its
   own sign adds to that side as a new lot, dated the transaction date.
   Holding `-2 X {101 USD}` and `5 X {102 USD}`, buying `3 X {102 USD}` gives
   a separate `3 X {102 USD}` lot. Python beancount's lot matching ignores
   sign, so it merges those units into the existing 102 lot, which gives them
   that lot's older acquisition date, and it rejects the same posting (`Not
   enough lots to reduce`) when the quantity is larger than that lot. Units
   and cost basis agree; the lot date, and whether the ledger is accepted,
   can differ. A cost that matches no lot on either side is rejected by
   both, as is a posting that names only a lot date or label. Tracked in
   [#2384](https://github.com/rustledger/rustledger/issues/2384).

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

Many Python plugins have native Rust equivalents. When a plugin name matches a built-in, the declaration is **unchanged** — it resolves to the native Rust implementation:

```beancount
; Before (Python) and after (rustledger) — identical.
; Resolves to the native `auto_accounts`, not Python.
plugin "beancount.plugins.auto_accounts"
```

### Custom Python Plugins: Reference by File Path

beancount's **module-name** plugin syntax does **not** carry over for custom plugins (those without a native equivalent). rustledger does not search the system Python path, so a bare module name is rejected — reference the file directly instead:

```beancount
; ❌ Not supported for a custom plugin
plugin "mypackage.mymodule"

; ✅ Reference the .py file (absolute, or relative to the ledger)
plugin "/abs/path/to/mymodule.py"
```

The plugin also runs in a sandbox that cannot see your virtualenv, so it must be **self-contained** (standard library plus the bundled beancount compat shim). See [Referencing a Python Plugin](../reference/plugins.md#referencing-a-python-plugin) for the full model.

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
