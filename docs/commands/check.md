______________________________________________________________________

## title: rledger check description: Validate beancount ledger files

# rledger check

Validate a beancount ledger file for syntax errors and semantic issues.

## Usage

```bash
rledger check [OPTIONS] [FILE]
```

## Arguments

| Argument | Description |
|----------|-------------|
| `FILE` | The beancount file to check (uses `$RLEDGER_FILE` or config if not specified) |

## Options

| Option | Description |
|--------|-------------|
| `-P, --profile <PROFILE>` | Use a profile from config (global flag) |
| `-v, --verbose` | Show verbose output including timing |
| `-q, --quiet` | Suppress all output (just use exit code) |
| `-C, --no-cache` | Disable the binary cache for parsed directives (also: `BEANCOUNT_DISABLE_LOAD_CACHE=1`) |
| `-a, --auto` | Implicitly enable auto-plugins (`auto_accounts`, etc.) |
| `--plugin <WASM_FILE>` | Load a WASM plugin (can be repeated) |
| `--native-plugin <PLUGIN>` | Enable a native plugin (can be repeated) |
| `-f, --format <FORMAT>` | Output format: `text`, `json` |

## Examples

### Basic Validation

```bash
rledger check ledger.beancount
```

Output on success:

```
✓ No errors found
```

Output with errors:

```
error[E3001]: Transaction does not balance
  --> ledger.beancount:42:1
   |
42 | 2024-01-15 * "Coffee shop"
   | ^^^^^^^^^^^^^^^^^^^^^^^^^
   = help: Expenses:Food has 5.00 USD, Assets:Bank has -4.99 USD
   = note: residual: 0.01 USD

✗ 1 error
```

### With Plugins

```bash
# Enable specific plugins
rledger check --native-plugin auto_accounts --native-plugin implicit_prices ledger.beancount

# Plugins declared in the file are auto-detected
# plugin "beancount.plugins.auto_accounts"  <- uses native implementation
```

### JSON Output

```bash
rledger check -f json ledger.beancount
```

```json
{
  "valid": false,
  "errors": [
    {
      "code": "E3001",
      "message": "Transaction does not balance",
      "file": "ledger.beancount",
      "line": 42,
      "help": "Expenses:Food has 5.00 USD, Assets:Bank has -4.99 USD"
    }
  ]
}
```

### Using Environment Variable

```bash
export RLEDGER_FILE="$HOME/finances/main.beancount"
rledger check  # uses $RLEDGER_FILE
```

## Cache File

To make subsequent runs near-instant, `rledger check` writes a binary snapshot of the parsed ledger next to the source file as a hidden dotfile:

```
ledger.beancount         → .ledger.beancount.cache
finances/main.beancount  → finances/.main.beancount.cache
```

The cache is invalidated automatically when any source file (the main ledger or anything it `include`s) changes. Invalidation is based on each file's path, modification time, and size — if any of those differ from when the cache was written, the cache is rejected and the ledger is re-parsed.

### Controlling the cache

| Mechanism | Effect |
|-----------|--------|
| `--no-cache` / `-C` flag | Disable for one invocation |
| `BEANCOUNT_DISABLE_LOAD_CACHE=1` | Disable persistently (env) |
| `BEANCOUNT_LOAD_CACHE_FILENAME=<pattern>` | Redirect to a custom path |

The `BEANCOUNT_LOAD_CACHE_FILENAME` pattern may contain `{filename}` (replaced with the source basename). Relative paths resolve against the source file's directory; absolute paths are used as-is.

```bash
# All caches in ~/.cache/rledger/, named after the source file
export BEANCOUNT_LOAD_CACHE_FILENAME="$HOME/.cache/rledger/{filename}.cache"
```

These environment variable names match Python beancount, so existing `bean-check` muscle memory works unchanged.

### Migration from earlier rustledger versions

Versions before this fix (issue #939) wrote the cache as a visible file (`ledger.beancount.cache`). Upgrading will silently delete the old visible file the first time `rledger check` writes a new cache for that ledger. No action required; if you've added `*.beancount.cache` to `.gitignore` you can safely remove the entry.

## Error Codes

Common validation errors:

| Code | Description |
|------|-------------|
| E1001 | Syntax error |
| E2001 | Account not opened |
| E2002 | Account already opened |
| E3001 | Transaction does not balance |
| E3002 | Invalid balance assertion |

See [Error Reference](../reference/errors.md) for all error codes.

## See Also

- [doctor](doctor.md) - Debugging tools
- [Error Reference](../reference/errors.md) - All error codes
