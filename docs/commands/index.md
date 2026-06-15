______________________________________________________________________

## title: Commands Reference description: Complete CLI reference for rustledger

# Commands Reference

rustledger provides several commands for working with beancount ledgers.

## Commands

| Command | Description |
|---------|-------------|
| [check](check.md) | Validate ledger files |
| [query](query.md) | Run BQL queries |
| [report](report.md) | Generate financial reports |
| [format](format.md) | Auto-format beancount files |
| [extract](extract.md) | Import from bank statements |
| [price](price.md) | Fetch commodity prices |
| [doctor](doctor.md) | Debugging and diagnostic tools |
| [config](config.md) | Manage configuration |
| [add](add.md) | Add transactions to beancount files |
| compat | Install or uninstall bean-* compatibility wrapper scripts |
| lint | Non-fatal advisory passes (e.g. detect inter-account transfer pairs) |
| completions | Generate shell completions |

## Global Options

These options work with all commands:

```
-P, --profile <PROFILE>  Use a specific profile from config
-h, --help               Print help information
-V, --version            Print version information
```

## Specifying the Ledger File

Most commands require a beancount file:

```bash
# Explicit file path
rledger check ledger.beancount

# Use RLEDGER_FILE environment variable
export RLEDGER_FILE="~/finances/main.beancount"
rledger check

# Use profile from config
rledger check -P personal
```

## Exit Codes

| Code | Meaning |
|------|---------|
| 0 | Success |
| 1 | Error (validation errors, file not found, etc.) |
| 2 | Invalid usage (bad arguments) |

## Bean-\* Aliases

For compatibility with Python beancount, rustledger can install wrapper scripts:

```bash
rledger compat install          # installs to same directory as rledger
rledger compat install --prefix ~/bin  # or a custom directory
rledger compat uninstall        # removes them
```

| Wrapper | Equivalent |
|---------|------------|
| `bean-check` | `rledger check` |
| `bean-query` | `rledger query` |
| `bean-format` | `rledger format` |
| `bean-report` | `rledger report` |
| `bean-doctor` | `rledger doctor` |
| `bean-extract` | `rledger extract` |
| `bean-price` | `rledger price` |
