# Beancount Compatibility Report

This document describes the compatibility between rustledger and Python beancount, based on testing 792 real-world beancount files from multiple sources.

## Summary

| Metric | Value |
|--------|-------|
| Files tested | 792 |
| Check exit match | **100%** |
| BQL query data match | **100%** |
| Full-AST match | **100%** |

## Test Sources

Files were collected from:

- beancount v2/v3 official repositories
- beancount-parser-lima test suite
- fava web interface fixtures
- beangulp importer framework
- ledger2beancount converter tests
- beancount-import test data
- Community plugin repositories

## Compatibility Status

With 100% check compatibility on 792 files, rustledger matches Python beancount's validation behavior on the tested corpus. The test suite includes files from:

- Official beancount v2/v3 repositories
- Parser conformance tests
- Real-world example ledgers
- Edge cases and error scenarios

Files with expected Python-only errors (plugin configuration, deprecated options) were excluded from the test set as they test Python-specific features.

## Known Differences

### 1. Multi-Currency Transactions

Python beancount allows transactions with multiple currencies without explicit conversion prices. Rustledger requires either:

- A price (`@` or `@@`) annotation
- All postings in the same currency
- Explicit balancing

**Workaround**: Add `@ 1.0 USD` or appropriate price to multi-currency transactions.

### 2. Python Plugin Loading

Rustledger does not execute Python plugins. Files using `plugin "some_python_plugin"` will:

- Parse successfully
- Report error E8001 "Plugin not found" for unknown plugins
- This matches Python beancount's behavior of failing on missing plugins

Rustledger supports 30 native plugins that match Python beancount behavior:

- `auto_accounts`, `auto_tag`, `box_accrual`, `gain_loss`
- `long_short`, `check_average_cost`, `check_closing`, `check_commodity`
- `check_drained`, `close_tree`, `coherent_cost`, `commodity_attr`
- `currency_accounts`, `effective_date`, `forecast`, `generate_base_ccy_prices`
- `implicit_prices`, `leafonly`, `noduplicates`, `nounused`
- `onecommodity`, `pedantic`, `rename_accounts`, `rx_txn_plugin`
- `sellgains`, `split_expenses`, `unique_prices`, `unrealized`
- `valuation`, `zerosum`

Additionally, `document_discovery` auto-discovers documents from `option "documents"` directories.

**Workaround**: Use rustledger's native plugins where available, or remove unsupported plugin directives.

### 3. Push/Pop Meta and Tag Validation

Python beancount validates that `pushtag`/`poptag` and `pushmeta`/`popmeta` directives are balanced. Rustledger's validation is less strict in some edge cases.

### 4. Deprecated Options

Python beancount reports errors for deprecated options like `plugin_processing_mode`. Rustledger ignores unknown options.

### 5. BQL Display Precision

Python's bean-query uses a "display context" that infers typical decimal precision for each currency based on the amounts seen in a file. When most amounts are integers, Python truncates decimal display:

```
# File contains: 111.11 USD
Python bean-query shows: 111 USD
Rustledger shows:        111.11 USD
```

This is a display-only difference - actual values are identical. Rustledger preserves the original precision, which is technically more accurate.

## BQL Query Compatibility

BQL (Beancount Query Language) compatibility was tested with 11 standard queries on 50 files:

| Query | Description |
|-------|-------------|
| `SELECT DISTINCT account ORDER BY account LIMIT 20` | List accounts |
| `SELECT COUNT(*) AS total` | Count postings |
| `SELECT currency, COUNT(*) GROUP BY currency` | Currency breakdown |
| `SELECT YEAR(date), COUNT(*) GROUP BY year` | Annual counts |
| `SELECT DISTINCT ROOT(account)` | Account roots |
| `SELECT DISTINCT LEAF(account)` | Account leaves |
| `SELECT account, SUM(position) GROUP BY account` | Balance summary |
| `SELECT MONTH(date), COUNT(*) GROUP BY month` | Monthly counts |
| `SELECT date, narration ORDER BY date LIMIT 10` | Transactions |
| `SELECT account, FIRST(date) GROUP BY account` | First dates |
| `SELECT MIN(date), MAX(date)` | Date range |

**Results: 100% data match**

The only remaining differences are display-only:

- Python's bean-query uses a "display context" that truncates decimals (e.g., shows `111 USD` for `111.11 USD`)
- Rustledger shows the actual precision (e.g., `111.11 USD`)

These do not affect the underlying values.

## Running Compatibility Tests

```bash
# Inside nix develop shell:

# Download the full test suite first
./scripts/fetch-compat-test-files.sh   # Populates tests/compatibility/files

# Run BQL comparison (bean-query vs rledger)
python scripts/compat-bql-test.py
```

## Directory Structure

```
tests/compatibility/                    # Compatibility test suite
├── README.md                    # Test documentation
├── sources.toml                 # Source documentation and licenses
├── exclusions.toml              # Files excluded from the metric
├── bql-queries.toml             # BQL queries run by compat-bql-test.py
└── files/                       # beancount files (mostly gitignored, downloaded)
```

## Scripts

- `scripts/fetch-compat-test-files.sh` - Downloads full test suite from GitHub
- `scripts/compat-bql-test.py` - BQL query comparison (bean-query vs rledger)

## Improving Compatibility

If you encounter a file that works with Python beancount but not rustledger:

1. Check if it uses Python plugins (expected to fail)
1. Check for multi-currency transactions without prices
1. File an issue at https://github.com/rustledger/rustledger/issues

______________________________________________________________________

*Generated: February 2026*
*Test environment: Beancount 3.2.0, beanquery 0.2.0, rustledger 0.15.0*
