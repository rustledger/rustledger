# Beancount Compatibility Report

This document describes the compatibility between rustledger and Python beancount, based on testing 600+ real-world beancount files from multiple sources.

## Summary

| Metric | Value |
|--------|-------|
| Files tested | 609 |
| Check exit match | **100%** (609/609) |
| BQL query data match | **99%** (544/550) |

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

With 100% check compatibility on 609 files, rustledger matches Python beancount's validation behavior exactly on the tested corpus. The test suite includes files from:

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

Rustledger supports 20 native plugins that match Python beancount behavior:
- `auto_accounts`, `auto_tag`, `check_closing`, `check_commodity`
- `check_drained`, `check_average_cost`, `close_tree`, `coherent_cost`
- `commodity_attr`, `currency_accounts`, `implicit_prices`, `leafonly`
- `noduplicates`, `nounused`, `onecommodity`, `pedantic`
- `sellgains`, `unique_prices`, `unrealized`, `document_discovery`

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

**Results: 99% data match (544/550 queries)**

Breakdown:
- **542 exact matches** - Identical output
- **2 precision differences** - Display precision only (acceptable)
- **6 data differences** - Real calculation bugs (see Known Issues below)

Acceptable differences:
- Python's bean-query uses a "display context" that truncates decimals (e.g., shows `111 USD` for `111.11 USD`)
- Rustledger shows the actual precision (e.g., `111.11 USD`)

### Known BQL Issues

The 6 failing queries involve **capital gains calculation** in cost lot sales:

1. **Missing interpolated capital gains**: When selling lots with `Income:Capital-Gains` as an elided posting, rustledger doesn't compute the gain (sale price - cost basis)

2. **Extra zero positions in inventory**: SUM(position) may show `0.000 CURRENCY` entries that Python filters out

These affect files with options trading and HSA investments that have buy/sell transactions with cost tracking.

## Running Compatibility Tests

```bash
# Inside nix develop shell:

# Quick test with curated files (~100 files, committed)
./scripts/compat-test.sh tests/compat/files

# Full test suite (~800 files, downloaded)
./scripts/fetch-compat-test-files.sh  # Download first
./scripts/compat-test.sh               # Runs on tests/compat-full/

# Run BQL comparison
./scripts/compat-bql-test.sh

# Analyze results
python scripts/analyze-compat-results.py
```

## Directory Structure

```
tests/compat/                    # Curated test suite (committed)
├── README.md                    # Test documentation
├── sources.toml                 # Source documentation and licenses
└── files/                       # ~100 curated beancount files
    ├── parser/                  # Parser edge cases
    ├── validation/              # Validation scenarios
    ├── plugins/                 # Plugin configurations
    ├── real-world/              # Real-world examples
    └── edge-cases/              # Known compatibility differences

tests/compat-full/               # Full test suite (gitignored, downloaded)
├── beancount-v2/                # Official beancount v2 files
├── beancount-v3/                # Official beancount v3 files
├── parser-lima/                 # Parser conformance tests
├── fava/                        # Fava web interface tests
├── beangulp/                    # Importer framework examples
├── ledger2beancount/            # Converter tests
├── beancount-import/            # Import test data
└── community/                   # Community project files

tests/compat-results/            # Test output (gitignored)
```

## Scripts

- `scripts/fetch-compat-test-files.sh` - Downloads full test suite from GitHub
- `scripts/compat-test.sh` - Main test harness (bean-check vs rledger-check)
- `scripts/compat-bql-test.sh` - BQL query comparison
- `scripts/analyze-compat-results.py` - Results analysis and reporting

## Improving Compatibility

If you encounter a file that works with Python beancount but not rustledger:

1. Check if it uses Python plugins (expected to fail)
2. Check for multi-currency transactions without prices
3. File an issue at https://github.com/rustledger/rustledger/issues

---

*Generated: January 2026*
*Test environment: Beancount 3.2.0, beanquery 0.2.0, rustledger 0.5.2*
