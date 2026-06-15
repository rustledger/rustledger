______________________________________________________________________

## title: Importing Data description: Import transactions from bank statements

# Importing Data

Import transactions from CSV and OFX bank statements into beancount format.

## Quick Start

```bash
# Basic CSV import
rledger extract bank-statement.csv -a Assets:Bank:Checking

# With duplicate detection
rledger extract statement.csv -a Assets:Bank --existing ledger.beancount

# Append to ledger
rledger extract statement.csv -a Assets:Bank >> ledger.beancount
```

## CSV Import

### Basic Usage

Most bank CSV exports work with minimal configuration:

```bash
rledger extract chase-statement.csv -a Assets:Bank:Chase
```

The importer auto-detects common CSV formats and column layouts.

### Custom Configuration

For non-standard formats, create `importers.toml`:

```toml
[[importers]]
name = "chase"
account = "Assets:Bank:Chase"

# Column mapping (0-indexed or by header name)
date_column = 0
payee_column = 1
narration_column = 2
amount_column = 3

# Date format
date_format = "%m/%d/%Y"

# Options
skip_header = true
invert_amounts = false  # Set true for credit cards

# Default for unmatched transactions
default_expense = "Expenses:Unknown"
```

Use with:

```bash
rledger extract --importer chase chase-statement.csv
```

The `importers.toml` file is searched for automatically in these locations (first found wins):

1. Path specified via `--config path/to/importers.toml` (the legacy spelling `--importers-config` is still accepted as an alias)
1. `importers.toml` in the current directory
1. `~/.config/rledger/importers.toml`

### Account Mapping

Map transaction descriptions to accounts automatically:

```toml
[[importers]]
name = "checking"
account = "Assets:Bank:Checking"
# ... other settings ...

[importers.mappings]
"AMAZON" = "Expenses:Shopping"
"WHOLE FOODS" = "Expenses:Food:Groceries"
"SHELL" = "Expenses:Transport:Gas"
"NETFLIX" = "Expenses:Entertainment:Streaming"
"PAYROLL" = "Income:Salary"
"INTEREST" = "Income:Interest"
```

Patterns are matched case-insensitively against the payee field first, then the
narration. Longer patterns are matched first, so more specific patterns take
priority over shorter ones. The first match wins.

## OFX Import

OFX (Open Financial Exchange) files from banks import directly:

```bash
rledger extract statement.ofx -a Assets:Bank:Checking
```

OFX files contain structured data, so no column mapping is needed.

## WASM Importers (custom formats)

For bank formats CSV and OFX don't cover — proprietary `.dat` files, PDF, MT940, FinTS, vendor-specific JSON — you can load a sandboxed `.wasm` module that implements the `Importer` trait. WASM importers participate in the same `identify`-then-`extract` dispatch as the built-ins; they're indistinguishable to the CLI once loaded.

```bash
# Single .wasm file (highest precedence — overrides discovered + built-in)
rledger extract --wasm-importer ./my-bank.wasm statement.dat -a Assets:Bank

# Or scan a directory at startup
rledger extract --wasm-importer-dir ~/.config/rledger/importers.d statement.dat -a Assets:Bank
```

Persistent setup goes in `importers.toml`:

```toml
# All `.wasm` files in this dir are loaded at startup. Subdirectories are
# not recursed into. Override on the CLI with --wasm-importer-dir.
wasm_importer_dir = "/etc/rledger/importers.d"
```

The sandbox is the same one used for directive plugins: no filesystem, no network, no WASI, with configurable memory (256 MiB default) and fuel (30 s default) caps. To **author** a WASM importer, depend on `rustledger-plugin-types` with the `guest` feature and use the `wasm_importer_main!` macro — see [`examples/wasm-importer-csv-example`](https://github.com/rustledger/rustledger/tree/main/examples/wasm-importer-csv-example) for a reference implementation.

## Multiple Accounts

Configure multiple importers for different accounts:

```toml
[[importers]]
name = "checking"
account = "Assets:Bank:Checking"
date_column = "Date"
amount_column = "Amount"
narration_column = "Description"

[[importers]]
name = "credit_card"
account = "Liabilities:CreditCard:Chase"
date_column = "Trans Date"
amount_column = "Amount"
narration_column = "Description"
invert_amounts = true  # Credit card amounts need inverting

[[importers]]
name = "savings"
account = "Assets:Bank:Savings"
date_column = 0
amount_column = 3
narration_column = 1
```

Select which importer to use:

```bash
rledger extract --importer credit_card chase-card.csv
```

Or specify a custom config path:

```bash
rledger extract --config path/to/importers.toml --importer credit_card chase-card.csv
```

## Enriched Imports

The import pipeline can automatically enrich transactions beyond basic CSV/OFX
extraction:

- **Auto-inference**: Automatically detect CSV delimiter, date format, and column roles
- **Merchant dictionary**: ~75 built-in merchant patterns (grocery, dining, transport, subscriptions, etc.) for automatic account categorization
- **Transaction fingerprinting**: Stable structural hashes for deduplication against existing ledger entries
- **Confidence scores**: Every enrichment decision carries a confidence value

### Auto-Detect Mode

Use `--auto` to skip manual column configuration. The importer will infer
delimiter, date format, and column roles from the file content:

```bash
rledger extract bank-statement.csv -a Assets:Bank:Checking --auto
```

This conflicts with manual column options (`--date-column`, `--amount-column`,
etc.) since the whole point is to infer them automatically.

### Merchant Dictionary

The built-in merchant dictionary maps common payee patterns (Amazon, Starbucks,
Netflix, Uber, etc.) to expense accounts. It is used as a low-priority fallback
-- user-defined mappings in `importers.toml` always take priority.

To enable the merchant dictionary in your importer configuration, use
`use_merchant_dict` in the library API via `CsvConfigBuilder`. This is not
yet available as a TOML config field.

### Regex Mappings

In addition to substring-based `[importers.mappings]`, the library supports
regex-based mappings via the `CsvConfigBuilder::regex_mappings()` API. Regex
patterns are compiled as case-insensitive and matched against payee and
narration fields.

### How Enrichment Works

All enrichment operations live in the `rustledger-ops` crate, which provides
pure functions with no I/O coupling:

- `rustledger_ops::categorize::RulesEngine` -- the rules engine that evaluates
  substring, regex, and merchant dictionary rules in priority order
- `rustledger_ops::fingerprint` -- structural hashing for deduplication
- `rustledger_ops::dedup` -- duplicate detection (structural and fuzzy)
- `rustledger_ops::enrichment::Enrichment` -- metadata describing how each
  transaction was categorized, with confidence and alternatives

The importer crate (`rustledger-importer`) consumes these operations and returns
`EnrichedImportResult` with directive-enrichment pairs.

## Duplicate Detection

Avoid importing the same transactions twice:

```bash
# Check against existing ledger
rledger extract statement.csv -a Assets:Bank --existing ledger.beancount
```

Duplicates are detected by matching:

- Date
- Amount
- Payee/narration (fuzzy match)

## Workflow

### Initial Import

```bash
# 1. Test import (preview output)
rledger extract statement.csv -a Assets:Bank

# 2. Review and append
rledger extract statement.csv -a Assets:Bank >> ledger.beancount

# 3. Validate
rledger check ledger.beancount
```

### Monthly Routine

```bash
# Download statements, then:
rledger extract march-statement.csv \
  --importer checking \
  --existing ledger.beancount \
  >> ledger.beancount

# Fix any unmatched accounts
rledger check ledger.beancount
```

### Categorization Tips

1. **Start broad**: Use `Expenses:Unknown` for unmatched
1. **Add patterns**: When you see repeated merchants, add mappings
1. **Refine over time**: Your mappings improve with each import

## Troubleshooting

### Wrong Date Format

If dates parse incorrectly, specify the format:

```toml
date_format = "%m/%d/%Y"   # US: 03/15/2024
date_format = "%d/%m/%Y"   # EU: 15/03/2024
date_format = "%Y-%m-%d"   # ISO: 2024-03-15
date_format = "%d.%m.%Y"   # German: 15.03.2024
```

### Wrong Amount Signs

Credit card statements often show purchases as positive. Invert them:

```toml
invert_amounts = true
```

### Encoding Issues

If you see garbled characters:

```bash
# Convert to UTF-8 first
iconv -f ISO-8859-1 -t UTF-8 statement.csv > statement-utf8.csv
rledger extract statement-utf8.csv -a Assets:Bank
```

### Column Detection Failed

Explicitly specify columns by index (0-based):

```toml
date_column = 0
amount_column = 3
narration_column = 2
```

Or by header name:

```toml
date_column = "Transaction Date"
amount_column = "Amount"
narration_column = "Description"
```

## See Also

- [extract command](../commands/extract.md) - Full command reference
- [doctor missing-open](../commands/doctor.md) - Generate missing account Open directives
