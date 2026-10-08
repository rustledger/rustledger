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
currency = "USD"  # required unless the ledger's `open` names one (see below)

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

An entry without `currency` takes the currency from the account's `open`
directive when you pass the ledger with `--ledger` or `--existing` and that
directive names exactly one currency (`2024-01-01 open Assets:Bank:Chase USD`).
`--ledger` decides when it opens the account; `--existing` is read only when it
does not. Included files are followed. Otherwise extract stops with an error
naming the importer. A configured `currency` (or `--currency`) always wins
over the `open`, but if the `open` does not allow it, extract warns, since
`rledger check` would reject every imported posting. A value that is not a
commodity at all (`usd`, `€`, an empty string) is an error naming its source. It never guesses a
currency, since amounts booked in the wrong one corrupt the ledger silently.

The `importers.toml` file is searched for automatically in these locations (first found wins):

1. Path specified via `--config path/to/importers.toml` (the legacy spelling `--importers-config` is still accepted as an alias)
1. `importers.toml` in the current directory
1. `$RLEDGER_CONFIG_DIR/importers.toml` if set
1. The platform default (`~/.config/rledger/importers.toml` on Linux,
   `~/Library/Application Support/rledger/importers.toml` on macOS)
1. Fallback on macOS (`~/.config/rledger/importers.toml`)

### Preserving a second date column

Bank statements often carry **two** dates per row — a booking/posted date and a
value/settlement date. `date_column` becomes the transaction date; rather than
dropping the other one, rledger preserves it as transaction **metadata** (#1623).

Auto-detect mode does this automatically: when a CSV has a second date-named
column (e.g. `Value Date` next to `Booking Date`), it is preserved under a key
slugified from its header (`value_date`):

```beancount
2024-01-15 * "Coffee Shop"
  value_date: 2024-01-17
  Assets:Bank:Checking  -4.50 USD
  Expenses:Unknown        4.50 USD
```

For explicit `importers.toml` configs, name the column:

```toml
[[importers]]
name = "mybank"
date_column = "Booking Date"
date_format = "%Y-%m-%d"

# Preserve the value date as `value_date:` metadata
secondary_date_column = "Value Date"
# secondary_date_format = "%Y-%m-%d"   # optional, defaults to date_format
# secondary_date_key    = "value_date" # optional, defaults to a slug of the column
```

The value is stored as a typed `date` metadatum, so it round-trips through the
ledger and is queryable in BQL via `meta("value_date")`.

### Transaction ids

If the bank's CSV has a unique id per transaction (Monzo's `Transaction ID`,
for example), name the column and every imported transaction carries it as a
`^csv-<id>` link, the CSV counterpart of OFX's `^ofx-<FITID>`. For a
Monzo-style export (`Transaction ID,Date,Time,Type,Name,…,Amount,Currency,…,Description,…`,
dates like `15/01/2024`):

```toml
[[importers]]
name = "monzo"
account = "Assets:Monzo"
currency = "GBP"
date_column = "Date"
date_format = "%d/%m/%Y"
payee_column = "Name"
narration_column = "Description"
amount_column = "Amount"
transaction_id_column = "Transaction ID"
```

`rledger extract --importer monzo monzo.csv` then writes:

```beancount
2024-01-15 * "Bakery" "Croissant" ^csv-tx_0000A1b2C3
  Assets:Monzo  -2.50 GBP
  Expenses:Unknown
```

Characters a link may not contain become `-`, and a blank cell adds no link.
A column the file does not have is an error naming the file's columns (with a
hint when the name differs from a header only in case or spaces), as is an
index past the last column or a column the importer already reads as
`amount_column`, `date_column` and so on. Ids
that repeat within one statement get a warning: the column must be unique per
transaction, since `--existing` treats an equal id with an equal amount as the
same transaction on any date.
Duplicate detection treats the id, together with the amount, as identity, so a
re-import with `--existing` matches a transaction even after you rename its
payee or narration, rather than relying on a fuzzy guess (see below).

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
priority over shorter ones. Patterns of the same length are tried in the order
the file lists them, so when two equally long patterns both match (`"foo"` and
`"bar"` against `FOOBAR`), the one written first wins, on every run. The first
match wins.

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

The sandbox is the same one used for directive plugins: no filesystem, no network, no WASI, with a 256 MiB memory cap and a time budget of at most 30 seconds per call. The budget is raised with `[plugins] max_time_secs` in the rledger config file or `--plugin-max-time-secs`; see [Plugin Time Budget](../getting-started/configuration.md#plugin-time-budget). To **author** a WASM importer, depend on `rustledger-plugin-types` with the `guest` feature and use the `wasm_importer_main!` macro — see [`examples/wasm-importer-csv-example`](https://github.com/rustledger/rustledger/tree/main/examples/wasm-importer-csv-example) for a reference implementation.

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
- **Merchant dictionary**: 75 built-in merchant patterns (grocery, dining, transport, subscriptions, etc.) for automatic account categorization
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

Only transactions posting to the importer's account, in the same commodity,
are compared. A new transaction is a duplicate when:

1. it shares an id link (`^ofx-…` from OFX, `^csv-…` from
   `transaction_id_column`) with an existing transaction and moves the same
   amount, whatever the date or text say; or
1. it has the same date and amount as an existing transaction and the same
   or a similar payee/narration — unless both carry ids of the same kind and
   those ids differ, which makes them two different transactions.

A ledger entry that splits the account's leg over several postings is
compared by its net movement too, and a transfer you already imported from the
other account's statement counts as a duplicate, since it already records this
account's leg. A row from a custom (WASM) importer that does not post to the
importer's account at all is compared by its first posting instead. Two rows
with no payee or narration match when date and amount do, so a statement with
no description column still re-imports to nothing; such a skip is flagged on
stderr (`-- check: nothing but the date and amount ties these together`),
because two different description-less rows on one day for one amount cannot
be told apart. Text is compared case-insensitively but is not Unicode
normalized: `é` written as one character and as `e` plus a combining accent
differ. Which rows are kept does
not depend on the order the statement or the ledger lists them in.

Each existing transaction absorbs at most one new one, so two identical
coffees on the same day are both kept when the ledger holds only one of them.
Skips are counted on stderr by kind, and up to 20 of each kind (ordinary, and
the flagged date-and-amount-only ones) are listed with the reason and the
existing entry they matched; the rest are summarized as `... and N more`. If
the `--existing` ledger has errors, a warning says so: transactions in the
parts that failed to load cannot be compared, so their duplicates may be
imported again.

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
