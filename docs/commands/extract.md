______________________________________________________________________

## title: rledger extract description: Import transactions from bank statements

# rledger extract

Import transactions from bank statements. Handles CSV and OFX/QFX out of the box; can also load third-party importers as sandboxed WASM modules via `--wasm-importer` / `--wasm-importer-dir`.

## Usage

```bash
rledger extract [OPTIONS] [FILE]
```

## Arguments

| Argument | Description |
|----------|-------------|
| `FILE` | CSV or OFX file to import (required unless using `--list-importers`) |

## Options

### Config-based Import

| Option | Description |
|--------|-------------|
| `-i, --importer <NAME>` | Use a named importer from config |
| `--config <FILE>` | Path to importers.toml configuration file |
| `--list-importers` | List available importers from config file and exit |

### Auto-Detection

| Option | Description |
|--------|-------------|
| `--auto` | Auto-detect CSV format (delimiter, columns, date format). Conflicts with manual column options. |

### Direct CLI Import

| Option | Description |
|--------|-------------|
| `-a, --account <ACCOUNT>` | Target account [default: Assets:Bank:Checking] |
| `-c, --currency <CURRENCY>` | Currency for amounts [default: USD] |
| `--date-column <COL>` | Date column name or index [default: Date] |
| `--date-format <FMT>` | Date format (strftime-style) [default: %Y-%m-%d] |
| `--narration-column <COL>` | Narration/description column [default: Description] |
| `--payee-column <COL>` | Payee column name (optional) |
| `--amount-column <COL>` | Amount column name or index [default: Amount] |
| `--amount-locale <LOCALE>` | Locale for parsing amounts (e.g., `en_US`) |
| `--amount-format <FMT>` | Custom format for parsing amounts |
| `--debit-column <COL>` | Debit column (for separate debit/credit) |
| `--credit-column <COL>` | Credit column (for separate debit/credit) |
| `--delimiter <CHAR>` | CSV delimiter [default: ,] |
| `--skip-rows <N>` | Number of header rows to skip [default: 0] |
| `--invert-sign` | Invert sign of amounts |
| `--no-header` | CSV has no header row |
| `--include-zero-amounts` | Preserve rows whose amount is exactly zero (default drops them; bank "status filler" rows) |

### Output Options

| Option | Description |
|--------|-------------|
| `-o, --output <FILE>` | Write output to file instead of stdout |
| `--existing <FILE>` | Existing ledger file for duplicate detection |
| `--suggest-categories` | Use ML (Naive Bayes on the `--existing` ledger) to suggest accounts for transactions the rules engine didn't categorize. Requires `--existing`. |
| `--balance <AMOUNT>` | Append a balance assertion directive with the given amount (e.g., `1234.56`) |
| `--balance-date <DATE>` | Date for the balance assertion (defaults to today) |

### WASM Importers

Third-party importers ship as sandboxed `.wasm` modules. Flags below override `wasm_importer_dir` from `importers.toml`.

| Option | Description |
|--------|-------------|
| `--wasm-importer <PATH>` | Register a specific `.wasm` importer ahead of built-ins. Repeatable. User-specified modules take precedence over discovered ones and built-ins. |
| `--wasm-importer-dir <DIR>` | Scan a directory for `*.wasm` importer modules at startup. Repeatable. Subdirectories are not recursed into; non-`.wasm` files are silently skipped. |

## Examples

### Basic CSV Import

```bash
rledger extract bank-statement.csv -a Assets:Bank:Checking
```

### With Configuration

Create `importers.toml`:

```toml
[[importers]]
name = "chase"
account = "Assets:Bank:Chase"
date_column = 0
narration_column = 2
amount_column = 3
date_format = "%m/%d/%Y"
skip_header = true

[importers.mappings]
"AMAZON" = "Expenses:Shopping"
"WHOLE FOODS" = "Expenses:Food:Groceries"
"SHELL" = "Expenses:Transport:Gas"
```

```bash
rledger extract --importer chase chase-statement.csv
```

### Auto-Detect CSV Format

```bash
rledger extract bank-statement.csv -a Assets:Bank:Checking --auto
```

The `--auto` flag infers the delimiter, date format, and column roles from the
file content. It cannot be combined with manual column options like
`--date-column` or `--amount-column`.

### OFX Import

```bash
rledger extract statement.ofx -a Assets:Bank:Checking
```

### Append to Ledger

```bash
rledger extract statement.csv -a Assets:Bank >> ledger.beancount
```

### Duplicate Detection

```bash
# Skip transactions already in ledger
rledger extract statement.csv -a Assets:Bank --existing ledger.beancount
```

## Importer Configuration

### CSV Options

```toml
[[importers]]
name = "my_bank"
account = "Assets:Bank:MyBank"

# Column mapping (0-indexed)
date_column = 0
payee_column = 1
narration_column = 2
amount_column = 3

# Or use column names (if CSV has header)
date_column = "Date"
amount_column = "Amount"

# Date parsing
date_format = "%Y-%m-%d"  # or "%m/%d/%Y", "%d.%m.%Y"

# Skip header row
skip_header = true

# Invert amounts (for credit card statements)
invert_amounts = true

# Default expense account
default_expense = "Expenses:Unknown"

# Pattern-based account mapping
[importers.mappings]
"GROCERY" = "Expenses:Food:Groceries"
"GAS STATION" = "Expenses:Transport:Gas"
"PAYROLL" = "Income:Salary"
```

### Enrichment Options

The importer library supports additional enrichment features via the
`CsvConfigBuilder` API:

| Builder Method | Description |
|----------------|-------------|
| `use_merchant_dict(true)` | Enable the built-in merchant dictionary (~150 common patterns) as a low-priority fallback for account categorization |
| `regex_mappings(vec)` | Add regex-based account mappings (case-insensitive, compiled at load time) |

These options are available in the Rust library API but are not yet exposed as
fields in `importers.toml` configuration. Substring-based mappings in
`[importers.mappings]` are supported in TOML and work the same way.

### Multiple Importers

```toml
[[importers]]
name = "checking"
account = "Assets:Bank:Checking"
# ...

[[importers]]
name = "credit_card"
account = "Liabilities:CreditCard"
invert_amounts = true
# ...
```

Use with:

```bash
rledger extract --importer checking statement.csv
```

The `importers.toml` file is auto-discovered from the current directory or `~/.config/rledger/`. To specify a custom path:

```bash
rledger extract --config path/to/importers.toml --importer checking statement.csv
```

### List Available Importers

Lists both TOML profiles (for `--importer <name>`) and registered importer engines (built-in CSV/OFX plus any WASM modules from `--wasm-importer`/`--wasm-importer-dir`):

```bash
rledger extract --config importers.toml --list-importers
```

### Using a WASM Importer

```bash
# One-off: register a single .wasm file
rledger extract --wasm-importer ./my-bank.wasm statement.dat -a Assets:Bank

# Or scan a whole directory at startup
rledger extract --wasm-importer-dir ~/.config/rledger/importers.d statement.dat -a Assets:Bank
```

Persistent setup goes in `importers.toml`:

```toml
wasm_importer_dir = "/etc/rledger/importers.d"
```

WASM importers participate in the same `identify`-then-`extract` dispatch as the built-ins. See [`examples/wasm-importer-csv-example`](https://github.com/rustledger/rustledger/tree/main/examples/wasm-importer-csv-example) for how to write one.

### Direct CLI Import (No Config)

```bash
rledger extract statement.csv \
  -a Assets:Bank:Checking \
  --date-column "Transaction Date" \
  --date-format "%m/%d/%Y" \
  --amount-column "Amount" \
  --narration-column "Description" \
  --skip-rows 1 \
  --invert-sign
```

## See Also

- [Importing Guide](../guides/importing.md) - Detailed import tutorial
- [Architecture: rustledger-ops](../reference/architecture.md) - Crate providing the enrichment operations
