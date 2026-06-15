______________________________________________________________________

## title: Options Reference description: Beancount file options

# Options Reference

Options configure beancount behavior and are specified in your ledger file.

## Syntax

```beancount
option "name" "value"
```

## Common Options

### title

Display title for the ledger.

```beancount
option "title" "Personal Finances 2024"
```

### operating_currency

Primary currency for reports.

```beancount
option "operating_currency" "USD"
```

Multiple currencies:

```beancount
option "operating_currency" "USD"
option "operating_currency" "EUR"
```

### name_assets / name_liabilities / name_equity / name_income / name_expenses

Rename root account categories.

```beancount
option "name_assets" "Actifs"
option "name_liabilities" "Passifs"
option "name_equity" "Capitaux"
option "name_income" "Revenus"
option "name_expenses" "Dépenses"
```

## Booking Options

### booking_method

Default booking method for reducing positions.

```beancount
option "booking_method" "FIFO"
```

Values:
| Method | Description |
|--------|-------------|
| `STRICT` | Exact lot match required (default) |
| `STRICT_WITH_SIZE` | Like STRICT, but exact-size matches accept oldest lot |
| `FIFO` | First-in, first-out |
| `LIFO` | Last-in, first-out |
| `HIFO` | Highest-in, first-out (highest cost lots reduced first) |
| `AVERAGE` | Average cost |
| `NONE` | No booking |

### account_previous_earnings

Account for previous period earnings in equity.

```beancount
option "account_previous_earnings" "Equity:Retained-Earnings"
```

### account_current_earnings

Account for current period earnings.

```beancount
option "account_current_earnings" "Equity:Current-Earnings"
```

### account_previous_balances

Account for opening/previous balances.

```beancount
option "account_previous_balances" "Equity:Opening-Balances"
```

### account_unrealized_gains

Account for unrealized gains reporting.

```beancount
option "account_unrealized_gains" "Income:Unrealized-Gains"
```

## Display Options

### render_commas

Use commas as thousand separators.

```beancount
option "render_commas" "TRUE"
```

### inferred_tolerance_default

Default tolerance for balance checking.

```beancount
option "inferred_tolerance_default" "*:0.005"
```

### inferred_tolerance_multiplier

Multiplier for inferred tolerances. This name is deprecated (warning `E7004`); use `tolerance_multiplier` instead.

```beancount
option "tolerance_multiplier" "1.1"
```

## Plugin Options

### plugin_processing_mode

How plugins handle errors.

```beancount
option "plugin_processing_mode" "raw"
```

Values:

- `default`: Normal processing
- `raw`: Skip some validations

## File Options

### documents

Root directory for documents.

```beancount
option "documents" "/home/user/finances/documents"
```

## All Options

| Option | Type | Default | Description |
|--------|------|---------|-------------|
| `title` | string | - | Ledger title |
| `operating_currency` | string | - | Primary currency (can specify multiple) |
| `booking_method` | string | STRICT | Lot booking method |
| `render_commas` | bool | FALSE | Thousand separators |
| `name_assets` | string | Assets | Assets root name |
| `name_liabilities` | string | Liabilities | Liabilities root name |
| `name_equity` | string | Equity | Equity root name |
| `name_income` | string | Income | Income root name |
| `name_expenses` | string | Expenses | Expenses root name |
| `account_previous_balances` | string | Equity:Opening-Balances | Opening balances account |
| `account_previous_earnings` | string | Equity:Earnings:Previous | Retained earnings account |
| `account_previous_conversions` | string | Equity:Conversions:Previous | Previous conversions account |
| `account_current_earnings` | string | Equity:Earnings:Current | Current earnings account |
| `account_current_conversions` | string | - | Current conversions account |
| `account_unrealized_gains` | string | - | Unrealized gains account |
| `account_rounding` | string | - | Rounding errors account |
| `conversion_currency` | string | - | Currency for conversions |
| `inferred_tolerance_default` | string | - | Balance tolerance |
| `inferred_tolerance_multiplier` | decimal | 0.5 | Tolerance multiplier (deprecated; renamed to `tolerance_multiplier`) |
| `tolerance_multiplier` | decimal | 0.5 | Tolerance multiplier |
| `infer_tolerance_from_cost` | bool | FALSE | Infer tolerance from cost |
| `use_legacy_fixed_tolerances` | bool | FALSE | Use legacy fixed tolerances |
| `experiment_explicit_tolerances` | bool | FALSE | Enable experimental explicit tolerances |
| `display_precision` | string | - | Per-currency display precision (e.g. `USD:0.01`) |
| `allow_pipe_separator` | bool | FALSE | Allow pipe separator (deprecated) |
| `documents` | string | - | Documents root directory |
| `plugin_processing_mode` | string | default | Plugin mode |
| `plugin` | string | - | Plugin (deprecated; use the `plugin` directive) |
| `filename` | string | - | Source filename (read-only, auto-set) |
| `long_string_maxlines` | int | 64 | Max lines for long strings |

## Example Configuration

```beancount
; ledger.beancount

option "title" "My Finances"
option "operating_currency" "USD"
option "booking_method" "FIFO"
option "render_commas" "TRUE"

option "account_previous_balances" "Equity:Opening-Balances"
option "account_unrealized_gains" "Income:Capital-Gains:Unrealized"

option "documents" "/home/user/finances/receipts"

plugin "beancount.plugins.auto_accounts"
plugin "beancount.plugins.implicit_prices"

include "accounts.beancount"
include "2024/*.beancount"
```

## Viewing Options

List available options:

```bash
rledger doctor list-options
```

Print options from a file:

```bash
rledger doctor print-options ledger.beancount
```

## See Also

- [Configuration](../getting-started/configuration.md) - Config files
- [Plugins](plugins.md) - Available plugins
- [doctor command](../commands/doctor.md) - List/print options
