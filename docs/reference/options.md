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

Where separators appear depends on whether the consumer has a **grammar**. A
Beancount reader does — grouped numerals are part of the syntax, so every
conforming reader accepts them. A CSV or JSON consumer does not: a separator
forces the field to be quoted and is then rejected by ordinary decimal parsers.

| Surface | Separators? |
|---------|-------------|
| `report`, `query` — text | yes, when the option is set |
| `report`, `query` — `--format csv` / `json` | **never** — machine interchange with no grammar |
| `query --format beancount` | yes — ledger text, same as `format` (matches Beancount's `print`) |
| `format` (the file on disk) | when the file's ledger declares them, see below |
| Editor format-on-save (LSP) | same rule as `format` |

The CSV/JSON row is absolute: it outranks both the option and any per-commodity
declaration, because the reason there is the consumer's missing grammar rather
than the ledger's preference.

Why presentation is the ledger's to declare at all, and where that stops, is
recorded in [ADR-0008](adr/0008-presentation-is-ledger-declared.md).

### Separators in the ledger file itself

`rledger format` finds the ledger a file belongs to and honors its
declarations:

```console
$ rledger format postings.beancount
  Assets:Local    1,234,567.89 IQD
```

It looks for the nearest root journal at or above the file — `main.beancount`,
`ledger.beancount`, `journal.beancount`, `index.beancount` and their `.bean`
spellings, nearest first — which is the same rule the language server uses. A
file therefore formats the same on save as it does in a pre-commit hook. This
matters because `format` is otherwise a per-file text transform: it cannot see
an `option` or `commodity` directive that sits in the root while the postings
sit in an `include`d file.

Discovery is a guess, so it is checked: a discovered ledger governs a file only
if it actually `include`s it. A scratch file or vendor export sitting beside
your journal is left alone.

| Flag | Effect |
|------|--------|
| *(none)* | Use the nearest root journal that includes this file |
| `--ledger <ROOT>` | Use exactly this root, and apply it to every file listed |
| `--no-ledger` | Do not look for a ledger; format from the file's bytes alone |

`--ledger` names *where the declarations live*, not what style to use, and it
is obeyed without the containment check — you pointed at it. Use it when the
root is somewhere discovery will not look, or to be explicit in CI. Use
`--no-ledger` where output must depend only on the file's own content, whatever
surrounds a checkout.

A grouped file is *canonical* for a ledger that asked for grouping, so
`format --check` accepts it and formatting stays idempotent. A ledger that
declares nothing is unaffected by any of this, which bounds the blast radius of
discovery: only a ledger that asked for separators can get them.

**In an editor**, the language server applies the same rule without any flag:
format-on-save, range formatting, and the *Align Amounts* command all group
when the ledger asks. It resolves the root from its own configuration or
workspace rather than by walking up from the file, but the fallbacks match — a
buffer no journal includes is left alone, and so is anything formatted before
the ledger has finished loading (formatting still works rather than blocking on
it).

### Per-commodity declarations

`render_commas` is the ledger-wide default; a commodity can override it:

```beancount
option "render_commas" "TRUE"

2020-01-01 commodity IQD          ; grouped: amounts run to 10 digits
2020-01-01 commodity USD
  render_commas: FALSE            ; not grouped: amounts are 2-4 digits
```

This is the same metadata mechanism as `precision:`, resolved by the same
tiers — amount-scan inference, then the global option, then commodity
metadata. Beancount ignores metadata keys it does not recognize, so a ledger
carrying this still round-trips through Beancount and Fava.

A commodity's declaration reaches every surface the global option does —
`report` and `query` text as well as `format`. It does **not** override the
surface rules in the table above: a commodity declaring `render_commas: TRUE`
is still written unseparated to CSV and JSON, because suppression there is
about the consumer's lack of a grammar, not about the ledger's preference.

Groups are three digits, which is all the parser accepts. Other conventions
(Indian lakh grouping, for instance) would need a grammar change first — the
formatter must never emit text its own parser rejects.

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
