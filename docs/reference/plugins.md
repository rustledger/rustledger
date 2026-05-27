______________________________________________________________________

## title: Plugins Reference description: Plugin architecture, built-in plugins, and custom plugin development

# Plugins Reference

rustledger supports a flexible plugin system for validation and transformation of your ledger data.

## Plugin Architecture

rustledger supports three types of plugins:

| Type | Performance | Use Case |
|------|-------------|----------|
| **Native Rust** | Fastest | Built-in plugins, core functionality |
| **WASM** | Fast | Custom plugins, external development |
| **Python** | Slow (10-100x) | Legacy compatibility, migration path |

```
┌─────────────────────────────────────────────────────────┐
│                    Beancount File                       │
│  plugin "beancount.plugins.auto_accounts"               │
│  plugin "my_custom_plugin.wasm"                         │
└─────────────────────────────────────────────────────────┘
                          │
                          ▼
┌─────────────────────────────────────────────────────────┐
│                   Plugin Loader                         │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐       │
│  │   Native    │ │    WASM     │ │   Python    │       │
│  │  Registry   │ │   Runtime   │ │   Runtime   │       │
│  │  (30 plugins)│ │ (Wasmtime)  │ │(CPython-WASI)│      │
│  └─────────────┘ └─────────────┘ └─────────────┘       │
└─────────────────────────────────────────────────────────┘
                          │
                          ▼
┌─────────────────────────────────────────────────────────┐
│              Plugin Interface (PluginInput)             │
│  - directives: Vec<DirectiveWrapper>                    │
│  - options: PluginOptions                               │
│  - config: Option<String>                               │
└─────────────────────────────────────────────────────────┘
                          │
                          ▼
┌─────────────────────────────────────────────────────────┐
│              Plugin Output (PluginOutput)               │
│  - ops: Vec<PluginOp>  (Keep/Modify/Insert/Delete)      │
│  - errors: Vec<PluginError>                             │
└─────────────────────────────────────────────────────────┘
```

`PluginOp` is an ordered operation list — not a replacement directive
list — so transformed directives can inherit the source span / `file_id`
of the input they came from. See [Custom Plugins Guide](../guides/custom-plugins.md)
for the variants and conventions.

### Plugin Loading

Plugins are specified in your beancount file using the `plugin` directive:

```beancount
; Built-in plugin (by name)
plugin "beancount.plugins.auto_accounts"

; WASM plugin (by path)
plugin "/path/to/my_plugin.wasm"

; Plugin with configuration
plugin "beancount.plugins.split_expenses" "alice bob"
```

### Plugin Execution Order

The loader splits plugin execution around booking. Synthesizer plugins
that inject directives the Early validator depends on
(`auto_accounts`, `document_discovery`) run BEFORE Early validation
and BEFORE booking. Every other plugin runs AFTER booking and BEFORE
Late validation so cost-spec-reading plugins (`implicit_prices`,
`sellgains`, `unrealized`, etc.) see filled-in `cost.number_per`
values from the booker.

The full pipeline is:

```
sort → synth-plugins → Early validation → booking
     → regular-plugins → Late validation → finalize
```

Native plugins declare their pass by implementing exactly one of two
marker subtraits — `SynthPlugin` or `RegularPlugin` — both of which
extend the base `NativePlugin` capability. The registry stores them in
two separately-typed `Vec`s, and the loader looks up the right kind via
`find_synth` / `find_regular`. The loader uses the `PluginPass` enum
(`PreBookingSynth`, `PostBooking`) to select which subset of plugins to
run on each pass. Callers that operate on already-booked input (LSP /
FFI / standalone tests) invoke `run_plugins` twice — once per pass —
matching the loader's own pipeline.

Within each pass, plugins still execute in the order they appear in
your file. This matters because:

- Transformation plugins modify directives that subsequent plugins see
- Validation plugins should typically run after transformation plugins

```beancount
; auto_accounts is a synthesizer — runs pre-booking, regardless of
; ordering with other plugins. Listed first by convention.
plugin "beancount.plugins.auto_accounts"

; Post-booking pass: implicit_prices reads booked cost specs.
plugin "beancount.plugins.implicit_prices"

; Post-booking pass: validation plugins run last.
plugin "beancount.plugins.check_commodity"
plugin "beancount.plugins.noduplicates"
```

## Using Plugins

Enable plugins in your beancount file:

```beancount
plugin "beancount.plugins.auto_accounts"
plugin "beancount.plugins.implicit_prices"
```

## Built-in Plugins

rustledger includes 30 native plugins. Here are the most commonly used:

### Validation Plugins

| Plugin | Description |
|--------|-------------|
| `check_average_cost` | Validate sales use correct average cost |
| `check_closing` | Zero balance assertion on posting with `closing: TRUE` |
| `check_commodity` | Ensure commodities are declared |
| `check_drained` | Zero balance assertion on balance sheet account close |
| `coherent_cost` | Validate cost specifications |
| `commodity_attr` | Validate commodity metadata attributes |
| `leafonly` | Restrict postings to leaf accounts |
| `noduplicates` | Detect duplicate transactions |
| `nounused` | Warn about unused accounts |
| `onecommodity` | One commodity per account |
| `pedantic` | Strict validation rules |
| `unique_prices` | One price per commodity per day |

### Transformation Plugins

| Plugin | Description |
|--------|-------------|
| `auto_accounts` | Auto-generate Open directives |
| `auto_tag` | Auto-tag transactions by account patterns |
| `box_accrual` | Split capital losses across multiple years |
| `close_tree` | Recursively close account trees |
| `currency_accounts` | Auto-generate currency trading postings |
| `document_discovery` | Auto-discover documents from directories |
| `effective_date` | Move postings to effective dates |
| `forecast` | Generate recurring transactions |
| `generate_base_ccy_prices` | Generate base currency prices from FX rates |
| `implicit_prices` | Generate prices from transactions |
| `long_short` | Classify capital gains as short/long term |
| `gain_loss` | Classify capital gains as gains/losses |
| `rename_accounts` | Rename accounts using regex patterns |
| `rx_txn_plugin` | Set defaults for Regular Expected Transactions |
| `sellgains` | Auto-generate capital gains postings |
| `split_expenses` | Split shared expenses |
| `unrealized` | Calculate unrealized gains/losses |
| `valuation` | Track opaque fund values |
| `zerosum` | Match zero-sum postings within date ranges |

### All Built-in Plugins

<details>
<summary>Complete list of 30 native plugins</summary>

| Plugin | Description |
|--------|-------------|
| `auto_accounts` | Auto-generate Open directives |
| `auto_tag` | Automatically tag transactions |
| `box_accrual` | Accrual accounting for boxed periods |
| `gain_loss` | Split capital gains into gain/loss accounts |
| `long_short` | Split capital gains by holding period |
| `check_average_cost` | Validate average cost bookings |
| `check_closing` | Zero balance on account close |
| `check_commodity` | Validate commodity declarations |
| `check_drained` | Ensure accounts drained before close |
| `close_tree` | Close descendant accounts |
| `coherent_cost` | Enforce cost OR price (not both) |
| `commodity_attr` | Validate commodity attributes |
| `currency_accounts` | Auto-generate currency trading postings |
| `effective_date` | Override posting date via metadata |
| `forecast` | Generate recurring transactions |
| `generate_base_ccy_prices` | Create base currency price entries |
| `implicit_prices` | Generate prices from costs |
| `leafonly` | Error on non-leaf account postings |
| `noduplicates` | Detect duplicate transactions |
| `nounused` | Warn on unused accounts |
| `onecommodity` | Single commodity per account |
| `pedantic` | Enable all strict validations |
| `rename_accounts` | Rename accounts via metadata |
| `rx_txn_plugin` | Link related transactions |
| `sellgains` | Cross-check capital gains |
| `split_expenses` | Split expenses across accounts |
| `unique_prices` | One price per day per pair |
| `unrealized` | Calculate unrealized gains |
| `valuation` | Mark-to-market valuation |
| `zerosum` | Group transactions that sum to zero |

</details>

## Plugin Details

### auto_accounts

Automatically generates `Open` directives for any accounts used in transactions.

```beancount
plugin "beancount.plugins.auto_accounts"

; No need for explicit Open directives
2024-01-15 * "Coffee"
  Expenses:Food:Coffee   5.00 USD
  Assets:Cash           -5.00 USD
```

Options: None

### check_commodity

Ensures all commodities are explicitly declared.

```beancount
plugin "beancount.plugins.check_commodity"

2020-01-01 commodity USD
2020-01-01 commodity AAPL
```

Options: None

### coherent_cost

Validates that cost specifications are consistent with prices.

```beancount
plugin "beancount.plugins.coherent_cost"
```

This plugin checks that when both cost and price are specified, they're coherent (e.g., for capital gains transactions).

Options: None

### implicit_prices

Generates price directives from transaction costs.

```beancount
plugin "beancount.plugins.implicit_prices"

2024-01-15 * "Buy stock"
  Assets:Brokerage   10 AAPL {150.00 USD}
  Assets:Cash       -1500.00 USD

; Generates:
; 2024-01-15 price AAPL 150.00 USD
```

Options: None

### leafonly

Restricts postings to leaf accounts only. Reports an error if you post to an account that has sub-accounts.

```beancount
plugin "beancount.plugins.leafonly"
```

```beancount
; ERROR: Cannot post to parent account
2024-01-15 * "Coffee"
  Expenses   5.00 USD    ; Error if Expenses:Food exists
  Assets:Cash

; OK: Posting to leaf account
2024-01-15 * "Coffee"
  Expenses:Food:Coffee   5.00 USD
  Assets:Cash
```

Options: None

### noduplicates

Detects duplicate transactions based on date, payee, narration, and amounts.

```beancount
plugin "beancount.plugins.noduplicates"
```

Options: None

### onecommodity

Ensures each account only holds one commodity.

```beancount
plugin "beancount.plugins.onecommodity"

2020-01-01 open Assets:Bank:USD   USD
2020-01-01 open Assets:Bank:EUR   EUR
```

Options: None

### pedantic

Enables strict validation:

- Requires explicit tags on all transactions
- Requires payees on all transactions
- Other strict checks

```beancount
plugin "beancount.plugins.pedantic"
```

Options: None

### sellgains

Automatically generates capital gains postings for sales.

```beancount
plugin "beancount.plugins.sellgains"

2024-01-15 * "Sell AAPL"
  Assets:Brokerage  -10 AAPL {} @ 175.00 USD
  Assets:Cash       1750.00 USD
  ; Auto-generates:
  ; Income:CapitalGains   -250.00 USD
```

Options: None

### split_expenses

Splits expenses among multiple people.

```beancount
plugin "beancount.plugins.split_expenses" "mark,john 50,50"

2024-01-15 * "Dinner" #shared
  Expenses:Food      100.00 USD
  Assets:Cash
```

Options: `"person1,person2 share1,share2"`

### unique_prices

Ensures only one price directive per commodity per day.

```beancount
plugin "beancount.plugins.unique_prices"
```

Options: None

______________________________________________________________________

## Additional Plugins

### auto_tag

Automatically tags transactions based on account patterns.

```beancount
plugin "beancount.plugins.auto_tag" "{'Expenses:Food:.*': 'food', 'Expenses:Transport:.*': 'transport'}"

2024-01-15 * "Coffee"
  Expenses:Food:Coffee   5.00 USD
  Assets:Cash
; Automatically gets #food tag
```

Options: Python dict mapping regex patterns to tag names.

### box_accrual

Splits capital losses across multiple years based on `synthetic_loan_expiry` metadata. Used for tax purposes when losses must be recognized proportionally.

```beancount
plugin "beancount.plugins.box_accrual"

2024-07-01 * "Sell synthetic"
  synthetic_loan_expiry: 2026-06-30
  Assets:Broker           1000 USD
  Income:Capital-Losses   -365 USD
; Splits the loss across 2024, 2025, 2026 proportionally
```

Options: None

### check_average_cost

Validates that sales of positions use the correct average cost basis. Reports a warning if the cost used differs from the calculated average by more than the tolerance.

```beancount
plugin "beancount.plugins.check_average_cost" "0.01"

; Buy 10 @ $100, then 10 @ $120 -> average = $110
; Selling at $100 cost would trigger a warning
```

Options: Tolerance as decimal (default: `0.01` = 1%)

### close_tree

Automatically closes all descendant accounts when a parent account is closed.

```beancount
plugin "beancount.plugins.close_tree"

2024-01-01 open Assets:Bank
2024-01-01 open Assets:Bank:Checking
2024-01-01 open Assets:Bank:Savings

2024-12-31 close Assets:Bank
; Automatically generates:
; 2024-12-31 close Assets:Bank:Checking
; 2024-12-31 close Assets:Bank:Savings
```

Options: None

### check_closing

Inserts zero balance assertions when a posting has `closing: TRUE` metadata. The assertion is dated one day after the transaction.

```beancount
plugin "beancount.plugins.check_closing"

2024-12-31 * "Close out position"
  Assets:Broker:AAPL  -10 AAPL {100 USD}
    closing: TRUE
  Assets:Cash          1000 USD
; Generates: 2025-01-01 balance Assets:Broker:AAPL 0 AAPL
```

Options: None

### check_drained

Inserts zero balance assertions when balance sheet accounts (Assets, Liabilities, Equity) are closed. The assertion is dated one day after the close directive.

```beancount
plugin "beancount.plugins.check_drained"

2024-01-01 open Assets:Bank USD
2024-12-31 close Assets:Bank
; Generates: 2025-01-01 balance Assets:Bank 0 USD
```

Options: None

### commodity_attr

Validates that Commodity directives have required metadata attributes.

```beancount
plugin "beancount.plugins.commodity_attr" "{'name': null, 'sector': ['Tech', 'Finance', 'Healthcare']}"

2024-01-01 commodity AAPL
  name: "Apple Inc"
  sector: "Tech"
```

Options: Python dict where:

- Keys are attribute names
- `null` means required but any value allowed
- `['a', 'b']` means required and must be one of the listed values

### currency_accounts

Automatically generates currency conversion postings through trading accounts when transactions involve multiple currencies.

```beancount
plugin "beancount.plugins.currency_accounts"

2024-01-15 * "Buy EUR"
  Assets:Bank:EUR    100 EUR @ 1.10 USD
  Assets:Bank:USD   -110 USD
; Generates postings through Equity:Conversions:EUR and Equity:Conversions:USD
```

Options: None

### document_discovery

Auto-discovers document files from directories. Scans directories specified in `option "documents"` for files matching the pattern `{Account}/YYYY-MM-DD.description.*`.

```beancount
option "documents" "/path/to/documents"
plugin "beancount.plugins.document_discovery"

; File: /path/to/documents/Assets/Bank/Checking/2024-01-15.statement.pdf
; Generates:
; 2024-01-15 document Assets:Bank:Checking "/path/to/documents/Assets/Bank/Checking/2024-01-15.statement.pdf"
```

Options: None (uses `option "documents"` paths)

### effective_date

Moves postings to their effective date using holding accounts. Add `effective_date` metadata to defer recognition.

```beancount
plugin "beancount.plugins.effective_date"

2024-01-15 * "Invoice"
  Income:Consulting  -1000 USD
    effective_date: 2024-02-15
  Assets:Receivable   1000 USD
; Creates a holding entry until 2024-02-15
```

Options: None

### forecast

Generates recurring transactions from templates. Use pattern syntax in the narration to specify recurrence.

```beancount
plugin "beancount.plugins.forecast"

2024-01-01 # "Rent [MONTHLY]"
  Expenses:Rent      2000 USD
  Assets:Checking   -2000 USD

2024-01-01 # "Gym [WEEKLY REPEAT 12 TIMES]"
  Expenses:Gym        50 USD
  Assets:Cash        -50 USD
```

Patterns:

- `[MONTHLY]` - Repeat monthly indefinitely
- `[WEEKLY]` - Repeat weekly indefinitely
- `[DAILY]` - Repeat daily indefinitely
- `[MONTHLY REPEAT N TIMES]` - Repeat N times
- `[WEEKLY SKIP 2]` - Repeat every 2 weeks
- `[MONTHLY UNTIL 2024-12-31]` - Repeat until date

Options: None

### gain_loss

Classifies capital gains transactions as gains or losses. Adds metadata `gain_loss: "gain"` or `gain_loss: "loss"` to transactions.

```beancount
plugin "beancount.plugins.gain_loss"

2024-01-15 * "Sell AAPL"
  Assets:Brokerage  -10 AAPL {100 USD} @ 150 USD
  Assets:Cash        1500 USD
  Income:CapitalGains
; Transaction gets gain_loss: "gain" metadata
```

Options: None

### generate_base_ccy_prices

Generates price entries in a base currency by applying exchange rates to existing prices.

```beancount
plugin "beancount.plugins.generate_base_ccy_prices" "USD"

2024-01-01 price EUR 1.10 USD
2024-01-01 price ETH 2000 EUR
; Generates: 2024-01-01 price ETH 2200 USD (2000 * 1.10)
```

Options: Base currency code (e.g., `"USD"`)

### long_short

Classifies capital gains transactions as short-term or long-term based on holding period. Adds metadata `holding_period: "short"` or `holding_period: "long"`.

```beancount
plugin "beancount.plugins.long_short"

2024-01-15 * "Sell AAPL"
  Assets:Brokerage  -10 AAPL {100 USD, 2023-01-01} @ 150 USD
  Assets:Cash        1500 USD
  Income:CapitalGains
; Gets holding_period: "long" (held > 1 year)
```

Options: None

### nounused

Reports warnings for accounts that are opened but never used in any transaction, balance, or other directive.

```beancount
plugin "beancount.plugins.nounused"

2024-01-01 open Assets:OldAccount
; Warning: Account 'Assets:OldAccount' is opened but never used
```

Options: None

### rename_accounts

Renames accounts using regex patterns. Useful for bulk account reorganization.

```beancount
plugin "beancount.plugins.rename_accounts" "{'Expenses:Food:(.*)': 'Expenses:Dining:$1'}"

2024-01-01 open Expenses:Food:Groceries
; Becomes: 2024-01-01 open Expenses:Dining:Groceries
```

Options: Python dict mapping regex patterns to replacement strings. Use `$1`, `$2` for capture groups.

### rx_txn_plugin

Sets default metadata for Regular Expected Transactions (for beanahead integration). Transactions tagged `#rx_txn` get default `final: None` and `roll: True` metadata.

```beancount
plugin "beancount.plugins.rx_txn_plugin"

2024-01-15 * "Monthly rent" #rx_txn
  Expenses:Rent      2000 USD
  Assets:Checking
; Gets metadata: final: None, roll: True
```

Options: None

### unrealized

Calculates unrealized gains and losses for positions at market value.

```beancount
plugin "beancount.plugins.unrealized" "Income:Unrealized"

2024-01-01 price AAPL 150 USD
; For positions bought at $100, generates unrealized gain entries
```

Options: Account for unrealized gains (e.g., `"Income:Unrealized"`)

### valuation

Tracks opaque fund values using synthetic commodities. Useful for retirement accounts or funds that don't provide per-share NAV.

```beancount
plugin "beancount.plugins.valuation"

2024-01-01 * "401k contribution"
  Assets:401k:Fund    100 FUND401K {50 USD}
  Assets:Checking    -5000 USD

2024-06-30 custom "valuation" Assets:401k:Fund 6000 USD
; Creates synthetic position reflecting current value
```

Options: None

### zerosum

Matches pairs of postings that sum to zero within a date range. Useful for tracking reimbursements, loans, or transfers.

```beancount
plugin "beancount.plugins.zerosum" "Assets:Reimbursable 30"

2024-01-15 * "Expense to be reimbursed"
  Assets:Reimbursable   100 USD
  Assets:Cash          -100 USD

2024-01-20 * "Reimbursement received"
  Assets:Bank           100 USD
  Assets:Reimbursable  -100 USD
; These two postings match and are linked
```

Options: `"Account:Pattern days"` - Account pattern to match and maximum days between matching postings

## Custom Plugins

For custom functionality, you can write plugins in two ways:

### WASM Plugins (Recommended)

Write plugins in Rust, compile to WebAssembly, and use them without modifying rustledger.

**Quick start:**

```bash
# Clone the template
git clone https://github.com/rustledger/rustledger
cp -r rustledger/examples/wasm-plugin-template my-plugin
cd my-plugin

# Build
rustup target add wasm32-unknown-unknown
cargo build --target wasm32-unknown-unknown --release

# Use in your beancount file
# plugin "/path/to/target/wasm32-unknown-unknown/release/my_plugin.wasm"
```

See the [Custom Plugins Guide](../guides/custom-plugins.md) for a complete walkthrough.

### Native Rust Plugins (Contributors)

For adding plugins to rustledger itself, see [Contributing Plugins](../development/contributing-plugins.md).

## Python Plugin Compatibility

::: warning Experimental Feature
Python plugin support is experimental and significantly slower than native plugins (10-100x). Use native equivalents when available.
:::

rustledger can run some Python beancount plugins using CPython compiled to WebAssembly (WASI). This is primarily for migration purposes.

### Supported Python Plugins

Most Python beancount plugins have native equivalents:

| Python Plugin | rustledger Equivalent |
|---------------|----------------------|
| `auto_accounts` | ✅ `auto_accounts` |
| `implicit_prices` | ✅ `implicit_prices` |
| `check_commodity` | ✅ `check_commodity` |
| `leafonly` | ✅ `leafonly` |
| `noduplicates` | ✅ `noduplicates` |
| `onecommodity` | ✅ `onecommodity` |
| `sellgains` | ✅ `sellgains` |
| `split_expenses` | ✅ `split_expenses` |
| `close_tree` | ✅ `close_tree` |
| `coherent_cost` | ✅ `coherent_cost` |
| `pedantic` | ✅ `pedantic` |
| `unique_prices` | ✅ `unique_prices` |
| `forecast` (beanahead) | ✅ `forecast` |
| `effective_date` | ✅ `effective_date` |
| `zerosum` | ✅ `zerosum` |
| `unrealized` | ✅ `unrealized` |
| `rename_accounts` | ✅ `rename_accounts` |
| Custom Python | Rewrite in Rust |

### Python Plugin Limitations

- **Performance**: 10-100x slower than native plugins
- **First run**: Downloads ~14MB CPython-WASI runtime
- **Compilation**: First execution compiles WASM (~30 seconds)
- **Not all plugins work**: C extensions and some stdlib modules unavailable
- **Debugging**: Error messages may be less helpful

### Migrating from Python Plugins

1. Check if a native equivalent exists (see table above)
1. If not, consider writing a [WASM plugin](../guides/custom-plugins.md)
1. As a last resort, Python plugins may work but with limitations

## See Also

- [Custom Plugins Guide](../guides/custom-plugins.md) - Writing WASM plugins
- [Contributing Plugins](../development/contributing-plugins.md) - Adding native plugins
- [check command](../commands/check.md) - Running validation
- [Migration](../migration/from-beancount.md) - Python plugin migration
