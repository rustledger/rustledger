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
│  │  (31 plugins)│ │ (Wasmtime)  │ │(CPython-WASI)│      │
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

rustledger includes 32 native plugins. Here are the most commonly used:

### Validation Plugins

| Plugin | Description |
|--------|-------------|
| `check_average_cost` | Validate sales use correct average cost |
| `check_closing` | Zero balance assertion on posting with `closing: TRUE` |
| `check_commodity` | Ensure commodities are declared |
| `check_drained` | Zero balance assertion on balance sheet account close |
| `check_option_expiry` | Error on option contracts open past expiry |
| `coherent_cost` | A currency is held at cost everywhere or nowhere |
| `commodity_attr` | Validate commodity metadata attributes |
| `leafonly` | Restrict postings to leaf accounts |
| `noduplicates` | Detect duplicate directives |
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
<summary>Complete list of 32 native plugins</summary>

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
| `check_option_expiry` | Error on option contracts open past expiry |
| `close_tree` | Close descendant accounts |
| `coherent_cost` | Held at cost everywhere or nowhere |
| `commodity_attr` | Validate commodity attributes |
| `currency_accounts` | Auto-generate currency trading postings |
| `document_discovery` | Auto-discover documents from directories |
| `effective_date` | Override posting date via metadata |
| `forecast` | Generate recurring transactions |
| `generate_base_ccy_prices` | Create base currency price entries |
| `implicit_prices` | Generate prices from costs |
| `leafonly` | Error on non-leaf account postings |
| `noduplicates` | Detect duplicate directives |
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

Automatically generates `Open` directives for any account a transaction, balance, pad, note, document or close names without one, dated at its first use.

```beancount
plugin "beancount.plugins.auto_accounts"

; No need for explicit Open directives
2024-01-15 * "Coffee"
  Expenses:Food:Coffee   5.00 USD
  Assets:Cash           -5.00 USD
```

Options: None

### check_commodity

Ensures all commodities are explicitly declared. Each undeclared currency is one error, `Missing Commodity directive for 'USD' in 'Assets:Bank'`, naming the first account (in sorted order) that uses it in a posting's units, cost or price, a `balance`, or an `open`'s currency list, or `Price Directive Context` when only `price` directives use it.

```beancount
plugin "beancount.plugins.check_commodity"

2020-01-01 commodity USD
2020-01-01 commodity AAPL
```

Options: optionally a Python dict of account regex to currency regex, as in beancount: a currency matching the second in an account matching the first (both matched at the start) is exempt, and so are its prices.

```beancount
plugin "beancount.plugins.check_commodity" "{'Assets:Options:.*': 'SPX_.*'}"
```

### coherent_cost

Checks that each currency is held either always at cost or never at cost. A currency some posting holds at cost (`{...}`) and another holds without one is an error, `Currency 'HOOL' is used both with and without cost`, located at the first transaction holding it without cost.

```beancount
plugin "beancount.plugins.coherent_cost"
```

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

Restricts postings to leaf accounts only. Reports an error if you post to an account that has sub-accounts: one per account, `Non-leaf account 'Expenses' has postings on it`, at its `open`. A `pad` counts as posting to both its accounts.

Unlike beancount, a `note`, `document`, `close` or `custom` naming a parent account is not reported: none of them posts anything.

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

Detects duplicate directives of every type but `price`, as beancount's does. Two directives are duplicates when every field but their metadata is equal: a transaction's flag, payee, narration, tags, links and postings; an `open`'s account, currencies and booking method; a `balance`'s account, amount and tolerance; a `note`'s or `document`'s account, text or path, tags and links; and so on. Tags, links, an `open`'s currencies, a `custom` directive's values and a transaction's postings are compared without regard to order, and a total price is compared as the per-unit price it stands for (`2 HOOL @@ 10 USD` is `2 HOOL @ 5 USD`). Numbers keep their scale (`10 USD` is not `10.00 USD`), as in beancount. A repeated `price` is allowed: a price source commonly repeats one for a day the market was closed. Each later copy is an error at the copy, naming it: `Duplicate entry: 2024-01-02 "Lunch"` for a transaction, `Duplicate entry: 2024-01-04 note Assets:Bank "hello"` for another directive.

Deliberate differences from beancount, which hashes the text of each field: beancount follows `Duplicate entry:` with both entries' Python representations; it does not compare the directive's type, so an `event "a" "b"` and a `query "a" "b"` on one date are duplicates there and not here; and it rounds the division of a total price or total cost to 28 digits, so `3 HOOL @@ 10 USD` is a duplicate of `3 HOOL @ 3.333333333333333333333333333 USD` there, while here a total that the per-unit number does not multiply back to exactly is compared as written.

```beancount
plugin "beancount.plugins.noduplicates"
```

Options: None

### onecommodity

Ensures each account only holds one commodity: its postings' and `balance` assertions' units in one currency, and its costs in one currency. An account with more is one error, `More than one currency in account 'Assets:Bank': EUR,USD` (or `More than one cost currency ...`), at the last entry that added a currency. An account whose `open` lists more than one currency, or has `onecommodity: FALSE`, is skipped.

```beancount
plugin "beancount.plugins.onecommodity"

2020-01-01 open Assets:Bank:USD   USD
2020-01-01 open Assets:Bank:EUR   EUR
```

Options: optionally a regular expression: only accounts whose `open` it matches (at the start) are checked.

### pedantic

Runs every pedantic plugin, as beancount's does, in its order: `check_commodity`, `coherent_cost`, `leafonly`, `noduplicates`, `nounused`, `onecommodity`, `sellgains`, `unique_prices`, then `check_drained`, each without a config.

```beancount
plugin "beancount.plugins.pedantic"
```

Options: None

### sellgains

Cross-checks a sale's proceeds against its price. For a transaction whose postings at cost all have a price, the priced value of those postings must match the weight of the transaction's Assets, Liabilities, Equity and Expenses postings (Income, the gain, is left out), within twice the transaction's tolerance. This catches a typo in the proceeds when the gain is elided. The tolerance uses beancount's default tolerance options (`inferred_tolerance_default` and the other tolerance options are not passed to plugins), and, unlike beancount's, counts the precision of a posting booking interpolated.

```beancount
plugin "beancount.plugins.sellgains"

2024-01-15 * "Sell AAPL"
  Assets:Brokerage  -10 AAPL {150.00 USD} @ 175.00 USD
  Assets:Cash       1760.00 USD
  Income:CapitalGains
; Error: Invalid price vs. proceeds/gains: (1750.00 USD) vs. (1760.00 USD); difference: (-10.00 USD)
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

Ensures prices of one commodity pair on one day agree. Prices that disagree are one error, `Disagreeing price entries`; a repeated price with the same value is allowed, as in beancount.

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

For accounts opened with the `NONE` booking method, checks that each reducing posting's cost is within the tolerance of the account's average cost before it. The average is of what the account holds, each sale included at the cost it was booked at, as beancount keeps it. Reports beancount's error at the transaction.

```beancount
plugin "beancount.plugins.check_average_cost" "0.01"

; Buy 10 @ $100, then 10 @ $120 -> average = $110
; Selling at $100 cost:
; Error: Cost basis on reducing posting is too far from the average cost (100 vs. 110)
```

Options: Tolerance as a Python float (default: `0.01` = 1%); anything else is an error.

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

Inserts zero balance assertions when a posting has a truthy `closing` metadata value (`TRUE`, a non-empty string, a non-zero number or amount), and removes the `closing` key from the posting. The assertion is dated one day after the transaction.

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

### check_option_expiry

Reports an error for each option contract whose net position in an account is non-zero after its expiry date. Contracts are recognized by their OCC symbol with spaces removed: a root of 1–6 characters, the expiry as `YYMMDD`, `C` or `P`, and the strike × 1000 as 8 digits (`AAPL261016P00230000` is the AAPL 2026-10-16 230 put). Other commodities are ignored.

"Today" is the date of the last directive in the ledger, so the check is deterministic. A close dated on the expiry day is accepted, and a ledger that ends on or before expiry is not reported. The plugin only reports; it never inserts or changes directives.

```beancount
plugin "check_option_expiry"

2026-01-01 open Assets:Broker:Cash USD
2026-01-01 open Assets:Broker:Options

2026-09-02 * "Sell to open 1 AAPL 2026-10-16 230 put"
  Assets:Broker:Options  -1 AAPL261016P00230000 {250.00 USD}
  Assets:Broker:Cash     250.00 USD

2026-10-20 balance Assets:Broker:Cash 250.00 USD
; Error: AAPL261016P00230000 expired 2026-10-16 but -1 contract(s) remain open in Assets:Broker:Options
```

This plugin is native to rustledger and has no Python beancount equivalent, so a `plugin` directive for it makes the file fail in Python beancount. To keep the file portable, enable it on the command line instead: `rledger check --native-plugin check_option_expiry ledger.beancount`.

Options: None

### commodity_attr

Validates that Commodity directives have required metadata attributes.

```beancount
plugin "beancount.plugins.commodity_attr" "{'name': None, 'sector': ('Tech', 'Finance', 'Healthcare')}"

2024-01-01 commodity AAPL
  name: "Apple Inc"
  sector: "Tech"
```

Options: Python dict where:

- Keys are attribute names
- `None` means required but any value allowed (`null` is accepted too)
- a tuple, list or set such as `('a', 'b')` means required and must be one of the listed values

A missing attribute is `Missing attribute 'name' for Commodity directive AAPL`, and a value not listed is `Invalid value 'x' for attribute sector, Commodity directive AAPL; valid options: Tech, Finance, Healthcare`, each at the `commodity` directive.

### currency_accounts

Automatically generates currency conversion postings through trading accounts when transactions involve multiple currencies.

```beancount
plugin "beancount.plugins.currency_accounts"

2024-01-15 * "Buy EUR"
  Assets:Bank:EUR    100 EUR @ 1.10 USD
  Assets:Bank:USD   -110 USD
; Generates postings through Equity:CurrencyAccounts:EUR and Equity:CurrencyAccounts:USD
```

Options: The base account (default `Equity:CurrencyAccounts`; a value that is not a valid account name falls back to it; beancount 3's plugin fails without a config, rledger's uses the default). A processed transaction is marked `currency_accounts_processed: TRUE`.

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

Reports an error, at its `open`, for each account that is opened but never named by any other directive (a transaction, balance, pad, note, document or close). Unlike beancount's, an account named only by a `custom` directive counts as used.

```beancount
plugin "beancount.plugins.nounused"

2024-01-01 open Assets:OldAccount
; Error: Unused account 'Assets:OldAccount'
```

Options: None

### rename_accounts

Renames accounts using regex patterns. Useful for bulk account reorganization.

```beancount
plugin "beancount.plugins.rename_accounts" "{'Expenses:Food:(.*)': 'Expenses:Dining:\\\\1'}"

2024-01-01 open Expenses:Food:Groceries
; Becomes: 2024-01-01 open Expenses:Dining:Groceries
```

Options: Python dict mapping regex patterns to replacement strings, applied as Python's `re.sub` applies them: every match anywhere in the account name is replaced, and the replacement refers to a group as `\1` or `\g<name>` (`$1` is literal text). The beancount string and the Python string literal each consume one level of backslashes, so `\1` is written `\\\\1` in the file (or `r'...\\1'` with a raw Python string).

Regular expressions in plugin configs (`rename_accounts`, `check_commodity`, `onecommodity`, `long_short`, `gain_loss`) are read as Python's `re` reads them. A construct Python supports and rledger cannot express (lookahead and lookbehind, backreferences, conditional and atomic groups, possessive quantifiers, `\N{...}`, the `(?a)` and `(?x)` flags, and the word boundaries `\b` and `\B`) is reported as an error naming the plugin and the construct, never matched differently. So is a `rename_accounts` pattern that can match the empty string, or that repeats something able to match empty: Python's `re.sub` substitutes those differently. With `(?i)`, case-insensitive matching of non-ASCII characters follows Unicode simple case folding, which differs from Python's for a few characters (Python matches `i` with the dotless `ı`).

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

::: tip Needs the plugin runtimes
WASM plugins, Python plugins and WASM importers run in builds with the plugin runtimes: `cargo install rustledger` and source builds. Release binaries (GitHub Releases, Homebrew, Scoop, `cargo binstall`) leave them out on purpose and report an error naming `cargo install rustledger`. See [Plugin Runtimes](../getting-started/installation.md#plugin-runtimes). Built-in native plugins run in every build.
:::

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

Python plugins need a build with the plugin runtimes: `cargo install rustledger` or a source build. Release binaries leave them out; see [Plugin Runtimes](../getting-started/installation.md#plugin-runtimes).

### Referencing a Python Plugin

How a plugin name resolves depends on whether it matches a built-in:

- **Built-in name → native implementation.** If the name matches a built-in plugin, rustledger runs the native Rust version, regardless of the `beancount.plugins.` prefix. So `plugin "beancount.plugins.auto_accounts"` "just works" — it resolves to the native `auto_accounts`, _not_ to Python. (See [Supported Python Plugins](#supported-python-plugins).)

- **Custom Python plugin → file path required.** A plugin with no native equivalent must be referenced by **file path**, not by module name. beancount's `plugin "mypackage.mymodule"` form is **not** supported:

  ```beancount
  ; ❌ Not supported — module names do not resolve to the host environment
  plugin "mypackage.mymodule"

  ; ✅ Reference the file directly (absolute, or relative to the ledger)
  plugin "/abs/path/to/mymodule.py"
  plugin "./plugins/mymodule.py"
  ```

  Referencing a custom plugin by module name fails with `… is not supported by module name; reference the file directly: plugin "…"`. This is intentional: rustledger does not search the system Python path, keeping it explicit which plugins still need native Rust implementations.

### Entry Points: `__plugins__`

rustledger runs a Python plugin file the way beancount's loader runs a plugin module: it calls the functions the module's `__plugins__` lists, in order, each on the entries the previous one returned.

```python
__plugins__ = ['add_tag', check]   # a name, or the function itself

def add_tag(entries, options_map):
    ...
    return entries, errors

def check(entries, options_map, config):   # config: the directive's string
    ...
    return entries, errors
```

Each function is called with `(entries, options_map)`, plus the config string when the `plugin` directive has one (`plugin "./my_plugin.py" "config"`). An exception in one function is reported as an error, and the next function gets the entries as they were before it, as in beancount.

Two cases are reported where beancount is silent or crashes:

- **No `__plugins__`**: nothing runs (beancount skips such a module silently), and rustledger warns that the plugin ran nothing, since that is almost always a forgotten line rather than a plugin meant to do nothing. A function merely named `plugin` is not an entry point.
- **A listed name the module does not define**: an error naming it, and nothing in the module runs (beancount aborts the whole load with an `AttributeError`).

### The Plugin Sandbox: Plugins Must Be Self-Contained

Python plugins run in a pinned CPython-WASI sandbox (wasmtime). On `sys.path` it sees only:

- the **plugin source file**, plus a bundled `beancount.core.data` **compatibility shim**, and
- the **bundled CPython standard library**.

The plugin sees exactly one directory, read-only: `/lib` (the standard library). Its inputs (the entries, options and config) reach it from memory, so nothing of the ledger is written to disk while it runs, and an interrupted run (Ctrl-C) leaves nothing behind. It cannot write files, read the ledger's directory or anything else of the host, or open network connections. What it prints goes to rledger's stderr (up to 4 MiB); its result travels back separately, so a `print` cannot corrupt it.

The host's virtualenv / `site-packages` is **never** mounted — there is no `VIRTUAL_ENV` or `site-packages` handling, by design (the sandbox has no host filesystem access). So even with the correct file-path reference, a plugin only loads if it is **self-contained**: standard library plus whatever the compat shim provides.

The compat shim covers the common beancount plugin surface — the `beancount.core.data` namedtuples (`Transaction`, `Posting`, `Amount`, `Open`, `Close`, `Balance`, `Price`, `Custom`, `Cost`, …), `data.new_metadata` and `data.filter_txns`, `amount.CURRENCY_RE`, the `beancount.core.{getters,flags}` helpers, `beancount.core.realization` (the account tree: `realize(entries, compute_balance=False)`, `iter_children`, `get`, `get_or_create`, `contains`, `postings_by_account`, `RealAccount`) and `beancount.core.compare` (`hash_entry`, `hash_entries`, `compare_entries`, `includes_entries`, `excludes_entries`), so beancount's own `leafonly` and `noduplicates` run unchanged. Entries carry their metadata, including `filename` and `lineno`, as in beancount, and an error a plugin returns (any object with `message` and `source`, such as a beancount-style namedtuple) is reported at its entry's location. Modules the shim does not provide, such as `beancount.core.inventory`, fail with an `ImportError` naming them; `realize` with balances (its default, `compute_balance=True`) needs that module, so it raises `NotImplementedError` saying to pass `compute_balance=False`. A plugin that imports third-party packages, C extensions, or unbundled stdlib modules will not load — rewrite it as a [native Rust plugin](../guides/custom-plugins.md) instead.

### Built-in Python Plugins

`check_commodity` and `leafonly` also have Python implementations that behave as beancount's do (same checks, same messages). `plugin "python:leafonly"` (or `"python:beancount.plugins.leafonly"`) runs that instead of the native plugin. `python:` before any other bare name is refused, like a module name; before a file path, it runs the file in Python.

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
- **Time budget**: each call has the same time budget as a WASM plugin (30 seconds by default), of which starting the interpreter takes about 1.2; a plugin over a very large ledger can need more. See [Plugin Time Budget](../getting-started/configuration.md#plugin-time-budget)
- **Memory**: the interpreter, and every entry as Python objects (about 1.2 KB per transaction), must fit in the sandbox memory cap, 256 MiB by default, which holds roughly 150,000 transactions. Raise it with `[plugins] max_memory_mb` or `--plugin-max-memory-mb`. See [Plugin Memory Cap](../getting-started/configuration.md#plugin-memory-cap)
- **Other resources**: a plugin may hold at most 256 open files and pending polls (`select`) at once; it is stopped when it runs past its time budget on the clock, including time spent sleeping
- **Not all plugins work**: C extensions and some stdlib modules unavailable
- **File-path references only**: custom Python plugins must be referenced by file path and be self-contained — see [Referencing a Python Plugin](#referencing-a-python-plugin)
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
