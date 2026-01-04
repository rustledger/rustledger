# Beancount Options Reference

Options are global configuration directives declared without a date:

```beancount
option "name" "value"
```

## Core Configuration

### title
- **Type:** String
- **Default:** (none)
- **Description:** The title of this ledger. Shows up in reports.

### operating_currency
- **Type:** String (repeatable)
- **Default:** (none)
- **Description:** Main currencies for reporting. Creates dedicated columns in reports. Can be specified multiple times.

```beancount
option "operating_currency" "USD"
option "operating_currency" "EUR"
```

## Account Root Names

Customize the five root account type names:

| Option | Default | Description |
|--------|---------|-------------|
| `name_assets` | "Assets" | Root name for asset accounts |
| `name_liabilities` | "Liabilities" | Root name for liability accounts |
| `name_equity` | "Equity" | Root name for equity accounts |
| `name_income` | "Income" | Root name for income accounts |
| `name_expenses` | "Expenses" | Root name for expense accounts |

Example:
```beancount
option "name_income" "Revenue"
option "name_equity" "Capital"
```

## Special Equity Accounts

Used by OPEN/CLOSE statement operators in BQL:

| Option | Default | Purpose |
|--------|---------|---------|
| `account_previous_balances` | "Opening-Balances" | Summarize prior balances |
| `account_previous_earnings` | "Earnings:Previous" | Prior retained earnings |
| `account_previous_conversions` | "Conversions:Previous" | Prior conversion residuals |
| `account_current_earnings` | "Earnings:Current" | Current period net income |
| `account_current_conversions` | "Conversions:Current" | Current conversion residuals |
| `account_rounding` | (disabled) | Accumulate rounding errors |

## Tolerance & Precision

### inferred_tolerance_default
- **Type:** Currency:Decimal mapping
- **Default:** (per-currency defaults)
- **Description:** Default tolerance when not inferrable from amounts.

```beancount
option "inferred_tolerance_default" "CHF:0.01"
option "inferred_tolerance_default" "JPY:1"
```

### inferred_tolerance_multiplier
- **Type:** Decimal
- **Default:** 1.1
- **Description:** Multiplier applied to inferred tolerances.

### infer_tolerance_from_cost
- **Type:** Boolean
- **Default:** True
- **Description:** Expand tolerance to include values inferred from cost currencies.

## Booking

### booking_method
- **Type:** String
- **Default:** "STRICT"
- **Values:** "STRICT", "FIFO", "LIFO", "AVERAGE", "NONE"
- **Description:** Default booking method for all accounts. Can be overridden per-account in `open` directive.

```beancount
option "booking_method" "FIFO"
```

## Documents

### documents
- **Type:** Path (repeatable)
- **Description:** Directory roots to search for document files.

```beancount
option "documents" "/home/user/documents/financial"
option "documents" "receipts/"
```

Document files must match pattern: `YYYY-MM-DD.description.extension`

## Rendering

### render_commas
- **Type:** Boolean
- **Default:** True
- **Description:** Include thousand separators in number output.

## Plugins

### plugin_processing_mode
- **Type:** String
- **Default:** "raw"
- **Values:** "default", "raw"
- **Description:** "default" enables built-in plugins; "raw" runs only user plugins.

## Implementation Notes

### Options Struct (Rust)

```rust
#[derive(Default)]
struct Options {
    title: Option<String>,
    operating_currencies: Vec<String>,

    // Account root names
    name_assets: String,      // default: "Assets"
    name_liabilities: String, // default: "Liabilities"
    name_equity: String,      // default: "Equity"
    name_income: String,      // default: "Income"
    name_expenses: String,    // default: "Expenses"

    // Special equity accounts
    account_previous_balances: String,
    account_previous_earnings: String,
    account_previous_conversions: String,
    account_current_earnings: String,
    account_current_conversions: String,
    account_rounding: Option<String>,

    // Tolerance
    inferred_tolerance_default: HashMap<String, Decimal>,
    inferred_tolerance_multiplier: Decimal,
    infer_tolerance_from_cost: bool,

    // Booking
    booking_method: BookingMethod,

    // Documents
    documents: Vec<PathBuf>,

    // Rendering
    render_commas: bool,

    // Plugin mode
    plugin_processing_mode: PluginProcessingMode,
}
```

### Parsing Options

Options can appear anywhere in the file (they're undated). Collect all options before processing directives:

```rust
fn parse_option(line: &str) -> Option<(String, String)> {
    // option "name" "value"
    let re = regex!(r#"option\s+"([^"]+)"\s+"([^"]*)""#);
    re.captures(line).map(|c| (c[1].to_string(), c[2].to_string()))
}
```
