# Decimal Arithmetic and Precision Specification

This document specifies decimal number handling, precision rules, and tolerance calculations.

## Why Decimals, Not Floats

Financial calculations require **exact decimal arithmetic**. Floating point (IEEE 754) cannot exactly represent values like `0.1`:

```
0.1 + 0.2 = 0.30000000000000004  // IEEE 754 float
0.1 + 0.2 = 0.3                   // Decimal
```

We use `rust_decimal` crate which provides 128-bit decimal representation.

## Decimal Representation

### rust_decimal Internals

```rust
// 96-bit mantissa + 8-bit scale + 1-bit sign
struct Decimal {
    // Stored as: mantissa / 10^scale
    lo: u32,
    mid: u32,
    hi: u32,
    flags: u32,  // Contains scale (0-28) and sign
}
```

- **Precision**: Up to 28-29 significant digits
- **Scale**: 0-28 decimal places
- **Range**: ±79,228,162,514,264,337,593,543,950,335

### Beancount Number Syntax

```
number      = integer | decimal
integer     = ["-"] digits
decimal     = ["-"] digits "." digits
            | ["-"] "." digits
digits      = digit+
            | digit{1,3} ("," digit{3})+
digit       = "0" | "1" | ... | "9"
```

Examples:
```
100           → Decimal(100, scale=0)
100.00        → Decimal(10000, scale=2)
0.123456789   → Decimal(123456789, scale=9)
1,234,567.89  → Decimal(123456789, scale=2)
.50           → Decimal(50, scale=2)
-.50          → Decimal(-50, scale=2)
```

## Precision Inference

The **scale** (decimal places) of a number is inferred from its textual representation:

```rust
fn infer_scale(text: &str) -> u32 {
    match text.find('.') {
        Some(pos) => (text.len() - pos - 1) as u32,
        None => 0,
    }
}
```

| Input | Scale | Decimal Value |
|-------|-------|---------------|
| `100` | 0 | 100 |
| `100.0` | 1 | 100.0 |
| `100.00` | 2 | 100.00 |
| `0.001` | 3 | 0.001 |

**Scale matters for tolerance calculation** (see below).

## Arithmetic Operations

### Addition / Subtraction

Result scale is maximum of operand scales:

```
100.00 + 0.5 = 100.50  (scale 2)
1.1 - 0.111 = 0.989    (scale 3)
```

### Multiplication

Result scale is sum of operand scales (then normalized):

```
10.00 × 5.5 = 55.000   (scale 2+1=3, may normalize to 55)
```

### Division

Division may produce non-terminating decimals. We use **banker's rounding** (round half to even) with configurable precision:

```rust
const DIVISION_SCALE: u32 = 12;  // Internal precision for division

fn divide(a: Decimal, b: Decimal) -> Decimal {
    a.checked_div(b)
        .map(|r| r.round_dp_with_strategy(DIVISION_SCALE, RoundingStrategy::MidpointNearestEven))
        .expect("division by zero")
}
```

## Tolerance Calculation

Tolerances determine when values are "close enough" to be considered equal.

### Inferred Tolerance

Tolerance is inferred from the **least precise** amount in a transaction:

```rust
fn infer_tolerance(amounts: &[Amount]) -> HashMap<Currency, Decimal> {
    let mut tolerances = HashMap::new();

    for amount in amounts {
        let scale = amount.number.scale();
        // Tolerance = 0.5 × 10^(-scale)
        // e.g., scale=2 → 0.005
        let tolerance = Decimal::new(5, scale + 1);

        tolerances
            .entry(amount.currency.clone())
            .and_modify(|t| *t = (*t).max(tolerance))
            .or_insert(tolerance);
    }

    tolerances
}
```

| Amount Scale | Tolerance |
|--------------|-----------|
| 0 (integer) | 0.5 |
| 1 | 0.05 |
| 2 | 0.005 |
| 3 | 0.0005 |

### Tolerance Multiplier

The `inferred_tolerance_multiplier` option (default: 0.5) scales inferred tolerances:

```rust
let tolerance = base_tolerance * options.inferred_tolerance_multiplier;
```

### Explicit Tolerance

Balance assertions can specify explicit tolerance:

```beancount
2024-01-01 balance Assets:Checking  1000.00 USD ~ 0.01
```

### Tolerance from Cost

When `infer_tolerance_from_cost` is enabled (default: true), cost currencies expand tolerance:

```beancount
2024-01-01 * "Buy"
  Assets:Stock  10 AAPL {150.00 USD}  ; USD gets tolerance from 150.00
  Assets:Cash  -1500.00 USD
```

The 2-decimal-place cost (150.00) contributes 0.005 tolerance to USD.

## Comparison Operations

### Equality

Two decimals are equal if their values are identical (scale-independent):

```rust
Decimal::new(100, 0) == Decimal::new(10000, 2)  // 100 == 100.00 → true
```

### Near-Equality (Tolerance Check)

```rust
fn near_equal(a: Decimal, b: Decimal, tolerance: Decimal) -> bool {
    (a - b).abs() <= tolerance
}
```

### Ordering

Standard numeric ordering. Scale does not affect ordering:

```rust
Decimal::new(100, 0) < Decimal::new(10001, 2)  // 100 < 100.01 → true
```

## Rounding Strategies

### Banker's Rounding (Default)

Round half to nearest even (reduces cumulative bias):

```
0.5   → 0    (round to even)
1.5   → 2    (round to even)
2.5   → 2    (round to even)
3.5   → 4    (round to even)
0.25  → 0.2  (round to even at scale 1)
0.35  → 0.4  (round to even at scale 1)
```

### When Rounding Occurs

1. **Division** - Internal divisions rounded to 12 decimal places
2. **Display** - Numbers formatted to original scale
3. **Never for storage** - Full precision preserved in memory

## Edge Cases

### Very Large Numbers

```beancount
2024-01-01 * "National debt"
  Assets:Government  28,000,000,000,000.00 USD
  Liabilities:Bonds
```

Supported up to ~10^28.

### Very Small Numbers

```beancount
2024-01-01 * "Satoshis"
  Assets:Bitcoin  0.00000001 BTC
  Assets:Cash
```

Supported up to 28 decimal places.

### Repeating Decimals

```beancount
2024-01-01 * "Split three ways"
  Expenses:Dinner  33.33 USD
  Expenses:Dinner  33.33 USD
  Expenses:Dinner  33.34 USD  ; Must manually adjust
  Assets:Cash  -100.00 USD
```

No automatic handling of repeating decimals. User must round explicitly.

### Arithmetic Expressions

Beancount supports expressions in amounts:

```beancount
2024-01-01 * "With expression"
  Assets:Cash  (100.00 / 3) USD   ; = 33.333... USD
  Expenses:Food
```

Division in expressions follows the same rounding rules.

## Implementation Notes

### Parsing

```rust
fn parse_number(text: &str) -> Result<Decimal, ParseError> {
    // Remove commas
    let cleaned = text.replace(",", "");

    // Parse with rust_decimal
    Decimal::from_str(&cleaned)
        .map_err(|e| ParseError::InvalidNumber(text.to_string(), e))
}
```

### Serialization

For WASM boundary and caching, decimals serialize as strings to preserve scale:

```rust
#[derive(Serialize, Deserialize)]
struct SerializedDecimal(String);

impl From<Decimal> for SerializedDecimal {
    fn from(d: Decimal) -> Self {
        SerializedDecimal(d.to_string())
    }
}
```

### Display

```rust
fn format_amount(amount: &Amount) -> String {
    format!("{} {}", amount.number, amount.currency)
}

// Options for display
struct FormatOptions {
    render_commas: bool,      // 1,234.56 vs 1234.56
    min_scale: Option<u32>,   // Minimum decimal places
}
```

## Testing Decimal Handling

### Property Tests

```rust
#[proptest]
fn addition_commutative(a: Decimal, b: Decimal) {
    prop_assert_eq!(a + b, b + a);
}

#[proptest]
fn tolerance_symmetric(a: Decimal, b: Decimal, tol: Decimal) {
    prop_assert_eq!(
        near_equal(a, b, tol),
        near_equal(b, a, tol)
    );
}

#[proptest]
fn parse_roundtrip(d: Decimal) {
    let text = d.to_string();
    let parsed = parse_number(&text).unwrap();
    prop_assert_eq!(d, parsed);
}
```

### Edge Case Tests

```rust
#[test]
fn test_tolerance_inference() {
    assert_eq!(infer_tolerance_scale(0), dec!(0.5));
    assert_eq!(infer_tolerance_scale(1), dec!(0.05));
    assert_eq!(infer_tolerance_scale(2), dec!(0.005));
}

#[test]
fn test_large_numbers() {
    let large = dec!(999_999_999_999_999_999.99);
    assert!(large.checked_add(dec!(0.01)).is_some());
}

#[test]
fn test_bankers_rounding() {
    assert_eq!(dec!(0.5).round(), dec!(0));
    assert_eq!(dec!(1.5).round(), dec!(2));
    assert_eq!(dec!(2.5).round(), dec!(2));
}
```
