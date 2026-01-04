# Beancount Inventory and Booking Specification

## Core Concepts

### Positions and Lots

A **Position** represents units of a commodity with optional acquisition metadata:
- **Units**: The quantity of the commodity (Decimal + Currency)
- **Cost**: Per-unit acquisition cost (cost basis)
- **Date**: Acquisition date (defaults to transaction date)
- **Label**: Optional user-specified identifier for the lot

An **Inventory** is an accumulation of positions, represented as a list. Positions are merged only when all attributes (commodity, cost, date, label) match exactly.

### Simple vs. Cost-Basis Positions

**Simple positions** contain no cost information; the cost attribute is null. These track commodity quantities without acquisition history.

**Positions held at cost** include cost basis and acquisition details, essential for tracking investments and calculating gains.

## Augmentations and Reductions

### Augmentations (Adding to Inventory)

When adding units to an account, a new position is created with provided lot specifications:

```beancount
2015-04-01 * "Buy shares"
  Assets:Invest    25 HOOL {23.00 USD, 2015-04-01, "first-lot"}
```

The cost specification data is attached to the position and preserved indefinitely. You may specify:
- Per-unit cost and currency
- Acquisition date (overrides transaction date if provided)
- Optional label string
- Any combination of these attributes

### Reductions (Removing from Inventory)

When removing units, the cost specification acts as a filter to identify which lot(s) to reduce:

```beancount
2015-05-15 * "Sell shares"
  Assets:Invest    -12 HOOL {23.00 USD}
```

The system matches this against existing inventory positions. Matched lots are reduced; unmatched information is discarded. You may specify any subset: cost only, date only, label only, or empty `{}` for single-lot accounts.

## Matching and Ambiguity Resolution

### Match Categories

**Single match**: Exactly one position matches the reduction specification; it is reduced by the requested amount.

**Total match**: Multiple positions match, but their combined units equal the reduction request exactly. All matched positions are reduced (fully consumed).

**No match**: No position satisfies the reduction specification. An error is raised.

**Ambiguous matches**: Multiple positions match with combined units exceeding the reduction request. The booking method determines how to proceed.

## Booking Methods

The default booking method is **STRICT**, configurable globally:

```beancount
option "booking_method" "FIFO"
```

Or per-account via the Open directive:

```beancount
2016-05-01 open Assets:Invest "AVERAGE"
```

### STRICT

Raises an error when ambiguous matches occur (unless a total match exception applies). This forces explicit disambiguation in source data.

### FIFO (First-In-First-Out)

Selects oldest (earliest-dated) matching lots first until the reduction is complete. Remaining volume carries forward to newer lots.

**Algorithm:**
1. Sort matching positions by acquisition date ascending
2. Reduce from oldest lot
3. If lot fully consumed, move to next oldest
4. Repeat until reduction satisfied

### LIFO (Last-In-First-Out)

Selects newest (latest-dated) matching lots first, working backward chronologically through the inventory.

**Algorithm:**
1. Sort matching positions by acquisition date descending
2. Reduce from newest lot
3. If lot fully consumed, move to next newest
4. Repeat until reduction satisfied

### AVERAGE

Merges all units of the affected commodity and recalculates average cost basis after every reduction.

**Algorithm:**
1. Compute total units and total cost across all matching positions
2. Calculate weighted average cost = total cost / total units
3. Replace all matching positions with single position at average cost
4. Reduce from this averaged position

### NONE

Disables booking entirely. Reducing positions are appended unconditionally without matching. Results in mixed-sign inventories where "only the total number of units and total cost basis are sensible numbers." Compatible with accounts like retirement plans where lot tracking is impractical.

## Cost Specifications

### Syntax

Cost specifications appear in curly braces `{}` and may contain (in any order):
- **Amount**: `23.00 USD` — per-unit cost
- **Date**: `2015-04-25` — acquisition date
- **Label**: `"lot-id"` — user identifier

Examples:
```beancount
{23.00 USD}
{2015-04-25}
{"lot-id"}
{23.00 USD, 2015-04-25}
{2015-04-25, 23.00 USD, "lot-id"}
```

### For Augmentations

Provide lot data to create new position:
- Omitted date defaults to transaction date
- Omitted cost must be inferred from other transaction postings (interpolation)
- Omitted label remains null

### For Reductions

The specification filters inventory contents by matching against stored lot attributes:
- Only positions matching ALL specified criteria are candidates
- Empty `{}` matches any position with cost basis
- Omitted specification matches any position (including those without cost)

## Prices vs. Cost Basis

**Prices are never used by the booking algorithm.** A posting with both cost and price uses the cost to determine inventory matching and balance calculations:

```beancount
2015-05-15 * "Sell shares"
  Assets:Invest:HOOL    -12 HOOL {23.00 USD} @ 24.70 USD
  Assets:Invest:Cash     296.40 USD
```

- The cost basis (23.00 USD) drives inventory reduction
- The price (24.70 USD) serves as metadata for records
- Capital gains = (price - cost) × quantity = (24.70 - 23.00) × 12 = 20.40 USD

## Weight Calculation

The "weight" of a posting determines its contribution to transaction balance:

| Posting Type | Weight Calculation |
|--------------|-------------------|
| Amount only | units × currency |
| With price (@) | units × price |
| With cost ({}) | units × cost |
| Cost + price | units × cost (price ignored) |

## Multiple Commodities

Accounts may contain multiple commodity types simultaneously. Postings affect only their specified commodity; other holdings remain unchanged.

Mixed inventories (containing both positive and negative units of the same commodity) are only permitted under NONE booking.

## Partial Lot Reduction

When a lot is partially reduced:
1. Original position units decrease by reduction amount
2. Cost basis per unit remains unchanged
3. Position date and label remain unchanged

Example:
```
Before: 25 HOOL {23.00 USD, 2015-04-01, "first-lot"}
Reduce: -12 HOOL
After:  13 HOOL {23.00 USD, 2015-04-01, "first-lot"}
```

## Error Conditions

1. **Insufficient units**: Reduction exceeds available matching positions
2. **No matching lots**: No positions satisfy the cost specification filter
3. **Ambiguous match with STRICT**: Multiple candidates, cannot determine which to reduce
4. **Negative units**: Attempting to reduce below zero (unless NONE booking)

## Implementation Notes

### Core Types (Rust)

```rust
struct Amount {
    number: Decimal,
    currency: String,
}

struct Cost {
    number: Decimal,
    currency: String,
    date: Option<NaiveDate>,
    label: Option<String>,
}

struct CostSpec {
    number: Option<Decimal>,
    currency: Option<String>,
    date: Option<NaiveDate>,
    label: Option<String>,
}

struct Position {
    units: Amount,
    cost: Option<Cost>,
}

struct Inventory {
    positions: Vec<Position>,
}
```

### Key Operations

```rust
impl Inventory {
    /// Add units to inventory, creating new position
    fn augment(&mut self, units: Amount, cost: Option<Cost>);

    /// Reduce units from inventory using booking method
    fn reduce(
        &mut self,
        units: Amount,
        cost_spec: Option<CostSpec>,
        booking: BookingMethod
    ) -> Result<Vec<Position>, BookingError>;

    /// Get positions matching a cost specification
    fn match_positions(&self, spec: &CostSpec) -> Vec<&Position>;
}
```
