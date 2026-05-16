# rustledger-core

Core types for the rustledger Beancount implementation.

## Key Types

| Type | Description |
|------|-------------|
| `Amount` | Decimal number with currency (e.g., `100.00 USD`) |
| `Position` | Units held at a specific cost |
| `Inventory` | Collection of positions with booking support |
| `Cost` | Acquisition cost of a lot |
| `CostSpec` | Specification for matching or creating costs |
| `BookingMethod` | Lot matching strategy (FIFO, LIFO, HIFO, etc.) |
| `Directive` | All directive types (Transaction, Balance, Open, etc.) |

## Example

```rust
use rustledger_core::{Amount, Cost, Position, Inventory, BookingMethod, naive_date};
use rust_decimal_macros::dec;

let mut inv = Inventory::new();

// Add a stock position
let cost = Cost::new(dec!(150.00), "USD")
    .with_date(naive_date(2024, 1, 15).unwrap());
inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost));

// Sell using FIFO
let result = inv.reduce(
    &Amount::new(dec!(-5), "AAPL"),
    None,
    BookingMethod::Fifo,
).unwrap();

assert_eq!(inv.units("AAPL"), dec!(5));
```

## Features

- `rkyv` (default) - Enable rkyv serialization for binary caching

## License

GPL-3.0
