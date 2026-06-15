# rustledger-booking

Beancount booking engine with 7 lot matching methods and amount interpolation.

## Booking Methods

| Method | Description |
|--------|-------------|
| `STRICT` | Lots must match exactly (default) |
| `STRICT_WITH_SIZE` | Exact-size matches accept oldest lot |
| `FIFO` | First in, first out |
| `LIFO` | Last in, first out |
| `HIFO` | Highest cost first |
| `AVERAGE` | Average cost basis |
| `NONE` | No cost tracking |

## Features

- Amount interpolation for incomplete postings
- Cost basis calculation
- Lot matching with configurable strategies
- Transaction balancing

## Example

```rust
use rustledger_booking::BookingEngine;
use rustledger_core::BookingMethod;

// Using the booking engine for a single transaction
let mut engine = BookingEngine::with_method(BookingMethod::Fifo);
let result = engine.book_and_interpolate(&transaction)?;

// Using the batch function for multiple transactions
use rustledger_booking::book_transactions;
let results = book_transactions(&transactions, BookingMethod::Fifo);
for result in results {
    match result {
        Ok(booked) => { /* handle successfully booked transaction */ }
        Err(err) => { /* handle booking error */ }
    }
}
```

## License

GPL-3.0
