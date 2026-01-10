# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- **String interning for core types** - Account names and currency codes are now interned using `Arc<str>`, reducing memory allocations and improving comparison performance
  - New `InternedStr` type in `rustledger-core` wrapping `Arc<str>`
  - Implements `Serialize`, `Deserialize`, `Hash`, `Eq`, `Ord`, `Borrow<str>` for seamless integration
  - Automatic deduplication of identical strings across the ledger

### Changed

- `Amount.currency` now uses `InternedStr` instead of `String`
- `Cost.currency` and `CostSpec.currency` now use `InternedStr`
- All directive types (`Open`, `Close`, `Balance`, `Pad`, `Note`, `Document`, `Commodity`, `Price`) use `InternedStr` for account and currency fields
- `Posting.account` now uses `InternedStr`
- `Inventory` and related types updated to use `InternedStr` for currency keys
- Validation and query engines updated to use `InternedStr` internally

### Performance

- **Parser**: 25-40% faster parsing throughput
- **Inventory operations**:
  - FIFO/LIFO reductions: 45-58% faster
  - Cost basis calculations: 35-47% faster
  - Book value calculations: 23-46% faster
  - Position additions: 16-31% faster
- Overall memory usage reduced due to string deduplication

### Migration

Code that constructs core types directly will need minor updates:

```rust
// Before
let amount = Amount::new(dec!(100), "USD".to_string());

// After - use .into() or pass &str directly
let amount = Amount::new(dec!(100), "USD");
```

The `.into()` conversion is automatically available for `&str`, `String`, and `&String`.
