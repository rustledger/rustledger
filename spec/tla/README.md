# TLA+ Specifications

This directory contains TLA+ formal specifications for critical rustledger algorithms.

## Files

| File | Description |
|------|-------------|
| `Inventory.tla` | Inventory data structure and operations |
| `BookingMethods.tla` | FIFO, LIFO, HIFO, STRICT, NONE booking algorithms |
| `TransactionBalance.tla` | Transaction balancing and interpolation |
| `*.cfg` | TLC model checker configuration files |
| `ROADMAP.md` | Plan for expanding TLA+ coverage to stellar level |

## Quick Start

### Using Just (Recommended)

```bash
# Run all TLA+ specifications
just tla-all

# Run a specific spec
just tla-inventory
just tla-booking
just tla-balance

# Run any spec by name
just tla-check Inventory
```

### Using TLC Directly

```bash
# Download TLA+ tools (one-time)
wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar

# Run model checker
java -jar tla2tools.jar -config Inventory.cfg Inventory.tla
```

### Using TLA+ Toolbox (GUI)

Download from: https://lamport.azurewebsites.net/tla/toolbox.html

Or use the VS Code extension: https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus

## Why TLA+?

These algorithms have subtle invariants that are easy to violate:

1. **Inventory**: Units must never go negative (except NONE booking)
2. **Booking**: FIFO must always select oldest, LIFO newest, HIFO highest cost, STRICT must reject ambiguity
3. **Balancing**: Transactions must balance per-currency within tolerance

TLA+ lets us:
- Formally specify the expected behavior
- Model check against all possible inputs (within bounds)
- Verify invariants hold in all states
- Generate counterexamples when they don't

## Configuration Files

Each `.tla` file has a corresponding `.cfg` file for TLC model checking:

```
# Inventory.cfg
CONSTANTS
    Currencies = {"USD", "AAPL", "GOOG"}
    MaxUnits = 50
    MaxPositions = 4

INVARIANTS
    Invariant
    TypeOK
```

## Key Invariants

### Inventory.tla

```tla
NonNegativeUnits ==
    \A curr \in Currencies :
        ~(\E op \in Range(operations) : op.type = "reduce_none")
        => TotalUnits(inventory, curr) >= 0
```

### BookingMethods.tla

```tla
\* FIFO always takes from oldest lot
FIFOProperty ==
    \A i \in 1..Len(history) :
        history[i].method = "FIFO" =>
            history[i].from_lot = Oldest(MatchingAtTime(i))

\* HIFO always takes from highest cost lot (tax optimization)
HIFOProperty ==
    \A i \in 1..Len(history) :
        history[i].method = "HIFO" =>
            history[i].from_lot = HighestCost(MatchingAtTime(i))
```

### TransactionBalance.tla

```tla
BalancedMeansZero ==
    state = "balanced" =>
        \A curr \in AllCurrencies(transaction) :
            Abs(WeightSum(transaction, curr)) <= Tolerance
```

## Translating to Rust

The TLA+ specs guide implementation. For example, `ReduceFIFO` in TLA+:

```tla
ReduceFIFO(units, spec) ==
    /\ LET matches == Matching(spec)
           oldest == Oldest(matches)
       IN ...
```

Becomes in Rust:

```rust
fn reduce_fifo(&mut self, units: Decimal, spec: &CostSpec) -> Result<...> {
    let mut matches: Vec<_> = self.matching(spec).collect();
    matches.sort_by_key(|p| p.cost.as_ref().map(|c| c.date));

    let oldest = matches.first().ok_or(BookingError::NoMatch)?;
    // ...
}
```

## CI Integration

TLA+ specifications are automatically checked on PRs that modify:
- `spec/tla/**` - TLA+ specs themselves
- `crates/rustledger-core/src/inventory.rs` - Inventory implementation
- `crates/rustledger-booking/src/**` - Booking implementation

See `.github/workflows/tla.yml` for details.

## Limitations

TLA+ model checking is bounded:
- We check with small `MaxLots`, `MaxUnits` values
- Exhaustive for those bounds, but not proof of correctness for all sizes
- For true proofs, would need TLAPS (TLA+ Proof System)

For our purposes, model checking with reasonable bounds (3-5 lots, 10-20 units) catches most bugs.

## Roadmap

See `ROADMAP.md` for the plan to expand TLA+ coverage including:
- AVERAGE and STRICT_WITH_SIZE booking methods
- Account lifecycle specification
- Validation error codes
- TLAPS proofs for critical invariants

## References

- [TLA+ Home](https://lamport.azurewebsites.net/tla/tla.html)
- [Learn TLA+](https://learntla.com/)
- [TLA+ Video Course](https://lamport.azurewebsites.net/video/videos.html)
- [Specifying Systems (book)](https://lamport.azurewebsites.net/tla/book.html)
