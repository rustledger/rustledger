# TLA+ Specifications

This directory contains TLA+ formal specifications for critical rustledger algorithms.

## Files

| File | Description |
|------|-------------|
| `Inventory.tla` | Inventory data structure and operations |
| `BookingMethods.tla` | FIFO, LIFO, STRICT, NONE booking algorithms |
| `TransactionBalance.tla` | Transaction balancing and interpolation |

## Why TLA+?

These algorithms have subtle invariants that are easy to violate:

1. **Inventory**: Units must never go negative (except NONE booking)
2. **Booking**: FIFO must always select oldest, LIFO newest, STRICT must reject ambiguity
3. **Balancing**: Transactions must balance per-currency within tolerance

TLA+ lets us:
- Formally specify the expected behavior
- Model check against all possible inputs (within bounds)
- Verify invariants hold in all states
- Generate counterexamples when they don't

## Running the Specs

### Install TLA+ Toolbox

Download from: https://lamport.azurewebsites.net/tla/toolbox.html

Or use the VS Code extension: https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus

### Model Checking

1. Open the `.tla` file in TLA+ Toolbox
2. Create a new model (Model → New Model)
3. Set constants (e.g., `Currencies = {"USD", "AAPL"}`)
4. Add invariants to check
5. Run the model checker

### Example: Checking BookingMethods

```
CONSTANTS
    Currency = "AAPL"
    CostCurrency = "USD"
    MaxLots = 3
    MaxUnits = 10

INVARIANTS
    Invariant
    TypeOK
    CostBasisTracked
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

## Limitations

TLA+ model checking is bounded:
- We check with small `MaxLots`, `MaxUnits` values
- Exhaustive for those bounds, but not proof of correctness for all sizes
- For true proofs, would need TLAPS (TLA+ Proof System)

For our purposes, model checking with reasonable bounds (3-5 lots, 10-20 units) catches most bugs.

## References

- [TLA+ Home](https://lamport.azurewebsites.net/tla/tla.html)
- [Learn TLA+](https://learntla.com/)
- [TLA+ Video Course](https://lamport.azurewebsites.net/video/videos.html)
- [Specifying Systems (book)](https://lamport.azurewebsites.net/tla/book.html)
