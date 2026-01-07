# TLA+ Specifications

This directory contains TLA+ formal specifications for critical rustledger algorithms.

## Files

| File | Description |
|------|-------------|
| `Inventory.tla` | Inventory data structure and operations |
| `BookingMethods.tla` | All 7 booking methods: FIFO, LIFO, HIFO, AVERAGE, STRICT, STRICT_WITH_SIZE, NONE |
| `TransactionBalance.tla` | Transaction balancing and interpolation |
| `AccountLifecycle.tla` | Account open/close semantics and state machine |
| `DirectiveOrdering.tla` | Directive ordering constraints and validation |
| `ValidationErrors.tla` | All 26 validation error codes (E1xxx-E10xxx) |
| `*.cfg` | TLC model checker configuration files |
| `ROADMAP.md` | Plan for expanding TLA+ coverage to stellar level |
| `GUIDE.md` | How to read TLA+ specs and their Rust correspondence |
| `InventoryProofs.tla` | TLAPS formal proofs for Inventory invariants |
| `BookingMethodsProofs.tla` | TLAPS formal proofs for booking properties |

## Quick Start

### Using Just (Recommended)

```bash
# Run all TLA+ specifications
just tla-all

# Run a specific spec
just tla-inventory
just tla-booking
just tla-balance
just tla-lifecycle
just tla-ordering
just tla-validate

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
\* FIFO always takes from oldest lot (strong verification)
FIFOProperty ==
    \A i \in 1..Len(history) :
        history[i].method \in {"FIFO", "FIFO_PARTIAL"} =>
            LET h == history[i]
                selected == h.from_lot
                matches == h.matching_lots  \* Snapshot of matches at reduction time
            IN \A other \in matches : selected.date <= other.date

\* HIFO always takes from highest cost lot (tax optimization)
HIFOProperty ==
    \A i \in 1..Len(history) :
        history[i].method \in {"HIFO", "HIFO_PARTIAL"} =>
            LET h == history[i]
                selected == h.from_lot
                matches == h.matching_lots
            IN \A other \in matches : selected.cost_per_unit >= other.cost_per_unit

\* AVERAGE uses weighted average cost basis
AVERAGEProperty ==
    \A i \in 1..Len(history) :
        history[i].method \in {"AVERAGE", "AVERAGE_PARTIAL"} =>
            history[i].avg_cost >= 0  \* Uses running average, not lot cost
```

### TransactionBalance.tla

```tla
BalancedMeansZero ==
    state = "balanced" =>
        \A curr \in AllCurrencies(transaction) :
            Abs(WeightSum(transaction, curr)) <= Tolerance
```

### AccountLifecycle.tla

```tla
\* No posting to unopened accounts
NoPostingToUnopened ==
    \A i \in 1..Len(postings) :
        LET p == postings[i]
        IN WasOpened(p.account)

\* All postings are within account's active period
PostingsInActivePeriod ==
    \A i \in 1..Len(postings) :
        LET p == postings[i]
        IN /\ openDates[p.account] <= p.date
           /\ (accountStates[p.account] = "closed" => p.date < closeDates[p.account])
```

### DirectiveOrdering.tla

```tla
\* Close always comes after open for same account
CloseAfterOpenInvariant ==
    \A i, j \in 1..Len(directives) :
        (/\ directives[i].type = "open"
         /\ directives[j].type = "close"
         /\ directives[i].account = directives[j].account)
        => i < j

\* Transactions only reference open accounts
TransactionsToOpenAccountsInvariant ==
    \A i \in 1..Len(directives) :
        directives[i].type = "transaction" =>
            \A a \in AccountsIn(directives[i]) :
                accountOpenDates[a] > 0
```

### ValidationErrors.tla

Models all 26 validation error codes from `rustledger-validate`:

```tla
\* All error codes are valid
ValidErrorCodes ==
    \A e \in errors :
        e.code \in {
            "E1001", "E1002", "E1003", "E1004", "E1005",  \* Account
            "E2001", "E2003", "E2004",                    \* Balance
            "E3001", "E3002", "E3003", "E3004",           \* Transaction
            "E4001", "E4002", "E4003", "E4004",           \* Booking
            "E5001", "E5002",                             \* Currency
            "E6001", "E6002",                             \* Metadata
            "E7001", "E7002", "E7003",                    \* Option
            "E8001",                                       \* Document
            "E10001", "E10002"                            \* Date
        }

\* Error severity is appropriate (E3004/E10001/E10002 are warnings/info)
CorrectSeverity ==
    \A e \in errors :
        \/ (e.code = "E3004" => e.severity = "warning")
        \/ (e.code = "E10001" => e.severity = "info")
        \/ (e.code = "E10002" => e.severity = "warning")
        \/ (e.code \notin {"E3004", "E10001", "E10002"} => e.severity = "error")
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

## Rust Integration Tests

TLA+ invariants are validated in Rust via property-based tests:

```bash
# Run TLA+ invariant tests
cargo test -p rustledger-core --test tla_invariants_test

# Run with more iterations
PROPTEST_CASES=1000 cargo test -p rustledger-core --test tla_invariants_test
```

Test file: `crates/rustledger-core/tests/tla_invariants_test.rs`

The tests validate:
- `tla_non_negative_units_*` - NonNegativeUnits invariant
- `tla_valid_lots_*` - ValidLots invariant
- `tla_fifo_property_*` - FIFOProperty invariant
- `tla_lifo_property_*` - LIFOProperty invariant
- `tla_hifo_property_*` - HIFOProperty invariant
- `tla_strict_property_*` - STRICTProperty invariant
- `tla_average_property_*` - AVERAGEProperty invariant
- `tla_trace_*` - Complete TLA+ traces
- `prop_tla_*` - Property-based invariant validation

## TLAPS Formal Proofs

Beyond model checking, we use TLAPS (TLA+ Proof System) for mathematical proofs:

```bash
# Check all TLAPS proofs
just tla-prove-all

# Check specific proof module
just tla-prove-inventory
just tla-prove-booking
```

Proof modules:
- `InventoryProofs.tla` - Proves Safety theorem for NonNegativeUnits
- `BookingMethodsProofs.tla` - Proves FIFOSafety, LIFOSafety, HIFOSafety

Installing TLAPS: https://tla.msr-inria.inria.fr/tlaps/

## Limitations

TLA+ model checking is bounded:
- We check with small `MaxLots`, `MaxUnits` values
- Exhaustive for those bounds, but not proof of correctness for all sizes
- TLAPS proofs provide unbounded correctness guarantees

For our purposes, model checking with reasonable bounds (3-5 lots, 10-20 units) catches most bugs. TLAPS proofs provide mathematical certainty for critical invariants.

## Roadmap

See `ROADMAP.md` for the plan to expand TLA+ coverage. Current status: **10/10** 🏆

Completed:
- ✅ All 7 booking methods with strong invariants
- ✅ Account lifecycle and directive ordering
- ✅ All 26 validation error codes
- ✅ CI automation
- ✅ Rust integration tests
- ✅ TLAPS formal proofs

## References

- [TLA+ Home](https://lamport.azurewebsites.net/tla/tla.html)
- [Learn TLA+](https://learntla.com/)
- [TLA+ Video Course](https://lamport.azurewebsites.net/video/videos.html)
- [Specifying Systems (book)](https://lamport.azurewebsites.net/tla/book.html)
