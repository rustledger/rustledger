# TLA+ Specifications

This directory contains TLA+ formal specifications for critical rustledger algorithms.

## Files

| File | Description |
|------|-------------|
| `Inventory.tla` | Inventory data structure and operations |
| `InventoryTyped.tla` | Apalache-typed version with type annotations |
| `BookingMethods.tla` | All 7 booking methods: FIFO, LIFO, HIFO, AVERAGE, STRICT, STRICT_WITH_SIZE, NONE |
| `TransactionBalance.tla` | Transaction balancing and interpolation |
| `AccountLifecycle.tla` | Account open/close semantics and state machine |
| `DirectiveOrdering.tla` | Directive ordering constraints and validation |
| `ValidationErrors.tla` | Validation error detection - proves no false negatives |
| `PriceDatabase.tla` | Price lookups with triangulation and date fallback |
| `InductiveInvariants.tla` | Inductive invariants (conservation of units) |
| `*.cfg` | TLC model checker configuration files |
| `ROADMAP.md` | Plan for expanding TLA+ coverage to stellar level |
| `GUIDE.md` | How to read TLA+ specs and their Rust correspondence |
| `InventoryProofs.tla` | TLAPS formal proofs for Inventory invariants |
| `BookingMethodsProofs.tla` | TLAPS formal proofs for booking properties |
| `ValidationErrorsProofs.tla` | TLAPS formal proofs for ValidationErrors |
| `InventoryRefinement.tla` | Refinement proof: Rust Inventory → TLA+ |
| `BookingRefinement.tla` | Refinement proof: Rust booking methods → TLA+ |

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

Verifies that the validator correctly identifies ALL invalid states (no false negatives):

```tla
\* CRITICAL INVARIANT: Every invalid transaction produces appropriate errors
AllInvalidTransactionsDetected ==
    \A i \in 1..Len(ledger) :
        LET txn == ledger[i]
        IN /\ MustFireE1001(txn) => "E1001" \in validationErrors  \* Unopened account
           /\ MustFireE1003(txn) => "E1003" \in validationErrors  \* Closed account
           /\ MustFireE3001(txn) => "E3001" \in validationErrors  \* Unbalanced
           /\ MustFireE3002(txn) => "E3002" \in validationErrors  \* Multiple NULLs
           /\ MustFireE3003(txn) => "E3003" \in validationErrors  \* No postings

\* Account lifecycle is monotonic (can't reopen closed accounts)
AccountLifecycleMonotonic ==
    [][accountStates[a] = "closed" => accountStates'[a] = "closed"]_vars
```

This catches bugs where the validator fails to detect invalid input.

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
# Run TLA+ booking invariant tests
cargo test -p rustledger-core --test tla_invariants_test

# Run TLA+ validation error tests
cargo test -p rustledger-validate --test tla_validation_errors_test

# Run with more iterations
PROPTEST_CASES=1000 cargo test -p rustledger-core --test tla_invariants_test
```

Test files:
- `crates/rustledger-core/tests/tla_invariants_test.rs` - BookingMethods.tla invariants
- `crates/rustledger-validate/tests/tla_validation_errors_test.rs` - ValidationErrors.tla invariants

The tests validate:

**BookingMethods.tla (tla_invariants_test.rs):**
- `tla_non_negative_units_*` - NonNegativeUnits invariant
- `tla_valid_lots_*` - ValidLots invariant
- `tla_fifo_property_*` - FIFOProperty invariant
- `tla_lifo_property_*` - LIFOProperty invariant
- `tla_hifo_property_*` - HIFOProperty invariant
- `tla_strict_property_*` - STRICTProperty invariant
- `tla_average_property_*` - AVERAGEProperty invariant
- `tla_trace_*` - Complete TLA+ traces
- `prop_tla_*` - Property-based invariant validation

**ValidationErrors.tla (tla_validation_errors_test.rs):**
- `tla_all_invalid_detected_*` - AllInvalidTransactionsDetected invariant
- `tla_account_state_machine_*` - AccountStateMachineValid invariant
- `tla_date_ordering_*` - DateOrderingValid invariant
- `tla_e1001_*` through `tla_e3003_*` - Individual error detection tests
- `tla_errors_monotonic` - ErrorsMonotonic property

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

## Refinement Checking

Refinement proofs verify that the Rust implementation correctly implements the abstract TLA+ specification:

```bash
# Check Inventory refinement
just tla-refine-inventory

# Check Booking methods refinement
just tla-refine-booking

# Check all refinements
just tla-refine-all
```

Refinement modules:
- `InventoryRefinement.tla` - Proves Rust `Inventory` refines abstract spec
- `BookingRefinement.tla` - Proves booking methods (FIFO, LIFO, HIFO, STRICT) refine abstract spec

What refinement checking proves:
1. **Initial State**: Rust's initial state corresponds to TLA+ initial state
2. **Step Correspondence**: Every Rust operation maps to a valid TLA+ transition
3. **Invariant Preservation**: All abstract invariants hold on the refined concrete state

Example: FIFO Refinement Property
```tla
FIFORefinement ==
    \A i \in 1..Len(reduction_history) :
        reduction_history[i].method = "FIFO" =>
            LET h == reduction_history[i]
            IN \A other \in h.matches :
                h.selected.cost.date <= other.cost.date
```

This proves that whenever the Rust code calls `inventory.reduce(BookingMethod::FIFO, ...)`,
it selects the lot with the minimum date among all matching lots.

## Apalache (Symbolic Model Checking)

[Apalache](https://github.com/informalsystems/apalache) provides symbolic model checking as an alternative to TLC's explicit-state approach:

```bash
# Setup Apalache (one-time download)
just apalache-setup

# Run Apalache on specific specs
just apalache-inventory
just apalache-booking
just apalache-validate

# Run on any spec
just apalache-check Inventory

# Run all Apalache checks
just apalache-all
```

Benefits over TLC:
- Finds bugs in unbounded state spaces
- Better for specs with infinite domains
- Produces SMT-based proofs

## Trace-to-Test Generator

Automatically generate Rust tests from TLA+ counterexamples:

```bash
# Capture trace from TLC (if invariant violated)
just tla-trace BookingMethods

# Generate Rust test from trace
just tla-gen-test traces/BookingMethods_trace.json

# Generate tests from all traces
just tla-gen-all-tests
```

How it works:
1. `tla_trace_to_json.py` parses TLC output and extracts counterexample states
2. `trace_to_rust_test.py` converts JSON traces to Rust test code
3. Tests reproduce the exact sequence of operations that violated an invariant

Example workflow:
```bash
# Find a bug in the spec
java -jar tools/tla2tools.jar -config spec/tla/Inventory.cfg spec/tla/Inventory.tla 2>&1 | \
    python3 scripts/tla_trace_to_json.py --spec Inventory > trace.json

# Generate Rust test
python3 scripts/trace_to_rust_test.py trace.json > test_from_trace.rs
```

## Inductive Invariants

Inductive invariants provide unbounded verification - proving correctness for ALL states, not just those within model checking bounds:

```bash
just tla-inductive
```

`InductiveInvariants.tla` proves the **conservation of units** invariant:

```tla
\* Core accounting invariant:
\* What's in inventory + what's been reduced = what's been added
ConservationInv ==
    TotalUnits(lots) + totalReduced = totalAdded

\* All lots have positive units (no zero-unit ghost lots)
PositiveUnitsInv ==
    \A l \in lots : l.units > 0

\* Can't reduce more than was added
ReduceBoundedInv ==
    totalReduced <= totalAdded
```

The spec includes formal proof sketches showing the invariants are truly inductive (preserved by all transitions).

## State Space Coverage Analysis

Analyze which TLA+ states are covered by Rust tests:

```bash
# Generate coverage report
just tla-coverage BookingMethods

# View HTML report
open coverage/BookingMethods_coverage.html
```

Reports include:
- State coverage percentage
- Transition coverage by action
- Per-variable value coverage
- List of uncovered states for test gap analysis

## Model-Based Testing (MBT)

Generate exhaustive Rust tests from TLA+ state machines:

```bash
# Generate tests from BookingMethods spec
just mbt-booking

# Generate from any spec with custom depth
just mbt-generate BookingMethods 3 50
```

MBT generates tests for ALL action sequences up to a depth, verifying TLA+ invariants hold in Rust.

## Limitations

TLA+ model checking is bounded:
- We check with small `MaxLots`, `MaxUnits` values
- Exhaustive for those bounds, but not proof of correctness for all sizes
- TLAPS proofs provide unbounded correctness guarantees
- Inductive invariants provide additional unbounded guarantees

For our purposes, model checking with reasonable bounds (3-5 lots, 10-20 units) catches most bugs. TLAPS proofs provide mathematical certainty for critical invariants.

## Roadmap

See `ROADMAP.md` for the plan to expand TLA+ coverage. Current status: **10/10** 🏆

Completed:
- ✅ All 7 booking methods with strong invariants
- ✅ Account lifecycle and directive ordering
- ✅ Validation error detection (reachability verification)
- ✅ CI automation
- ✅ Rust integration tests
- ✅ TLAPS formal proofs
- ✅ Apalache symbolic model checking
- ✅ Trace-to-test generator
- ✅ PriceDatabase specification
- ✅ Refinement proofs (Rust → TLA+)
- ✅ Apalache type annotations
- ✅ Inductive invariants (conservation of units)
- ✅ State space coverage analysis
- ✅ Model-based testing generator

## References

- [TLA+ Home](https://lamport.azurewebsites.net/tla/tla.html)
- [Learn TLA+](https://learntla.com/)
- [TLA+ Video Course](https://lamport.azurewebsites.net/video/videos.html)
- [Specifying Systems (book)](https://lamport.azurewebsites.net/tla/book.html)
