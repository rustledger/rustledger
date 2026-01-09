# TLA+ Specification Guide

This guide explains how to read rustledger's TLA+ specifications and how they relate to the Rust implementation.

## What is TLA+?

TLA+ (Temporal Logic of Actions) is a formal specification language for describing and verifying concurrent and distributed systems. We use it to:

1. **Formally specify** the expected behavior of critical algorithms
2. **Model check** against all possible inputs within bounds
3. **Verify invariants** hold in all reachable states
4. **Generate counterexamples** when properties are violated

## File Structure

```
spec/tla/
├── Conservation.tla       # Core invariant: units conservation
├── Conservation.cfg
├── DoubleEntry.tla        # Double-entry: debits = credits
├── DoubleEntry.cfg
├── LotSelection.tla       # FIFO/LIFO/HIFO lot selection
├── LotSelection.cfg
├── AccountStateMachine.tla # Account lifecycle state machine
├── AccountStateMachine.cfg
├── Interpolation.tla      # NULL posting interpolation
├── Interpolation.cfg
├── FIFOCheck.tla          # FIFO date ordering verification
├── FIFOCheck.cfg
├── SimpleInventory.tla    # Demo: basic operations
├── SimpleInventory.cfg
├── BuggyInventory.tla     # Demo: TLC catching bugs
├── BuggyInventory.cfg
├── README.md              # Overview and quick start
├── ROADMAP.md             # Status and future plans
└── GUIDE.md               # This file
```

## TLA+ to Rust Mapping

### BookingMethods.tla → inventory.rs

| TLA+ Concept | Rust Implementation |
|--------------|---------------------|
| `Lot` record | `Position` struct |
| `lots` variable | `Inventory.positions` |
| `BookingMethod` | `BookingMethod` enum |
| `Matching(spec)` | `matching_positions()` helper |
| `Oldest(lotSet)` | `oldest_lot()` / sort by date |
| `Newest(lotSet)` | `newest_lot()` / sort by date desc |
| `HighestCost(lotSet)` | `highest_cost_lot()` / sort by cost |
| `ReduceFIFO` action | `Inventory::reduce_fifo()` |
| `ReduceLIFO` action | `Inventory::reduce_lifo()` |
| `ReduceHIFO` action | `Inventory::reduce_hifo()` |
| `ReduceAverage` action | `Inventory::reduce_average()` |
| `ReduceStrict` action | `Inventory::reduce_strict()` |
| `ReduceStrictWithSize` action | `Inventory::reduce_strict_with_size()` |
| `ReduceNone` action | `Inventory::reduce_none()` |

### Reading TLA+ Specifications

#### Basic Syntax

```tla
\* Comment (like // in Rust)

\* Variable declaration
VARIABLES lots, method, history

\* Constant declaration
CONSTANTS MaxLots, MaxUnits

\* Set membership
l \in lots              \* l is in lots (like lots.contains(&l))

\* Set operations
lots \cup {l}          \* Union (add l to lots)
lots \ {l}             \* Difference (remove l from lots)

\* Record (like struct)
[units: 1..100, cost: 1..1000]

\* Sequence (like Vec)
<<a, b, c>>
Append(seq, x)         \* Push to sequence
Head(seq)              \* First element
Tail(seq)              \* All but first
Len(seq)               \* Length

\* Logic
/\                     \* AND
\/                     \* OR
=>                     \* IMPLIES
~                      \* NOT
\A x \in S : P(x)     \* FOR ALL x in S, P(x) holds
\E x \in S : P(x)     \* EXISTS x in S where P(x)

\* Primed variables (next state)
lots' = lots \cup {l}  \* lots in next state equals current lots with l added
```

#### Example: FIFO Reduction

```tla
\* TLA+ Specification
ReduceFIFO(units, spec) ==
    /\ method = "FIFO"                              \* Precondition: method is FIFO
    /\ units > 0                                     \* Precondition: positive units
    /\ LET matches == Matching(spec)                \* Get matching lots
       IN /\ matches # {}                           \* Must have matches
          /\ LET oldest == Oldest(matches)          \* Find oldest
             IN IF oldest.units >= units            \* If lot has enough
                THEN lots' = UpdateLot(oldest)      \* Reduce lot
                ELSE lots' = lots \ {oldest}        \* Consume entire lot
          /\ history' = Append(history, [...])      \* Record in history
    /\ UNCHANGED method                              \* Method doesn't change
```

```rust
// Rust Implementation
fn reduce_fifo(&mut self, units: &Amount, spec: &CostSpec) -> Result<BookingResult, BookingError> {
    // Precondition: method is FIFO (handled by dispatch)
    // Precondition: units > 0 (caller's responsibility)

    // Get matching lots
    let matches = self.matching_positions(units, spec);

    // Must have matches
    if matches.is_empty() {
        return Err(BookingError::NoMatchingLot { ... });
    }

    // Find oldest (first in insertion order for FIFO)
    // Reduce from oldest first...

    Ok(BookingResult { matched, cost_basis })
}
```

## Key Invariants

### NonNegativeUnits
```tla
NonNegativeUnits == method # "NONE" => TotalUnits >= 0
```
**Meaning**: For all booking methods except NONE, total units must never go negative.

**Rust test**: `tla_non_negative_units_after_fifo()`

### ValidLots
```tla
ValidLots == \A l \in lots : l.units > 0
```
**Meaning**: Every lot in the inventory must have positive units (no empty lots).

**Rust test**: `tla_valid_lots_after_partial_reduction()`

### FIFOProperty
```tla
FIFOProperty ==
    \A i \in 1..Len(history) :
        history[i].method = "FIFO" =>
            \A other \in history[i].matching_lots :
                history[i].from_lot.date <= other.date
```
**Meaning**: FIFO always selects the oldest lot among all matches.

**Rust test**: `tla_fifo_property_selects_oldest()`

### HIFOProperty
```tla
HIFOProperty ==
    \A other \in matches : selected.cost_per_unit >= other.cost_per_unit
```
**Meaning**: HIFO always selects the highest-cost lot (tax optimization).

**Rust test**: `tla_hifo_property_selects_highest_cost()`

## Running TLA+ Model Checker

### Using Just
```bash
just tla-all        # Run all specs
just tla-booking    # Run BookingMethods.tla
just tla-inventory  # Run Inventory.tla
```

### Using TLC Directly
```bash
java -jar tools/tla2tools.jar \
    -config spec/tla/BookingMethods.cfg \
    -workers auto \
    spec/tla/BookingMethods.tla
```

### Understanding Output
```
TLC2 Version 2.18
Running breadth-first search...
Finished computing initial states: 1 distinct state generated.
Progress: 1000 states generated, 500 distinct states found
...
Model checking completed. No error has been found.
  States generated: 12345
  Distinct states:  6789
  Queue: 0
```

**Error example**:
```
Error: Invariant FIFOProperty is violated.
The behavior up to this point is:
1: <Init>
2: <AddLot(...)>
3: <ReduceFIFO(...)>  <-- Violation here
```

## Writing New Specifications

### Template

```tla
------------------------- MODULE MySpec -------------------------
(*
 * Description of what this spec models
 *)

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    MaxItems    \* Upper bound for model checking

VARIABLES
    items,      \* The main state
    history     \* Operation history

vars == <<items, history>>

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ items = {}
    /\ history = <<>>

-----------------------------------------------------------------------------
(* Actions *)

AddItem(item) ==
    /\ item \notin items
    /\ items' = items \cup {item}
    /\ UNCHANGED history

RemoveItem(item) ==
    /\ item \in items
    /\ items' = items \ {item}
    /\ history' = Append(history, item)

Next ==
    \/ \E i \in Items : AddItem(i)
    \/ \E i \in Items : RemoveItem(i)

-----------------------------------------------------------------------------
(* Invariants *)

\* Example invariant
ItemsNonEmpty == Cardinality(items) >= 0

TypeOK ==
    /\ items \subseteq Items

Invariant == ItemsNonEmpty /\ TypeOK

-----------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

=============================================================================
```

### Creating .cfg File

```
CONSTANTS
    MaxItems = 10

INIT Init
NEXT Next

INVARIANTS
    Invariant
    TypeOK
```

## Rust Test Correspondence

Each TLA+ invariant should have a corresponding Rust test in:
- `crates/rustledger-core/tests/tla_invariants_test.rs`

The tests use the naming convention:
- `tla_<invariant_name>_<scenario>()`
- `tla_trace_<trace_description>()`
- `prop_tla_<property_name>()` for property-based tests

## Contributing

When modifying booking algorithms:

1. **Update TLA+ spec first** - Define the expected behavior formally
2. **Run model checker** - Verify the spec is consistent
3. **Implement in Rust** - Match the TLA+ specification
4. **Add TLA+ tests** - Create tests that validate TLA+ invariants
5. **Update this guide** - Document any new mappings

## Resources

- [TLA+ Home](https://lamport.azurewebsites.net/tla/tla.html)
- [Learn TLA+](https://learntla.com/)
- [TLA+ Video Course](https://lamport.azurewebsites.net/video/videos.html)
- [Specifying Systems (book)](https://lamport.azurewebsites.net/tla/book.html)
