# TLA+ Specifications

This directory contains TLA+ formal specifications for critical rustledger algorithms.

## Working Specifications

| File | States | Description |
|------|--------|-------------|
| `Conservation.tla` | 679 | **Core invariant**: units_in + units_reduced = units_added |
| `DoubleEntry.tla` | 259 | Double-entry accounting: debits = credits |
| `FIFOCorrect.tla` | 219 | **FIFO correctness**: selects oldest lot by date |
| `LIFOCorrect.tla` | 219 | **LIFO correctness**: selects newest lot by date |
| `HIFOCorrect.tla` | 219 | **HIFO correctness**: selects highest cost lot |
| `AccountStateMachine.tla` | 16,223 | Account lifecycle: unopened → open → closed |
| `Interpolation.tla` | 481 | NULL posting interpolation (balancing amount) |
| `MultiCurrency.tla` | 1,301 | Multi-currency conservation invariant |
| `PriceDB.tla` | 142 | Price database: self-prices never set |
| `STRICTCorrect.tla` | 55 | **STRICT correctness**: requires exactly one matching lot |
| `AVERAGECorrect.tla` | 263 | **AVERAGE correctness**: weighted average cost basis |
| `NONECorrect.tla` | 135 | **NONE correctness**: allows any reduction |
| `ValidationCorrect.tla` | 3,141 | Balance assertion validation logic |
| `PluginCorrect.tla` | 160 | Plugin execution ordering guarantees |
| `ConcurrentAccess.tla` | 231 | Concurrent read/write locking invariants |
| `QueryExecution.tla` | 10,182 | BQL query execution invariants |

### Bug-Finding Specifications

| File | Status | Description |
|------|--------|-------------|
| `FIFOCheck.tla` | FAILS | Models buggy FIFO (insertion order) - **proves the bug exists** |

### Demo Specifications

| File | Description |
|------|-------------|
| `SimpleInventory.tla` | Demo: basic add/reduce with conservation |
| `BuggyInventory.tla` | Demo: TLC catching a conservation violation |

## Quick Start

```bash
# Run model checker on a spec
java -jar tools/tla2tools.jar -config spec/tla/Conservation.cfg spec/tla/Conservation.tla

# Run with multiple workers
java -XX:+UseParallelGC -Xmx1g -jar tools/tla2tools.jar \
    -config spec/tla/Conservation.cfg \
    -workers auto \
    spec/tla/Conservation.tla
```

## Key Invariants

### Conservation.tla
```tla
(* What's in inventory + what's been taken out = what was put in *)
ConservationInvariant ==
    inventory + totalReduced = totalAdded
```

### DoubleEntry.tla
```tla
(* Every transaction must balance: debits = credits *)
TransactionsBalance ==
    \A i \in 1..Len(ledger) : ledger[i].amount > 0

(* No self-transfers *)
NoSelfTransfer ==
    \A i \in 1..Len(ledger) : ledger[i].debit # ledger[i].credit
```

### FIFOCorrect.tla
```tla
(* After a FIFO reduction, the selected date must be <= all remaining dates *)
FIFOSelectsOldest ==
    lastSelected.date > 0 =>
        \A d \in lastSelected.allDates : lastSelected.date <= d
```

### LIFOCorrect.tla
```tla
(* After a LIFO reduction, the selected date must be >= all remaining dates *)
LIFOSelectsNewest ==
    lastSelected.date > 0 =>
        \A d \in lastSelected.allDates : lastSelected.date >= d
```

### HIFOCorrect.tla
```tla
(* After a HIFO reduction, the selected cost must be >= all remaining costs *)
HIFOSelectsHighest ==
    lastSelected.cost > 0 =>
        \A c \in lastSelected.allCosts : lastSelected.cost >= c
```

### AccountStateMachine.tla
```tla
(* Closed accounts must have zero balance *)
ClosedHaveZeroBalance ==
    \A a \in Accounts :
        state[a] = "closed" => balance[a] = 0
```

### Interpolation.tla
```tla
(* At most one NULL posting per transaction *)
AtMostOneNull ==
    ~(posting1 = NULL /\ posting2 = NULL)

(* After completion, transaction is balanced *)
CompleteImpliesBalanced ==
    complete => posting1 + posting2 = 0
```

### ValidationCorrect.tla
```tla
(* If error was detected, the first error assertion was indeed a mismatch *)
ErrorMeansFirstMismatch ==
    hasError => (errorExpected # errorActual)

(* Error details are set iff hasError *)
ErrorDetailsConsistent ==
    hasError <=> (errorExpected # UNSET /\ errorActual # UNSET)
```

### PluginCorrect.tla
```tla
(* Plugins execute in order: plugin p+1 doesn't start before p completes *)
PluginsInOrder ==
    \A p \in 1..NumPlugins :
        (currentPlugin = p + 1) => (p \in pluginComplete)

(* Each plugin processes directives in order *)
DirectivesInOrder ==
    \A p \in 1..NumPlugins, d \in 2..MaxDirectives :
        HasProcessed(p, d) => HasProcessed(p, d - 1)
```

### ConcurrentAccess.tla
```tla
(* No data race: readers and writers are mutually exclusive *)
NoDataRace ==
    ~(readLock > 0 /\ writeLock)

(* Write lock is exclusive - no readers when writing *)
ExclusiveWriteLock ==
    writeLock => (readLock = 0)
```

### QueryExecution.tla
```tla
(* Filter correctness: selected IDs only include matching postings *)
FilterCorrectness ==
    filterApplied =>
        \A id \in selectedIds :
            \E p \in postings : p.id = id

(* Count is accurate: count equals size of matching set *)
CountAccuracy ==
    aggregated =>
        queryResult.count = Cardinality({p \in postings : p.id \in selectedIds})
```

## Booking Method Verification Strategy

We use two complementary approaches to verify booking methods:

### 1. Bug-Finding Specs (model buggy behavior)
`FIFOCheck.tla` models the **OLD buggy behavior** (insertion order selection) and is expected to FAIL when run with TLC. This proves the bug exists.

### 2. Correctness Specs (model correct behavior)
All booking methods now have correctness specs that PASS TLC:
- `FIFOCorrect.tla` - First-In First-Out (select oldest by date)
- `LIFOCorrect.tla` - Last-In First-Out (select newest by date)
- `HIFOCorrect.tla` - Highest-In First-Out (select highest cost)
- `STRICTCorrect.tla` - Requires exactly one matching lot
- `AVERAGECorrect.tla` - Uses weighted average cost basis
- `NONECorrect.tla` - Allows any reduction (most permissive)

## Real Bug Found

The FIFOCheck spec discovered a real bug in `inventory.rs`:

**Problem**: FIFO was selecting lots by insertion order, not by acquisition date.

**Counterexample from TLC**:
1. Add lot: 10 AAPL @ $150 (date: 2024-01-02) - inserted first
2. Add lot: 10 AAPL @ $100 (date: 2024-01-01) - inserted second
3. Reduce 5 AAPL using FIFO
4. **Bug**: Selected $150 lot (inserted first) instead of $100 lot (oldest by date)

**Fix**: Added date sorting to `reduce_ordered()` in `inventory.rs:330`:
```rust
indices.sort_by_key(|&i| self.positions[i].cost.as_ref().and_then(|c| c.date));
```

See `crates/rustledger-core/tests/tla_fifo_bug_test.rs` for the test case.

## Practical TLA+ Workflow

1. **Write Spec**: Model the algorithm abstractly in TLA+
2. **Run TLC**: Model checker exhaustively explores state space
3. **Get Counterexample**: If invariant violated, TLC shows exact sequence
4. **Write Test**: Convert counterexample to Rust test
5. **Fix Bug**: Update Rust code until test passes
6. **Verify**: All TLC states pass, test passes

## Configuration Files

Each `.tla` file has a matching `.cfg` file:

```
CONSTANTS
    MaxUnits = 3
    MaxOperations = 6

INIT Init
NEXT Next

INVARIANTS
    ConservationInvariant
    NonNegativeInventory
```

## State Space Bounds

TLC uses bounded model checking. Keep bounds small to avoid state explosion:
- `MaxUnits = 1-3` for amounts
- `MaxLots = 2-3` for lot counts
- `MaxDate = 3` for date values
- Track only `lastSelected`, not full history, to avoid sequence explosion

## References

- [TLA+ Home](https://lamport.azurewebsites.net/tla/tla.html)
- [Learn TLA+](https://learntla.com/)
- [TLC Model Checker](https://lamport.azurewebsites.net/tla/tools.html)
