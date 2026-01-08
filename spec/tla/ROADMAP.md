# TLA+ Formal Verification Status

## Current Working Specifications

All specifications listed below have been verified with TLC model checker:

| Specification | States | Key Invariants |
|---------------|--------|----------------|
| `Conservation.tla` | 679 | ConservationInvariant, NonNegativeInventory |
| `DoubleEntry.tla` | 259 | TransactionsBalance, NoSelfTransfer |
| `LotSelection.tla` | 415 | FIFOCorrect, LIFOCorrect, HIFOCorrect |
| `AccountStateMachine.tla` | 16,223 | ClosedHaveZeroBalance, TypeOK |
| `Interpolation.tla` | 481 | AtMostOneNull, CompleteImpliesBalanced |
| `FIFOCheck.tla` | 132 | FIFOSelectsOldest |
| `SimpleInventory.tla` | demo | Basic add/reduce example |
| `BuggyInventory.tla` | demo | Shows TLC catching bugs |

## Real Bug Found

The TLA+ specs found a real bug in the Rust implementation:

**FIFOCheck.tla** discovered that `inventory.rs` was selecting lots by insertion order instead of by acquisition date. TLC provided a counterexample that was converted to a Rust test case in `crates/rustledger-core/tests/tla_fifo_bug_test.rs`. The bug was fixed by adding date-based sorting in `reduce_ordered()`.

## Practical Value

These specs are designed to **actually run and find bugs**:

1. **Conservation.tla** - Catches bugs where units appear from nothing or disappear
2. **DoubleEntry.tla** - Catches broken transaction balancing
3. **LotSelection.tla** - Catches wrong lot selection in FIFO/LIFO/HIFO
4. **AccountStateMachine.tla** - Catches invalid state transitions
5. **Interpolation.tla** - Catches NULL posting interpolation bugs

## Running the Specs

```bash
# Run all specs
for spec in Conservation DoubleEntry LotSelection AccountStateMachine Interpolation FIFOCheck; do
    java -jar tools/tla2tools.jar -config spec/tla/$spec.cfg spec/tla/$spec.tla
done

# Run single spec with multi-core
java -XX:+UseParallelGC -Xmx1g -jar tools/tla2tools.jar \
    -config spec/tla/Conservation.cfg \
    -workers auto \
    spec/tla/Conservation.tla
```

## Future Improvements

Potential specs that could be added:

1. **Multi-currency conservation** - Track units per currency
2. **Price database** - Price lookups and triangulation
3. **Pad directive** - Balance padding algorithm
4. **Query execution** - BQL query correctness

## Design Principles

These TLA+ specs follow principles that make them practical:

1. **Actually run** - No unsupported operators (LAMBDA, FoldSeq, etc.)
2. **Small state space** - Use small bounds (3-5) to avoid explosion
3. **Simple models** - Model essence, not implementation details
4. **Testable invariants** - Invariants that catch real bugs
5. **Counterexample-driven** - TLC traces convert to test cases
