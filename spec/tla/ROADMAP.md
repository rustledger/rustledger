# TLA+ Formal Verification Status

## Current Working Specifications

The repository contains 18 `.tla` specs. The 16 specs below are model-checked
on every CI run (see `.github/workflows/tla.yml`):

| Specification | Key Invariants |
|---------------|----------------|
| `Conservation.tla` | ConservationInvariant, NonNegativeInventory |
| `DoubleEntry.tla` | TransactionsBalance, NoSelfTransfer |
| `AccountStateMachine.tla` | ClosedHaveZeroBalance, TypeOK |
| `Interpolation.tla` | AtMostOneNull, CompleteImpliesBalanced |
| `FIFOCorrect.tla` | FIFO selects oldest lot |
| `LIFOCorrect.tla` | LIFO selects newest lot |
| `HIFOCorrect.tla` | HIFO selects highest-cost lot |
| `STRICTCorrect.tla` | STRICT requires exactly one matching lot |
| `AVERAGECorrect.tla` | AVERAGE weighted cost basis |
| `NONECorrect.tla` | NONE allows any reduction |
| `MultiCurrency.tla` | Multi-currency conservation |
| `PriceDB.tla` | Price database consistency |
| `ValidationCorrect.tla` | Balance assertion validation |
| `PluginCorrect.tla` | Plugin execution ordering |
| `ConcurrentAccess.tla` | Concurrent read/write safety |
| `QueryExecution.tla` | BQL query execution invariants |

The remaining two specs are illustrative demos, not run in CI:

| Specification | Purpose |
|---------------|---------|
| `SimpleInventory.tla` | Basic add/reduce example |
| `BuggyInventory.tla` | Shows TLC catching bugs |

`FIFOCheck.tla` also remains in the tree for historical reference (it found the
original FIFO bug, see below) but has been superseded in CI by `FIFOCorrect.tla`.

## Real Bug Found

The TLA+ specs found a real bug in the Rust implementation:

**FIFOCheck.tla** discovered that `inventory.rs` was selecting lots by insertion order instead of by acquisition date. TLC provided a counterexample that was converted to a Rust test case in `crates/rustledger-core/tests/tla_fifo_bug_test.rs`. The bug was fixed by adding date-based sorting in `reduce_ordered()`.

## Practical Value

These specs are designed to **actually run and find bugs**:

1. **Conservation.tla** - Catches bugs where units appear from nothing or disappear
1. **DoubleEntry.tla** - Catches broken transaction balancing
1. **FIFOCorrect.tla / LIFOCorrect.tla / HIFOCorrect.tla** - Catch wrong lot selection per method
1. **STRICTCorrect.tla / AVERAGECorrect.tla / NONECorrect.tla** - Catch booking-method violations
1. **AccountStateMachine.tla** - Catches invalid state transitions
1. **Interpolation.tla** - Catches NULL posting interpolation bugs

## Running the Specs

```bash
# Run all CI-checked specs
for spec in Conservation DoubleEntry AccountStateMachine Interpolation \
            FIFOCorrect LIFOCorrect HIFOCorrect STRICTCorrect AVERAGECorrect NONECorrect \
            MultiCurrency PriceDB ValidationCorrect PluginCorrect ConcurrentAccess QueryExecution; do
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

1. **Pad directive** - Balance padding algorithm

## Design Principles

These TLA+ specs follow principles that make them practical:

1. **Actually run** - No unsupported operators (LAMBDA, FoldSeq, etc.)
1. **Small state space** - Use small bounds (3-5) to avoid explosion
1. **Simple models** - Model essence, not implementation details
1. **Testable invariants** - Invariants that catch real bugs
1. **Counterexample-driven** - TLC traces convert to test cases
