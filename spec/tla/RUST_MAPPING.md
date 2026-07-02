# TLA+ to Rust Mapping

This document maps TLA+ specifications to their Rust implementations and test coverage.

## Overview

rustledger uses a **multi-layered verification approach**:

1. **TLA+ Model Checking** (`spec/tla/`) - Verifies algorithm design
1. **Kani Proofs** (`crates/rustledger-core/src/kani_proofs.rs`) - Verifies numerical invariants
1. **Property-Based Tests** (`crates/*/tests/tla_proptest.rs`) - Verifies implementation with real types
1. **Unit Tests** - Verifies specific behaviors

## Behavior-Replay Conformance (model-based testing)

The specs' bounds are tiny (Conservation.cfg: MaxUnits=3, MaxOperations=6 →
207 states / 678 transitions), so TLC can enumerate the COMPLETE state graph.
`scripts/tla-behaviors.py` turns that graph into an edge-coverage behavior
corpus (`spec/tla/behaviors/<Spec>.json`, one behavior per transition), and
`crates/rustledger-core/tests/tla_behavior_replay.rs` replays every behavior
against the real `Inventory`, asserting after each step:

- **Abstraction**: `inv.units(..) == inventory`, harness accumulators equal
  `totalAdded`/`totalReduced`.
- **Enabledness**: an action the model says is enabled must succeed in the
  implementation (a spec-legal `Reduce` may not `Err`).

This is exhaustive conformance **up to the model bound** — strictly stronger
than the sampled properties above, one notch below a refinement proof. The
corpus is committed so the replay runs in plain `cargo test` (no Java); the
TLA+ CI workflow regenerates it from the spec and fails on drift, so model
and corpus cannot silently diverge. The generator output is canonical
(content-derived ordering, no node ids), so regeneration is byte-stable.

Covered specs (≈4,000 behaviors total, all replayed in <1s of `cargo test`):

| Corpus | Behaviors | Replay checks |
|--------|-----------|---------------|
| Conservation | 678 | units + totalAdded/totalReduced abstraction, enabledness |
| FIFOCorrect / LIFOCorrect | 422 each | per-date unit totals; the matched lot's DATE equals the model's selection |
| HIFOCorrect | 422 | per-cost unit totals; matched lot's COST equals the model's selection |
| STRICTCorrect | 136 | per-currency totals; model `success`/`no_match`/`ambiguous` ↔ impl `Ok`/`NoMatchingLot`/`AmbiguousMatch` |
| AVERAGECorrect | 3,584 | units exactly, AND pool value against the model's exact rational `valueNum/valueDen` (compared within the implementation's 28-digit Decimal rounding tolerance); the model also proves `ZeroUnitsZeroValue` — full liquidation empties the pool exactly |
| NONECorrect | 396 | balance (shorts allowed) + totals abstraction |
| MultiCurrency | 10,116 | per-currency inventory over a multi-commodity `Inventory` — every currency asserted after every step, so cross-commodity unit leaks fail |
| AccountStateMachine | 16,222 | validator lifecycle (in `rustledger-validate/tests/`): each model-legal open/close/post/transfer sequence, converted to directives, must `validate()` with zero errors (the E1001/E1002/E1003 state machine) |
| PriceDB | 690 | `PriceDatabase` (in `rustledger-query/tests/`): every model-set `(base, quote)` reads back via `get_latest_price`; model-unset entries not asserted (the implementation legitimately derives inverse rates) |

Two specs are deliberately NOT replayed:

- **DoubleEntry** — its balance invariant holds *by construction* in the
  model (each `AddTransaction` appends a balanced record), so a replay would
  only re-verify what the type system and residual property tests already
  rule out; below the machinery's catch-a-real-bug-class bar.
- **Interpolation** — mappable in principle (posting records with holes →
  `rustledger_booking::interpolate`), but the highest-effort mapping of the
  family; deferred until the interpolator next changes materially.

The abstraction deliberately collapses the specs' lot SEQUENCES to per-key
unit totals: the implementation merges identical (cost, date) lots on add, so
lot count is not preserved — per-key totals are. The STRICT replay gives each
added lot a distinct acquisition date so the model's lot-count ambiguity is
faithfully reproduced.

Extending to another spec = a `derive` entry in `scripts/tla-behaviors.py`'s
SPECS registry + a replay interpreter in `tla_behavior_replay.rs` + the
corpus file, all guarded by the CI lockstep check.

## Dual-Direction Trace Validation

The behavior replay above checks **model → implementation** exhaustively. The
dual direction — **implementation → model**, i.e. the implementation never
takes a transition the model forbids — is checked by trace validation:
`crates/rustledger-core/examples/conservation_trace_gen.rs` drives the real
`Inventory` through seeded-random Add/Reduce sequences and records the
abstract state after every operation; `scripts/tla-trace-validate.py` turns
each trace into a trace-following TLA+ spec and has TLC verify the
`[][Conservation!Next]_vars` action property over it. The TLA+ CI workflow
runs this on every triggering change with a fresh seed (printed for exact
reproduction), after a self-test that proves the harness rejects a corrupted
trace. Together the two directions give two-sided refinement checking —
exhaustive on the model side, continuously sampled on the implementation
side.

## Refinement Obligations

The specs model **atomic** actions: when a guard (e.g. `Conservation.tla`'s
`ReduceBound`) is false, the action is simply *disabled* — TLA+ cannot express
"mutate halfway, then fail", so TLC can never detect it. The Rust
implementation is not atomic, which leaves a proof obligation the models
cannot carry:

> **Every `Err` return must refine a stutter step** — the observable state
> after a failed operation is identical to the state before it.

This is checked at the implementation level, not the model level:

| Obligation | Where checked |
|------------|---------------|
| Failed `Inventory::reduce` leaves the inventory untouched (all 7 methods × oversell / wrong currency / unknown label / unmatched cost / ambiguous) | `tla_proptest.rs::prop_failed_reduce_is_a_stutter` |
| Failed reductions inside randomized op sequences (engine level) | `rustledger-booking/tests/booking_properties.rs` |
| Conservation holds across sequences **containing** failed reduces | `tla_proptest.rs::prop_conservation_invariant` |

Why this section exists: TLC was green while `reduce_ordered`/`reduce_hifo`
drained lots before erroring (#1677) — an oversell error corrupted every later
balance assertion on the account. The bug was at the refinement boundary, and
the then-current conformance tests clamped their generators to in-bounds
amounts and skipped `Err` branches, so the state was unreachable. When adding
a conformance test for a new spec, always (1) generate inputs that violate the
guards, and (2) assert state equality on `Err` — never `if let Ok(..)`-skip.

## Specification Mapping

### Conservation.tla

**Purpose**: Verifies that units are never created or destroyed.

**Invariant**: `inventory + totalReduced = totalAdded`

| TLA+ Element | Rust Implementation | Test Coverage |
|--------------|---------------------|---------------|
| `ConservationInvariant` | `Inventory::add`, `Inventory::reduce` | `prop_conservation_invariant` |
| `AddAmount` | `Inventory::add()` | `proof_conservation_add_reduce` |
| `ReduceAmount` | `Inventory::reduce()` | `proof_conservation_multiple_operations` |
| `ReduceBound` | `Inventory::reduce()` returns error if insufficient | `prop_fifo_conservation`, etc. |

**Files**:

- TLA+: `spec/tla/Conservation.tla`
- Rust: `crates/rustledger-core/src/inventory/mod.rs`
- Proptest: `crates/rustledger-core/tests/tla_proptest.rs`
- Kani: `crates/rustledger-core/src/kani_proofs.rs`

______________________________________________________________________

### FIFOCorrect.tla

**Purpose**: Verifies FIFO (First-In-First-Out) lot selection.

**Invariant**: `selected_date <= all other lot dates`

| TLA+ Element | Rust Implementation | Test Coverage |
|--------------|---------------------|---------------|
| `FIFOSelectsOldest` | `BookingMethod::Fifo` | `prop_fifo_selects_oldest` |
| `FIFO` action | `Inventory::reduce()` with `BookingMethod::Fifo` | `proof_fifo_selects_oldest_of_two` |

**Files**:

- TLA+: `spec/tla/FIFOCorrect.tla`
- Rust: `crates/rustledger-core/src/inventory/booking.rs`
- Proptest: `crates/rustledger-core/tests/tla_proptest.rs`
- Kani: `crates/rustledger-core/src/kani_proofs.rs`

______________________________________________________________________

### LIFOCorrect.tla

**Purpose**: Verifies LIFO (Last-In-First-Out) lot selection.

**Invariant**: `selected_date >= all other lot dates`

| TLA+ Element | Rust Implementation | Test Coverage |
|--------------|---------------------|---------------|
| `LIFOSelectsNewest` | `BookingMethod::Lifo` | `prop_lifo_selects_newest` |
| `LIFO` action | `Inventory::reduce()` with `BookingMethod::Lifo` | `proof_lifo_selects_newest` |

**Files**:

- TLA+: `spec/tla/LIFOCorrect.tla`
- Rust: `crates/rustledger-core/src/inventory/booking.rs`
- Proptest: `crates/rustledger-core/tests/tla_proptest.rs`
- Kani: `crates/rustledger-core/src/kani_proofs.rs`

______________________________________________________________________

### HIFOCorrect.tla

**Purpose**: Verifies HIFO (Highest-In-First-Out) lot selection.

**Invariant**: `selected_cost >= all other lot costs`

| TLA+ Element | Rust Implementation | Test Coverage |
|--------------|---------------------|---------------|
| `HIFOSelectsHighestCost` | `BookingMethod::Hifo` | `prop_hifo_selects_highest_cost` |
| `HIFO` action | `Inventory::reduce()` with `BookingMethod::Hifo` | `proof_hifo_selects_highest_cost` |

**Files**:

- TLA+: `spec/tla/HIFOCorrect.tla`
- Rust: `crates/rustledger-core/src/inventory/booking.rs`
- Proptest: `crates/rustledger-core/tests/tla_proptest.rs`
- Kani: `crates/rustledger-core/src/kani_proofs.rs`

______________________________________________________________________

### DoubleEntry.tla

**Purpose**: Verifies double-entry bookkeeping (debits = credits).

**Invariant**: `sum(postings) = 0` for every transaction

| TLA+ Element | Rust Implementation | Test Coverage |
|--------------|---------------------|---------------|
| `TransactionsBalance` | `rustledger_booking::calculate_residual()` | `prop_transfer_conserves_amount` |
| `Debit/Credit` | Posting amounts | `proof_double_entry_two_postings` |
| `Balance` | `rustledger_validate::validate()` | `proof_double_entry_multiple_postings` |

**Files**:

- TLA+: `spec/tla/DoubleEntry.tla`
- Rust: `crates/rustledger-booking/src/interpolate.rs`
- Proptest: `crates/rustledger-core/tests/tla_proptest.rs`
- Kani: `crates/rustledger-core/src/kani_proofs.rs`

______________________________________________________________________

### Interpolation.tla

**Purpose**: Verifies missing amount inference (auto-fill).

**Invariants**:

- `AtMostOneNull`: At most one posting per currency can have missing amount
- `CompleteImpliesBalanced`: After interpolation, sum = 0

| TLA+ Element | Rust Implementation | Test Coverage |
|--------------|---------------------|---------------|
| `AtMostOneNull` | `interpolate()` error handling | `prop_interpolation_at_most_one_null_enforced` |
| `CompleteImpliesBalanced` | `interpolate()` result | `prop_interpolation_completes_balanced` |
| `HasNullAccurate` | `InterpolationResult.filled_indices` | `prop_interpolation_fills_correct_postings` |

**Files**:

- TLA+: `spec/tla/Interpolation.tla`
- Rust: `crates/rustledger-booking/src/interpolate.rs`
- Proptest: `crates/rustledger-booking/tests/tla_proptest.rs`

______________________________________________________________________

### MultiCurrency.tla

**Purpose**: Verifies per-currency conservation.

**Invariants**:

- `ConservationPerCurrency`: Each currency has its own conservation
- `NoCurrencyMixing`: Units don't leak between currencies

| TLA+ Element | Rust Implementation | Test Coverage |
|--------------|---------------------|---------------|
| `ConservationPerCurrency` | `Inventory` stores by currency | `prop_multi_currency_conservation` |
| `NonNegativeInventory` | `Inventory::reduce()` returns error | `prop_multi_currency_non_negative` |
| `NoCurrencyMixing` | Currency keys in `Inventory` | `prop_multi_currency_isolation` |

**Files**:

- TLA+: `spec/tla/MultiCurrency.tla`
- Rust: `crates/rustledger-core/src/inventory/mod.rs`
- Proptest: `crates/rustledger-core/tests/tla_proptest.rs`

______________________________________________________________________

### ValidationCorrect.tla

**Purpose**: Verifies balance assertion validation.

**Invariants**:

- `ErrorMeansFirstMismatch`: Error implies expected != actual
- `ErrorDetailsConsistent`: Error details are accurate

| TLA+ Element | Rust Implementation | Test Coverage |
|--------------|---------------------|---------------|
| `ErrorMeansFirstMismatch` | `validate()` balance checks | `prop_balance_error_means_mismatch` |
| `NonNegativeBalance` | Balance tracking | `prop_balance_tracking_accurate` |
| Tolerance handling | `ValidationOptions.tolerance` | `prop_tolerance_bounds_respected` |

**Files**:

- TLA+: `spec/tla/ValidationCorrect.tla`
- Rust: `crates/rustledger-validate/src/lib.rs`
- Proptest: `crates/rustledger-validate/tests/tla_proptest.rs`

______________________________________________________________________

### QueryExecution.tla

**Purpose**: Verifies BQL query correctness.

**Invariants**:

- `FilterCorrectness`: WHERE selects only matching rows
- `CountAccuracy`: COUNT returns exact count
- `SumAccuracy`: SUM returns exact sum

| TLA+ Element | Rust Implementation | Test Coverage |
|--------------|---------------------|---------------|
| `FilterCorrectness` | `Executor::execute_select()` | `prop_filter_no_false_positives` |
| `CountAccuracy` | `COUNT()` aggregate | `prop_count_accuracy` |
| `SumAccuracy` | `SUM()` aggregate | `prop_sum_accuracy` |
| `ResultMatchesSelection` | Query result filtering | `prop_result_matches_selection` |

**Files**:

- TLA+: `spec/tla/QueryExecution.tla`
- Rust: `crates/rustledger-query/src/executor/mod.rs`
- Proptest: `crates/rustledger-query/tests/tla_proptest.rs`

______________________________________________________________________

### PriceDB.tla

**Purpose**: Verifies price database invariants.

**Invariants**:

- `IdentityProperty`: `price(X, X) = 1`
- `SelfPricesNeverSet`: Self-prices are not stored

| TLA+ Element | Rust Implementation | Test Coverage |
|--------------|---------------------|---------------|
| `IdentityProperty` | `PriceDatabase::get_price()` | `prop_price_identity` |
| `SelfPricesNeverSet` | Self-price handling | `prop_no_self_prices` |
| `InverseReciprocal` | `PriceDatabase::get_price()` | `prop_price_inverse_reciprocal` |
| `ChainTransitivity` | Price chain resolution | `prop_price_chain_transitivity` |

**Files**:

- TLA+: `spec/tla/PriceDB.tla`
- Rust: `crates/rustledger-query/src/price.rs`
- Proptest: `crates/rustledger-query/tests/tla_proptest.rs`

______________________________________________________________________

### PluginCorrect.tla

**Purpose**: Verifies plugin execution ordering.

**Invariants**:

- `PluginsInOrder`: Plugin N+1 doesn't start before N completes
- `DirectivesInOrder`: Sequential directive processing
- `NoFutureDirectives`: Plugin can't see later plugins' additions

| TLA+ Element | Rust Implementation | Test Coverage |
|--------------|---------------------|---------------|
| `PluginsInOrder` | `PluginManager::execute_all()` | `prop_plugins_execute_in_order` |
| `DirectivesInOrder` | Plugin process loop | `prop_directives_maintain_order` |
| `NoFutureDirectives` | Input cloning | `prop_plugin_isolation` |

**Files**:

- TLA+: `spec/tla/PluginCorrect.tla`
- Rust: `crates/rustledger-plugin/src/runtime.rs`, `src/native/mod.rs`
- Proptest: `crates/rustledger-plugin/tests/tla_proptest.rs`

______________________________________________________________________

## Test Coverage Summary

| TLA+ Spec | Kani Proofs | Proptest | Unit Tests |
|-----------|-------------|----------|------------|
| Conservation.tla | 3 proofs | 4 tests | Many |
| FIFOCorrect.tla | 2 proofs | 2 tests | Many |
| LIFOCorrect.tla | 1 proof | 2 tests | Many |
| HIFOCorrect.tla | 1 proof | 2 tests | Many |
| DoubleEntry.tla | 2 proofs | 1 test | Many |
| Interpolation.tla | - | 8 tests | Many |
| MultiCurrency.tla | - | 4 tests | Many |
| ValidationCorrect.tla | - | 8 tests | Many |
| QueryExecution.tla | - | 13 tests | Many |
| PriceDB.tla | - | 4 tests | Many |
| PluginCorrect.tla | - | 8 tests | Many |

## Running Verification

```bash
# Run TLA+ model checking
cd spec/tla
tlc Conservation.tla

# Run Kani proofs
cd crates/rustledger-core
cargo kani --all-features

# Run property-based tests
cargo test --all-features tla_proptest

# Run mutation testing
cargo mutants --package rustledger-core
```

## Adding New Specifications

When adding a new TLA+ specification:

1. Create `spec/tla/NewSpec.tla` with invariants
1. Run TLC to verify the model
1. Add proptest coverage in `crates/*/tests/tla_proptest.rs`
1. (Optional) Add Kani proofs for numerical properties
1. Update this mapping document

## Design Rationale

### Why Both TLA+ and Rust Tests?

- **TLA+** verifies that the *algorithm design* is correct at an abstract level
- **Proptest** verifies that the *implementation* matches the design using real Rust types
- **Kani** provides bit-precise verification of numerical invariants
- **Unit tests** cover specific edge cases and integration scenarios

This layered approach catches bugs at different abstraction levels:

- TLA+ catches design flaws before implementation
- Proptest catches implementation bugs with random inputs
- Kani catches numerical edge cases (overflow, precision)
- Unit tests catch regression and integration issues

### Why Property-Based Testing?

Property-based tests (proptest) are the primary verification layer because:

1. They test real Rust types (`Inventory`, `Decimal`, etc.)
1. They generate thousands of test cases automatically
1. They find edge cases humans would miss
1. They map directly to TLA+ invariants

Kani proofs complement proptest for numerical properties where bit-precise verification matters (e.g., overflow checks).
