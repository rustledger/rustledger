# Formal Verification Roadmap

> Part of the [rustledger roadmap](./index.md).

Forward-looking plan for rustledger's formal-verification work: TLA+ specs
model-checked in CI, Kani proofs over the Rust core, and the tooling that ties
counterexamples back to executable tests. Items here are not-yet-done; shipped
work lives in the changelog.

This is part of the [substrate](./index.md#the-substrate-keep-raising-the-floor):
the value isn't proofs for their own sake, it's that the engine's core invariants
— balance, conservation, non-negative inventory — stay machine-checked as the code
evolves, and that every counterexample TLC finds becomes a pinned Rust regression
test. The bar for adding a spec is therefore practical: it has to catch a class of
bug that property tests and types don't already rule out.

## Now / In progress

| Item | Notes |
|------|-------|
| Restore the TLA+ trace → Rust-test converter | The counterexample-driven workflow that turned the FIFO TLC trace into `tla_fifo_bug_test.rs` is currently missing. Bring back automated conversion of TLC counterexamples into Rust regression tests so future bugs become pinned tests by default. |

## Next

| Item | Notes |
|------|-------|
| Pad-directive TLA+ spec | Model the balance-padding algorithm and its invariants. Previously listed as a candidate spec; well-scoped to add alongside the existing 16 CI-checked specs. |
| Expand Kani proofs: decimal arithmetic | Add Kani harnesses over decimal arithmetic (addition, scaling, rounding) to bound-check overflow and precision behavior in the core. |
| Expand Kani proofs: inventory reductions | Prove inventory reduction operations (lot selection and quantity decrement) against the same invariants the TLA+ booking specs check — conservation and non-negative inventory. |

## Exploring / Later

| Item | Notes |
|------|-------|
| TLA+ model for plugin commutativity | *(Exploratory)* Model whether plugin application order is safe to reorder — i.e. which plugin passes commute and which must stay sequenced. Complements the existing `PluginCorrect.tla` ordering spec. |
| Further candidate specs | *(Exploratory)* Continue identifying directive/algorithm areas that benefit from a small, runnable spec, following the design principles below. |

## Design principles

New specs and proofs should stay practical and continue to follow the
established principles:

- **Actually run** — no unsupported operators (LAMBDA, FoldSeq, etc.).
- **Small state space** — small bounds (3–5) to avoid state explosion.
- **Simple models** — model the essence, not implementation details.
- **Testable invariants** — invariants that catch real bugs.
- **Counterexample-driven** — TLC traces convert into Rust test cases.

---

Shipped: see [CHANGELOG](https://github.com/rustledger/rustledger/blob/main/CHANGELOG.md) for completed formal-verification work.
