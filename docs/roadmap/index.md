# Rustledger Roadmap

This is a **forward-looking** document: where rustledger is going and why. It
lists what's planned and what we're weighing, not what's already done — shipped
work lives in the [CHANGELOG](https://github.com/rustledger/rustledger/blob/main/CHANGELOG.md).

## Where we are

Rustledger is a fast, Rust-native, Beancount-compatible plain-text accounting
engine: 100% check / BQL / full-AST parity on the compatibility corpus, ~10–30×
faster than Python Beancount, with a property-tested pipeline, formal specs in
CI, and a stable plugin ABI. The foundation is solid. That changes what the
roadmap is *for*: the leverage now is less in raw speed and more in **removing
the reasons someone wouldn't switch** and **making the engine a platform**.

## Strategy

Three bets, in priority order. Everything in the per-area files ladders up to
one of these.

### 1. Finish compatibility — make "drop-in" literally true
"99% compatible" is not a migration story; the last 1% is where trust is won or
lost. The remaining gaps are narrow and worth closing completely:

- **Arbitrary-precision decimal** ([#1240](https://github.com/rustledger/rustledger/issues/1240)) — the only known numeric divergence. `rust_decimal` caps at 28–29 digits; beancount uses Python's unbounded `Decimal`. This is the single most-cited reason a ledger could produce different numbers.
- **Tooling parity** — a deliberate audit of `bean-price` / `bean-query` / `bean-report` against rustledger's equivalents at the flag and output level, so scripts and muscle memory port over unchanged.
- **Plugin commutativity** — the one pipeline-invariant family not yet pinned (does plugin order matter where it shouldn't?). Needs a `COMMUTATIVE` marker on the plugin trait. See [Testing & Quality](./testing-and-quality.md).

### 2. Make ingestion painless — the real adoption barrier
For plain-text accounting, the hard part isn't the ledger format; it's getting
bank data *into* it. This is where most product leverage sits, and where the
existing ML/WASM building blocks pay off — kept **local-first**, with cloud/LLM
strictly opt-in:

- **Declarative institution profiles** so common banks work without per-user CSV column-mapping, plus built-in profiles for the most common institutions.
- **Reconciliation that builds trust** — extract statement balances, compare against the computed ledger, and surface mismatches instead of silently importing.
- **Categorization that improves** — feed user corrections back into the existing Naive-Bayes model; offer an opt-in LLM suggestion path for what rules + ML leave uncategorized.

See [Importing & Ingestion](./importing.md). Statement OCR and bank-API sync
are further out and gated on real demand.

### 3. Be a platform, not just a CLI
Lower the on-ramp and meet people where they work:

- A **browser playground** — `rustledger-wasm` already compiles the engine to WASM, so a "try it in the browser" surface is mostly packaging, and it doubles as live, runnable docs.
- **Incremental, low-latency LSP** so editor responsiveness stays flat as ledgers grow (range-based reparse over the lossless CST), plus the missing refactors (rename, code actions).
- A **stable, documented plugin surface** (the SemVer gate is the first step) so third-party native and WASM plugins are safe to depend on.

## The substrate: keep raising the floor

These don't ship features, but they're why the above can move fast without
regressions — and they're the cheapest insurance the project has:

- **[Performance](./performance.md)** — protect the speed lead; only chase bottlenecks profiling actually shows.
- **[Testing & Engineering Quality](./testing-and-quality.md)** — extend the property tests, fuzzing, and API-stability gates.
- **[Formal Verification](./formal-verification.md)** — keep the core's invariants machine-checked, and turn counterexamples into regression tests.

## How this is organized

Each area file is **forward-only** and groups work into **Now** (in progress /
next up), **Next** (committed, well-scoped), and **Exploring / Later**
(genuinely uncertain — may be reshaped or dropped). When something ships it
moves to the [CHANGELOG](https://github.com/rustledger/rustledger/blob/main/CHANGELOG.md),
so these files never accumulate stale "done" entries.

> Lifecycle: **idea** (Exploring) → **tracked issue** (Next) → **in progress**
> (Now) → **shipped** (CHANGELOG). The roadmap captures intent and rationale;
> GitHub issues track the committed work.
