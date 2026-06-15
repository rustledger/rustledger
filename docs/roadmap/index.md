# Rustledger Roadmap

Where rustledger is headed. This is a **forward-looking** document — it lists
what's planned and what we're exploring, not what's already done. For shipped
work, see the [CHANGELOG](https://github.com/rustledger/rustledger/blob/main/CHANGELOG.md).

## How this is organized

The roadmap is split by area, and each area file is forward-only:

| Area | What it covers |
|------|----------------|
| [Performance](./performance.md) | Parser/loader/query speed, memory, caching |
| [Importing & Ingestion](./importing.md) | Bank/broker imports, categorization, source archive |
| [Testing & Engineering Quality](./testing-and-quality.md) | Test depth, fuzzing, formal bridges, API stability, lint ratchets |
| [Formal Verification](./formal-verification.md) | TLA+ specs, Kani proofs |

Each area groups work into **Now** (in progress / next up), **Next**
(committed, well-scoped), and **Exploring / Later** (aspirational). Completed
items move out of the roadmap into the [CHANGELOG](https://github.com/rustledger/rustledger/blob/main/CHANGELOG.md), which
keeps these files from accumulating stale "done" entries.

> Lifecycle: **idea** (Exploring) → **tracked issue** (Next) → **in progress**
> (Now) → **shipped** (CHANGELOG). The roadmap captures intent; GitHub issues
> track committed work.

## Cross-cutting themes

A few directions span multiple areas and set the medium-term agenda:

### 1. Close the last beancount gaps
Rustledger is at 100% check / BQL / full-AST compatibility on the corpus. The
remaining divergences are narrow:
- **Arbitrary-precision decimal** ([#1240](https://github.com/rustledger/rustledger/issues/1240)) — the last numeric divergence from Python beancount.
- A **bean-price / bean-query / bean-report parity audit** to confirm flag- and output-level parity.
- **Plugin commutativity** — the one pipeline-invariant family not yet pinned (needs a `COMMUTATIVE` plugin marker). See [Testing & Quality](./testing-and-quality.md).

### 2. AI-assisted bookkeeping
The pieces already exist (a Naive-Bayes categorizer in `rustledger-ops`, WASM
plugins, a clean query/extract API). Natural next steps:
- An **MCP server** exposing query / extract / categorize so AI agents can
  drive rustledger directly.
- **LLM / MCP categorization** as an alternative to the statistical model, and
  **online learning** that improves the existing model from user corrections.
- **Anomaly / duplicate detection** on import.

### 3. Editor, web & developer experience
- A **browser playground** — the `rustledger-wasm` crate already compiles the
  engine to WASM; a web "try it" surface is mostly packaging.
- **LSP feature completeness** (rename, more code actions/refactors) and a
  possible **TUI report viewer**.
- Continued **diagnostics / `doctor`** improvements.

### 4. Extensibility & ecosystem
- A **shareable importer registry** (community `importers.toml` profiles).
- A **plugin registry / marketplace** for native and WASM plugins.

## Tracked work

Items with a GitHub issue are the committed near-term work:

- [#1240](https://github.com/rustledger/rustledger/issues/1240) — arbitrary-precision decimal
- [#923](https://github.com/rustledger/rustledger/issues/923) — IBKR importer

Everything else lives in the per-area files above until it's promoted to an
issue.
