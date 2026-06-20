# ADR-0007: AVERAGE booking realizes a single weighted-average pool

## Status

Accepted

## Context

Rustledger supports an `AVERAGE` booking method on accounts (`open ... "AVERAGE"`)
— a weighted-average-cost (WAC) model where all lots of a commodity share one
running cost. Python Beancount notably does *not* implement AVERAGE (it errors
with "AVERAGE method is not supported"), so there is no upstream oracle.

The original implementation was broken in two ways, found by dogfooding:

- A partial sale across multiple lots returned **every** matched lot from
  `reduce_average`, which the booking consumer (`book.rs`) expanded into one
  reduction posting per lot — silently **emptying the whole position** and
  booking a garbage capital gain.
- The account balance showed each purchase lot separately
  (`10 {150}  10 {170}  -5 {160}`) instead of a single pool.

We surveyed how WAC is actually modeled — hledger `SPEC-lots`, Beancount PR #591
("AVERAGE booking ≡ `{*}` lot merging"), GnuCash "scrub by average cost",
ERPNext / Odoo (AVCO), QuickBooks Desktop. **They are unanimous: AVERAGE is a
single running weighted-average pool**, recomputed on each acquisition; a sale
draws COGS at the current average and leaves the average unchanged. Keeping
separate lots is the FIFO / specific-identification model, not average.

Two design risks that make AVERAGE "rare in PTA" were investigated and found not
to apply to rustledger:

- **Rolling-state balance assertions.** Editing a past transaction shifts the
  running average for every later one, which would make cost-bearing balance
  assertions history-dependent. Rustledger's `balance` assertions are
  **quantity-only** (they ignore the `{cost}` annotation today), so there is no
  rolling-state interaction to manage.
- **Decimal precision.** Repeating-decimal averages (e.g. `2450/15 = 163.333…`)
  compute exactly under `rust_decimal` (28 digits); gains were already correct
  to full precision.

## Decision

Model an `AVERAGE` account as **one weighted-average pool**, realized at the
balance, while the **journal keeps the real per-lot purchase costs** (matching
hledger: the pool is rewritten, the journal is not).

- `Inventory::reduce_average` returns a **single synthetic matched lot** of the
  reduced quantity at the average cost, and keeps the average cost on the
  remainder.
- `Inventory::merge_average` collapses all cost-bearing lots of a currency into
  one weighted-average lot (`Σ(units·cost) / Σ units`); cost-less (cash)
  positions and net-zero currencies are handled cleanly.
- The query **realizes** an AVERAGE account as a single pool: the query
  `AccountInfo` carries the account's booking method, and `sum(position)` over a
  group whose postings all belong to one AVERAGE account calls `merge_average`.
  FIFO / LIFO / STRICT / HIFO / NONE accounts are unaffected.

## Consequences

- The realized balance of an AVERAGE account is a single `N COMM {avg}` lot, as
  every other WAC implementation produces. Capital gains use the running
  average.
- The journal (`JOURNAL`, the raw postings) still shows the true acquisition
  costs, preserving the audit trail. Only aggregated balances merge.
- The realization merge is applied in the per-account aggregation path. A bare
  `sum(position)` that spans *multiple* accounts is left unmerged (merging across
  accounts is ill-defined); this is a documented seam, not a correctness issue.
- Because `balance` assertions are quantity-only, AVERAGE introduces no
  rolling-state assertion problems. If cost-aware balance assertions are added
  later, their interaction with the rolling average must be revisited.

## Prior art

- hledger `SPEC-lots` — single running pool; pool cost rewritten on acquisition.
- Beancount PR #591 / issue #213 — AVERAGE ≡ automatic `{*}` lot merging.
- GnuCash average-cost scrub; ERPNext Moving Average; Odoo AVCO; QuickBooks
  Desktop average costing.
