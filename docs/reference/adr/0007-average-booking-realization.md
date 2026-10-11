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
  (Since #2394 it pools each side, long and short, separately; see the
  amendments below.)
- The query **realizes** an AVERAGE account as a single pool: the query
  `AccountInfo` carries the account's booking method, and `sum(position)` over a
  group whose postings all belong to one AVERAGE account calls `merge_average`.
  FIFO / LIFO / STRICT / HIFO / NONE accounts are unaffected. (Since #2394 the
  group is first replayed through booking; see the amendments below.)

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

## Amendment: one pool per side (#2393)

"All lots of a commodity share one running cost" holds while an account is on
one side. An account can hold a long and a short in the same commodity, and
pooling both sides was wrong: holding 5 at 102 and a short of 2 at 101, a sale
of 2 was booked at 102.67 instead of 102, the short vanished into the merged
remainder, and a cover of the short at 95 reported a loss of 8 instead of a
gain of 6. The surveyed systems model a single position, so they are silent on
this; the rule follows from the other booking methods and `{*}`, which all
match only lots of the opposite sign.

So an AVERAGE reduction pools the SIDE it takes from, the lots whose sign is
opposite the reduction's, and leaves the other side unchanged. A single-sided
account, the case this ADR was written for, is unaffected.

`merge_average` (the `sum(position)` realization above) was not changed here. It
merged a sum of postings, where every sale is already a negative lot at the
pool's cost, so sign cannot separate sales from shorts; on a mixed account
that view was wrong, and is fixed by the next amendment (#2394).

## Amendment: `sum(position)` realizes through booking (#2394)

The previous amendment left `merge_average` pooling both sides, because it
was handed a sum of postings in which a sale is a negative lot at the pool's
cost. On an account holding a long and a short that netted one into the
other: `-2 X {101}` beside `3 X {102}` came out as `1 X {104}`.

`sum(position)` over one AVERAGE account now replays the group's postings
through `BookingEngine::replay_transaction`, the walk `BALANCES` and
`account_balance` use, so every sale is taken from its pool before anything
is merged. In that realized inventory a negative lot is a short, so
`merge_average` now pools each side apart, as a reduction does. The account
counts as AVERAGE whether its `open` says so or the ledger's
`option "booking_method"` does.

Two seams remain, both deliberate:

- A subset booking cannot realize (a `WHERE` keeping a sale but not what it
  sold from) keeps the plain sum of its postings. `BALANCES` over the same
  `FROM` subset errors; erroring here would fail queries that answered
  before, and the plain sum is exactly what the selected postings add up to.
- Booking keeps an AVERAGE account's purchases as separate lots until a sale
  merges them, so before the first sale `BALANCES` and `report balances`
  list them while `sum(position)` shows the pool. The Decision above says
  the realized balance is the pool, so it is those surfaces that lag; making
  them present the pool is a separate change.

A property test (`sum_position_balances_agreement`) holds `sum(position)` to
`BALANCES` presented one pool per side, over generated ledgers and `FROM` and
`WHERE` subsets.

## Amendment: every surface presents the pool (#2543)

The second seam above is closed. An AVERAGE account is presented as its pool
on every surface, before a sale and after one: `BALANCES`, `sum(position)`,
the running `balance` column of `SELECT` and `JOURNAL`, `account_balance`, and
`report balances`. This is presentation only; booking is unchanged, so the
dated lots and their exact totals stay underneath for what needs them
(`report capgains`).

- **Pool key:** commodity, cost currency and side. X held at a USD cost never
  pools with X at a EUR cost; each pools its own lots. `merge_average` used to
  leave a side with mixed cost currencies unmerged altogether.
- **Pool contents:** undated, at the exact total cost of its lots; the
  per-unit cost is rounded only for display (`report balances` printed it at
  full `Decimal` precision). A single lot is a pool too, so it shows undated.
- **One implementation:** `rustledger_booking::present_inventory`, which is
  `merge_average` for an AVERAGE account and nothing for any other.
  `BookingEngine::into_presented_inventories` applies it to a realization,
  for `BALANCES` and `report balances`; `account_balance` applies it to its
  snapshot; the running `balance` column realizes each AVERAGE account's
  rows as `sum(position)` does (each transaction's rows replayed as one, in
  booking's order) and applies it to that.

The running `balance` column was never realized at all: after a sale it listed
both lots bought plus the sale as a negative lot, which the account never held.
It keeps the plain sum, unmerged, for rows booking cannot realize, as
`sum(position)` does. Every other account's rows are still summed as
bean-query sums them. The property test now holds `sum(position)` to `BALANCES`
exactly, and the running balance's last row to `sum(position)`.

## Amendment: a stated cost is a claim about the pool (#2603)

A sale is booked at the pool's average, so the cost number in its spec had no
role, and it was dropped: `-1 X {99.00 EUR}` from a pool at 11.00 EUR booked at
11.00 without a word. Under every other method a written cost is a filter and
one no lot matches is an error, so here the number is a claim about the
average, checked rather than discarded. The currency was already checked
(#2589).

The claim holds when it is within the transaction's tolerance for the cost
currency of the pool's exact average: `|claim - total / units| <= tolerance`,
compared as `|claim × units - total| <= tolerance × |units|` with the pool's
exact unit and cost totals (each lot's kept exact total, #2425), so the average
is never rounded. The tolerance is the balance check's, rounded down, so it is
never looser than the one the transaction balances to (#2562, #2582). A
transaction that infers none in that currency holds the claim to the places it
is written to, half a unit in its last place, which is the rule a `{*}` claim
follows (#2398); without that, no claim could hold for an average with no
finite decimal. A total cost states the total divided by the units sold, and a
compound cost `a + b / units`. The check runs in booking only, as the `{*}`
check does: the validator and BQL see the booked posting, whose cost is the
pool's by then, and a filtered BQL replay builds a different pool on purpose
(#1985).

## Prior art

- hledger `SPEC-lots` — single running pool; pool cost rewritten on acquisition.
- Beancount PR #591 / issue #213 — AVERAGE ≡ automatic `{*}` lot merging.
- GnuCash average-cost scrub; ERPNext Moving Average; Odoo AVCO; QuickBooks
  Desktop average costing.
