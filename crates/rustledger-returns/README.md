# rustledger-returns

Investment returns math for beancount ledgers — the shared, pure computation
engine behind `rledger`'s returns reporting ([#1814]).

This crate owns only the math. It has no ledger loading, no price database, and
no I/O, so every consumer (the CLI `report returns` command, and later the query
engine, the FFI component, and rustfava) reuses one implementation instead of
re-deriving it. Cash-flow *extraction* from a ledger — deciding which postings
cross an investment's boundary, classifying dividends, converting to a single
reporting currency, and valuing the position still held at the report end date —
is the caller's job.

## Status

- [x] `xirr` — money-weighted return (annualized internal rate of return) over
  an irregularly-spaced cash-flow series, via Newton's method with a bisection
  fallback. Actual/365 day count, matching spreadsheet `XIRR` and beangrow.
- [ ] Time-weighted return (Modified Dietz / true TWR) — lands with the
  cash-flow extraction layer, which supplies the per-date portfolio valuations
  it needs.

## Sign convention

Flows are investor-centric: money put in (a purchase) is negative; money taken
out (sale proceeds, dividends, and the terminal market value of the position) is
positive.

[#1814]: https://github.com/rustledger/rustledger/issues/1814
