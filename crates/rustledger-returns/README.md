# rustledger-returns

Investment returns math for beancount ledgers — the shared, pure computation
engine behind `rledger`'s returns reporting ([#1814]).

This crate owns the returns *math* and the *extraction* that feeds it — turning
a booked ledger into the dated, single-currency cash-flow series a return is
computed from (deciding which postings cross an investment's boundary, excluding
internal transfers, valuing the position still held at the report end date, and
converting to one reporting currency). It has no ledger loading, no price index,
and no I/O: prices arrive through the `PriceOracle` trait, so the crate stays a
leaf and every consumer (the CLI `report returns` command, and later the query
engine, the FFI component, and rustfava) reuses one implementation instead of
re-deriving it.

## Status

- [x] `xirr` — money-weighted return (annualized internal rate of return) over
  an irregularly-spaced cash-flow series, via Newton's method with a Brent's
  method fallback. Actual/365 day count, matching spreadsheet `XIRR` and beangrow.
- [x] `extract_cash_flows` — booked ledger + account-role `Scope` +
  `PriceOracle` + end date → the `CashFlow` series, with structural
  internal-transfer exclusion and a terminal market valuation of the position
  still held.
- [x] `twr` — annualized time-weighted return via the unit-value (NAV) method:
  values the portfolio at each cash-flow date and chains the sub-period returns,
  so it measures the investments' performance independent of contribution
  timing. Shares the `investment_value_at` realization primitive with
  `terminal_value`.
- [ ] Dividend / ex-dividend breakout (total vs. ex-income return).
- [ ] Per-commodity / named-group breakdown ([#1820]).

[#1820]: https://github.com/rustledger/rustledger/issues/1820

## Sign convention

Flows are investor-centric: money put in (a purchase) is negative; money taken
out (sale proceeds, dividends, and the terminal market value of the position) is
positive.

[#1814]: https://github.com/rustledger/rustledger/issues/1814
