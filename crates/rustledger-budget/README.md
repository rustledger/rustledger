# rustledger-budget

Budgeting for beancount ledgers — the shared model behind `rledger`'s budget
reporting.

Beancount has no budgeting of its own; the de-facto convention is **Fava's
`custom "budget"` directive**, which is plain, unextended Beancount syntax:

```beancount
2024-01-01 custom "budget" Expenses:Food      "monthly" 400.00 USD
2024-01-01 custom "budget" Expenses:Transport "weekly"   25.00 USD
2024-06-01 custom "budget" Expenses:Food      "monthly" 450.00 USD
```

A ledger already budgeted for Fava works unchanged — no new syntax, and the
ledger stays the only source of truth.

This crate owns the budget *model*: reading those directives, the calendar
interval arithmetic, supersession, and the per-day accrual that pro-rates a
budget over an arbitrary window. It does no ledger loading, no rendering and no
I/O, so every consumer — the CLI `report budget` command, the FFI component,
rustfava — shares one implementation rather than re-deriving rules subtle
enough to drift:

- **Per-day accrual with real calendar denominators.** Each day accrues
  `amount / days_in_its_calendar_interval`, so a monthly budget divides by 28,
  29, 30 or 31 and a yearly one by 365 or 366. Partial windows pro-rate with no
  special case. A fully covered interval accrues *exactly* the stated amount.
- **Calendar anchoring.** Intervals align to calendar boundaries (month = the
  1st, quarter = Jan/Apr/Jul/Oct 1, year = Jan 1, week = ISO Monday), not to the
  date the directive was written.
- **Supersession per (account, currency).** A later directive replaces an
  earlier one for the same account *and* currency from its own date; budgets in
  different currencies for one account stay simultaneously active.
- **Not retroactive.** A budget applies from its own date onward.

## Usage

```rust,ignore
use rustledger_budget::Budgets;

let (budgets, errors) = Budgets::from_directives(&directives);
for e in &errors {
    eprintln!("warning: {}: {}", e.date, e.reason);
}
let budgeted = budgets.accrue("Expenses:Food", "USD", from, to);
```

Malformed directives come back as errors rather than being dropped: a budget
that silently does not apply is worse than one that is reported, because the
report would otherwise show `0.00` budgeted and look like deliberate
under-spend.

## License

Licensed under either of Apache License, Version 2.0 or MIT license at your
option.
