______________________________________________________________________

## title: rledger report description: Generate financial reports

# rledger report

Generate standard financial reports from your ledger.

## Usage

```bash
rledger report [OPTIONS] [FILE] [COMMAND]
```

A report subcommand (e.g. `balances`, `journal`) is required — running `rledger report FILE` with no subcommand errors. `FILE` precedes the subcommand.

## Subcommands

| Command | Alias | Description |
|---------|-------|-------------|
| `balances` | | All account balances |
| `balsheet` | `bal` | Balance sheet (Assets, Liabilities, Equity) |
| `income` | `is` | Income statement (Income, Expenses) |
| `journal` | `register` | Transaction register |
| `holdings` | | Investment holdings with cost basis |
| `returns` | | Investment returns — money-weighted (XIRR) and time-weighted |
| `networth` | | Net worth over time |
| `accounts` | | List all accounts |
| `commodities` | | List all currencies/commodities |
| `prices` | | List price entries |
| `stats` | | Ledger statistics |

## Global Options

| Option | Description |
|--------|-------------|
| `-P, --profile <PROFILE>` | Use a profile from config |
| `-f, --format <FORMAT>` | Output: `text`, `csv`, `json` |
| `-v, --verbose` | Show verbose output |
| `--no-pager` | Disable pager for output |
| `--no-cache` | Disable the on-disk parse cache (always re-parse) |

## Examples

### Account Balances

```bash
rledger report ledger.beancount balances
```

Filter by account:

```bash
rledger report ledger.beancount balances -a Expenses
rledger report ledger.beancount balances -a Assets:Bank
```

### Balance Sheet

```bash
rledger report ledger.beancount balsheet
# or
rledger report ledger.beancount bal
```

Output:

```
Assets
  Bank:Checking         5,234.00 USD
  Bank:Savings         12,000.00 USD
  Investments           8,500.00 USD
───────────────────────────────────────
Total Assets           25,734.00 USD

Liabilities
  CreditCard              -450.00 USD
───────────────────────────────────────
Total Liabilities         -450.00 USD

Net Worth              25,284.00 USD
```

### Income Statement

```bash
rledger report ledger.beancount income
# or
rledger report ledger.beancount is
```

### Transaction Journal

```bash
# All transactions
rledger report ledger.beancount journal

# Filter by account
rledger report ledger.beancount journal -a Expenses:Food

# Limit entries
rledger report ledger.beancount journal -l 20
```

### Holdings

```bash
rledger report ledger.beancount holdings
```

Output:

```
Account                   Units     Cost Basis    Market Value    Gain/Loss
─────────────────────────────────────────────────────────────────────────────
Assets:Brokerage:AAPL     10.00     1,500.00 USD   1,750.00 USD   +250.00 USD
Assets:Brokerage:GOOGL     5.00     2,000.00 USD   2,100.00 USD   +100.00 USD
```

### Investment Returns

`returns` reports the annualized return of a portfolio, both:

- **Money-weighted return (MWR / XIRR)** — the internal rate of return on *your*
  cash: it accounts for how much you invested and *when*. This is "what did I
  earn on the money I put in".
- **Time-weighted return (TWR)** — the return of the *investments themselves*,
  with the effect of contribution timing removed (the GIPS / fund-comparison
  metric). This is "how did my picks perform", independent of when you added money.

You must tell it which accounts form the portfolio. Because a return is a single
number in one currency, the report is always single-currency.

| Option | Description |
|--------|-------------|
| `-i, --investments <PREFIX>` | **Required, repeatable.** Account prefix(es) holding the investments — the portfolio boundary, e.g. `Assets:Brokerage`. |
| `-n, --income <PREFIX>` | Repeatable. Account prefix(es) for the investments' income/expenses — dividends, realized gains, broker fees, e.g. `Income:Dividends`. Including them makes the return **dividend-inclusive**. |
| `-c, --currency <CCY>` | Reporting currency. Defaults to the ledger's first `operating_currency`. |
| `-e, --end <YYYY-MM-DD>` | Valuation date — the horizon (later activity is ignored) and the date the still-held position is priced. Defaults to today. |
| `--by-group` | Add one row per `returns-group:` group (see below). |

```bash
rledger report ledger.beancount returns \
  --investments Assets:Brokerage \
  --income Income:Dividends \
  --end 2023-12-31
```

Output:

```
Returns
============================================================

Reporting currency      USD (as of 2023-12-31)
Cash flows              5
Invested                22700 USD
Distributions           60 USD
Current value           25550 USD

Money-weighted return   6.43%
Time-weighted return    6.24%
```

> **Prices are required.** The report errors — naming the missing commodity and
> date — if it can't value the position still held at `--end`, or convert a
> boundary cash flow to the reporting currency. (A missing price at an
> *intermediate* cash-flow date is less fatal: it degrades the time-weighted
> return to `n/a` while the rest of the summary is still reported.) Provide
> `price` directives to cover your holdings at the report date.

#### What the report computes over

Both returns are derived from two things: your **cash flows** — money crossing the
portfolio boundary, i.e. contributions in and withdrawals/dividends out — and the
**market value** of the position still held at `--end` (`net units × price`). They
do **not** depend on cost basis or lot matching. Cost lots matter for *realized
capital gains*, which these figures don't use.

A practical consequence: an **imperfect or freshly-imported ledger still reports.**
Brokerage imports routinely leave cost-basis gaps — an empty-cost `{}` sale with no
matching lot, a sale of more units than the ledger records buying, or a holding
whose opening purchase predates the import. `report returns` sums the *net* units
(a net-short position simply values **negative** at market) and reports the return;
it does not refuse. Validate the bookkeeping itself — unmatched lots, unbalanced
transactions — separately with [`rledger check`](check.md) (the equivalent of
`bean-check`). **`report returns` is a reporting tool, not a validator.**

What this means in practice:

- **Short / negative positions** value at market (negatively) and are reported, not
  treated as errors.
- **Losing portfolios** produce a real **negative** rate (e.g. `-42.10%`), never a
  crash or a silent `n/a`.
- Because returns ignore cost basis, they can **disagree with `report balances` /
  `report holdings`** (which lot-match) on a ledger with **booking / lot errors**
  (e.g. an over-sell that does not book cleanly) — the over-sell shows as a negative
  net position here but is ignored there. That is a signal the ledger's bookkeeping
  is broken; run [`rledger check`](check.md) to find and fix it.
- **Only two things** actually stop a figure. First, a missing **price** for a
  *held position at `--end`* or an *unconvertible boundary flow* — note a missing
  price at an intermediate cash-flow date is **not** fatal (it degrades only TWR to
  `n/a`, per the callout above). Second, a posting whose **units are elided** and
  could not be interpolated — either a held quantity (unknown holding) or a boundary
  cash leg (unknown flow). Both errors name exactly what is missing.

#### Per-group breakdown

To see the return of each part of your portfolio with `--by-group`, tag the relevant `open`
directives with `returns-group: "Name"` and pass `--by-group`. A group that also
tags its dividend/income account reports a **dividend-inclusive** return.

```beancount
2022-01-01 open Assets:Brokerage:AAPL
  returns-group: "Stocks"
2022-01-01 open Assets:Brokerage:VOO
  returns-group: "Stocks"
2022-01-01 open Assets:Brokerage:BND
  returns-group: "Bonds"
2022-01-01 open Income:Dividends
  returns-group: "Stocks"
```

```bash
rledger report ledger.beancount returns \
  --investments Assets:Brokerage \
  --income Income:Dividends \
  --by-group --end 2023-12-31
```

Output:

```
Returns  (USD, as of 2023-12-31)
===============================================================================

Group                        MWR      TWR    Invested Distributions     Current
-------------------------------------------------------------------------------
Bonds                     -5.58%   -5.58%        8000             0        7200
Stocks                    11.96%   11.97%       14700            60       18350
-------------------------------------------------------------------------------
TOTAL                      6.43%    6.24%       22700            60       25550
Note: TOTAL is the whole portfolio, not the sum of the groups.
```

Notes on grouping:

- **Opt-in and independent.** Grouping only happens with `--by-group`. Each group
  is an *independent sub-portfolio* — its return is computed over just its own
  accounts, like a separate report. This matches how beangrow and hledger `roi`
  present grouped returns.
- **Groups do not sum to TOTAL.** The `TOTAL` row is the whole portfolio, printed
  for reference — not the sum of the group rows. (Untagged in-scope holdings are
  counted in TOTAL but appear in no group.) Two groups that share a cash account,
  for instance, can't be added up cleanly.
- **Warnings.** rledger prints a `warning:` to stderr for cases that would
  otherwise mislead:
  - a `returns-group:` tag on an account outside `--investments`/`--income`;
  - a non-string `returns-group:` value;
  - two groups whose accounts overlap by prefix (the shared holding is counted
    in both);
  - a group that is **not self-contained** — it shares an in-scope account
    (typically pooled settlement cash) with the rest of the portfolio, so its
    return counts an internal transfer as a flow;
  - a group named `TOTAL` (it collides with the total row in text/CSV output);
  - `--by-group` with no in-scope `returns-group:` tags (the report then shows
    only the TOTAL row).
- **Partial reports.** Because each group is valued independently, a group (or the
  `TOTAL`) that hits one of the two blockers above — an unpriced commodity or an
  elided posting — shows `n/a` across its row, with a `warning:` naming the reason,
  while the other groups still report their figures. The rows are always rendered;
  only when *every* row is unvaluable is nothing shown. In `--format json` an
  unvaluable row carries an `"error"` field (with `null` figures); a computed row's
  `"error"` is `null`, so the schema is the same for both.

  **Exit status.** When any row is unvaluable, `rledger` **exits non-zero** even
  though it still prints the partial report — an incomplete report is not a full
  success, so a script gating on the exit code (`rledger ... && ...`) stops rather
  than consuming a report with silent `n/a` holes. For CSV and text (which have no
  error column) the exit code is the only machine-readable "incomplete" signal.

See [`returns-group:` metadata](../reference/syntax.md#returns-group-metadata) for
the tagging syntax.

### Net Worth Over Time

```bash
rledger report ledger.beancount networth
```

### Statistics

```bash
rledger report ledger.beancount stats
```

Output:

```
Ledger Statistics
─────────────────
Transactions:     1,234
Accounts:            45
Commodities:          3
Directives:       1,456
Date range:       2020-01-01 to 2024-03-15
```

### Output Formats

```bash
# CSV for spreadsheets
rledger report -f csv ledger.beancount balances > balances.csv

# JSON for scripts
rledger report -f json ledger.beancount balances | jq '.'
```

## See Also

- [query](query.md) - Custom queries with BQL
- [Common Queries](../guides/common-queries.md) - More report examples
