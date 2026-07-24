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
| `capgains` | | Realized capital gains/losses per tax lot (short vs long term) |
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

### Realized Capital Gains

`capgains` reports **realized** gains and losses — what you *sold*, one row per
disposed tax lot — where `holdings` shows what you still *hold*. Each row carries
the lot's acquisition date, holding period, proceeds, cost basis, and gain/loss,
classified short vs long term.

```bash
rledger report ledger.beancount capgains
```

```text
Realized capital gains
===============================================================================

Sold       Commodity / account      Units  Acquired    Term   Proceeds       Gain
-------------------------------------------------------------------------------
2024-03-01 AAPL Stock                   8  2020-01-01    LT       1200        400
2024-04-01 AAPL Stock                   2  2020-01-01    LT        350        150
2024-04-01 AAPL Stock                   2  2023-06-01    ST        350        110
-------------------------------------------------------------------------------
Short-term    1 disposals   proceeds          350   gain          110 USD
Long-term     2 disposals   proceeds         1550   gain          550 USD
TOTAL       net realized gain          660 USD
```

| Option | Description |
|--------|-------------|
| `--account <PREFIX>` | Only disposals from accounts under this prefix. |
| `--year <YYYY>` | Only disposals in this calendar/tax year. |
| `--end <YYYY-MM-DD>` | Exclude disposals after this date. |
| `--long-term-days <N>` | Override the long-term threshold with a fixed day count (held strictly more than `N` days is long-term). |

**How it works.**

- A **disposal** is a reduction that carries a sale price (`@` per-unit or `@@`
  total). A sale crossing several lots produces **one row per lot** — each with its
  own acquisition date and cost basis — which is the shape tax forms (e.g. US Form
  8949) want. A costless transfer of a lot is not a disposal.
- **Proceeds** come from the sale price. For a `@@` total price the proceeds are
  pro-rated across the matched lots so they **sum exactly to the stated total**
  (a single-lot `@@` records the total verbatim, with no division rounding).
- **Cost basis** is the matched lot's booked cost; **gain = proceeds − cost basis**.
- **Short vs long term.** By default a lot is long-term when the sale is **more than
  one calendar year** after acquisition — the leap-year-correct US rule (a 366-day
  holding across a leap day is *not* yet long-term). `--long-term-days N` replaces
  this with a fixed day count. A lot with **no acquisition date** — e.g. under
  `AVERAGE` booking, which merges lots and drops their dates — has an indeterminate
  holding period and is reported as **`unknown`**, never silently short.
- **Short positions.** Covering a short is a disposal: the proceeds are what you
  received opening the short and the cost basis is what you paid to cover (the
  mirror of a long sale, so a cover *below* the short price is a gain). Short-sale
  gains are always **short-term**.
- **Lot matching** uses the ledger's own booking method (`option "booking_method"`,
  per-account `open ... "METHOD"`), so results match `rledger check`. A sale the
  ledger cannot book unambiguously (e.g. a bare `{}` reduction spanning
  different-cost lots under strict booking) is **skipped, not guessed** — run
  `rledger check` first to see those errors.
- **Consumes the loader's booking.** The gains come straight from the ledger's own
  booking pass (`report capgains` never re-books), so the report cannot disagree
  with `rledger check`. A transaction the ledger cannot book is reported as a normal
  load error on stderr, so an incomplete report is never silently mistaken for a
  complete one.
- **Total prices split exactly.** For a multi-lot `@@` (total) sale, each lot gets
  its exact pro-rata share (`total × units ÷ total_units`), unrounded — so the split
  is faithful (matching Python beancount) and never distorts or goes negative.
  Rounding to a display precision is left to the presentation layer.
- **Cross-currency disposals are flagged, not dropped silently.** If a sale's price
  is in a different currency than the lot's cost basis, the realized gain would need
  an FX rate this tool does not apply, so that disposal is omitted from the rows and
  a `warning:` with the count is printed to stderr.

Not a tax filing: wash-sale adjustments, separating currency gains from asset
gains, lots seeded by `pad` (no well-defined cost basis), and jurisdiction rules
beyond the long-term threshold are out of scope. Gains are reported in each lot's
**cost currency**, summarized per currency for a multi-currency ledger.

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
