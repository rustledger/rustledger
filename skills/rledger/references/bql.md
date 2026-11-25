# BQL for rledger

BQL is the query language of `bean-query`, which `rledger query` implements.
Every query below was run against the complete ledger in
[beancount-syntax.md](beancount-syntax.md). The full language, with every
column and function, is the
[BQL reference](https://github.com/rustledger/rustledger/blob/main/docs/reference/bql.md).

```bash
rledger query ledger.beancount "QUERY"
rledger query -f json ledger.beancount "QUERY"
```

## The model: one row per posting

A plain `SELECT` returns one row per **posting**, not per transaction. A
two-posting transaction matches twice unless the `WHERE` picks one posting
(usually by `account`). `count(*)` counts postings. Use `SELECT DISTINCT` on
transaction-level columns to get one row per transaction.

```sql
SELECT DISTINCT date, narration WHERE 'trip-paris' IN links
```

## Shape of a query

```sql
SELECT [DISTINCT] columns
[FROM [OPEN ON date] [CLOSE ON date] [CLEAR]]
[WHERE condition]
[GROUP BY columns] [HAVING condition]
[ORDER BY columns [ASC|DESC]] [LIMIT n]
```

Comments are `/* ... */`. `--` is **not** a comment (`3--2` is `3 - -2`).
Strings use single quotes; dates are bare literals (`2024-01-01`).

## Columns you will use

| Column | Meaning |
|--------|---------|
| `date`, `year`, `month`, `day` | transaction date and its parts |
| `flag` | `*` or `!` |
| `payee`, `narration`, `description` | header strings (`payee` may be NULL) |
| `tags`, `links` | sets: test with `'name' IN tags`, never `=` or `~` |
| `account` | this posting's account |
| `position` | units plus cost (`10 AAPL {150.00 USD}`) |
| `units`, `number`, `currency` | units, its number, its currency |
| `cost_number`, `cost_currency`, `cost_date` | the lot's cost |
| `weight` | the amount the posting contributes to balancing |
| `price` | the `@` price, if any |
| `balance` | running total over the rows the `WHERE` keeps |
| `filename`, `lineno` | the source file and the posting's line |

## Functions you will use

| Function | Meaning |
|----------|---------|
| `sum(x)`, `count(*)`, `min(x)`, `max(x)`, `first(x)`, `last(x)` | aggregates |
| `units(p)`, `cost(p)` | a position or inventory's units, or its total cost |
| `value(p)` | market value at the latest `price` |
| `convert(p, 'USD')` | convert to a currency through prices |
| `year(date)`, `month(date)`, `quarter(date)`, `yearmonth(date)` | date parts (`yearmonth` is the first of the month, a date) |
| `meta('k')` / `entry_meta('k')` / `any_meta('k')` | posting / transaction / either metadata |
| `has_account('regex')` | in `PRINT FROM`, entries touching a matching account |

`meta('k')` reads posting metadata only. For a key written under the
transaction header, use `entry_meta('k')` or `any_meta('k')`; `meta` quietly
returns NULL there.

## Matching

`~` is an unanchored, case-sensitive regular expression search:
`account ~ 'Food'` matches `Expenses:Food:Coffee` and `Assets:Food-Bank`.
Anchor it (`'^Expenses:Food'`), add `(?i)` for case-insensitive, or use `=`
for an exact account.

## Shortcuts

| Statement | Equivalent |
|-----------|------------|
| `BALANCES` | balance of every account |
| `BALANCES AT cost` / `BALANCES AT value` | at cost, or at market value |
| `JOURNAL 'Assets:Bank'` | postings with running balance (regex) |
| `PRINT FROM has_account('Rent')` | matching entries as Beancount text (use `-f beancount`) |

## Tested examples

Balances by account:

```sql
SELECT account, sum(position) GROUP BY account ORDER BY account
```

Spending by category in 2024, largest first:

```sql
SELECT account, sum(position) WHERE account ~ '^Expenses:' AND year = 2024 GROUP BY account ORDER BY sum(position) DESC
```

Monthly spending converted to one currency:

```sql
SELECT yearmonth(date) AS month, sum(convert(position, 'USD')) AS spent WHERE account ~ '^Expenses:' GROUP BY month ORDER BY month
```

Holdings at units, cost and market value:

```sql
SELECT account, units(sum(position)) AS units, cost(sum(position)) AS cost, value(sum(position)) AS market WHERE account ~ '^Assets:Brokerage' GROUP BY account
```

Balance sheet accounts as of a date (`CLOSE ON` is exclusive):

```sql
SELECT account, sum(position) FROM CLOSE ON 2024-04-01 WHERE account ~ '^Assets:' GROUP BY account
```

Total income in a date range:

```sql
SELECT sum(position) WHERE account ~ '^Income:' AND date >= 2024-01-01 AND date < 2025-01-01
```

Running balance of one account (for a failing balance assertion):

```sql
SELECT date, narration, position, balance WHERE account = 'Assets:Bank:Checking' AND date < 2024-03-01
```

Transactions by metadata, tag or flag:

```sql
SELECT DISTINCT date, narration, entry_meta('receipt') AS receipt WHERE entry_meta('receipt') IS NOT NULL
```

```sql
SELECT date, account, position WHERE flag = '!'
```

Case-insensitive text search with source location:

```sql
SELECT filename, lineno, date, narration, position WHERE narration ~ '(?i)coffee'
```

Filter on an aggregate:

```sql
SELECT account, sum(position) WHERE account ~ '^Expenses:' GROUP BY account HAVING sum(number) > 50
```

## Output for programs

`-f json` gives `{"columns": [...], "row_count": N, "rows": [[...]]}`. Decimal
numbers are strings (`"82.15"`), so parse them as decimals, not floats;
counts are integers; a position is
`{"units": {"number", "currency"}, "cost": {...}}`. `-f csv` writes a header row
and one line per row. `-m` drops currencies from amounts.

`sum(position)` is an inventory, which in JSON is
`{"positions": [{"number": "82.15", "currency": "USD"}, ...]}` even when it
holds one currency. Use `sum(number)` with `GROUP BY currency`, or
`convert(...)`, when you need a single number.
