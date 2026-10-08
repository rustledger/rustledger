# Beancount Compatibility Report

This document describes the compatibility between rustledger and Python beancount, based on testing 792 real-world beancount files from multiple sources.

## Summary

| Metric | Value |
|--------|-------|
| Files tested | 792 |
| Check exit match | **100%** |
| BQL query data match | **100%** |
| Full-AST match | **100%** |

## Test Sources

Files were collected from:

- beancount v2/v3 official repositories
- beancount-parser-lima test suite
- fava web interface fixtures
- beangulp importer framework
- ledger2beancount converter tests
- beancount-import test data
- Community plugin repositories

## Compatibility Status

With 100% check compatibility on 792 files, rustledger matches Python beancount's validation behavior on the tested corpus. The test suite includes files from:

- Official beancount v2/v3 repositories
- Parser conformance tests
- Real-world example ledgers
- Edge cases and error scenarios

Files with expected Python-only errors (plugin configuration, deprecated options) were excluded from the test set as they test Python-specific features.

## Known Differences

### 1. Multi-Currency Transactions

Python beancount allows transactions with multiple currencies without explicit conversion prices. Rustledger requires either:

- A price (`@` or `@@`) annotation
- All postings in the same currency
- Explicit balancing

**Workaround**: Add `@ 1.0 USD` or appropriate price to multi-currency transactions.

### 2. Python Plugin Loading

Rustledger does not execute Python plugins. Files using `plugin "some_python_plugin"` will:

- Parse successfully
- Report error E8001 "Plugin not found" for unknown plugins
- This matches Python beancount's behavior of failing on missing plugins

Rustledger supports 31 native plugins that match Python beancount behavior:

- `auto_accounts`, `auto_tag`, `box_accrual`, `gain_loss`
- `long_short`, `check_average_cost`, `check_closing`, `check_commodity`
- `check_drained`, `close_tree`, `coherent_cost`, `commodity_attr`
- `currency_accounts`, `effective_date`, `forecast`, `generate_base_ccy_prices`
- `implicit_prices`, `leafonly`, `noduplicates`, `nounused`
- `onecommodity`, `pedantic`, `rename_accounts`, `rx_txn_plugin`
- `sellgains`, `split_expenses`, `unique_prices`, `unrealized`
- `valuation`, `zerosum`

Additionally, `document_discovery` auto-discovers documents from `option "documents"` directories.

**Workaround**: Use rustledger's native plugins where available, or remove unsupported plugin directives.

### 3. Push/Pop Meta and Tag Validation

Python beancount validates that `pushtag`/`poptag` and `pushmeta`/`popmeta` directives are balanced. Rustledger's validation is less strict in some edge cases.

### 4. Deprecated Options

Python beancount reports errors for deprecated options like `plugin_processing_mode`. Rustledger ignores unknown options.

### 5. BQL Display Precision

Python's bean-query uses a "display context" that infers typical decimal precision for each currency based on the amounts seen in a file. When most amounts are integers, Python truncates decimal display:

```
# File contains: 111.11 USD
Python bean-query shows: 111 USD
Rustledger shows:        111.11 USD
```

This is a display-only difference - actual values are identical. Rustledger preserves the original precision, which is technically more accurate.

### 6. Balance Tolerance Grammar

Beancount's tolerance grammar is `NUMBER ~ NUMBER CURRENCY` — one currency,
trailing — and it rejects any currency written before the `~`. Rustledger
differs in both directions, on one rule: **accept what has exactly one meaning,
diagnose what has none or contradicts itself.**

| form | beancount 3.2.3 | rustledger |
|---|---|---|
| `1.00 ~ 0.01 USD` | ok | ok |
| `0.25 + 0.75 ~ 0.01 USD` | ok | ok |
| `1.00 ~ 0.005 + 0.005 USD` | ok | ok |
| `1.00 USD ~ 0.01 USD` | syntax error | **accepted** |
| `0.25 + 0.75 USD ~ 0.01 USD` | syntax error | **accepted** |
| `1.00 USD ~ 0.01 EUR` | syntax error | **diagnosed** |
| `1.00 ~ 0.001 0.02 USD` | syntax error | **diagnosed** |
| `1.00 ~ 0.01 ~ 0.02 USD` | syntax error | **diagnosed** |
| `1.00 USD ~ 0.01` | syntax error | **accepted** |
| `1.00 USD ~` | syntax error | **diagnosed** |

**Laxer, deliberately.** `1.00 USD ~ 0.01 USD` states the currency twice and
agrees with itself. There is one reading, and `rledger format` canonicalizes it
to `1.00 ~ 0.01 USD` losslessly, so refusing it would reject a file whose
meaning is not in doubt.

**Stricter, deliberately.** The other two are not redundancy. A tolerance
denominated in a currency the amount does not use asserts something the model
has no field for, and a second juxtaposed number has no reading at all. Both
used to be accepted, read in part, and the remainder discarded without a word —
and `rledger format` then wrote that loss back to the file, turning
`1.00 USD ~ 0.01 EUR` into `1.00 ~ 0.01 USD`.

`1.00 USD ~ 0.01` follows from the same rule: the currency is stated once and
the tolerance inherits it, so there is one reading. Each rejection is diagnosed
for its own reason rather than a generic one — a second `~` is reported as a
second tolerance, not as juxtaposed numbers.

**Portability note.** A file using the accepted-but-non-standard spelling loads
in rustledger and is a syntax error in beancount and tools built on it. Prefer
the single trailing currency if the file needs to load elsewhere.

Pinned by `balance_tolerance_accepts_one_reading_and_diagnoses_none`, whose
table records what beancount does for each row (issue #2193).

### 7. Cross-File Booking Order

Directives sharing a date and type keep the order they were parsed in. Within
one file that matches Python's `(date, type_priority, lineno)`. Across
`include`s it does not, and the difference shows up in reported gains.

Python compares `lineno` values taken from different files, so a directive on
line 1 of a file included second sorts ahead of one on line 5 of a file
included first. Rustledger keeps include order: everything from the first
included file, in its own order, then the second.

Two same-date lots therefore enter the inventory in different orders, and a
FIFO sale whose lot-date comparison ties falls through to that order:

```beancount
; first.beancount, included FIRST, buy on line 5
2024-06-01 * "buy-at-10"
  Assets:S      1 HOOL {10.00 USD}
  Assets:Cash            -10.00 USD

; second.beancount, included SECOND, buy on line 1
2024-06-01 * "buy-at-20"
  Assets:S      1 HOOL {20.00 USD}
  Assets:Cash            -20.00 USD
```

Selling one unit at 30.00:

| | lot consumed | `Income:Gains` |
|---|---|---|
| beancount 3.2.3 | 20.00 | -10.00 USD |
| rustledger | 10.00 | -20.00 USD |

Swapping the two `include` lines pins each rule down: beancount is invariant
and reports -10.00 either way; rustledger tracks include order and reports
-20.00 in one arrangement, -10.00 in the other. Neither errors nor warns.

This one is deliberate. Ordering two directives by comparing a line number from
one file against a line number from a different file is not a fact about the
ledger -- adding a comment to one file silently changes which lot a sale in
another file consumes. Include order at least reflects how the author assembled
the ledger. Beancount's rule is not purely line-number driven either:
directives sharing a line number across files fall back to include order
through its own stable sort.

Ledgers that need a specific lot should name it (`{10.00 USD, 2024-06-01}`, or
a label) rather than relying on either tiebreak.

Fixture: `tests/fixtures/cross-file-order/`. Pinned by
`cross_file_same_date_directives_keep_include_order` (issue #2149).

### 8. Same-Date Directive Ordering in `#entries`

beancount sorts entries by `(date, type_priority, lineno)`, and its priorities
put Transaction, Pad, Note, Price, Event, Query, Commodity and Custom in ONE
bucket, tie-broken by line number. We give each type its own priority, so
same-date directives group by type rather than interleaving by line.

Visible when a `pad` shares its date with a `note`, `price` or `close`:

```text
bean-query   balance pad transaction note price close
rustledger   balance pad note price close transaction
```

Cosmetic: notes, prices and closes carry no postings, so no balance moves. The
balance-affecting case -- a pad sharing its date with an unrelated transaction
-- agrees, and a synthesized padding transaction sits at the end of its date
group in both tools rather than displacing entries ahead of it.

This is the same type-grouping-versus-`lineno` difference as issue #2149,
which also covers the cross-file half described in section 7. Pad placement
specifically is pinned by `pad_insertion_index` and its tests (issue #2188).

### 9. Shorthand Command Column Names

`BALANCES` and `JOURNAL` name their columns differently:

| query | bean-query | rustledger |
|---|---|---|
| `BALANCES` | `account, SUM((position))` | `account, balance` |
| `JOURNAL` | `date, flag, MAXWIDTH(payee, 48), MAXWIDTH(narration, 80), ...` | `date, flag, payee, narration, ...` |
| `JOURNAL ... AT COST` | `..., cost(position), cost(balance)` | `..., position, balance` |

The rows agree in every case; only the labels differ.

bean-query's names are not chosen. `transform_journal` builds the query by
parsing a SQL string template whose targets carry no `AS` aliases, so the names
fall through to the generic "render the expression as its name" path --
`MAXWIDTH(payee, 48)` is a display-truncation call leaking into a column name,
and `SUM((position))` carries the doubled parens of its desugared expression.
Ours are what the template meant.

Keeping ours on purpose: matching would mean printing an implementation detail
of bean-query's query compiler as a user-facing column name. Recorded in
`KNOWN_HEADER_DIVERGENCES` in `scripts/compat-bql-test.py`, scoped to headers
so a data regression on the same query is still caught (issue #2221).

Contrast `PIVOT BY`, whose column names bean-query sets in its evaluator and
exposes through its API -- those are part of the result's structure and we do
match them (issue #2217).

### 10. Multi-Currency Inventory Rendering

`SELECT account, SUM(position) GROUP BY account` over a multi-currency result:

```text
bean-query   Assets:CORP," 100 CORP { 1 USD},        "
             Assets:Cash,"                  ,-100 USD"

rustledger   Assets:CORP,100 CORP { 1 USD}
             Assets:Cash,-100 USD
```

bean-query renders one field holding a slot per currency seen anywhere in the
result, empty slots padded so currencies line up vertically. That is its
`InventoryRenderer` doing table layout -- its API returns a plain `Inventory`
(`(100 CORP {1 USD})`), with no slots and no padding, which is what we emit.

The values agree. Reproducing the slots would mean carrying a column-alignment
artifact into a machine-readable format, where the padding has nothing to align
(issue #2222).

### 11. PIVOT BY, ORDER BY and LIMIT

`ORDER BY` and `LIMIT` apply to the PIVOTED rows here; bean-query applies them
to the rows going IN to the pivot, and its pivot then re-sorts by the key.

```text
... GROUP BY account, year ORDER BY account DESC PIVOT BY account, year LIMIT 2

bean-query   Equity:O                  <- one row; DESC not visible
rustledger   Equity:O, Assets:B        <- two rows, in the requested order
```

Two consequences of bean-query's order: an explicit `ORDER BY` never reaches
the output, and `LIMIT` can change the result's SHAPE — limiting the rows going
in can leave a pivot value unrepresented, so a column disappears. `LIMIT 2` on
the query above with no `ORDER BY` drops the 2025 column entirely.

These are one decision, not two. bean-query's `ORDER BY` loss is an artifact
rather than a policy: `EvalPivot.__call__` sorts rows by the key column
immediately before `itertools.groupby`, which only groups ADJACENT equal keys,
so the sort is a precondition of grouping and discards the requested order as a
side effect. Nothing upstream tests `PIVOT BY` with either clause. Its `LIMIT`
behavior is coherent under its own model — pivot as a display reshape over a
finished query — but that model is what discards `ORDER BY`. Once the requested
order is honored on the pivoted rows, `LIMIT` has to count those same rows:
ordering one row set and limiting a different one would be incoherent.

So matching bean-query here is a package deal that includes silently ignoring
an explicit clause. Pinned by
`crates/rustledger-query/tests/pivot_pipeline_order_test.rs` (issue #2219).

The other axes match bean-query (issue #2440). The COLUMNS are the spread
values sorted by value, whatever the `ORDER BY`, as bean-query's
`sorted(keys)` and DuckDB's `PIVOT` lay them out; they used to follow the
order values first appeared in the sorted rows, so with no `ORDER BY` on the
spread column the layout was ledger order and one new transaction could
reorder it. With no `ORDER BY`, the ROWS are the row keys sorted, as
bean-query's are. One deliberate difference: a NULL spread value is a column
of its own, sorted first as `ORDER BY` sorts NULL, where bean-query fails with
`TypeError: '<' not supported between instances of 'str' and 'NoneType'`.
Pinned by `crates/rustledger-query/tests/pivot_axis_order.rs`.

### 12. SUM Over a Boolean

`sum(number > 0)` counts the rows where the comparison is true. Python sums
booleans as integers, so bean-query computes the same number -- but prints it
as `TRUE`:

```
$ bean-query -f csv f.bean "SELECT sum(number > 0) FROM #postings"
TRUE

$ rledger query -f csv f.bean "SELECT sum(number > 0) FROM #postings"
2
```

The values agree; only the rendering differs. bean-query types the result
column from its argument, so the integer it computed is formatted through the
boolean formatter. Through its API the number is visible:

```python
conn.execute("SELECT sum(number > 0) FROM #postings").fetchall()
# [(2,)]
```

We print the value. Reproducing `TRUE` would mean reproducing a display bug,
and `2` is what a user asking "how many postings are positive" means.

`count(number > 0)` answers a different question -- it counts non-NULL
comparisons, so on the same data it is 4, in both tools.

Pinned by `crates/rustledger-query/tests/sum_over_booleans_test.rs` (issue
#2214).

### 13. Comparisons Against a Missing Value

A comparison with a NULL operand is NULL, in both tools. On a posting whose
transaction has no payee, `payee != ''`, `payee ~ 'x'` and `payee IN ('a')` are
each NULL rather than a boolean, so `count(payee != '')` is 0 and not the row
count.

This is agreement, not divergence, and is listed here because it is easy to
assume the opposite: `WHERE payee != ''` still filters those rows out, since
NULL is falsy. Only projecting or counting a comparison shows the difference.

`NOT (NULL)` is `TRUE` -- Python's rule, which beanquery follows, rather than
SQL three-valued logic. An empty collection is not NULL: `'food' IN tags` on an
untagged posting is `FALSE`, again in both tools.

Pinned by `crates/rustledger-query/tests/null_comparison_test.rs` (issue
#2213).

### 14. Adding to One Side of a Long-and-Short Holding

When an account holds a commodity both long and short, a posting whose cost
names a lot of its own sign adds a new lot on that side, dated the transaction
date:

```beancount
2020-01-01 * "a short at 101, a long at 102"
  Assets:Stock  -2 X {101 USD}
  Assets:Stock   5 X {102 USD}
  Assets:Cash  -308 USD

2020-01-05 * "buy 3 more at 102"
  Assets:Stock   3 X {102 USD}
  Assets:Cash  -306 USD
```

| | holdings after the buy |
|---|---|
| rustledger | `-2 X {101, 2020-01-01}`, `5 X {102, 2020-01-01}`, `3 X {102, 2020-01-05}` |
| Python beancount | `-2 X {101, 2020-01-01}`, `8 X {102, 2020-01-01}` |

Python's lot matching ignores sign. The account holds a short, so it treats
the buy as a reduction, matches the long 102 lot, and "reduces" that lot by a
positive amount, which grows it: the three units take the 2020-01-01
acquisition date. It also rejects the same posting, with `Not enough lots to
reduce`, when the quantity is larger than that lot. rustledger keeps the
purchase's own date, and accepts it whatever its size. Units and cost basis
agree.

Both reject a cost that matches no lot on either side (`-5 X {101 USD}` while
holding only `10 X {100 USD}`), so a mistyped cost still fails, and so does a
posting that names only a lot date or label.

Pinned by `crates/rustledger-loader/tests/mixed_sign_holdings_test.rs` and the
core test `a_cost_matching_only_its_own_side_is_an_augmentation` (issue
#2384).

### 15. ORDER BY on Positions

`ORDER BY` sorts amounts by currency, then number, exactly as bean-query does
(beancount's `amount.sortkey`). Positions sort by beancount's
`Position.sortkey`: units currency rank, then cost number, cost currency and
units number. The rank puts a fixed list first, in order (`USD`, `EUR`, `JPY`,
`CAD`, `GBP`, `AUD`, `NZD`, `CHF`), so an operating currency sorts before the
commodities held against it. It differs in how it ranks every OTHER currency:

| | `ORDER BY position` on `2 GLD {130 USD}`, `2 VHT {40 USD}`, `1 GLD {10 USD}` |
|---|---|
| rustledger | `1 GLD {10}`, `2 GLD {130}`, `2 VHT {40}` |
| bean-query | `1 GLD {10}`, `2 VHT {40}`, `2 GLD {130}` |

beancount ranks an unlisted currency by the LENGTH of its name, although its
comment says "all the rest in alphabetical order". So all unlisted currencies
of one length tie, and their lots interleave by cost, the fault a currency key
exists to prevent; longer names also sort after shorter ones (`HOOL` before
`BRICKHOME`). rustledger ranks unlisted currencies alphabetically. Over the
repository's test ledgers, inventory `ORDER BY` agrees with bean-query on 143
of 148, and the five that differ are exactly this.

Inventories sort as beancount's `Inventory.__lt__` does, by their positions
sorted, compared in turn, with this position order. A position of zero units,
which rustledger keeps for a cost-less holding that nets to zero, holds nothing
and is left out, as beancount has none. Pinned by
`crates/rustledger-query/tests/order_by_amounts.rs` (issue #2445).

`MIN` and `MAX` over amounts, positions and inventories use this same order:
`MIN` returns the first value `ORDER BY` gives ascending, `MAX` the first it
gives descending. The order has ties between values that are not equal (two
lots that differ only in date or label, as in beancount's `Position.sortkey`);
those keep input order, and `MIN` and `MAX` both return the first of them.
bean-query's `MIN` does too; its `MAX` uses the tuple fallback described
below, which compares the lot dates and picks the later lot. `MIN` agrees with
bean-query, except over positions whose currencies the rank above orders
differently: `min(position)` over `2 X {20 USD}` and `1 Y {5 USD}` is
`2 X {20 USD}` here and `1 Y {5 USD}` in bean-query, as with `ORDER BY`. `MAX`
differs where values span currencies, deliberately:
bean-query's `MAX` keeps a value when `value > current`, and beancount's
`Amount` and `Position` define only `<`, so `>` falls back to plain tuple
comparison, number first.

| | over `Assets:A` holding `5 EUR` and `3 USD` |
|---|---|
| `SELECT units(position) AS u ORDER BY u` (both) | `5 EUR`, `3 USD` |
| rustledger `min(units(position)), max(units(position))` | `5 EUR`, `3 USD` |
| bean-query `min(units(position)), max(units(position))` | `5 EUR`, `5 EUR` |

bean-query's `MAX` names as largest the value its own `ORDER BY` sorts first.
Under beancount's comparisons `5 EUR < 3 USD` and `5 EUR > 3 USD` are both
true, so its `MAX` follows no order at all. Within one currency the two agree.
Across currencies neither rule measures size: rustledger's `MAX` of `-30 USD`
and `10 EUR` is `-30 USD`, the last value in currency order. Pinned by
`crates/rustledger-query/tests/min_max_amounts_test.rs` (issue #2447).

### 16. PRINT Output Layout

`PRINT` writes each entry the way `rledger format` writes it, so the layout
comes from rustledger's formatter, not beancount's printer. The entries are
the same; how they are written differs:

| | rustledger | bean-query |
|---|---|---|
| `open` | `2024-01-01 open Assets:Cash USD` | account padded to a fixed column, then `USD` |
| `price` | `2024-01-03 price X 110 USD` | number right-aligned at a fixed column |
| `balance` | `2024-01-04 balance Assets:Cash -300 USD` | number right-aligned at a fixed column |
| failing `balance` | the assertion only | adds `; Diff: <amount>` |
| postings | aligned within each entry | aligned within each entry |
| `render_commas` | no separators | separators |
| comments inside a transaction | kept | dropped |
| empty payee or narration | `""` kept | omitted |
| metadata | keys sorted | source order |
| tags and links | source order | sorted |
| newline in a string | `\n` escape | raw newline |

The fixed columns are beancount's printer layout. rustledger keeps one
canonical form for every directive it writes as text (`rledger format`,
`rledger add`, `rledger extract`, the component's `format.entry`), so
anything `PRINT` prints is already formatted. Metadata is sorted because
rustledger stores it unordered, so source order is not available. One
difference from `rledger format` remains: `rledger format` aligns postings
across a whole file, and `PRINT`, like bean-query, aligns each entry on its
own. Thousands separators would need the ledger's display context in the
query engine, which `PRINT` does not have yet.

Over the 742 files of the downloaded compatibility corpus, 342 of the 615
that both tools print (bean-query fails on 45 more, and rustledger declines
82 that did not parse or book, #1908) come out identical, or identical but
for spacing. The rest differ by the rows above, or by the loader differences
listed elsewhere on this page (decimal precision, booking, plugins), which
`SELECT` shows as well. Pinned by
`crates/rustledger-query/tests/print_entry_stream.rs` (issue #2426).

## BQL Query Compatibility

BQL (Beancount Query Language) compatibility was tested with 11 standard queries on 50 files:

| Query | Description |
|-------|-------------|
| `SELECT DISTINCT account ORDER BY account LIMIT 20` | List accounts |
| `SELECT COUNT(*) AS total` | Count postings |
| `SELECT currency, COUNT(*) GROUP BY currency` | Currency breakdown |
| `SELECT YEAR(date), COUNT(*) GROUP BY year` | Annual counts |
| `SELECT DISTINCT ROOT(account)` | Account roots |
| `SELECT DISTINCT LEAF(account)` | Account leaves |
| `SELECT account, SUM(position) GROUP BY account` | Balance summary |
| `SELECT MONTH(date), COUNT(*) GROUP BY month` | Monthly counts |
| `SELECT date, narration ORDER BY date LIMIT 10` | Transactions |
| `SELECT account, FIRST(date) GROUP BY account` | First dates |
| `SELECT MIN(date), MAX(date)` | Date range |

**Results: 100% data match**

The only remaining differences are display-only:

- Python's bean-query uses a "display context" that truncates decimals (e.g., shows `111 USD` for `111.11 USD`)
- Rustledger shows the actual precision (e.g., `111.11 USD`)

These do not affect the underlying values.

## Running Compatibility Tests

```bash
# Inside nix develop shell:

# Download the full test suite first
./scripts/fetch-compat-test-files.sh   # Populates tests/compatibility/files

# Run BQL comparison (bean-query vs rledger)
python scripts/compat-bql-test.py
```

## Directory Structure

```
tests/compatibility/                    # Compatibility test suite
├── README.md                    # Test documentation
├── sources.toml                 # Source documentation and licenses
├── exclusions.toml              # Files excluded from the metric
├── bql-queries.toml             # BQL queries run by compat-bql-test.py
└── files/                       # beancount files (mostly gitignored, downloaded)
```

## Scripts

- `scripts/fetch-compat-test-files.sh` - Downloads full test suite from GitHub
- `scripts/compat-bql-test.py` - BQL query comparison (bean-query vs rledger)

## Improving Compatibility

If you encounter a file that works with Python beancount but not rustledger:

1. Check if it uses Python plugins (expected to fail)
1. Check for multi-currency transactions without prices
1. File an issue at https://github.com/rustledger/rustledger/issues

______________________________________________________________________

*Generated: February 2026*
*Test environment: Beancount 3.2.0, beanquery 0.2.0, rustledger 0.15.0*
