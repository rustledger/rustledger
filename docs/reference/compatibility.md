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

### 9. SUM Over a Boolean

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

### 10. Comparisons Against a Missing Value

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
