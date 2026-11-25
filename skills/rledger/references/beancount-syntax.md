# Beancount syntax for agents

Enough Beancount to write entries `rledger check` accepts. The full grammar is
in the [syntax reference](https://github.com/rustledger/rustledger/blob/main/docs/reference/syntax.md)
and the [Beancount language docs](https://beancount.github.io/docs/beancount_language_syntax.html).

## A complete ledger

This file passes `rledger check` and is already `rledger format`ted (a test in
the rustledger repository checks both):

<!-- skill-test: check-clean -->

```beancount
option "title" "Household"
option "operating_currency" "USD"

2020-01-01 commodity USD
2020-01-01 commodity AAPL
  name: "Apple Inc."

2024-01-01 open Assets:Bank:Checking USD
2024-01-01 open Assets:Brokerage AAPL,USD
2024-01-01 open Assets:Cash:EUR EUR
2024-01-01 open Liabilities:CreditCard USD
2024-01-01 open Income:Salary USD
2024-01-01 open Income:CapitalGains USD
2024-01-01 open Expenses:Food
2024-01-01 open Expenses:Travel
2024-01-01 open Equity:Opening-Balances

2024-01-01 pad Assets:Bank:Checking Equity:Opening-Balances
2024-01-02 balance Assets:Bank:Checking 5000.00 USD

2024-01-15 * "Employer" "January salary"
  Assets:Bank:Checking   3000.00 USD
  Income:Salary

2024-01-20 ! "Corner Market" "Groceries" #household
  receipt: "2024-01-20-market.pdf"
  Expenses:Food            82.15 USD
  Liabilities:CreditCard

2024-02-01 * "Exchange" "Buy euros for trip" ^trip-paris
  Assets:Cash:EUR         200.00 EUR @ 1.10 USD
  Assets:Bank:Checking   -220.00 USD

2024-02-03 * "Cafe de Flore" "Coffee" ^trip-paris
  Expenses:Travel           7.15 USD
  Assets:Cash:EUR          -6.50 EUR @@ 7.15 USD

2024-03-01 * "Broker" "Buy AAPL"
  Assets:Brokerage            10 AAPL {150.00 USD}
  Assets:Bank:Checking  -1500.00 USD

2024-06-03 * "Broker" "Sell AAPL"
  Assets:Brokerage            -4 AAPL {150.00 USD} @ 190.00 USD
  Assets:Bank:Checking    760.00 USD
  Income:CapitalGains    -160.00 USD

2024-06-04 price AAPL 191.00 USD

2024-06-05 balance Assets:Brokerage 6 AAPL

2024-06-30 note Liabilities:CreditCard "Called about annual fee"
```

## Rules that matter

- **Every directive starts with a date**, `YYYY-MM-DD`, at column 0. Postings
  and metadata lines are indented (two spaces is the convention).
- **A transaction header needs a flag**: `*` (cleared), `!` (pending) or the
  keyword `txn`. Then an optional payee string and a narration string, both in
  double quotes: `2024-01-15 * "Payee" "Narration"`. One string is the
  narration.
- **Accounts** are `Root:Component:...`. The root is one of `Assets`,
  `Liabilities`, `Equity`, `Income`, `Expenses` (renamable by option); each
  component starts with a capital letter or a digit (letters from other
  scripts are fine). No spaces.
- **Every account needs an `open`** dated on or before its first use. An
  `open` may restrict currencies (`open Assets:Bank USD,EUR`) and set a booking
  method (`open Assets:Brokerage "FIFO"`).
- **Currencies/commodities** are uppercase (`USD`, `AAPL`, `VBMPX`). Every
  amount needs one: `5.00 USD`, never `5.00` alone.
- **Signs**: money flows out of an account as a negative amount. Income
  postings are negative, expenses positive; a credit-card purchase makes the
  liability more negative.
- **Postings must balance** to zero per currency. One posting per currency may
  leave its amount out and is filled in.
- **Strings** use double quotes. Comments start with `;`.
- **Tags** `#name` and **links** `^name` go after the narration.
  **Metadata** (`key: "value"`, key lowercase) goes on the line under the
  directive or under a posting, indented further.

## Costs and prices

| Syntax | Meaning | Weight |
|--------|---------|--------|
| `10 AAPL {150.00 USD}` | buy a lot at a per-unit cost | 1500.00 USD |
| `-4 AAPL {150.00 USD} @ 190.00 USD` | sell from the 150 USD lot at 190 | 600.00 USD (cost, not price) |
| `-4 AAPL {}` | sell, let booking pick the lot | the lot's cost |
| `200.00 EUR @ 1.10 USD` | currency conversion, per-unit price | 220.00 USD |
| `-6.50 EUR @@ 7.15 USD` | conversion, total price | 7.15 USD |

A sale at cost with a price leaves the gain unbalanced, so add an income
posting (`Income:CapitalGains`), with or without an amount. Under the default
STRICT booking, `{}` that matches more than one lot is an error (`E4003`); give
the account a booking method or name the lot by cost, date (`{2024-03-01}`) or
label.

## Directives besides transactions

| Directive | Example |
|-----------|---------|
| `open` / `close` | `2024-01-01 open Assets:Bank USD` · `2025-01-01 close Assets:Bank` |
| `balance` | `2024-02-01 balance Assets:Bank 1234.56 USD`: checked at the **start** of that day |
| `pad` | `2024-01-01 pad Assets:Bank Equity:Opening-Balances`, then a `balance` on a **later** date |
| `price` | `2024-06-04 price AAPL 191.00 USD` |
| `commodity` | `2020-01-01 commodity AAPL` (optional metadata below it) |
| `note`, `event`, `document`, `custom` | annotations, rarely needed |
| `option` | `option "operating_currency" "USD"` (undated, top of the root file) |
| `include` | `include "2024/*.beancount"` (undated; paths relative to the including file) |
| `plugin` | `plugin "beancount.plugins.auto_accounts"` |

A `balance` dated the same day as the `pad` before it fails; put the balance
at least one day later.

## Where rledger is stricter than Python beancount

rledger matches beancount's behavior and deliberately differs only where it
judges beancount wrong. The differences an agent can hit:

- **`option "booking_method"` is case-sensitive** in both, but rledger refuses
  to answer `query` and `report` when the value is invalid (`"fifo"`), where
  `bean-query` answers with STRICT booking. Write `"FIFO"`.
- **A `{*}` cost (average-cost merge)** is an rledger extension; beancount
  refuses it.
- **BQL**: text after a query's final `;` is an error (beancount drops it), and
  a few aggregate and comparison results differ; see section "BQL Query
  Compatibility" of the
  [compatibility notes](https://github.com/rustledger/rustledger/blob/main/docs/reference/compatibility.md).
- **Python plugins** run in a WASM sandbox, and only when referenced by file
  path (`plugin "/path/to/plugin.py"`); a module name is `E8004`. The
  common `beancount.plugins.*` plugins have native equivalents and work as
  written. Release binaries (Homebrew, Scoop, GitHub Releases,
  `cargo binstall`) leave the Python and WASM plugin runtimes out (`E8005`);
  `cargo install rustledger` includes them.

The [migration guide](https://github.com/rustledger/rustledger/blob/main/docs/migration/from-beancount.md)
lists the rest.

## Mistakes agents make

- Leaving out the flag (`2024-01-12 "Lunch"`): a parse error now.
- Inventing account names instead of using the ledger's. List them first:
  `rledger report ledger.beancount accounts`.
- Using an account before its `open` date, or opening it in a file the root
  does not include.
- Writing `5.00` without a currency, or a lowercase currency.
- Getting the sign of a refund or a card payment backwards. The transaction
  still balances, so `check` cannot catch it; reason about each posting.
- Asserting a balance on the same day as the transactions it should include.
- Appending entries out of order. Directives are sorted by date, so file
  order only matters between entries of the same day (booked in file order),
  but keep files chronological for the user.
- Editing an included file and checking only that file.
