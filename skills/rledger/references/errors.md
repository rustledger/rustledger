# Diagnosing rledger errors

Get the list as JSON, fix parse errors first, then work through the rest by
code:

```bash
rledger check -f json ledger.beancount
rledger check --show-summary ledger.beancount     # how many of each code
rledger explain E4003                             # cause and fix for one code
rledger doctor context ledger.beancount 42        # the directive at line 42
```

A diagnostic's `line` is where the directive starts. For a transaction-level
error (`E3001`), the span covers the whole transaction; for a posting-level one
(`E3002`), the posting.

The full catalogue is the
[error reference](https://github.com/rustledger/rustledger/blob/main/docs/reference/errors.md).

## Parse errors (`P` codes, `phase: "parse"`)

The file is not valid Beancount at that point. Common causes:

| Message contains | Likely cause | Fix |
|------------------|--------------|-----|
| `a transaction needs a flag` | `2024-01-12 "Lunch"` with no flag | write `2024-01-12 * "Lunch"` |
| `invalid token 'Assets:cash'` | an account component starts lowercase | `Assets:Cash` |
| `unexpected input` at a posting | posting not indented, single-quoted string, lowercase currency | indent postings, use `"double quotes"`, `USD` not `usd` |

`rledger query`, `rledger report` and `rledger format` all refuse a file with
parse errors, so fix these before anything else.

## Validation errors (`E` codes)

| Code | Message (abridged) | Usual fix |
|------|--------------------|-----------|
| `E1001` | Account X was never opened | add `YYYY-MM-DD open X` dated on or before first use; `rledger doctor missing-open FILE` generates them. If the `open` exists in another file, check the root file instead. |
| `E1002` | duplicate open | delete the second `open` |
| `E1003` | Posting to inactive account X (closed on D) | the account was closed before this entry: fix the date, the account, or move the `close` |
| `E1005` | Invalid account name | the root must be `Assets`, `Liabilities`, `Equity`, `Income` or `Expenses` (or a root renamed with `option "name_assets"` etc.) |
| `E2001` | Balance failed for X: expected A, got B | a transaction is missing, duplicated or has the wrong amount before that date; see below |
| `E2003` | Unused Pad entry | the `pad` has no later `balance` for that account, or the balance already held |
| `E3001` | Transaction does not balance: residual R | the postings' weights do not sum to zero; correct the wrong amount, or leave one posting's amount blank to be filled in |
| `E3002` | N postings with missing amounts | only one posting per currency may omit its amount |
| `E4001` | No matching lot for C in X | a sale's `{cost}` matches no lot held: use the lot's actual cost, `{}`, or a date/label |
| `E4002` | Not enough units in X | selling more than held: check quantity and earlier purchases |
| `E4003` | Ambiguous lot match | `{}` matches several lots under STRICT booking: name the lot (`{150 USD}`, `{2024-01-02}`, `{"label"}`) or set a booking method on the account's `open` (`"FIFO"`) |
| `E5002` | Invalid currency C not allowed in account X | the `open` lists allowed currencies: add C there, or post to another account |
| `E7002` | Invalid option value | e.g. `option "booking_method" "fifo"`: values are case-sensitive, write `"FIFO"` |
| `BOOK` | interpolation failed: cannot infer currency | a number with no currency (`Expenses:Food 5`): write the currency |

## Working an E2001 (balance assertion)

A `balance` directive asserts the balance at the **start** of its date: entries
dated the same day are not included. So

```beancount
2024-01-05 * "Deposit"
  Assets:Cash  10 USD
  Income:Gift
2024-01-05 balance Assets:Cash 10 USD
```

fails (`got 0 USD`); the assertion belongs on 2024-01-06. Otherwise, list
what happened to the account before the assertion and compare with the
statement:

```bash
rledger query ledger.beancount "SELECT date, narration, position, balance WHERE account = 'Assets:Bank:Checking' AND date < 2024-03-01"
```

Do not change the asserted amount to match the computed one unless the user
confirms the statement says so; the assertion is usually the trustworthy side.

## Working an E3001 (does not balance)

Each posting's weight is its amount, or amount times cost (`{...}`), or amount
times price (`@`), or the total price (`@@`). The weights must sum to zero per
currency, within a small tolerance inferred from the numbers' precision. The
message gives the residual; one posting is usually off by exactly that, or has
the wrong sign.

## Warnings

Warnings (`severity: "warning"`, such as `E7011` for an option value read as
false) do not fail `check`: the exit code stays 0. Report them; fix them when
they are clearly mistakes.
