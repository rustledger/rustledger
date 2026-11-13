______________________________________________________________________

## title: rledger lint description: Run non-fatal advisory passes over a ledger

# rledger lint

Run a named advisory pass over one or more ledger files. Every lint follows
one exit rule:

| Exit | Meaning |
|------|---------|
| 0 | It answered, whether or not it found anything |
| 1 | It found something an opt-in fail flag names (`linked-transit --fail-on` or `cross-group --fail-on-findings`) |
| 2 | It could not answer: a missing file, a file that does not load, or a ledger or configuration it refuses, as `rledger check` exits 2 on a file it cannot read |

## Usage

```bash
rledger lint <LINT> <FILE>... [OPTIONS]
```

| Lint | What it reports |
|------|-----------------|
| `transfers` | Likely inter-account transfer pairs; `--apply` links them |
| `linked-transit` | Explicitly linked transfers through a transit account whose legs do not agree |
| `cross-group` | Transactions touching more than one configured account group |
| `closed-nonempty` | Accounts closed while still holding a balance (`check` stays silent on these, as `bean-check` does) |
| `control-chars` | Control characters in narrations, payees, metadata and comments |

Every lint takes `-f, --format <text|json>`.

## What each lint reads, and when it refuses

Every lint loads its files the same way, and what it does with a file that
has load errors (a parse error, a missing include) depends on what it reads:

| Lint | Reads | Load errors | Booking or plugin failure |
|------|-------|-------------|---------------------------|
| `linked-transit` | The booked ledger, as `check` sees it | Refused, exit 2 | Refused, exit 2 |
| `cross-group` | The booked ledger, as `check` sees it | Refused, exit 2 | Refused, exit 2 |
| `closed-nonempty` | The booked ledger, as `check` sees it | Refused, exit 2 | Refused, exit 2 |
| `transfers --apply` | The source, as written | Refused before any file is written, exit 2 | Not run |
| `transfers` (preview) | The source, as written | Answers over what parsed, with a warning | Not run |
| `control-chars` | The source, as written | Answers over what parsed, with a warning | Not run |

A lint that refuses load errors refuses every one, including those the
loader counts as harmless to the ledger's contents (a duplicate include, an
include cycle, an include glob that matches nothing), as `bean-check`
reports each of them as an error. The refusal, and the warning below, list
each load error, a parse error as `file:line: Pnnnn: message`, up to ten,
then how many more there are.

A lint that reads the booked ledger refuses one whose booking or plugins
failed: a transaction booking rejected is left out of the balances, and a
failed plugin leaves the ledger other than it would have been, so a clean
"nothing found" over either could be wrong. The refusal names each failure:

```text
error: main.beancount: cannot inspect a ledger whose processing failed: ...
```

`transfers --apply` rewrites transaction lines in the source files, so it
refuses to work from a parse that went wrong. A read-only `transfers` and
`control-chars` still answer: a control character is often what broke the
parse, and the parser recovers enough to find it. Both say that the file had
load errors, so a clean report never passes as complete:

```text
warning: main.beancount: has load errors, so findings may be incomplete: ...
```

Warnings go to stderr; in `ag-rledger` they are the envelope's `warnings`,
this one with the code `LOAD_ERRORS`.

## cross-group

Report transactions with postings in two or more user-defined account groups:

```bash
rledger lint cross-group main.beancount \
  --group UnitA=Assets:UnitA,Income:UnitA,Expenses:UnitA \
  --group UnitB=Assets:UnitB,Income:UnitB,Expenses:UnitB \
  --format json --fail-on-findings
```

Each `--group` names a group and one or more comma-separated account
prefixes. Group names use ASCII letters, digits, `_`, or `-`. At least two
distinct groups are required; repeat a group name to add prefixes. Several
groups may also be given in one value, separated by `;`
(`--group "UnitA=Assets:UnitA;UnitB=Assets:UnitB"`); an empty group, as a
stray `;` leaves, is refused. A prefix matches itself or a descendant
separated by `:`, not a similarly named sibling. A prefix is an account name
with a root and at least one component: a bare root such as `Liabilities` is
refused (name a component, `Liabilities:UnitA`), as are invalid prefixes and
overlapping prefixes assigned to different groups (one group's prefix nested
under another's, in either order). A prefix that matches no opened or posted
account is a warning, with the code `GROUP_PREFIX_NOT_IN_LEDGER` in
`ag-rledger`.

The report includes the location, date, narration and participating accounts
for each crossing, and the number of distinct unassigned posting accounts.
Repeated input paths and included files are deduplicated. It reads the booked
ledger with plugins and validation; validation diagnostics are warnings, not
proof that the ledger is valid. A transaction that differs between input
ledgers in its date, narration or accounts (a file included by two inputs
whose plugins treat it differently) is refused. A padding entry is compared
by its date and accounts only: its narration states the padded amount, which
depends on what each input posted before the `pad`, so the same `pad` read
through two inputs is one finding, reported with the first input's
narration.

Padding counts. A `pad` that a `balance` makes move an amount produces a
padding entry, as `rledger query` shows it, and a padding entry between two
groups is reported like any other crossing: at the `pad`'s line, with the
entry's narration (`(Padding inserted for Balance of 5 USD for difference 5
USD)`). A `pad` that pads several currencies produces one entry, and so one
finding, per currency. Its source account counts toward the unassigned
accounts when it is in no group.

A plugin can insert transactions that share a source location with another
(`forecast`'s copies keep the template's, `effective_date`'s keep the
parent's) or have none. Those cannot be told apart, so when the transactions
at one such location together touch two or more groups the run is refused
(exit 2):

```text
error: main.beancount:4: cannot audit transactions touching groups A, B: several transactions share one source location (a plugin inserted one)
```

This covers `effective_date` splitting a transaction into two halves in
different groups, though neither half crosses on its own. Such transactions
touching at most one group do not affect the answer and are not refused. A
padding entry whose `pad` a plugin inserted with no location is judged on its
own, never pooled with another such entry; one whose `balance` alone has no
location is still reported at its `pad`.

`--fail-on-findings` exits 1 on a crossing; without it findings are advisory.
Exit 2 means the lint could not answer. This audit detects account-group
co-occurrence, not a transfer, gateway, legal classification, or settlement.
It does not prevent edits outside the lint. `ag-rledger lint cross-group`
accepts the same options; there a run that cannot answer is an envelope with
`ok: false` and the error, where findings are `ok: true`.

## linked-transit

Checks transfers that go out through a transit account and come back in a
second transaction, linked by a shared `^link`:

```bash
rledger lint linked-transit main.beancount --link-prefix xfer- \
  --account Assets:Transit --format json
```

| Option | Description |
|--------|-------------|
| `--link-prefix <PREFIX>` | Inspect links starting with this, written without the `^` (required) |
| `--account <ACCOUNT>` | An exact transit account name; repeat for several (required) |
| `--fail-on <STATUS>,...` | Exit 1 when a link ends in one of these statuses (see below) |
| `-f, --format <text\|json>` | Output format (default: `text`) |

Only links that start with the prefix and touch a configured account are
reported. Includes and repeated input paths are deduplicated. Each link ends
in one status:

| Status | Meaning |
|--------|---------|
| `matched` | Two transactions, one transit posting each, on the same account, with equal non-zero amounts in one currency and opposite signs |
| `mismatch` | Two comparable legs that differ; the reason says how: `account: A vs B`, `currency: ...`, `zero transit amount: ...`, `direction: ... (same sign)` or `amount: 100.00 USD vs -90.00 USD` |
| `missing` | Only one leg goes through a transit account |
| `ambiguous` | Not something the lint can compare safely: a fee or other extra posting, a price or cost, several scoped links on one transaction, more than two legs, an error on a leg, or a transaction a plugin inserted |

The text output lists the links that did not match, then a count line
(`312 matched, 2 mismatch, 1 missing, 0 ambiguous`). The JSON has every
finding, with `link`, `status`, `reason` and `locations` (each with `file`,
`line` and its `transit` postings, the number as a string), plus `counts`.

### What the lint reads

It reads the ledger as `rledger check` does: booked, with plugins and
validation run, so an elided transit amount is the amount booking computed.
What processing reports is handled by what it does to the answer:

- A file with load errors, a transaction that cannot be booked, or a plugin
  that fails (it cannot run, its output is discarded, or a built-in plugin
  cannot use its config and leaves the ledger as it was) is refused: those
  drop or alter transactions, or skip changes the ledger relies on, so any
  answer could be wrong. A WASM or Python plugin's own errors are read as
  findings.
- Any other error located on a linked transaction (an unbalanced leg, an
  unopened or closed account, a plugin's finding on that transaction) makes
  the link `ambiguous`, with the error as the reason.
- Errors elsewhere in the ledger, errors with no transaction location (such
  as `check_commodity`'s), and warnings are passed through as warnings and
  do not stop the lint.

A transaction a plugin inserted with no source location of its own, or at a
location another transaction already has (`forecast` copies, `effective_date`
splits), makes its link `ambiguous`: it cannot be told apart from the other.

### Configuration mistakes

An `--account` that is not a valid account name is refused. A leading `^` on
`--link-prefix` is dropped with a note. A configured account the ledger never
opens or posts to, and a prefix that no link starts with, are warnings, so a
typo does not pass as "No linked transit transfers found." Warnings go to
stderr; in `ag-rledger` they are the envelope's `warnings`, each with a
`code` and, for a ledger error, its `file` and `line`.

### Exit status

| Exit | `rledger lint linked-transit` |
|------|-------------------------------|
| 0 | It ran; no link ends in a `--fail-on` status (always, without `--fail-on`) |
| 1 | A link ends in a status `--fail-on` names, as `rledger check` exits 1 on an error |
| 2 | It could not answer: a missing file, load errors, a processing failure, or a configuration it refuses, as `rledger check` exits 2 on a file it cannot read |

`--fail-on mismatch,missing,ambiguous` takes the statuses comma-separated or
repeated, so the lint can gate CI or a pre-commit hook, and 1 always means a
finding. In `ag-rledger` a `--fail-on` failure is still `"ok": true`, with
`exit_code` and `result.exit_status` 1, as for `check`; a run that could not
answer is an error envelope, `"ok": false`, whose `error.code` says why
(`FILE_NOT_FOUND`, exit 3, or `COMMAND_FAILED`, exit 1). Exit 2 there means a
usage error, so it is not reused.

A match is not evidence of external settlement, domain isolation, or a
persistent transfer lifecycle.
