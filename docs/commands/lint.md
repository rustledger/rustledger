______________________________________________________________________

## title: rledger lint description: Run non-fatal advisory passes over a ledger

# rledger lint

Run a named advisory pass over one or more ledger files. A lint reports what
it finds without failing: unless a lint's own option says otherwise, it exits
0 whether or not it finds anything, and 1 only when it cannot run (a missing
file, a file that does not load).

## Usage

```bash
rledger lint <LINT> <FILE>... [OPTIONS]
```

| Lint | What it reports |
|------|-----------------|
| `transfers` | Likely inter-account transfer pairs; `--apply` links them |
| `linked-transit` | Explicitly linked transfers through a transit account whose legs do not agree |
| `closed-nonempty` | Accounts closed while still holding a balance (`check` stays silent on these, as `bean-check` does) |
| `control-chars` | Control characters in narrations, payees, metadata and comments |

Every lint takes `-f, --format <text|json>`.

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
  that fails to run (or whose output is discarded) is refused: those drop or
  alter transactions, so any answer could be wrong.
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

Findings exit 0 unless `--fail-on` names a status: `--fail-on
mismatch,missing,ambiguous` (comma-separated or repeated) exits 1 when any
link ends in one of them, as `rledger check` exits 1 on an error, so the lint
can gate CI or a pre-commit hook. A refusal also exits 1. In `ag-rledger` a
`--fail-on` failure is still `"ok": true`, with `exit_code` and
`result.exit_status` 1, as for `check`.

A match is not evidence of external settlement, domain isolation, or a
persistent transfer lifecycle.
