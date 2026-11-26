---
name: rledger
description: Validate, query, format, report on, and import into Beancount plain-text accounting ledgers with the rledger CLI (rustledger, a fast Rust implementation of Beancount). Use when working with .beancount or .bean files, double-entry bookkeeping, BQL queries, balance assertions, Beancount errors such as "Transaction does not balance" or "Account was never opened", importing bank CSV/OFX statements, or when a user mentions beancount, bean-check, bean-query, bean-format, Fava, or rustledger.
license: GPL-3.0-only
---

# rledger

`rledger` is the command-line interface of rustledger, a pure-Rust
implementation of [Beancount](https://beancount.github.io/). It reads the same
`.beancount` files as Python beancount (`bean-check`, `bean-query`,
`bean-format`) and is much faster, so it is cheap to re-run after every edit.

Run `rledger --version` to confirm it is installed. If it is not, see
[Install](#install).

## Ground rules

1. **Always pass the ledger file explicitly.** Without it, rledger falls back to
   `$RLEDGER_FILE` or a config default, and exits 2 with
   `error: FILE is required` when neither exists.
1. **Always pass the query string to `rledger query`.** With no query it reads
   one from stdin, or opens an interactive shell when stdin is a terminal,
   which blocks an agent.
1. **Point rledger at the root file**, the one that `include`s the others.
   Checking an included file on its own can report its accounts as never
   opened.
1. **Run `rledger check` after every edit** and before saying a change is done.
1. **Leave alignment to `rledger format`**, and only where the user's files are
   already formatted with it (`rledger format --check` exits 0); otherwise it
   rewrites lines you did not touch. Running it twice changes nothing.
1. **Do not invent amounts.** If a transaction does not balance, find out which
   posting is wrong; do not add a plug posting to make the error go away.

## Validate: `rledger check`

```bash
rledger check ledger.beancount               # human-readable diagnostics
rledger check -f json ledger.beancount       # machine-readable, on stdout
rledger check -q ledger.beancount            # no output, exit code only
rledger check --show-summary ledger.beancount
rledger check --include-rules E2001 ledger.beancount
```

Exit codes: **0** clean, or warnings only; **1** at least one error (parse or
validation); **2** the command could not run (missing file, bad arguments).
`--include-rules`/`--exclude-rules` change what is printed, never the exit code.

JSON output is one object:

```json
{
  "diagnostics": [
    {
      "file": "/abs/path/ledger.beancount",
      "line": 3, "column": 1, "end_line": 7, "end_column": 1,
      "severity": "error",
      "phase": "validate",
      "code": "E3001",
      "message": "Transaction does not balance: residual 1.00 USD"
    }
  ],
  "error_count": 1, "warning_count": 0,
  "parse_error_count": 0, "validate_error_count": 1
}
```

`severity` is `error` or `warning`; `phase` is `parse` or `validate`; some
diagnostics also carry a `hint`. Parse errors have `P` codes (`P0012`);
validation errors have `E` codes. `rledger explain E3001` (or `P0012`)
describes a code and how to fix it, and `rledger explain` lists them all. Fix
parse errors first: one bad line can hide everything after it.

See [references/errors.md](references/errors.md) for the common codes and
their fixes.

## Query: `rledger query`

BQL (Beancount Query Language) is SQL over postings: every row of a plain
`SELECT` is one posting.

```bash
rledger query ledger.beancount "BALANCES"
rledger query ledger.beancount "SELECT account, sum(position) WHERE account ~ '^Expenses:' GROUP BY account ORDER BY account"
rledger query -f json ledger.beancount "SELECT date, payee, narration, position WHERE account ~ 'Food'"
rledger query -f csv -o out.csv ledger.beancount "SELECT date, account, position"
rledger query -F report.bql ledger.beancount
```

Formats: `text` (default), `csv`, `json`, `beancount` (for `PRINT`). JSON is
`{"columns": [...], "row_count": N, "rows": [[...], ...]}`, rows positional
against `columns`. Decimal numbers are JSON strings (`"12.50"`, to keep their
precision), counts are integers, and a position is an object
(`{"units": {"number": "10", "currency": "VTI"}, "cost": {...}}`).

`query` answers despite validation errors (it lists them on stderr; `-q`
hides them), but refuses, printing no rows and exiting 1, when the file did not
parse or a transaction could not be booked. Run `rledger check` then.

See [references/bql.md](references/bql.md) for columns, functions and
tested example queries.

## Format: `rledger format`

```bash
rledger format ledger.beancount               # print formatted text to stdout
rledger format --in-place ledger.beancount    # rewrite the file
rledger format --check ledger.beancount       # exit 1 if it would change
rledger format --check --diff ledger.beancount
```

`format` refuses a file with parse errors (exit 2) and writes nothing.
`--diff` is only accepted together with `--check`.

## Reports: `rledger report`

The file goes before or after the report name:

```bash
rledger report balances ledger.beancount
rledger report balsheet ledger.beancount
rledger report income ledger.beancount --year 2024
rledger report register ledger.beancount -a Assets:Bank --from 2024-01-01 --to 2024-02-01
rledger report -f json ledger.beancount holdings
```

Reports: `balances`, `balsheet`, `income`, `journal`, `register`, `holdings`,
`networth`, `accounts`, `commodities`, `stats`, `prices`, `returns`, `capgains`,
`budget`. `--to` is exclusive.

## Other commands

| Command | Use it to |
|---------|-----------|
| `rledger doctor missing-open FILE` | print `open` directives for accounts used but never opened |
| `rledger doctor context FILE LINE` | show the directive at a line (for a diagnostic's line) |
| `rledger doctor linked FILE ^link` | find transactions sharing a link or `#tag` |
| `rledger add FILE -n --quick ...` | build a balanced transaction (`-n` previews, `-y` appends) |
| `rledger extract FILE.csv -a ACCOUNT` | turn a bank CSV/OFX file into transactions on stdout |
| `rledger lint closed-nonempty FILE` | advisory checks that `check` does not run |
| `rledger price -f FILE --dry-run` | show which prices would be fetched (`-f` is the file here) |
| `rledger split` / `rledger merge` | restructure files; `-n` previews and verifies |
| `rledger explain [CODE]` | explain any diagnostic code `check` prints (`E`, `P`, `BOOK`, ...) |

`rledger add` asks before appending. When stdin is not a terminal, only an
explicit `y` on stdin appends, and no answer is an error, so pass `-y` to
append or `-n` to preview. Without `--quick` it is interactive.

Every command takes `--help`. Full flag lists and examples:
[references/commands.md](references/commands.md).

## Editing a ledger safely

1. Before editing, run `rledger check -f json ledger.beancount` to know which
   errors were already there, and `rledger format --check FILE` on the file
   you will edit to know whether it is kept formatted.
1. Make the edit. Keep entries in date order and follow the file's existing
   account names (`rledger report ledger.beancount accounts` lists them).
1. `rledger check -f json ledger.beancount` again. Compare against step 1; fix
   only what you introduced unless asked to fix the rest.
1. If the file was formatted in step 1, `rledger format --in-place FILE`, then
   check once more.

Beancount syntax essentials and the mistakes agents make most:
[references/beancount-syntax.md](references/beancount-syntax.md).

## Alternatives for agents

- **`ag-rledger`** ships next to `rledger` in the release archives. It takes the
  same commands and wraps every result in one JSON envelope
  (`ok`, `exit_code`, `result`, `next_actions`); with `-f json` the command's
  own JSON is parsed into `result.data`. `ok` is true whenever the command
  ran: read `exit_code` for the verdict.
- **MCP server**: `npx @rustledger/mcp-server` exposes validate, query,
  format, reports and editor tools over the Model Context Protocol. See
  [its README](https://github.com/rustledger/rustledger/tree/main/packages/mcp-server).

## Install

| Platform | Command |
|----------|---------|
| macOS, Linux | `brew install rustledger` |
| Arch Linux | `yay -S rustledger-bin` |
| Windows | `scoop bucket add rustledger https://github.com/rustledger/scoop-rustledger && scoop install rustledger` |
| Cargo | `cargo binstall rustledger` or `cargo install rustledger` |
| Nix | `nix run github:rustledger/rustledger` |
| Binaries | [GitHub Releases](https://github.com/rustledger/rustledger/releases) |

More (Fedora, Docker): the
[installation guide](https://github.com/rustledger/rustledger/blob/main/docs/getting-started/installation.md).
