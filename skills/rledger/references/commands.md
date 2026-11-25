# rledger command reference

Every command and flag below exists in the current `rledger` (a test in the
rustledger repository checks this file against the CLI). For anything not
covered here, `rledger <command> --help` is authoritative, and the
[command docs](https://github.com/rustledger/rustledger/tree/main/docs/commands)
go deeper.

Contents: [global flags](#global-flags) · [check](#check) · [query](#query) ·
[format](#format) · [report](#report) · [doctor](#doctor) · [lint](#lint) ·
[add](#add) · [extract](#extract) · [price](#price) ·
[split and merge](#split-and-merge) · [explain](#explain) ·
[config, compat, completions](#config-compat-completions)

## Global flags

Accepted before or after any command:

| Flag | Meaning |
|------|---------|
| `-P, --profile <PROFILE>` | use a profile from the config file |
| `--plugin-max-time-secs <SECS>` | time budget per WASM/Python plugin call (default 30) |
| `--plugin-max-memory-mb <MB>` | memory cap per WASM/Python plugin call (default 256) |

The ledger file defaults to `$RLEDGER_FILE`, then the config file's default.
Pass it explicitly anyway.

## Exit codes

| Code | Meaning |
|------|---------|
| 0 | success; `check` found no errors (warnings are allowed) |
| 1 | `check` found errors; `format --check` would change the file; `query` or a report refused to answer, or the BQL did not parse |
| 2 | could not run: file missing, no FILE, bad arguments, `format` on a file with parse errors, a lint that cannot answer |

## check

```bash
rledger check [OPTIONS] FILE
```

| Flag | Meaning |
|------|---------|
| `-f, --format <text\|json>` | `json` prints one object on stdout (see SKILL.md) |
| `-q, --quiet` | print nothing; use the exit code |
| `-v, --verbose` | include timing |
| `--show-summary` | count diagnostics per code, most frequent first (in JSON: a `rule_summary` object) |
| `--include-rules <CODES>` | show only these codes, comma-separated (`E2001,E1001`) |
| `--exclude-rules <CODES>` | show everything except these codes |
| `-C, --no-cache` | do not read or write the parse cache |
| `-a, --auto` | enable auto-plugins such as `auto_accounts` |
| `--native-plugin <NAME>` | run a built-in plugin (repeatable), e.g. `implicit_prices` |
| `--plugin <WASM_FILE>` | load a WASM plugin (repeatable) |
| `--lint <NAME>` | also run an advisory lint (`transfers`); findings are warnings |
| `--lint-min-confidence <VALUE>` | confidence floor for `--lint transfers` (default 0.8) |

Filters change only what is shown; the exit code still counts every error.

`check` writes a cache file next to the ledger (`.ledger.beancount.cache`).
It is invalidated automatically when any loaded file changes. Use `-C` (or
`BEANCOUNT_DISABLE_LOAD_CACHE=1`) to avoid creating it, for example in a
read-only checkout.

```bash
rledger check -f json ledger.beancount | jq -r '.diagnostics[] | "\(.file):\(.line): \(.code) \(.message)"'
rledger check --show-summary ledger.beancount
rledger check --exclude-rules E2001 ledger.beancount
rledger check --native-plugin auto_accounts ledger.beancount
```

## query

```bash
rledger query [OPTIONS] FILE "QUERY"
```

| Flag | Meaning |
|------|---------|
| `-f, --format <text\|csv\|json\|beancount>` | output format; `beancount` suits `PRINT` |
| `-o, --output <FILE>` | write to a file instead of stdout |
| `-F, --query-file <FILE>` | read the query from a file |
| `-m, --numberify` | drop currencies, print bare numbers |
| `-q, --no-errors` | do not list the ledger's validation errors on stderr |
| `--no-cache` | always re-parse |

The query may also come on stdin (`rledger query FILE < q.bql`); it is read
whole, so it may span lines. With no query argument, no `-F`, and a terminal on
stdin, `query` opens an interactive shell. Avoid that in automation.

`query` answers when the ledger has validation errors (as `bean-query` does)
but refuses, exit 1 and no rows, when a file did not parse, a transaction
could not be booked, or `option "booking_method"` is invalid. BQL is covered in
[bql.md](bql.md).

## format

```bash
rledger format [OPTIONS] FILE...
```

| Flag | Meaning |
|------|---------|
| `-i, --in-place` | rewrite the files |
| `-o, --output <OUTPUT>` | write to a file (one input only) |
| `--check` | exit 1 if any file would change; writes nothing |
| `--diff` | with `--check`, show what would change |
| `--ledger <ROOT>` | read display options (`render_commas`) from this root |
| `--no-ledger` | ignore any root; format the file's bytes alone |

Without `-i` or `-o` the result goes to stdout. A file with a parse error is
refused (exit 2). Formatting is idempotent, and it aligns amounts; it does not
reorder entries or change any number.

```bash
rledger format --check --diff ledger.beancount
rledger format --in-place main.beancount accounts.beancount
```

## report

```bash
rledger report [OPTIONS] FILE <REPORT> [REPORT OPTIONS]
```

The file must come before the report name. Common options, accepted before or
after the report name: `-f, --format <text|csv|json>`, `--no-pager`,
`--no-cache`, `-v`.

| Report | What it shows | Its options |
|--------|---------------|-------------|
| `balances` | every account's balance | `-a` prefix, window |
| `balsheet` (`bal`) | assets, liabilities, equity | window |
| `income` (`is`) | income and expenses | window |
| `journal` | transactions | `-a`, `-l, --limit`, `--running`, window |
| `register` | journal with running balance | `-a`, `-l`, window |
| `holdings` | units and cost basis | `-a`, window |
| `networth` | net worth per period | `-p, --period <daily\|weekly\|monthly\|yearly>`, `-c, --currency`, `-a`, `--no-zero` |
| `accounts` | account list | |
| `commodities` | commodity list | |
| `stats` | directive counts and date range | |
| `prices` | price entries | `-c, --commodity` |
| `returns` | money- and time-weighted return | `-i, --investments` (required), `-n, --income`, `-c`, `-e, --end`, `--by-group` |
| `capgains` | realized gains per lot | `-a`, `-y, --year`, `-e, --end`, `--long-term-days`, `--irr` |
| `budget` | budget vs actual (`custom "budget"`) | `-a`, `--children`, window |

"Window" means `--from DATE` (inclusive) and/or `--to DATE` (**exclusive**:
the first day not reported), or `--year YYYY`, or `--time EXPR` (Fava syntax:
`2024-Q1`, `2024-03`, `year-1`, ...). `--year` and `--time` combine with no
other window flag.

```bash
rledger report ledger.beancount income --time 2024-Q1
rledger report ledger.beancount journal -a Expenses:Food --year 2024
rledger report ledger.beancount networth -p yearly
rledger report ledger.beancount returns -i Assets:Brokerage -n Income:Dividends
rledger report -f json ledger.beancount balances
```

## doctor

Debugging tools. Each takes the file as a positional argument.

| Command | Use |
|---------|-----|
| `rledger doctor missing-open FILE` | print an `open` for each account used but never opened, dated at its first use |
| `rledger doctor context FILE LINE` | source lines around LINE and the directive there |
| `rledger doctor linked FILE ^link` | transactions sharing a link (also `#tag` or a line number) |
| `rledger doctor region FILE START END` | transactions in a line range and their net change |
| `rledger doctor print-options FILE` | options in effect |
| `rledger doctor list-options` | every option the loader knows, with its type |
| `rledger doctor display-context FILE` | inferred display precision per currency |
| `rledger doctor roundtrip FILE` | parse/format round-trip check |
| `rledger doctor parse FILE` | parsed directives |
| `rledger doctor lex FILE` | lexer tokens |
| `rledger doctor directories FILE DIR...` | check a document folder tree against account names |
| `rledger doctor stats FILE` | ledger statistics |

`missing-open` output is valid Beancount; review it, then append it to the
root file and re-run `check`.

## lint

Advisory checks `check` does not run. Each takes one or more files and
`-f, --format <text|json>`. They exit 0 when they answer (findings
included, unless a fail flag is given), 1 on a finding under a fail flag, and
2 when they cannot answer.

| Command | Reports |
|---------|---------|
| `rledger lint closed-nonempty FILE` | accounts closed with a non-zero balance |
| `rledger lint control-chars FILE` | control characters in strings and comments |
| `rledger lint transfers FILE` | likely unlinked transfer pairs; `--apply` writes `^xfer-...` links into the files |
| `rledger lint linked-transit --link-prefix xfer- --account Assets:Transit FILE` | linked transfer legs that do not match; `--fail-on mismatch,missing` |
| `rledger lint cross-group --group A=Assets:A,Income:A --group B=Assets:B FILE` | transactions spanning groups; `--fail-on-findings` |

`lint transfers` also takes `--min-confidence`, `--date-window` and
`--amount-tolerance`. Preview before `--apply`.

## add

```bash
rledger add FILE -n -d 2024-03-05 --quick "Payee" "Narration" Expenses:Food "42.10 USD" Assets:Bank:Checking
rledger add FILE -y -d 2024-03-05 --quick "Payee" "Narration" Expenses:Food "42.10 USD" Assets:Bank:Checking
```

`--quick` takes payee, narration, then account and amount pairs; the last
amount may be left out and is balanced. Each amount needs its currency and
must be one argument (quote it). Put FILE before `--quick`, because `--quick`
consumes everything after it.

- `-n, --dry-run` prints the transaction and appends nothing.
- `-y, --yes` appends without asking. Without `-y` it asks, and when stdin is
  not a terminal the answer defaults to yes, so the transaction is appended.
- `-d, --date` defaults to today (also `yesterday`, `+1`, `-1`).
- Without `--quick`, `add` is interactive. Do not use that from an agent.

`add` does not check that the accounts are open; run `rledger check` after.

## extract

Turns a bank statement (CSV, OFX/QFX) into Beancount transactions on stdout.

```bash
rledger extract bank.csv -a Assets:Bank:Checking
rledger extract bank.csv --auto -a Assets:Bank:Checking --existing ledger.beancount
rledger extract bank.csv -a Assets:Bank:Checking --balance 1234.56 --balance-date 2024-03-04
rledger extract statement.ofx -a Liabilities:CreditCard -o new.beancount
```

| Flag | Meaning |
|------|---------|
| `-a, --account <ACCOUNT>` | the statement's account |
| `-c, --currency <CURRENCY>` | currency (default USD) |
| `--auto` | detect delimiter, columns and date format |
| `--date-column`, `--narration-column`, `--payee-column`, `--amount-column` | CSV column names or indexes |
| `--debit-column`, `--credit-column` | separate debit and credit columns |
| `--date-format <FMT>` | strftime format (default `%Y-%m-%d`) |
| `--delimiter`, `--skip-rows`, `--no-header`, `--invert-sign` | CSV shape |
| `--existing <FILE>` | skip transactions already in this ledger |
| `--use-merchant-dict` | categorize known merchants (`NETFLIX` → `Expenses:Subscriptions:Streaming`) |
| `--suggest-categories` | guess counter-accounts from `--existing` (Naive Bayes) |
| `--balance <AMOUNT>`, `--balance-date <DATE>` | append a balance assertion |
| `-o, --output <FILE>` | write to a file; refuses a non-empty one unless `--force` |
| `-i, --importer <NAME>`, `--config <FILE>`, `--list-importers` | named importers from `importers.toml` |

Uncategorized rows go to `Expenses:Unknown` or `Income:Unknown`, which the
ledger usually has not opened. Review the output, replace those accounts, then
append it and run `rledger check`. See the
[importing guide](https://github.com/rustledger/rustledger/blob/main/docs/guides/importing.md).

## price

Fetches commodity prices from online sources. **`-f` is the ledger file here,
not the format.**

```bash
rledger price -f ledger.beancount --dry-run      # what would be fetched, no network
rledger price -f ledger.beancount -b             # fetch, print price directives
rledger price AAPL MSFT -b
rledger price --list-sources
```

Only commodities with `price:` or `quote_currency:` metadata that are
currently held are fetched by default; `--undeclared` and `--inactive` widen
that. `-b, --beancount` prints `price` directives to append to the ledger.

## split and merge

```bash
rledger split --by year --dry-run ledger.beancount
rledger merge --dry-run ledger.beancount
```

`split --by year|month` moves dated directives into one file per period and
leaves `include`s in the root; `merge` inlines a file's includes. Both verify
that the ledger loads to the same directives and refuse to write if not.
Always run with `-n` first.

## explain

```bash
rledger explain E2001     # also e2001 or 2001
rledger explain           # list codes
```

It knows the validator's `E` codes; it does not explain parse (`P`) codes or
every option code (see [errors.md](errors.md)).

## config, compat, completions

- `rledger config path` shows where config files are looked for;
  `rledger config show` prints the merged config; `rledger config init` writes
  a default config.
- `rledger compat install` installs `bean-check`, `bean-query`, ... wrapper
  scripts that call rledger.
- `rledger completions bash` (or `zsh`, `fish`, `elvish`, `powershell`) prints a
  shell completion script.
