______________________________________________________________________

## title: rledger extract description: Import transactions from bank statements

# rledger extract

Import transactions from bank statements. Handles CSV and OFX/QFX out of the box; can also load third-party importers as sandboxed WASM modules via `--wasm-importer` / `--wasm-importer-dir`.

## Usage

```bash
rledger extract [OPTIONS] [FILE]
```

## Arguments

| Argument | Description                                                          |
| -------- | -------------------------------------------------------------------- |
| `FILE`   | CSV or OFX file to import (required unless using `--list-importers`) |

## Options

### Config-based Import

| Option                  | Description                                        |
| ----------------------- | -------------------------------------------------- |
| `-i, --importer <NAME>` | Use a named importer from config                   |
| `--config <FILE>`       | Path to importers.toml configuration file          |
| `--list-importers`      | List available importers from config file and exit |

### Auto-Detection

| Option   | Description                                                                                     |
| -------- | ----------------------------------------------------------------------------------------------- |
| `--auto` | Auto-detect CSV format (delimiter, columns, date format). Conflicts with manual column options. |

### Direct CLI Import

| Option                      | Description                                                                                |
| --------------------------- | ------------------------------------------------------------------------------------------ |
| `-a, --account <ACCOUNT>`   | Target account [default: Assets:Bank:Checking]                                             |
| `-c, --currency <CURRENCY>` | Currency for amounts [default: USD]                                                        |
| `--date-column <COL>`       | Date column name or index [default: Date]                                                  |
| `--date-format <FMT>`       | Date format (strftime-style) [default: %Y-%m-%d]                                           |
| `--narration-column <COL>`  | Narration/description column [default: Description]                                        |
| `--payee-column <COL>`      | Payee column name (optional)                                                               |
| `--amount-column <COL>`     | Amount column name or index [default: Amount]                                              |
| `--amount-locale <LOCALE>`  | Locale for parsing amounts (e.g., `en_US`)                                                 |
| `--amount-format <FMT>`     | Custom format for parsing amounts                                                          |
| `--debit-column <COL>`      | Debit column (for separate debit/credit)                                                   |
| `--credit-column <COL>`     | Credit column (for separate debit/credit)                                                  |
| `--delimiter <CHAR>`        | CSV delimiter [default: ,]                                                                 |
| `--skip-rows <N>`           | Number of header rows to skip [default: 0]                                                 |
| `--invert-sign`             | Invert sign of amounts                                                                     |
| `--no-header`               | CSV has no header row                                                                      |
| `--include-zero-amounts`    | Preserve rows whose amount is exactly zero (default drops them; bank "status filler" rows) |

If you name no account at all, `extract` refuses an OFX statement that
describes a **liability** (a credit card or line of credit) rather than posting
it to the `Assets:Bank:Checking` default, since that would invert the sign of
every transaction and use an account you never chose. Naming one — with
`--account`, an `importers.toml` entry, or an `open` directive plus `--ledger` —
is always enough.

### Output Options

| Option                  | Description                                                                                                                                     |
| ----------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------- |
| `-o, --output <FILE>`   | Write output to file instead of stdout. Refuses to overwrite a file that already has content (use `--force`, or append with `>>`)               |
| `--force`               | Allow `--output` to overwrite a non-empty file, replacing its contents                                                                         |
| `--ledger <FILE>`       | Read importer profiles from a ledger's `open` directives (see below)                                                                           |
| `--existing <FILE>`     | Existing ledger file for duplicate detection                                                                                                    |
| `--suggest-categories`  | Use ML (Naive Bayes on the `--existing` ledger) to suggest accounts for transactions the rules engine didn't categorize. Requires `--existing`. |
| `--balance <AMOUNT>`    | Append a balance assertion directive with the given amount (e.g., `1234.56`)                                                                    |
| `--balance-date <DATE>` | Date for the balance assertion (defaults to today)                                                                                              |

### WASM Importers

Third-party importers ship as sandboxed `.wasm` modules. Flags below override `wasm_importer_dir` from `importers.toml`.

| Option                      | Description                                                                                                                                          |
| --------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------- |
| `--wasm-importer <PATH>`    | Register a specific `.wasm` importer ahead of built-ins. Repeatable. User-specified modules take precedence over discovered ones and built-ins.      |
| `--wasm-importer-dir <DIR>` | Scan a directory for `*.wasm` importer modules at startup. Repeatable. Subdirectories are not recursed into; non-`.wasm` files are silently skipped. |

## Examples

### Basic CSV Import

```bash
rledger extract bank-statement.csv -a Assets:Bank:Checking
```

### With Configuration

Create `importers.toml`:

```toml
[[importers]]
name = "chase"
account = "Assets:Bank:Chase"
date_column = 0
narration_column = 2
amount_column = 3
date_format = "%m/%d/%Y"
skip_header = true

[importers.mappings]
"AMAZON" = "Expenses:Shopping"
"WHOLE FOODS" = "Expenses:Food:Groceries"
"SHELL" = "Expenses:Transport:Gas"
```

```bash
rledger extract --importer chase chase-statement.csv
```

### Auto-Detect CSV Format

```bash
rledger extract bank-statement.csv -a Assets:Bank:Checking --auto
```

The `--auto` flag infers the delimiter, date format, and column roles from the
file content. It cannot be combined with manual column options like
`--date-column` or `--amount-column`.

### OFX Import

```bash
rledger extract statement.ofx -a Assets:Bank:Checking
```

OFX statements carry two things beyond the transactions themselves, and both
are used.

**`FITID` becomes a link.** Every transaction gets `^ofx-<id>` from the bank's
own transaction id, sanitized to the characters a link may contain:

```beancount
2024-01-15 * "COFFEE SHOP" ^ofx-202401150001
  Assets:Bank:Checking  -50.00 USD
  Expenses:Unknown
```

A link rather than a tag because it is identity, not a category. It is stable
across re-imports even if you rewrite the payee or narration.

**`LEDGERBAL` becomes a balance assertion**, dated the day after the
statement's `DTASOF`, because a beancount `balance` asserts the balance at the
*start* of its date while a bank states the close of business:

```beancount
2024-02-01 balance Assets:Bank:Checking  1234.56 USD
```

> **Expect this to fail on a first import, and that is the point.** The
> assertion says "after these transactions, the account holds exactly this".
> A ledger containing only one imported statement has no opening balance, so
> it will not add up:
>
> ```
> Balance failed for Assets:Bank:Checking: expected 1234.56 USD, got -50.00 USD
> ```
>
> Give the account its opening balance (the usual `Equity:Opening-Balances`
> pattern), or import the earlier statements, and it passes. That is the
> assertion doing its job: it fails until the account's history is complete,
> which is the difference between hoping an import is complete and knowing it.

No assertion is emitted when the statement does not state a balance, when the
`LEDGERBAL` is missing either its amount or its date, or when one file holds
several statements — their balances cannot be attributed to a single account,
and a warning says so.

### Append to Ledger

```bash
rledger extract statement.csv -a Assets:Bank >> ledger.beancount
```

`>>` is the right way to add to a ledger you are keeping. `--output` **replaces**
the file rather than appending, so it is for writing a fresh file. Pointing it at
a ledger that already has content is refused:

```console
$ rledger extract feb.csv --output ledger.beancount
error: refusing to overwrite ledger.beancount (163 bytes)
  --output truncates the target, which would destroy its current contents
  try: append with `rledger extract … >> ledger.beancount`, write elsewhere,
  or pass --force to overwrite deliberately
```

`--existing` is for duplicate detection only and does not protect a file from
being overwritten, so naming the same file for both `--existing` and `--output`
is refused outright.

### Output Order

`extract` writes a statement oldest-first, whichever way the bank exported it,
and keeps the export's own sequence within each day. This applies to every
importer: CSV, OFX and WASM.

For each input file it looks at the dates of consecutive rows, counting how
often the date goes up and how often it goes down (rows sharing a date are not
counted):

- **More steps down than up** means a newest-first export. The rows are
  reversed first, then sorted by date, so each day's rows come out in the
  reverse of the order the bank listed them.
- **Otherwise** the rows are sorted by date as they are. An oldest-first export
  comes out exactly as it went in, and an unsorted or grouped one (by payee,
  say) is sorted with each day's rows in file order.
- **A tie**, including a file whose rows all share one date, keeps file order:
  the direction cannot be told, so it is not guessed.

Rows on the same date are never reordered against each other except by that
one reversal. Other directives an importer produces, such as the balance
assertion from an OFX `LEDGERBAL`, are placed by date in the canonical order
`rledger format` and booking use. Moving a balance assertion never changes
whether it holds: beancount and `rledger check` evaluate a `balance` at the
start of its date, before that day's transactions, whichever line it is on, so
one dated on the statement's last day is written ahead of that day's rows. The
`--balance` assertion is always written last. Duplicate detection (`--existing`) runs after ordering, so its report of
skipped rows lists them in output order.

The assumption behind the reversal: **a bank that lists days newest-first lists
the rows within a day newest-first too.** Neither CSV nor OFX carries a time of
day that `extract` could check this against, and no time of day survives
import. A bank that sorts days descending but lists each day's rows
oldest-first would come out with those days' rows reversed.

### Importer Profiles in the Ledger

An account's `open` directive already declares the account and its currency,
which are two of the three things an importer needs. `--ledger` lets it declare
the third, so they need not be repeated in `importers.toml`:

```beancount
2024-01-01 open Liabilities:CreditCard USD
  importer: "ofx"
  importer-pattern: "*.qfx"
```

```bash
rledger extract card.qfx --ledger main.beancount
```

The transactions post to `Liabilities:CreditCard` in `USD`, both taken from the
directive. No `importers.toml` is needed for a format like OFX that describes
its own columns.

| key | meaning |
|-----|---------|
| `importer` | A built-in parser (`csv`, `ofx`; `qfx` is accepted for `ofx`) **or** the `name` of an `importers.toml` entry whose column mappings to use |
| `importer-pattern` | Filename glob selecting which files this account claims |

Rules worth knowing:

- **Opt-in.** Without `--ledger` nothing changes. Accounts with no `importer`
  key are ignored, so pointing it at an ordinary ledger is harmless.
- **The currency is only taken when the account opens with exactly one.**
  `open Assets:X USD,EUR` cannot be narrowed to one, and guessing which a
  statement uses would be a silent wrong answer, so the CLI value applies.
- **Both keys or neither.** `importer` without `importer-pattern` can never
  match a file; `importer-pattern` without `importer` says which files an
  account claims without saying how to read them. Either half alone is an
  error, not a preference.
- **A key with a non-string value is an error**, not an absence. `importer: 42`
  is something you wrote on purpose, so it is not read as "no profile here".
- **Two accounts claiming one file is an error.** Picking one would make the
  result depend on directive order.
- **`--importer` outranks a profile.** The flag names the entry to use, which
  settles both the parser and the account, so a profile matched by filename is
  dropped rather than merged — and a warning says so, since a silently ignored
  `--ledger` would be worse than a noisy one.
- **A ledger that does not parse is an error.** `--ledger` is an explicit
  request to read a file, so being unable to read it is not a reason to carry
  on with defaults.
- **Patterns match the filename, not the path.** `importer-pattern:
  "statements/*.qfx"` never matches, the same as `filename_pattern` in
  `importers.toml`.
- **A profile outranks `importers.toml` for the account and currency.** The
  `open` directive *is* the account's declaration; a config file disagreeing
  with it is the bug.
- **`--ledger` is separate from `--existing`.** The latter is only about
  duplicate detection. Passing both is fine, and they may name the same file.

### Duplicate Detection

```bash
# Skip transactions already in ledger
rledger extract statement.csv -a Assets:Bank --existing ledger.beancount
```

Only transactions in `ledger.beancount` that post to the importer's account,
in the same commodity, are candidates. A new transaction is a duplicate when it
shares an id link with one (`^ofx-…`, or `^csv-…` from
`transaction_id_column`) and moves the same amount on any date, or when it has
the same date and amount and the same or a similar payee/narration. Ids of the
same kind that differ mean two different transactions, however alike they
look; when only one side has an id (a ledger imported before ids existed), the
text decides. An entry that splits the account's leg over several postings is
also compared by its net movement, so a transfer already imported from the
other account's statement is recognized. Which rows are kept does not depend
on the order the statement or the ledger lists them in.

Each existing transaction absorbs at most one new one: two identical coffees on
one day both import when the ledger already holds only one. Skips are counted
on stderr, and up to 20 of each kind are listed (the rest are summarized as
`... and N more`):

```text
Filtered 1 duplicate transaction(s) already in the existing ledger (0 by id link, 1 by date, amount and text):
  skipped 2024-01-15 "Bakery" "Croissant" -2.50 EUR (same date, amount and text; existing: 2024-01-15 "Bakery" "Croissant" -2.50 EUR)
```

Rows with no payee or narration on either side match on date and amount alone
(so a statement without a description column re-imports to nothing), and each
such skip is flagged, since two different description-less rows on one day for
one amount look identical:

```text
Filtered 1 duplicate transaction(s) already in the existing ledger (0 by id link, 0 by date, amount and text, 1 by date and amount alone):
  skipped 2024-01-15 "" -60.00 EUR (same date and amount, and neither has a payee or narration to compare; existing: 2024-01-15 "" -60.00 EUR) -- check: nothing but the date and amount ties these together
```

## Importer Configuration

### CSV Options

```toml
[[importers]]
name = "my_bank"
account = "Assets:Bank:MyBank"

# Currency of the amounts. There is no default: when this is left out,
# extract uses the currency of the account's `open` directive in the
# --ledger ledger (or in --existing, if --ledger does not open the
# account), when that `open` names exactly one, and otherwise stops with
# an error rather than guess. Precedence, highest first: a --ledger
# profile, --currency, this key, the account's `open`. A value that is not
# a commodity (`usd`, `€`, "") is an error naming where it came from, for
# CSV, OFX and WASM importers alike, and a value the account's `open` does
# not allow is a warning.
currency = "EUR"

# Column mapping (0-indexed)
date_column = 0
payee_column = 1
narration_column = 2
amount_column = 3

# Or use column names (if CSV has header) instead of the indices above;
# each key may appear only once
# date_column = "Date"
# amount_column = "Amount"

# Date parsing
date_format = "%Y-%m-%d"  # or "%m/%d/%Y", "%d.%m.%Y"

# A per-row currency, for multi-currency exports. A blank cell uses
# `currency`. A lower- or mixed-case code (`usd`, `Eur`) is upper-cased,
# since the bank's file cannot be fixed and the code means the same either
# way; a cell that is still not a commodity (`€`, `US$`) is a row error
# naming the row, this column and the value.
# currency_column = "Currency"

# A unique per-transaction id from the bank, added as a `^csv-<id>` link
# that `--existing` uses as identity when deduplicating
transaction_id_column = "Transaction ID"

# The file has NO header row. Columns must then be 0-based indices,
# and the first row is read as data. Leave this out when the file has
# a header: the header row is then read as column names, not imported.
# (It is the same setting as `--no-header`, despite the name.)
# skip_header = true

# Invert amounts (for credit card statements)
invert_amounts = true

# Default expense account
default_expense = "Expenses:Unknown"

# Pattern-based account mapping
[importers.mappings]
"GROCERY" = "Expenses:Food:Groceries"
"GAS STATION" = "Expenses:Transport:Gas"
"PAYROLL" = "Income:Salary"
```

### Command-Line Flags and `importers.toml`

A flag you pass outranks the matching key in the entry, which outranks the
built-in default:

```text
built-in default  <  importers.toml entry  <  command-line flag
```

That lets one entry describe a bank's CSV layout while each file says which
account it belongs to:

```toml
[[importers]]
name = "santander"
date_column = "date"
payee_column = "payee"
credit_column = "money_in"
debit_column = "money_out"
currency = "GBP"
# no account, no invert_amounts: those differ per account
```

```bash
rledger extract --importer santander --account Assets:Santander:Current current.csv
rledger extract --importer santander --account Liabilities:Santander:Credit \
  --invert-sign --skip-rows 1 credit.csv
```

Passing a flag is equivalent to writing its key in the entry — it goes
through the same parsing and validation. Two names differ between the two:

| Flag | `importers.toml` key |
|------|----------------------|
| `--invert-sign` | `invert_amounts = true` |
| `--no-header` | `skip_header = true` |

Boolean flags can only turn a setting on, so omitting `--invert-sign` leaves
an entry's `invert_amounts = true` in force.

A `--ledger` profile still outranks both for the account and currency: the
`open` directive is the account's declaration.

### Enrichment Options

The importer library supports additional enrichment features via the
`CsvConfigBuilder` API:

| Builder Method            | Description                                                                                                         |
| ------------------------- | --------------------------------------------------------------------------------------------------------------------- |
| `use_merchant_dict(true)` | Enable the built-in merchant dictionary (75 common patterns) as a low-priority fallback for account categorization  |
| `regex_mappings(vec)`     | Add regex-based account mappings (case-insensitive, compiled at load time)                                          |

These options are available in the Rust library API but are not yet exposed as
fields in `importers.toml` configuration. Substring-based mappings in
`[importers.mappings]` are supported in TOML and work the same way.

### Multiple Importers

```toml
[[importers]]
name = "checking"
account = "Assets:Bank:Checking"
# ...

[[importers]]
name = "credit_card"
account = "Liabilities:CreditCard"
invert_amounts = true
# ...
```

Use with:

```bash
rledger extract --importer checking statement.csv
```

The `importers.toml` file is auto-discovered from the current directory or the user config directory
(`$RLEDGER_CONFIG_DIR` if set, otherwise the platform default such as `~/.config/rledger/`). To specify a custom path:

```bash
rledger extract --config path/to/importers.toml --importer checking statement.csv
```

### Choosing an Entry by the File's Columns

Without `--importer`, the entry is chosen by `filename_pattern`. When several
entries match a file's name, `extract` reads that file's header and keeps only
the entries whose columns are all there. Each entry's header is read the way
that entry would read it (its own `delimiter` and header setting).

This tells apart statements that share a filename and differ only in their
columns, such as a multi-currency account's exports:

```toml
[[importers]]
name = "starling-gbp"
filename_pattern = "StarlingStatement_*.csv"
account = "Assets:Starling"
currency = "GBP"
amount_column = "Amount (GBP)"

[[importers]]
name = "starling-eur"
filename_pattern = "StarlingStatement_*.csv"
account = "Assets:Starling"
currency = "EUR"
amount_column = "Amount (EUR)"
```

A statement whose header has `Amount (EUR)` uses `starling-eur`, and one with
`Amount (GBP)` uses `starling-gbp`.

Only a column the entry names (a `*_column` key set to a header name) can rule
it out. An entry is never ruled out when the header cannot speak to it: one
whose columns are all indices or left to the defaults, a headerless one
(`skip_header = true`), an OFX entry, or one that runs `preprocess` (its
columns describe the command's output, not this file). When exactly one entry
is left it is used; otherwise `extract` still refuses, and lists for each
entry which of its columns the header lacks:

```console
error: Multiple importers match file 'StarlingStatement_2023.csv': starling-gbp, starling-eur. Use --importer to select one.
  the file's header did not settle it:
    'starling-gbp': header has no amount_column "Amount (GBP)"
    'starling-eur': header has no amount_column "Amount (EUR)"
```

A file matched by one entry's `filename_pattern` uses that entry, as before,
without reading its header.

### List Available Importers

Lists both TOML profiles (for `--importer <name>`) and registered importer engines (built-in CSV/OFX plus any WASM modules from `--wasm-importer`/`--wasm-importer-dir`):

```bash
rledger extract --config importers.toml --list-importers
```

### Using a WASM Importer

```bash
# One-off: register a single .wasm file
rledger extract --wasm-importer ./my-bank.wasm statement.dat -a Assets:Bank

# Or scan a whole directory at startup
rledger extract --wasm-importer-dir ~/.config/rledger/importers.d statement.dat -a Assets:Bank
```

Persistent setup goes in `importers.toml`:

```toml
wasm_importer_dir = "/etc/rledger/importers.d"
```

WASM importers participate in the same `identify`-then-`extract` dispatch as the built-ins. See [`examples/wasm-importer-csv-example`](https://github.com/rustledger/rustledger/tree/main/examples/wasm-importer-csv-example) for how to write one.

### Direct CLI Import (No Config)

```bash
rledger extract statement.csv \
  -a Assets:Bank:Checking \
  --date-column "Transaction Date" \
  --date-format "%m/%d/%Y" \
  --amount-column "Amount" \
  --narration-column "Description" \
  --skip-rows 1 \
  --invert-sign
```

## External Preprocessing (PDF and other formats)

An importer entry can declare a `preprocess` command — an argv array run
before format detection and extraction. Any `{input}` argument is replaced
with the statement's path; the command's stdout becomes the content the
rest of the pipeline (auto-inference, column mapping, categorization)
consumes. This is how PDF statements import today, until a native parser
exists:

```toml
[[importers]]
name = "mybank-pdf"
filename_pattern = "*.pdf"
account = "Assets:Checking"
# pdftotext's -layout output piped through a small table-to-CSV script.
# Note the path goes in as a positional ("$1"), NOT spliced into the string:
preprocess = ["sh", "-c", "pdftotext -layout \"$1\" - | mybank-table-to-csv", "_", "{input}"]
date_column = "Date"
narration_column = "Description"
amount_column = "Amount"
```

The command runs with the CLI only — the WASI component cannot exec and
rejects entries that set `preprocess` (a GUI host runs the preprocessor
itself and passes the output as content).

**Trust model**: `preprocess` executes a program named by the config, so it
is honored only when the config is yours:

| where the config came from | `preprocess` |
|---|---|
| `--config path/to/importers.toml` | runs |
| `~/.config/rledger/importers.toml` | runs |
| `./importers.toml`, found by looking around | **ignored, with a warning** |

The last row is the point. Without it, `rledger extract statement.csv` would
execute whatever an `importers.toml` in the current directory says — an
unzipped statement bundle, a cloned repo, a shared downloads folder — because
of where your terminal happened to be. The entry still works for declaring
columns; only the command is withheld. Pass it with `--config` if it really is
yours.

### `{input}` and shells

`{input}` is substituted by plain text replacement, so **where** you put it
decides whether a filename can become code:

| form | safe? | why |
|---|---|---|
| `["pdftotext", "-layout", "{input}", "-"]` | ✅ | no shell; the path is one argv element whatever it contains |
| `["sh", "-c", "… \"$1\" …", "_", "{input}"]` | ✅ | the path arrives in `$1`, which the shell does not re-parse |
| `["sh", "-c", "… {input} …"]` | ❌ **rejected** | `sh -c` parses its argument as source, so `a;rm -rf ~;b.pdf` runs `rm` |

The trust model above is about the *config*. The **filename is a separate
untrusted input** — importing files you downloaded is the entire point of this
feature — so a config you wrote yourself is not enough to make the third row
safe. `rledger extract ~/Downloads/*.pdf` would be arbitrary code execution.
The CLI refuses that shape and tells you the positional rewrite.

Only write commands you trust, and treat an `importers.toml` you did not author
like a shell script. A community profile registry must never carry
`preprocess` entries.

## See Also

- [Importing Guide](../guides/importing.md) - Detailed import tutorial
- [Architecture: rustledger-ops](../reference/architecture.md) - Crate providing the enrichment operations
