______________________________________________________________________

## title: rledger split description: Split a ledger file into one file per year or month

# rledger split

Split a beancount file into one file per year or month, plus a root file of
`include` lines. The ledger is loaded before and after, and nothing is written
unless the two load identically.

## Usage

```bash
rledger split --by <year|month> [OPTIONS] [FILE]
```

## Arguments

| Argument | Description |
|----------|-------------|
| `FILE` | The file to split (default: the config's default file). It becomes the root. |

## Options

| Option | Description |
|--------|-------------|
| `--by <year\|month>` | Period each new file covers (required) |
| `--dir <DIR>` | Directory for the period files (default: a directory named after `FILE`, next to it; if `FILE` is a symlink, next to the file it points to) |
| `--ledger <ROOT>` | The ledger root `FILE` belongs to, when `FILE` is itself included by another file. The equivalence check loads this root. |
| `-n, --dry-run` | Show the plan and run the equivalence check, but write nothing |
| `-P, --profile <PROFILE>` | Use a profile from config |

## Example

```bash
rledger split --by year ledger.beancount
```

```text
Plan: split ledger.beancount by year
  create   ledger/2023.beancount  (412 dated directives)
  create   ledger/2024.beancount  (388 dated directives)
  rewrite  ledger.beancount  (keeps 4 option/plugin/include lines; adds 2 includes)
Equivalence check passed: 812 directives, 0 errors and warnings, options and plugins unchanged.
Backup of the original files: .rledger-backup/20241011T120000Z-split
Done; the ledger was reloaded from disk and matches.
```

`ledger.beancount` now holds its options, plugins and existing includes, and:

```beancount
include "ledger/2023.beancount"
include "ledger/2024.beancount"
```

## What goes where

- **Dated directives** (transactions, `open`, `balance`, `price`, ...) go to the
  file for their year or month, in their original order.
- **Comments move with the directive they precede**, copied verbatim. Nothing is
  reformatted; the only lines `split` writes itself are the new `include` lines
  and the `pushtag`/`poptag` lines described below, and it drops blank lines at
  the very top of each new file. The file's header (the comments above the first directive, up to
  the last blank line) and anything after the last directive stay in the root.
- **`option`, `plugin` and `include`** stay in the root. The new `include` lines
  go in front of any `include` the file already had.
- **`pushtag` / `pushmeta`** apply per file, so a span that crosses a period
  boundary is closed at the end of one file and re-opened at the top of the
  next. Every directive keeps exactly the tags and metadata it had.

## The equivalence check

Before writing, `split` loads the ledger as it is and as it would be, with
plugins, booking and validation, and compares:

- the processed directive stream, in booking order;
- options and plugins;
- every error and warning, and the directive it is attached to;
- where each `document` path resolves to;
- realized capital gains and failing balance assertions.

If anything differs, `split` prints the first difference and exits with status 1
without writing anything. After writing, it loads the ledger from disk once more
and restores the backup if that load disagrees.

A common refusal is a relative `document` path: it resolves against the
directory of the file that contains it, so moving it into `ledger/` would point
it elsewhere. Use `--dir .` to keep the period files beside the root.

## Why only by date

Same-date directives book in the order their files are loaded. Splitting by date
keeps every date in one file, in its original order, so which lot a sale matches
cannot change. Splitting by account would send same-date transactions to
different files and could change it, so it is not offered.

## Writing and backups

The original is first copied to `.rledger-backup/<timestamp>-split/`, keeping
its group and permissions, with a `manifest.txt` listing every file saved and
created. The new files are then written next to their targets under
temporary names and moved into place, the root last. Until the root is replaced
the old ledger is intact, and once it is the new one is complete. If anything
fails before that point, nothing but the backup is left on disk. `split` refuses
to overwrite a period file that already exists.

Files that are encrypted, not valid UTF-8, or have parse errors are refused.

## Exit Codes

| Code | Meaning |
|------|---------|
| 0 | Split written (or, with `--dry-run`, would be) |
| 1 | The equivalence check refused; nothing was written |
| 2 | Error (file not found, parse errors, a target already exists, ...) |

## See Also

- [merge](merge.md) - The inverse: inline includes back into one file
- [format](format.md) - Format files in the canonical style
