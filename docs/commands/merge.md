______________________________________________________________________

## title: rledger merge description: Inline a ledger's includes back into one file

# rledger merge

Merge a beancount file and everything it includes into one file: the inverse of
[split](split.md). The ledger is loaded before and after, and nothing is written
unless the two load identically.

## Usage

```bash
rledger merge [OPTIONS] [FILE]
```

## Arguments

| Argument | Description |
|----------|-------------|
| `FILE` | The file whose includes to inline (default: the config's default file) |

## Options

| Option | Description |
|--------|-------------|
| `-o, --output <OUTPUT>` | Write the merged ledger to this new file; `FILE` and its includes are left untouched |
| `--keep-included` | Keep the inlined files on disk instead of removing them |
| `--ledger <ROOT>` | The ledger root `FILE` belongs to, when `FILE` is itself included by another file. The equivalence check loads this root. |
| `-n, --dry-run` | Show the plan and run the equivalence check, but write nothing |
| `-P, --profile <PROFILE>` | Use a profile from config |

## Example

```bash
rledger merge ledger.beancount
```

```text
Plan: merge ledger.beancount and the files it includes
  inline and remove  ledger/2023.beancount
  inline and remove  ledger/2024.beancount
  rewrite  ledger.beancount
Equivalence check passed: 812 directives, 0 errors and warnings, options and plugins unchanged.
Backup of the original files: .rledger-backup/20241011T121500Z-merge
Done; the ledger was reloaded from disk and matches.
```

## How files are combined

The merged file is `FILE`'s own text with its `include` lines removed (comments
written above them, or on the same line, stay), followed by the content of each
included file in include order. Nested includes and glob patterns are followed
the way the loader follows them. Directives and comments are copied verbatim;
nothing is reformatted. Only a blank line between files is added, and a
byte-order mark at the top of an included file is dropped.

That order is the order the loader reads files in, so same-date directives keep
their booking order.

By default the inlined files are removed after the merged file is in place. They
are copied to `.rledger-backup/<timestamp>-merge/` first, with a `manifest.txt`,
and written as described for [split](split.md#writing-and-backups).
Only plain files inside `FILE`'s directory are removed: an include outside it, or
one reached through a symlink, may belong to another ledger and is left in place
(the plan says so), together with everything it includes.

The merged file is no more readable than the most private file merged into it:
it keeps `FILE`'s group, and loses group or other read access that any merged
file withholds (a file in another group withholds group access). Backups keep
the group and permissions of the files they copy. Where a group cannot be
copied, group access is dropped instead.

With `--output`, `FILE` is also loaded with the new file in place, so an output
path that one of `FILE`'s include globs would pick up is refused.

A `FILE` that is a symlink to a file in another directory is refused, as in
[split](split.md): opened through the link, its includes are the files next to
the link, while `merge` would work on the file it points to and inline that
file's neighbors instead. Merge the file it points to if nothing opens the
ledger through the link.

## The equivalence check

`merge` runs the same check as [split](split.md#the-equivalence-check). Typical
refusals:

- An included file sets an `option` that the loader ignores in an included file
  (such as `booking_method`). Inlined into the root, it would take effect.
- A relative `document` path in an included file in another directory would
  resolve against the root's directory instead.
- The original layout reports an error that only exists because of the file
  structure, such as a file included twice.

## Exit Codes

| Code | Meaning |
|------|---------|
| 0 | Merge written (or, with `--dry-run`, would be) |
| 1 | The equivalence check refused; nothing was written |
| 2 | Error (file not found, parse errors, nothing to merge, ...) |

## See Also

- [split](split.md) - Split a file into one file per year or month
