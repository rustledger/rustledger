# Upstream Check Coverage

Every check beancount can report to a user has a row in
`crates/rustledger/tests/fixtures/upstream-checks/checks.toml`.
Each row records what rledger does about that check. The table exists because
a whole class of bugs came from checks that were never ported: two of them
were found by reading beancount's `ops/validation.py` one function at a time
(#3044, #3045). The table does that walk for every module, and a test fails
when beancount gains a check the table does not list.

## What counts as an upstream check

`enumerate.py`, which sits beside the table, lists the checks in the
installed beancount by reading its source (Python's `ast`). It finds five
kinds:

| Kind | Id | What it is |
|---|---|---|
| Error site | `site:<module.function>:<message>` | A construction of one of beancount's error tuples (`ValidationError`, `BalanceError`, `ParserError`, `LoadError`, a plugin's own `...Error`, ...) in `core/`, `ops/`, `parser/`, `plugins/` or `loader.py`. The message is the source's template, with each interpolation written `{}`. A message the source does not spell out (one built in C, or `str(exc)`) is written `<dynamic>`. |
| Raised exception | `raise:<module.function>:<message>` | A `raise` in `ops/`, `parser/`, `plugins/` or `loader.py`. Beancount turns several of these into errors: an option converter's `ValueError` becomes `Error for option ...`, and an exception escaping a plugin becomes `Error applying plugin ...`. |
| Plugin | `plugin:beancount.plugins.<name>` | Every module under `beancount/plugins/`, including the ones that report nothing themselves (`check_closing` and `check_drained` work by adding balance assertions). |
| Deprecated option | `option-deprecated:<name>` | Every option whose descriptor carries a deprecation message. |
| Manual | `manual:<name>` | A check the source scan cannot see (gpg decryption). |

The module scope matches the walk: the validations, balance, pad and document
passes, the options and the grammar's builder, booking and interpolation, the
loader, and every plugin. The C lexer and parser report through two builder
methods, `build_lexer_error` and `build_grammar_error`, so the table has one
row for each. Their full parity is the job of the parse-error-parity CI job.

## Statuses

| Status | Meaning | Required fields |
|---|---|---|
| `covered` | rledger reports the same condition | `rledger` (the code and the function), and a `case`, a `test`, or both |
| `deviation` | rledger deliberately behaves differently | `compat`, a link to a heading of [compatibility.md](compatibility.md) |
| `not-applicable` | no ledger can reach it in beancount, or it checks something rledger does not have | `reason` |
| `missing` | beancount reports it and rledger does not | `note`, saying what rledger does instead |

## Cases

A row's `case` names a small ledger in `cases/`. The test runs that ledger
through both `rledger check` and beancount's `bean-check`, and checks that:

- rledger reports the row's `code` on exactly the row's lines. A `code` of the form `E8004|E8005` accepts any of the listed codes, for a code that depends on the build's features. A row with no
  `code` must produce no errors at all.
- beancount reports the row's message on exactly the row's lines. The message
  is matched against the template in the id, or against the substring in
  `python_message`.

When both tools report on the same line, the row says `lines`. When they
differ, it gives `python_lines` and `rledger_lines`, and a `covered` row must
then have a `note` saying how they differ. Beancount reports a load-time,
plugin-configuration or end-of-file error at line 0. Where rledger points at
a real line instead, the row records that. `python_crash = true` marks a case
where bean-check 3.2.3 crashes with a traceback, even though it recorded the
error first.

Every row is pinned in both directions. Suppose a fix makes rledger report a
`missing` row's error. The case then disagrees with the table, and the row has
to be updated to `covered`. A row cannot go stale this way.

## The tests

`crates/rustledger/tests/upstream_checks_test.rs`:

| Test | Needs | Checks |
|---|---|---|
| `upstream_checks_table_is_well_formed` | nothing | each row has what its status requires; the case files, named tests and compatibility links exist; no case is unused |
| `upstream_checks_rledger_matches_the_table` | `rledger` | rledger's side of every case |
| `upstream_checks_beancount_matches_the_table` | Python with beancount | beancount's side of every case |
| `upstream_checks_table_lists_every_upstream_check` | Python with beancount | the drift guard: `enumerate.py`'s list and the table's ids are the same set |

The two Python tests look for `python3`, or for the interpreter named by
`RLEDGER_UPSTREAM_PYTHON`. If beancount cannot be imported they print
`Skipping: Python beancount not available` and pass. The
`python-gated-cargo-tests` job in `.github/workflows/compat.yml` installs
beancount and fails on that marker, so in CI they always run.

The guard introspects the installed package instead of pinning a hash of the
scanned files. A hash would go red on any edit to those files, including a
docstring or a refactor, and would not say which check changed. Introspection
goes red only when a check is added, removed or reworded, and it names that
check.

## When the guard goes red

On a beancount upgrade, the failure lists the ids that beancount has and the
table lacks, and the ids the table has that beancount no longer has. For each
new id:

1. Read the check in beancount's source. Under what conditions can a ledger
   reach it?
1. Write a ledger in `cases/` that triggers it. Run it through `bean-check`
   and through `rledger check`.
1. Add the row with its status. If rledger does not report it and beancount's
   behavior is right, add the check to rledger (see "Adding a validation
   error" in `AGENTS.md`), then mark the row `covered`.

A reworded message shows up as one id removed and one added. Move the row to
the new id.

To run the tests locally, point them at a Python that has beancount:

```bash
RLEDGER_UPSTREAM_PYTHON=/path/to/python3 cargo test -p rustledger --test upstream_checks_test
```
