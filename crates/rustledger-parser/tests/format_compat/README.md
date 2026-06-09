# Format-compat suite (phase 4.2, #1262)

Each subdirectory of `cases/` is one regression fixture pinning the
formatter's promise on a historical destructive-formatting bug class.

## Layout

```
cases/
  <case_name>/
    input.bean        # what the user typed (or an editor stored)
    expected.bean     # the byte-exact output format_source MUST emit
```

## Adding a fixture

1. Create a new subdirectory under `cases/`. Name it after the bug
   class (e.g. `posting_trailing_comment`, `issue_NNNN_repro`).
2. Drop the input source as `input.bean`.
3. Drop the canonical-form output as `expected.bean`.
4. Run `cargo test -p rustledger-parser --test format_compat` — the
   harness validates input/expected, idempotence, and parseability.

The harness asserts a floor on the fixture count
(`MIN_FIXTURES` in `tests/format_compat.rs`). Bump it when you add
cases; lowering it requires a justification in the PR description.

## What belongs here vs `IDEMPOTENCE_MATRIX`

- `cst::format::tests::IDEMPOTENCE_MATRIX` — inline string fixtures
  that pin per-rule canonical-form behavior, exercised by
  property-style tests (idempotence, lexer agreement, round-trip
  via `canonicalize_directives`). Hand-edit those in code review.

- `tests/format_compat/cases/` — reviewable file pairs for
  historical bug reproducers and the user-facing contract surface.
  Browse the directory to see what the formatter promises.

Both layers are load-bearing; the file-pair layer is the one users
read when they want to understand "what will rledger format do to
my file."
