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
4. Run `cargo test -p rustledger-parser --test format_compat` - the
   harness validates input/expected, idempotence, and parseability.

**Adding a fixture is free** - the harness does NOT enforce a count
floor on the number of fixtures. The coverage gate is a
[`REQUIRED_FIXTURES`](../format_compat.rs) name-set in the harness
that lists the bug-class fixtures CI requires to exist. New cases
beyond that set are encouraged and do not need any constant bumped.

Promoting a new fixture into the required set (because it pins a
bug class CI must always cover) means adding its name to
`REQUIRED_FIXTURES`. Removing a name from that set is the explicit,
reviewable signal that a regression class is being retired.

## What belongs here vs `IDEMPOTENCE_MATRIX`

The inline `IDEMPOTENCE_MATRIX` in `cst::format::tests` and the
file-pair fixtures here cover overlapping ground; they are not
strictly disjoint. The split is by audience:

- `IDEMPOTENCE_MATRIX` - inline string fixtures exercised by
  property-style tests (idempotence, lexer agreement, round-trip
  through `canonicalize_directives`). Hand-edited in code review,
  optimized for compactness.

- `cases/` - file-pair golden fixtures readable side by side
  without running the test runner. The intended audience is
  **external users** asking "what will `rledger format` do to my
  file?" Browse the directory to see what the formatter promises
  on each historical bug class.

Roughly half of the file-pair fixtures (`balance_leading_unary_minus_preserves_sign`,
`cost_spec_with_negative_amount`, `metadata_arithmetic_value`, etc.)
are reviewable mirrors of an `IDEMPOTENCE_MATRIX` entry. The other
half (`issue_1252_destructive_repro`, `bom_dropped`,
`missing_final_newline_added`, `multiple_trailing_blank_lines_collapsed`,
`pushtag_poptag_pair_preserved`, `pushmeta_popmeta_pair_preserved`,
`section_header_comments_tight`, `commas_stripped_per_canonical_form`,
`unary_plus_stripped_per_canonical_form`,
`posting_with_interleaved_metadata`, etc.) are genuinely-new
coverage shapes that don't fit the inline-string format
ergonomically - multi-directive reproducers, BOM and CRLF cases,
canonical-form choices that are still being negotiated in the
issue thread.

Both layers are kept; the file-pair layer is the one external
users read.
