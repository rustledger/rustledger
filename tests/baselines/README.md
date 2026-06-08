# Output baselines

This directory holds the parser-output baseline for the compatibility
corpus under `tests/compatibility/files/`. It implements phase 0 of
the parser-CST migration tracking issue
([#1262](https://github.com/rustledger/rustledger/issues/1262)).

The formatter-output baseline that lived here through phases 0-3 was
retired when phase 4.1 landed the opinionated CST-backed formatter
(#1284). That formatter has its own canonical-form unit tests in
`rustledger-parser::cst::format::tests` instead of a corpus gate, since
the canonical form is a closed property over each AST shape rather
than a byte-fingerprint of arbitrary input files.

## Contract

One file, rebuilt from the corpus on every CI run. Each line is:

```text
relative/path<TAB>source_blake3<TAB>output_blake3
```

The TWO hashes per line let the gate distinguish "the compatibility
corpus drifted upstream" from "the parser changed":

- Source hash matches AND output hash matches: no change.
- Source hash matches AND output hash differs: real drift, fails CI.
- Source hash differs: upstream-corpus change for this file. The
  output hash is NOT compared (different input, different output is
  expected). Test logs report this as an `info:` line; regenerate
  the manifest when convenient. Strict mode does NOT treat this as
  failure because corpus content drift is outside the PR author's
  control.

Manifest:

- `parser-corpus.manifest` — output hash covers a canonical
  serialization of the full `ParseResult` (directives via
  `serde_json::to_value` so metadata maps sort deterministically,
  plus `Debug` of `options`, `includes`, `plugins`, `comments`,
  `errors`, `warnings`, `currency_occurrences`, and the
  `has_leading_bom` flag). The runtime test
  `fingerprint_covers_every_parse_result_field` plus a compile-time
  exhaustive-destructure sentinel in `rustledger-parser` keep the
  field list and the hash in sync as `ParseResult` evolves.

The manifest is sorted lexically by path so diffs are localized.

## CI behavior

The `Parser Baselines` workflow (`.github/workflows/parser-baselines.yml`)
runs on every PR and push to main. It:

1. Restores or fetches the compat corpus.
2. Runs the baseline tests with `STRICT_BASELINE=1`.
3. Fails if any committed manifest entry has a different current hash,
   or if the corpus is smaller than the manifest expects.

Strict mode is what makes the gate a gate. In default mode (no env
var), the test passes when no entries overlap; local devs without
the corpus see the test skip, not fail.

## Regenerating the manifest

When a parser change shifts output bytes intentionally:

```bash
# Download corpus if needed (one-time, ~3 minutes).
./scripts/fetch-compat-test-files.sh

# Regenerate the manifest.
./scripts/regen-corpus-baselines.sh

# Review the diff. Every changed hash must trace back to a code
# change in the PR. If you can't explain a change, find out why
# before committing.
git diff tests/baselines/

# Commit when satisfied.
git add tests/baselines/
git commit -m 'chore(baselines): regenerate parser manifest'
```

The regen script gates on a populated corpus and runs the parser test
with `BASELINE_UPDATE=1`.

## Phase-3-of-#1262 staleness

When `rustledger-cst::parse` becomes the production parser (phase 3.2
of #1262), this gate still runs against the OLD `rustledger-parser`
until phase 5.1. Between those phases the gate measures a parser
users no longer invoke. A phase-3.5+ PR should add a parallel CST
baseline alongside this one, or this gate should be removed when
phase 5.1 lands. The current manifest scheme (path + source_hash +
output_hash) lets a parallel CST baseline reuse the corpus and
source hashes cheaply.

## Why this exists

The parser-CST migration in #1262 stands up a parallel parser and
gates equivalence via a differential test. Before that work starts,
we need a contract for "the current parser's output is what it is."
Without this baseline, an unrelated PR could silently shift parser
output between the start of phase 1 and the differential test in
phase 2, and we'd discover the regression at the worst possible
moment — when the new parser disagreed with the old.

The baseline is independently valuable: it makes drift detection
explicit on every PR, not just when something downstream fails. We
keep it after #1262 closes.

## Local workflow

Run the baseline test as part of your normal cycle when you change
parsing:

```bash
# Default mode: tolerates empty corpus, skips silently. CI uses
# STRICT_BASELINE=1.
cargo test -p rustledger-parser --test corpus_baseline

# Strict mode locally (must have corpus populated):
STRICT_BASELINE=1 cargo test -p rustledger-parser --test corpus_baseline
```

If a failure surprises you, **don't regenerate yet**. Look at the
diff first, find the code change that caused it, and decide whether
the new output is correct.
