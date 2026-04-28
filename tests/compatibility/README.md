# Beancount Compatibility Tests

This directory contains test infrastructure for verifying compatibility between rustledger and Python beancount.

## Directory Structure

```
tests/compatibility/
├── README.md           # This file
├── sources.toml        # Documentation of file sources and licenses
└── files/              # Downloaded test files (~800, gitignored)
    ├── beancount-v2/   # Files from beancount v2
    ├── beancount-v3/   # Files from beancount v3
    ├── fava/           # Files from fava
    ├── ledger2beancount/
    └── ...             # Other sources
```

## Setup

Test files are **not committed** to the repository. Download them before running tests:

```bash
# Inside nix develop
./scripts/fetch-compat-test-files.sh
```

This downloads ~800 beancount files from 10+ open source repositories.

## Running Tests

### Check Compatibility (bean-check vs rledger check)

```bash
./scripts/compat-test.sh
```

### BQL Query Compatibility (bean-query vs rledger query)

```bash
python3 scripts/compat-bql-test.py
```

The harness loads a query corpus from `bql-queries.toml`, runs each
query against both bean-query and rledger on every test file that
both tools could parse, and diffs the results row-by-row.

The corpus is biased toward columns and functions where the two tools
have historically diverged in *semantics* — not just syntax — because
those are the bugs that ship undetected through parse-only checks.
See issue #929 for the motivating example: a `balance` column
semantic mismatch that went unnoticed for two releases while CI
reported 100% BQL match because the corpus was three queries that
didn't touch `balance`.

When adding a new column or aggregation function to the query engine,
add a query to `bql-queries.toml` that exercises it. Real-world
bean-query patterns are preferred over synthetic ones.

**Diagnostics** the harness emits beyond pass/fail:

- **Per-query coverage rate** — what % of files the query produced
  non-empty results on. A query returning 0 rows on >50% of files
  isn't really being tested by the corpus and gets flagged as weak;
  add data that exercises it or reformulate the query.
- **Multi-row mismatch detail** — on a divergence, prints up to 3
  differing rows (not just the first), so you can tell a single-row
  issue from a wholesale wrong-answer bug.
- **Order-aware comparison** — queries with `ORDER BY` (or `preserve_order = true`)
  compare row sequences; everything else compares as a sorted set.
- **Corpus-size floor** — script aborts if the corpus shrinks below
  `MIN_CORPUS_SIZE`, preventing accidental regressions in coverage.

### AST Comparison

```bash
python3 ./scripts/compat-ast-test.py
```

## Test Sources

Files are fetched from:

| Source | Description |
|--------|-------------|
| beancount v2/v3 | Official beancount examples and test data |
| fava | Web UI test files |
| beangulp | Importer framework tests |
| ledger2beancount | Conversion tool test cases |
| beancount-import | Import web UI test data |
| smart_importer | ML importer tests |
| Community repos | Various community examples |

See `sources.toml` for detailed source information and licenses.

## CI Integration

CI workflows automatically fetch test files before running compatibility tests.
Files are cached to avoid re-downloading on every run.

## Results

Test results are written to `tests/compatibility-results/` (also gitignored):

- `results_*.jsonl` - Check compatibility results
- `bql_results_*.jsonl` - BQL query results
- `summary_*.md` - Human-readable summary
