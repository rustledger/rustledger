______________________________________________________________________

on:
schedule: weekly on friday
workflow_dispatch:

permissions:
contents: read
issues: read
pull-requests: read
discussions: write

safe-outputs:
create-discussion:
max: 1

______________________________________________________________________

# Weekly Project Report

Generate a comprehensive weekly report for the rustledger project and post it to Discussions.

## Context

rustledger is a Rust implementation of Beancount (double-entry bookkeeping) with:

- 16 crates in a cargo workspace
- CLI tool (`rledger`) with multiple commands
- WASM library target
- 694 compatibility tests against Python beancount (99.86% pass rate)
- 20 built-in native plugins
- BQL query engine

Key repositories and branches:

- `main` - Primary development branch
- `compatibility` - Compatibility test results
- `benchmarks` - Performance benchmark data

## Instructions

Generate a single comprehensive weekly report covering ALL of the following sections. This is a READ-ONLY analysis - do not create PRs or make code changes.

### 1. Project Activity

- Count commits to main branch this week
- List merged pull requests with brief descriptions
- Count new/closed issues
- Note any blocked PRs or stale issues
- Identify active contributors

### 2. Compatibility Test Status

- Check the `compatibility` branch for test results
- Report current pass rate (target: 99.86% or higher)
- List any new failures since last week
- Categorize failures: parsing, validation, booking, or known limitations
- Note the decimal precision limitation (documented in CLAUDE.md)

### 3. Performance Status

- Check the `benchmarks` branch for recent data
- Compare against baselines:
  - Parse time for 10k transactions: < 100ms
  - Validation time: < 50ms
  - Query execution: < 10ms
- Flag any regressions from recent commits
- Note any performance improvements

### 4. CI Health

- Check recent CI runs for failures
- Report test pass rates across platforms
- Note any flaky tests
- Check dependency update status (Dependabot PRs)
- Security advisory status (cargo deny)

### 5. Documentation Status

- Check if README.md stats are current (crate count, plugin count, etc.)
- Note any public API changes that might need doc updates
- Flag any outdated examples in documentation

### 6. Plugin Status

- Check for any plugin-related issues or PRs
- Note any compatibility concerns with Python beancount plugins
- Report on native plugin test coverage

### 7. Suggested Focus Areas

Based on the analysis, suggest 2-3 priority items for the coming week.

## Output Format

Create a GitHub Discussion in the "Announcements" category.

Title: `Weekly Report: {start_date} - {end_date}`

Use this structure:

```markdown
## Summary

[2-3 sentence high-level overview]

## Project Activity

| Metric | This Week | Trend |
|--------|-----------|-------|
| Commits | X | ... |
| PRs Merged | X | ... |
| Issues Opened | X | ... |
| Issues Closed | X | ... |

### Merged PRs
- PR #X: description
- PR #Y: description

### Notable Issues
- Issue #X: description

## Compatibility Tests

**Pass Rate:** X% (X/Y tests)

[Any new failures or improvements]

## Performance

**Status:** [Green/Yellow/Red]

[Any regressions or improvements noted]

## CI Health

**Status:** [Green/Yellow/Red]

[Any failing checks or flaky tests]

## Documentation & Plugins

[Brief notes on any needed updates]

## Focus Areas for Next Week

1. [Priority item 1]
2. [Priority item 2]
3. [Priority item 3]
```

Use tables and bullet points for clarity. Keep the report concise but comprehensive.
