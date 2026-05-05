#!/usr/bin/env bash
# Lint plugin tests against the policies in CONTRIBUTING.md ("Plugin
# testing requirements"). Runs in CI and as a pre-push step.
#
# Phase 5 of the plugin-testing-quality plan documented in issue #992.
#
# Catches:
#   1. Weak count assertions like `assert!(... >= N)` on emission counts.
#      The original #992 bug shipped because the test had `assert!(count >= 1)`,
#      which accepted both correct and over-emission. Catches both spaced
#      (`x >= 1`) and unspaced (`x>=1`) variants. To opt out (e.g. on
#      registry-shape tests where the count grows with each plugin
#      addition), prefix the assert with `// allow weak-count: <reason>`
#      within 5 lines of leading context.
#   2. `(partial)` test ports — incomplete upstream test conversions.
#      A full port catches more bugs than a partial one; partials had
#      historically been used as a shortcut and the comment was the only
#      evidence of incomplete coverage.
#
# Usage: scripts/check-plugin-test-quality.sh
# Exit code 0 if clean, 1 if any policy violation found.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TESTS_DIR="$REPO_ROOT/crates/rustledger-plugin/tests"

EXIT=0

echo "=== Checking plugin-test-quality policies ==="
echo ""

# ----------------------------------------------------------------------
# Policy 1: no weak count assertions on emission counts
# ----------------------------------------------------------------------

echo "[1/2] weak count assertions ('assert!(... >= N)' / '> N')"

# Match: assert!(<anything>.{count|len}()<anything>(>= or >)<digit>)
# The pattern is intentionally narrow — `assert!(plugins.len() >= 13)`
# in registry-shape tests is fine (it tests a registration property,
# not emission). We exclude:
#   - registry tests (filenames or comments mentioning "registry")
#   - explicit allow comments: "// allow weak-count: <reason>"

# Match three weak-assertion shapes:
#   1. `assert!(x.count() >= N)` / `assert!(x.len() > N)` (with optional whitespace)
#   2. `assert!(x.count()>=N)` / `assert!(x.len()>N)` (no whitespace)
#   3. `assert!(price_count >= N)` — precomputed count var (any ident ending
#      in `_count`, `_len`, `_size`, or named exactly `count`/`len`/`size`).
# The original #992 bug used pattern 3 (`assert!(price_count >= 1)`).
WEAK_PATTERN='assert!\([^)]*((\.(count|len|size)\(\))|\b(count|len|size|[a-z_]+_(count|len|size)))[^)]*[[:space:]]*(>|>=)[[:space:]]*[0-9]+'

# Find every line matching the pattern with file:line prefixes.
# Then for each match, check the 5 preceding lines for the
# `// allow weak-count` opt-out annotation. Pre-fix used `grep -B 5`
# + an awk block parser that lost violations when multiple matches
# were close together within the same 5-line context window.
matches=$(grep -rEn "$WEAK_PATTERN" "$TESTS_DIR" 2>/dev/null || true)

bad=""
while IFS= read -r match; do
    [ -z "$match" ] && continue
    # match looks like: path/to/file.rs:LINENO:assert!(...)
    file_part="${match%%:*}"
    rest="${match#*:}"
    lineno="${rest%%:*}"
    # Look back 5 lines for the opt-out annotation.
    start=$(( lineno > 5 ? lineno - 5 : 1 ))
    if ! sed -n "${start},${lineno}p" "$file_part" | grep -q "allow weak-count"; then
        bad="${bad}${match}"$'\n'
    fi
done <<< "$matches"
bad="${bad%$'\n'}"  # trim trailing newline

if [ -n "$bad" ]; then
    echo "  ERROR: weak count assertions found (no 'allow weak-count' annotation)"
    echo ""
    echo "$bad"
    echo ""
    echo "  Replace with strict assert_eq!(...) or add explicit allow:"
    echo "    // allow weak-count: <reason>"
    echo "    assert!(emitted.len() >= 1, \"...\")"
    echo ""
    EXIT=1
else
    echo "  OK"
fi
echo ""

# ----------------------------------------------------------------------
# Policy 2: no `(partial)` test ports
# ----------------------------------------------------------------------

echo "[2/2] '(partial)' test port labels"

# `(partial)` in a test comment means an upstream test was only partly
# converted to Rust. CONTRIBUTING.md requires either full ports or
# explicit per-case skip annotations.

partial_matches=$(grep -rn "(partial)" "$TESTS_DIR" 2>/dev/null || true)

if [ -n "$partial_matches" ]; then
    echo "  ERROR: '(partial)' test port labels found"
    echo ""
    echo "$partial_matches"
    echo ""
    echo "  Either:"
    echo "  - Port the remaining upstream test cases, OR"
    echo "  - Document each skipped case explicitly with rationale"
    echo ""
    EXIT=1
else
    echo "  OK"
fi
echo ""

# ----------------------------------------------------------------------

if [ "$EXIT" -eq 0 ]; then
    echo "=== All plugin-test-quality policies pass ==="
else
    echo "=== Plugin-test-quality FAILED ==="
    echo ""
    echo "See CONTRIBUTING.md → 'Plugin testing requirements' for the policy."
    echo "See issue #992 for the bug class these policies prevent."
fi

exit "$EXIT"
