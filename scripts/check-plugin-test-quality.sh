#!/usr/bin/env bash
# Lint plugin tests against the policies in CONTRIBUTING.md ("Plugin
# testing requirements"). Runs in CI and as a pre-push step.
#
# Phase 5 of the plugin-testing-quality plan documented in issue #992.
#
# Catches:
#   1. Weak count assertions like `assert!(... >= N)` on emission counts.
#      The original #992 bug shipped because the test had `assert!(count >= 1)`,
#      which accepted both correct and over-emission.
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

WEAK_PATTERN='assert!\([^)]*(\.count|\.len)\(\)[^)]*( >=| >) [0-9]+'
# `-B 5` includes up to 5 lines above each match, so we can find
# `// allow weak-count` annotations in the leading comment block.
raw=$(grep -rEnB 5 "$WEAK_PATTERN" "$TESTS_DIR" 2>/dev/null || true)

# awk script: split on `--`, check each block for "allow weak-count",
# emit only the assert line from blocks that DON'T have the annotation.
bad=$(echo "$raw" | awk '
BEGIN { allowed = 0; assert_line = "" }
/^--$/ {
    if (!allowed && assert_line != "") print assert_line
    allowed = 0; assert_line = ""
    next
}
/allow weak-count/ { allowed = 1 }
/assert!\(.*\.(count|len)\(\).*( >=| >) [0-9]+/ { assert_line = $0 }
END {
    if (!allowed && assert_line != "") print assert_line
}
')

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
