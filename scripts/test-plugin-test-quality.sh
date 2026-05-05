#!/usr/bin/env bash
# Self-test for check-plugin-test-quality.sh.
#
# The lint script's regexes are non-trivial; a typo or accidental
# deletion of a pattern would silently disable detection. This test
# generates synthetic test files in a temp dir, points the lint at
# them via `TESTS_DIR`, and asserts that each known-bad shape gets
# caught and each known-clean shape does not.
#
# Usage: scripts/test-plugin-test-quality.sh
# Exit code 0 if all cases pass, 1 if any case fails.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
LINT_SCRIPT="$REPO_ROOT/scripts/check-plugin-test-quality.sh"

if [ ! -x "$LINT_SCRIPT" ]; then
    echo "ERROR: lint script not found or not executable: $LINT_SCRIPT" >&2
    exit 1
fi

TMPDIR=$(mktemp -d -t plugin-lint-test.XXXXXX)
trap 'rm -rf "$TMPDIR"' EXIT

PASS=0
FAIL=0

# Run the lint with $TMPDIR as TESTS_DIR. Asserts:
#   - exit code matches $expected_exit (0 or 1)
#   - if $must_match is non-empty, the output contains it (substring)
run_case() {
    local name="$1"
    local expected_exit="$2"
    local content="$3"
    local must_match="${4:-}"

    printf '%s\n' "$content" > "$TMPDIR/synth_test.rs"

    local out rc=0
    out=$(TESTS_DIR="$TMPDIR" "$LINT_SCRIPT" 2>&1) || rc=$?

    if [ "$rc" != "$expected_exit" ]; then
        echo "FAIL  [$name]"
        echo "  expected exit $expected_exit, got $rc"
        echo "  --- script output ---"
        echo "$out" | sed 's/^/  /'
        echo "  ---"
        FAIL=$((FAIL + 1))
        return
    fi

    if [ -n "$must_match" ] && ! grep -qF "$must_match" <<< "$out"; then
        echo "FAIL  [$name]"
        echo "  output missing substring: '$must_match'"
        echo "  --- script output ---"
        echo "$out" | sed 's/^/  /'
        echo "  ---"
        FAIL=$((FAIL + 1))
        return
    fi

    PASS=$((PASS + 1))
    echo "PASS  [$name]"
}

echo "=== Self-testing plugin-test-quality lint ==="
echo ""

# ----------------------------------------------------------------------
# Shape A: assert!(... >= N) / >
# ----------------------------------------------------------------------

run_case "shape A: assert!(x.len() >= 1)" 1 \
    '#[test] fn t() { assert!(emitted.len() >= 1); }' \
    "synth_test.rs:1:"

run_case "shape A: assert!(x.count() > 0)" 1 \
    '#[test] fn t() { assert!(emitted.count() > 0); }'

run_case "shape A: precomputed price_count >= 1 (the actual #992 bug shape)" 1 \
    '#[test] fn t() { let price_count = 0; assert!(price_count >= 1); }'

run_case "shape A: bare 'count >= 1'" 1 \
    '#[test] fn t() { let count = 0; assert!(count >= 1); }'

# ----------------------------------------------------------------------
# Shape B: assert_ne!(..., 0)
# ----------------------------------------------------------------------

run_case "shape B: assert_ne!(x.len(), 0)" 1 \
    '#[test] fn t() { assert_ne!(emitted.len(), 0); }'

run_case "shape B: with msg" 1 \
    '#[test] fn t() { assert_ne!(emitted.len(), 0, "msg"); }'

# ----------------------------------------------------------------------
# Shape C: assert!(!x.is_empty())
# ----------------------------------------------------------------------

run_case "shape C: assert!(!x.is_empty())" 1 \
    '#[test] fn t() { assert!(!emitted.is_empty()); }'

run_case "shape C: with msg" 1 \
    '#[test] fn t() { assert!(!output.errors.is_empty(), "msg"); }'

# ----------------------------------------------------------------------
# Shape D: assert!(x.len() != 0)
# ----------------------------------------------------------------------

run_case "shape D: assert!(x.len() != 0)" 1 \
    '#[test] fn t() { assert!(emitted.len() != 0); }'

run_case "shape D: assert!(price_count != 0)" 1 \
    '#[test] fn t() { let price_count = 0; assert!(price_count != 0); }'

# ----------------------------------------------------------------------
# Multi-line forms (the line-anchored grep above misses these — the
# multi-line form is more common when the assert carries a message).
# ----------------------------------------------------------------------

run_case "multi-line shape C: assert!(\\\\n    !x.is_empty(),\\\\n    \"msg\"\\\\n)" 1 \
    '#[test] fn t() {
    assert!(
        !output.errors.is_empty(),
        "should warn"
    );
}'

run_case "multi-line shape B: assert_ne!(\\\\n    x.len(),\\\\n    0\\\\n)" 1 \
    '#[test] fn t() {
    assert_ne!(
        emitted.len(),
        0
    );
}'

run_case "multi-line shape D: assert!(\\\\n    x.len() != 0,\\\\n    \"msg\"\\\\n)" 1 \
    '#[test] fn t() {
    assert!(
        emitted.len() != 0,
        "msg"
    );
}'

# ----------------------------------------------------------------------
# Word-boundary guards: prop_assert! / debug_assert! must NOT match
# even though they contain the literal substring `assert!`.
# ----------------------------------------------------------------------

run_case "prop_assert!(!x.is_empty()) does NOT fire (property tests)" 0 \
    '#[test] fn t() {
    prop_assert!(
        !output.directives.is_empty(),
        "Plugin should produce valid output"
    );
}'

run_case "debug_assert!(!x.is_empty()) does NOT fire (invariant)" 0 \
    'fn invariant() {
    debug_assert!(
        !cache.is_empty(),
        "cache should be populated by init"
    );
}'

# Multi-line ML_PAT_B/D used to match ANY `, 0` / `!= 0` assertion;
# they're now scoped to count/len/size LHS the same as PAT_B/D
# (Copilot review on PR #1005). These guards confirm non-count
# zero-comparisons do NOT fire the lint.
run_case "ML_PAT_B guard: assert_ne!(balance, 0) (non-count) does NOT fire" 0 \
    '#[test] fn t() {
    assert_ne!(
        balance,
        0
    );
}'

run_case "ML_PAT_D guard: assert!(balance != 0) (non-count) does NOT fire" 0 \
    '#[test] fn t() {
    assert!(
        balance != 0,
        "should be non-zero"
    );
}'

# ----------------------------------------------------------------------
# Allow annotation
# ----------------------------------------------------------------------

run_case "allow annotation with reason suppresses violation" 0 \
    '#[test] fn t() {
    // allow weak-count: stable shape
    assert!(plugins.len() >= 13);
}'

run_case "EMPTY allow reason still fires lint (item 2 from review)" 1 \
    '#[test] fn t() {
    // allow weak-count:
    assert!(plugins.len() >= 13);
}'

run_case "whitespace-only allow reason still fires" 1 \
    '#[test] fn t() {
    // allow weak-count:
    assert!(plugins.len() >= 13);
}'

# ----------------------------------------------------------------------
# Clean shapes (must NOT fire)
# ----------------------------------------------------------------------

run_case "clean: assert_eq!(x.len(), 1)" 0 \
    '#[test] fn t() { assert_eq!(emitted.len(), 1); }'

run_case "clean: assert_eq!(x.len(), 0)" 0 \
    '#[test] fn t() { assert_eq!(emitted.len(), 0); }'

run_case "clean: assert!(x.len() == 1) (positive equality)" 0 \
    '#[test] fn t() { assert!(emitted.len() == 1); }'

run_case "clean: no asserts at all" 0 \
    'fn t() { let x = vec![1, 2, 3]; let _ = x.len(); }'

# ----------------------------------------------------------------------
# Partial-port shape
# ----------------------------------------------------------------------

run_case "partial: 'Converted from x_test.py (partial)'" 1 \
    '// Converted from foo_test.py (partial)
#[test] fn t() {}' \
    "Converted from foo_test.py (partial)"

run_case "partial: false positive — '(partial overlap with foo)' should NOT fire" 0 \
    '// Edge case (partial overlap with foo): handle gracefully
#[test] fn t() {}'

run_case "partial: allow annotation with reason suppresses" 0 \
    '// allow partial: documentation reference, not a port
// Converted from foo_test.py (partial)
#[test] fn t() {}'

# ----------------------------------------------------------------------
# Missing-dir hard-fail (regression: pre-fix this silently passed)
# ----------------------------------------------------------------------

if TESTS_DIR=/nonexistent/dir-that-does-not-exist "$LINT_SCRIPT" >/dev/null 2>&1; then
    echo "FAIL  [missing TESTS_DIR should hard-fail]"
    echo "  script returned 0 for nonexistent dir — this is the bug from"
    echo "  feedback_no_error_swallowing.md. Should exit non-zero."
    FAIL=$((FAIL + 1))
else
    PASS=$((PASS + 1))
    echo "PASS  [missing TESTS_DIR hard-fails]"
fi

# ----------------------------------------------------------------------

echo ""
echo "=== $PASS passed, $FAIL failed ==="

if [ "$FAIL" -gt 0 ]; then
    exit 1
fi
