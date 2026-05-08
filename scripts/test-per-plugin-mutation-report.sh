#!/usr/bin/env bash
# Self-test for per-plugin-mutation-report.sh.
#
# The script's per-plugin parsing and floor enforcement are easy to
# break with a typo (sed regex, awk arithmetic, sort key). This test
# constructs synthetic `mutants.out` directories and asserts the
# script's exit code and key output substrings for each scenario.
#
# Usage: scripts/test-per-plugin-mutation-report.sh
# Exit code 0 if all cases pass, 1 if any case fails.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SCRIPT="$REPO_ROOT/scripts/per-plugin-mutation-report.sh"

if [ ! -x "$SCRIPT" ]; then
    echo "ERROR: script not found or not executable: $SCRIPT" >&2
    exit 1
fi

TMPDIR=$(mktemp -d -t mutation-report-test.XXXXXX)
trap 'rm -rf "$TMPDIR"' EXIT

PASS=0
FAIL=0

# Build a synthetic mutants.out under $TMPDIR/$1, populating each .txt
# file from the heredoc-style content passed via the named env vars.
# Args: $1 = subdir name; uses $CAUGHT, $MISSED, $TIMEOUT, $UNVIABLE.
make_fixture() {
    local sub="$1"
    local dir="$TMPDIR/$sub/mutants.out"
    mkdir -p "$dir"
    printf '%s' "${CAUGHT:-}" > "$dir/caught.txt"
    printf '%s' "${MISSED:-}" > "$dir/missed.txt"
    printf '%s' "${TIMEOUT:-}" > "$dir/timeout.txt"
    printf '%s' "${UNVIABLE:-}" > "$dir/unviable.txt"
    echo "$dir"
}

# Run the script with MUTANTS_DIR pointed at the fixture.
# Asserts exit code matches $2 and output contains $3 (if set).
# Optional env: $FLOOR sets MUTATION_FLOOR; $ANNOTATIONS sets GITHUB_ANNOTATIONS.
run_case() {
    local name="$1"
    local expected_exit="$2"
    local must_match="${3:-}"
    local fixture="$4"

    local out rc=0
    out=$(
        MUTANTS_DIR="$fixture" \
        MUTATION_FLOOR="${FLOOR:-10}" \
        GITHUB_ANNOTATIONS="${ANNOTATIONS:-0}" \
        "$SCRIPT" 2>&1
    ) || rc=$?

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

    echo "PASS  [$name]"
    PASS=$((PASS + 1))
}

# ----------------------------------------------------------------------
# Case 1: empty mutants.out → "no mutants" status, exit 0
# ----------------------------------------------------------------------
unset CAUGHT MISSED TIMEOUT UNVIABLE
fixture=$(make_fixture case1)
run_case "empty-mutants-out" 0 "All plugins pass" "$fixture"

# ----------------------------------------------------------------------
# Case 2: all caught for one plugin → exit 0
# ----------------------------------------------------------------------
CAUGHT='crates/rustledger-plugin/src/native/plugins/foo.rs:1:1: replace x -> u32 with 0
crates/rustledger-plugin/src/native/plugins/foo.rs:2:1: replace y -> u32 with 0
crates/rustledger-plugin/src/native/plugins/foo.rs:3:1: replace z -> u32 with 0'
MISSED='' TIMEOUT='' UNVIABLE=''
fixture=$(make_fixture case2)
run_case "all-caught-passes" 0 "All plugins pass" "$fixture"

# ----------------------------------------------------------------------
# Case 3: one plugin >10% → exit 1
# Plugin foo: 5 caught, 1 missed → 16.7% (over 10% floor)
# ----------------------------------------------------------------------
CAUGHT='crates/rustledger-plugin/src/native/plugins/foo.rs:1:1: a
crates/rustledger-plugin/src/native/plugins/foo.rs:2:1: b
crates/rustledger-plugin/src/native/plugins/foo.rs:3:1: c
crates/rustledger-plugin/src/native/plugins/foo.rs:4:1: d
crates/rustledger-plugin/src/native/plugins/foo.rs:5:1: e'
MISSED='crates/rustledger-plugin/src/native/plugins/foo.rs:6:1: f'
TIMEOUT='' UNVIABLE=''
fixture=$(make_fixture case3)
run_case "plugin-over-floor-fails" 1 "exceeds 10% floor" "$fixture"

# ----------------------------------------------------------------------
# Case 4: only _infrastructure exceeds floor → exit 0 (not enforced)
# ----------------------------------------------------------------------
CAUGHT=''
MISSED='crates/rustledger-plugin/src/native/registry.rs:1:1: a
crates/rustledger-plugin/src/native/registry.rs:2:1: b
crates/rustledger-plugin/src/native/registry.rs:3:1: c'
TIMEOUT='' UNVIABLE=''
fixture=$(make_fixture case4)
run_case "infrastructure-not-enforced" 0 "(not enforced)" "$fixture"

# ----------------------------------------------------------------------
# Case 5: MUTATION_FLOOR=0 disables enforcement (report-only)
# ----------------------------------------------------------------------
CAUGHT=''
MISSED='crates/rustledger-plugin/src/native/plugins/foo.rs:1:1: a
crates/rustledger-plugin/src/native/plugins/foo.rs:2:1: b'
TIMEOUT='' UNVIABLE=''
fixture=$(make_fixture case5)
FLOOR=0 run_case "floor-zero-report-only" 0 "report-only mode" "$fixture"
unset FLOOR

# ----------------------------------------------------------------------
# Case 6: missing mutants.out → exit 2 (configuration error)
# ----------------------------------------------------------------------
nonexistent="$TMPDIR/case6_no_dir/mutants.out"
out=$(MUTANTS_DIR="$nonexistent" "$SCRIPT" 2>&1) || rc=$?
if [ "${rc:-0}" = 2 ] && grep -qF "not found" <<< "$out"; then
    echo "PASS  [missing-mutants-dir-exit-2]"
    PASS=$((PASS + 1))
else
    echo "FAIL  [missing-mutants-dir-exit-2] expected exit 2, got ${rc:-0}"
    FAIL=$((FAIL + 1))
fi
unset rc

# ----------------------------------------------------------------------
# Case 7: GITHUB_ANNOTATIONS=1 emits ::warning:: lines for missed mutants
# ----------------------------------------------------------------------
CAUGHT='crates/rustledger-plugin/src/native/plugins/foo.rs:1:1: a
crates/rustledger-plugin/src/native/plugins/foo.rs:2:1: b
crates/rustledger-plugin/src/native/plugins/foo.rs:3:1: c
crates/rustledger-plugin/src/native/plugins/foo.rs:4:1: d
crates/rustledger-plugin/src/native/plugins/foo.rs:5:1: e
crates/rustledger-plugin/src/native/plugins/foo.rs:6:1: f
crates/rustledger-plugin/src/native/plugins/foo.rs:7:1: g
crates/rustledger-plugin/src/native/plugins/foo.rs:8:1: h
crates/rustledger-plugin/src/native/plugins/foo.rs:9:1: i
crates/rustledger-plugin/src/native/plugins/foo.rs:10:1: j'
MISSED='crates/rustledger-plugin/src/native/plugins/foo.rs:99:5: replace bar -> bool with true'
TIMEOUT='' UNVIABLE=''
fixture=$(make_fixture case7)
ANNOTATIONS=1 run_case "github-annotations-emitted" 0 "::warning file=" "$fixture"
unset ANNOTATIONS

# ----------------------------------------------------------------------
# Case 8: utils.rs / mod.rs are bucketed as _infrastructure, not as a
# plugin. A surviving mutant in utils.rs must NOT count against any
# real plugin's survival rate.
# ----------------------------------------------------------------------
CAUGHT='crates/rustledger-plugin/src/native/plugins/foo.rs:1:1: a
crates/rustledger-plugin/src/native/plugins/foo.rs:2:1: b
crates/rustledger-plugin/src/native/plugins/foo.rs:3:1: c
crates/rustledger-plugin/src/native/plugins/foo.rs:4:1: d
crates/rustledger-plugin/src/native/plugins/foo.rs:5:1: e
crates/rustledger-plugin/src/native/plugins/foo.rs:6:1: f
crates/rustledger-plugin/src/native/plugins/foo.rs:7:1: g
crates/rustledger-plugin/src/native/plugins/foo.rs:8:1: h
crates/rustledger-plugin/src/native/plugins/foo.rs:9:1: i
crates/rustledger-plugin/src/native/plugins/foo.rs:10:1: j'
MISSED='crates/rustledger-plugin/src/native/plugins/utils.rs:5:1: a
crates/rustledger-plugin/src/native/plugins/mod.rs:5:1: b'
TIMEOUT='' UNVIABLE=''
fixture=$(make_fixture case8)
run_case "utils-and-mod-are-infrastructure" 0 "(not enforced)" "$fixture"

# ----------------------------------------------------------------------
# Case 9: edge case — exactly at the floor (10%) is OK; over (10.001%)
# is not. Use 9 caught + 1 missed = 10% (passes) and 9 caught + 2 missed
# + 1 timeout = 16.7% (fails).
# ----------------------------------------------------------------------
CAUGHT='crates/rustledger-plugin/src/native/plugins/foo.rs:1:1: a
crates/rustledger-plugin/src/native/plugins/foo.rs:2:1: b
crates/rustledger-plugin/src/native/plugins/foo.rs:3:1: c
crates/rustledger-plugin/src/native/plugins/foo.rs:4:1: d
crates/rustledger-plugin/src/native/plugins/foo.rs:5:1: e
crates/rustledger-plugin/src/native/plugins/foo.rs:6:1: f
crates/rustledger-plugin/src/native/plugins/foo.rs:7:1: g
crates/rustledger-plugin/src/native/plugins/foo.rs:8:1: h
crates/rustledger-plugin/src/native/plugins/foo.rs:9:1: i'
MISSED='crates/rustledger-plugin/src/native/plugins/foo.rs:10:1: j'
TIMEOUT='' UNVIABLE=''
fixture=$(make_fixture case9a)
run_case "exactly-10-percent-passes" 0 "All plugins pass" "$fixture"

# ----------------------------------------------------------------------
# Case 10: regression test for the truncation bug. 11 missed out of
# 101 total = 10.89%, which is strictly greater than the 10% floor and
# MUST fail. A naïve `m * 100 / total` integer division would compute
# 10 and incorrectly pass — this case pins the cross-multiplication
# fix from PR #1041 review (Copilot inline comment).
# ----------------------------------------------------------------------
CAUGHT_LINES=""
for i in $(seq 1 90); do
    CAUGHT_LINES="${CAUGHT_LINES}crates/rustledger-plugin/src/native/plugins/foo.rs:$i:1: a${i}"$'\n'
done
MISSED_LINES=""
for i in $(seq 91 101); do
    MISSED_LINES="${MISSED_LINES}crates/rustledger-plugin/src/native/plugins/foo.rs:$i:1: m${i}"$'\n'
done
CAUGHT="${CAUGHT_LINES%$'\n'}"
MISSED="${MISSED_LINES%$'\n'}"
TIMEOUT='' UNVIABLE=''
fixture=$(make_fixture case10)
run_case "just-over-10-percent-fails" 1 "exceeds 10% floor" "$fixture"

# ----------------------------------------------------------------------

echo ""
echo "Summary: $PASS passed, $FAIL failed"
if [ "$FAIL" -gt 0 ]; then
    exit 1
fi
