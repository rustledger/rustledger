#!/usr/bin/env bash
# Lint plugin tests against the policies in CONTRIBUTING.md ("Plugin
# testing requirements"). Runs in CI and as a pre-push hook.
#
# Phase 5 of the plugin-testing-quality plan documented in issue #992.
#
# Catches:
#   1. Weak count assertions on emission counts. Three semantically-
#      identical shapes — all accept "1 emission OR 100", which is the
#      failure mode that hid #992:
#         assert!(emitted.len() >= 1)         / assert!(price_count >= 1)
#         assert_ne!(emitted.len(), 0)
#         assert!(!emitted.is_empty())
#      To opt out (e.g. on registry-shape tests where the count grows
#      with each plugin addition), prefix the assertion with
#      `// allow weak-count: <reason>` within 5 lines of leading
#      context.
#   2. `(partial)` test ports — incomplete upstream test conversions.
#      Matches the literal `Converted from ... (partial)` shape that
#      historically marked a half-done port; opt-out is
#      `// allow partial: <reason>`.
#
# Usage: scripts/check-plugin-test-quality.sh
# Exit code 0 if clean, 1 if any policy violation found.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
# Override-able for the script's self-test (see test-plugin-test-quality.sh).
# Defaults to the real plugin tests dir for normal CI/pre-push use.
TESTS_DIR="${TESTS_DIR:-$REPO_ROOT/crates/rustledger-plugin/tests}"

# Hard-fail if the tests directory disappeared (path moved, broken
# worktree, etc.). Pre-fix this script silenced grep stderr with
# `2>/dev/null` and used `|| true` to swallow non-zero exits, which
# meant a missing TESTS_DIR would make the lint silently pass with
# "All policies pass". Two npm releases shipped that way in the past
# (per project memory `feedback_no_error_swallowing.md`); we
# explicitly differentiate "no matches" (grep exit 1) from "real
# error" (grep exit 2+) below.
if [ ! -d "$TESTS_DIR" ]; then
    echo "ERROR: tests directory not found at $TESTS_DIR" >&2
    exit 1
fi

EXIT=0

echo "=== Checking plugin-test-quality policies ==="
echo ""

# Run grep, tolerating "no matches" (exit 1) but failing loudly on
# real errors (exit 2+). Caller passes pattern + dir; we echo the
# matches to stdout. Returns success either way; on real error we
# bail the whole script via `exit 1`.
grep_or_die() {
    local pat="$1"
    local dir="$2"
    local rc=0
    local out
    out=$(grep -rEn "$pat" "$dir") || rc=$?
    case "$rc" in
        0|1) printf '%s' "$out" ;;
        *)
            echo "ERROR: grep failed for pattern '$pat' under $dir (exit $rc)" >&2
            exit 1
            ;;
    esac
}

# For a `path:lineno:line` match, scan the 5 lines ending at lineno
# (inclusive) for the given allow annotation. Requires a NON-EMPTY
# reason after the colon — `// allow weak-count:` (no reason) doesn't
# count, because the whole point of the opt-out is to force the author
# to articulate why the lint should be bypassed. Returns 0 if found.
has_allow_above() {
    local match="$1"
    local annotation="$2"
    local file lineno start
    IFS=: read -r file lineno _ <<< "$match"
    start=$(( lineno > 5 ? lineno - 5 : 1 ))
    sed -n "${start},${lineno}p" "$file" | grep -qE "${annotation}:[[:space:]]*\S"
}

# Find multi-line regex matches across all `*.rs` files under $1 and
# emit them in `path:lineno:first-line-of-match` format that the rest
# of the script consumes like `grep -rn` output.
#
# `grep -rEn` is line-anchored, so `assert!(\n  !x.is_empty()` (the
# multi-line form, very common when the assertion has a message arg)
# slips through the line-by-line patterns above. Python's `re` with
# `DOTALL` handles cross-line matches cleanly and gives us correct
# line numbers; bash + grep can't easily do both.
#
# Args: $1 = tests dir, remaining args = patterns to find.
find_multiline_in_rs() {
    local dir="$1"
    shift
    python3 - "$dir" "$@" <<'PYEOF'
import re
import sys
from pathlib import Path

dir_arg = sys.argv[1]
patterns = sys.argv[2:]
for path in sorted(Path(dir_arg).rglob("*.rs")):
    text = path.read_text()
    for pat in patterns:
        for m in re.finditer(pat, text, flags=re.DOTALL):
            lineno = text.count("\n", 0, m.start()) + 1
            first_line = m.group(0).split("\n", 1)[0]
            print(f"{path}:{lineno}:{first_line}")
PYEOF
}

# ----------------------------------------------------------------------
# Policy 1: no weak count assertions on emission counts
# ----------------------------------------------------------------------

echo "[1/2] weak count assertions"

# Four shapes — all accept "1 OR 100":
#   A. `assert!(x.len() >= N)` / `assert!(x.count() > N)` and
#      precomputed `*_count` / `*_len` / `*_size` (or bare
#      `count`/`len`/`size`) idents. The original #992 bug used
#      `assert!(price_count >= 1)`.
#   B. `assert_ne!(x.len(), 0)` / `assert_ne!(emitted_count, 0)`
#   C. `assert!(!x.is_empty())`
#   D. `assert!(x.len() != 0)` / `assert!(price_count != 0)` —
#      semantically identical to B but written as an inequality
#      instead of using `assert_ne!`.
#
# Per-match allowlist: `// allow weak-count: <reason>` within 5
# leading lines.
# `(^|[^[:alnum:]_])` prefix is a word-boundary check. Without it,
# `prop_assert!(...)` and `debug_assert!(...)` would match the
# `assert!(...)` substring inside them. property tests legitimately
# use lower-bound assertions (different inputs produce different
# output shapes), and `debug_assert!` is for invariants, not test
# coverage. Both should be ignored.
WB='(^|[^[:alnum:]_])'
PAT_A="${WB}"'assert!\([^)]*((\.(count|len|size)\(\))|\b(count|len|size|[a-z_]+_(count|len|size)))[^)]*(>|>=)[[:space:]]*[0-9]+'
PAT_B="${WB}"'assert_ne!\([^,]*((\.(count|len|size)\(\))|\b(count|len|size|[a-z_]+_(count|len|size)))[^,]*,[[:space:]]*0[[:space:]]*[,)]'
PAT_C="${WB}"'assert!\([[:space:]]*!.+\.is_empty\(\)'
PAT_D="${WB}"'assert!\([^)]*((\.(count|len|size)\(\))|\b(count|len|size|[a-z_]+_(count|len|size)))[^)]*!=[[:space:]]*0[[:space:]]*[,)]'

# Multi-line forms of the same shapes. The line-anchored ERE patterns
# above miss `assert!(\n    !x.is_empty(), "msg"\n)` and friends, which
# is the more common form when the assertion carries a message arg.
# These run via Python (re.DOTALL) so newlines between `(` and the
# operand don't break matching. Patterns mirror their single-line
# siblings but use `\s*` (which includes `\n`), a bounded ident
# match to avoid swallowing the rest of the file, and PCRE
# negative-lookbehind to skip `prop_assert!` / `debug_assert!`.
#
# IMPORTANT: ML_PAT_B/D restrict the LHS to count-shaped expressions
# the same way single-line PAT_B/D do — `.count()`/`.len()`/`.size()`
# method calls or `*_count`/`*_len`/`*_size` (or bare `count`/`len`/
# `size`) idents. Without this restriction the multi-line patterns
# would false-positive on every `assert_ne!(balance, 0)` style check
# (Copilot review on PR #1005).
COUNT_LHS='(?:\w[\w.]*\.(?:count|len|size)\(\)|(?:\w+_)?(?:count|len|size))'
ML_PAT_C='(?<!\w)assert!\(\s*!\w[\w.]*\.is_empty\(\)'
ML_PAT_B='(?<!\w)assert_ne!\(\s*'"$COUNT_LHS"'\s*,\s*0\s*[,)]'
ML_PAT_D='(?<!\w)assert!\(\s*'"$COUNT_LHS"'\s*!=\s*0\s*[,)]'

bad=""
for pat in "$PAT_A" "$PAT_B" "$PAT_C" "$PAT_D"; do
    matches=$(grep_or_die "$pat" "$TESTS_DIR")
    [ -z "$matches" ] && continue
    while IFS= read -r match; do
        [ -z "$match" ] && continue
        if ! has_allow_above "$match" "allow weak-count"; then
            bad="${bad}${match}"$'\n'
        fi
    done <<< "$matches"
done

# Multi-line scan. Filter out anything already caught by the
# single-line passes above (same file:lineno) so we don't double-
# report.
ml_matches=$(find_multiline_in_rs "$TESTS_DIR" "$ML_PAT_C" "$ML_PAT_B" "$ML_PAT_D")
if [ -n "$ml_matches" ]; then
    while IFS= read -r match; do
        [ -z "$match" ] && continue
        # Skip if the same file:lineno already appears in `bad`
        # (single-line pattern already caught it).
        IFS=: read -r ml_file ml_lineno _ <<< "$match"
        if grep -qF "${ml_file}:${ml_lineno}:" <<< "$bad"; then
            continue
        fi
        if ! has_allow_above "$match" "allow weak-count"; then
            bad="${bad}${match}"$'\n'
        fi
    done <<< "$ml_matches"
fi

bad="${bad%$'\n'}"

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

# Match the historical bad shape `// Converted from <something> (partial)`
# specifically — broader `(partial)` substring matches would false-positive
# on unrelated comments like "(partial overlap with foo)". Opt-out:
# `// allow partial: <reason>` in the 5 leading lines.
PARTIAL_PATTERN='Converted from.*\(partial\)'

partial_bad=""
partial_matches=$(grep_or_die "$PARTIAL_PATTERN" "$TESTS_DIR")
if [ -n "$partial_matches" ]; then
    while IFS= read -r match; do
        [ -z "$match" ] && continue
        if ! has_allow_above "$match" "allow partial"; then
            partial_bad="${partial_bad}${match}"$'\n'
        fi
    done <<< "$partial_matches"
fi
partial_bad="${partial_bad%$'\n'}"

if [ -n "$partial_bad" ]; then
    echo "  ERROR: '(partial)' test port labels found"
    echo ""
    echo "$partial_bad"
    echo ""
    echo "  Either:"
    echo "  - Port the remaining upstream test cases, OR"
    echo "  - Document each skipped case explicitly with rationale, OR"
    echo "  - Add '// allow partial: <reason>' if it's a false positive"
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
