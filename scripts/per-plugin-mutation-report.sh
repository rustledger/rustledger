#!/usr/bin/env bash
# Compute per-plugin mutation survival rate from a `cargo mutants` run.
#
# Phase 3 of the plugin-testing-quality plan documented in issue #992.
# This is the script that backs the per-plugin floor enforcement in
# `.github/workflows/mutation.yml`.
#
# Reads `mutants.out/{caught,missed,timeout,unviable}.txt` (left behind
# by `cargo mutants`), groups outcomes by source file, and prints a
# per-plugin table with survival rates. Survival rate is defined as
# `missed / (caught + missed + timeout)` — `unviable` mutants didn't
# compile and are excluded from the denominator.
#
# Exits non-zero if any plugin's survival rate exceeds MUTATION_FLOOR
# (default 10%, override via env). Use this to gate PRs that touch
# `crates/rustledger-plugin/src/native/plugins/*.rs`.
#
# Usage:
#   scripts/per-plugin-mutation-report.sh                     # default floor (10%)
#   MUTATION_FLOOR=15 scripts/per-plugin-mutation-report.sh   # custom floor
#   MUTATION_FLOOR=0  scripts/per-plugin-mutation-report.sh   # disable enforcement
#                                                             # (report only)
#   GITHUB_ANNOTATIONS=1 scripts/per-plugin-mutation-report.sh # also emit
#                                                              # ::warning:: lines
#                                                              # for inline PR
#                                                              # annotations
#
# Inputs:
#   mutants.out/caught.txt   list of caught mutant names (one per line)
#   mutants.out/missed.txt   list of surviving mutants
#   mutants.out/timeout.txt  list of mutants that hit the timeout
#   mutants.out/unviable.txt list of mutants that didn't compile (ignored)
#
# Output:
#   stdout:  per-plugin table + summary
#   stderr:  errors only
#   exit 0:  every plugin ≤ floor (or floor=0 disabled enforcement)
#   exit 1:  at least one plugin exceeded the floor
#   exit 2:  configuration error (missing inputs, etc.)

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
MUTANTS_DIR="${MUTANTS_DIR:-$REPO_ROOT/mutants.out}"
MUTATION_FLOOR="${MUTATION_FLOOR:-10}"
GITHUB_ANNOTATIONS="${GITHUB_ANNOTATIONS:-0}"

# Plugin source files live here. Anything under this directory becomes a
# per-plugin bucket; everything else is bucketed as "_infrastructure"
# (which is reported but does NOT count toward the per-plugin floor).
PLUGIN_DIR_RE='^crates/rustledger-plugin/src/native/plugins/'
# Files under PLUGIN_DIR_RE that aren't actual plugins. `mod.rs` is
# the module facade, `utils.rs` is shared helpers — neither is a
# user-facing plugin and grouping their mutants under one plugin name
# would be misleading.
NON_PLUGIN_FILES='mod\.rs|utils\.rs'

if [ ! -d "$MUTANTS_DIR" ]; then
    echo "ERROR: mutants.out directory not found at $MUTANTS_DIR" >&2
    echo "Run 'cargo mutants -p rustledger-plugin' first." >&2
    exit 2
fi

for f in caught.txt missed.txt timeout.txt; do
    if [ ! -f "$MUTANTS_DIR/$f" ]; then
        echo "ERROR: $MUTANTS_DIR/$f not found" >&2
        echo "Did 'cargo mutants' run to completion?" >&2
        exit 2
    fi
done

# Extract the source file from a mutant line. The line format is:
#   crates/rustledger-plugin/src/<path>/<file>.rs:<line>:<col>: replace ...
# We want just the file path (everything before the first ':<digit>').
extract_file() {
    sed -E 's/^([^:]+\.rs):.*$/\1/'
}

# Map a source file to its bucket name. Plugin files become their
# basename without `.rs`; everything else becomes `_infrastructure`.
bucket_for() {
    local file="$1"
    if echo "$file" | grep -qE "$PLUGIN_DIR_RE"; then
        local basename
        basename="$(basename "$file" .rs)"
        if echo "$basename.rs" | grep -qE "^($NON_PLUGIN_FILES)$"; then
            echo "_infrastructure"
        else
            echo "$basename"
        fi
    else
        echo "_infrastructure"
    fi
}

# Build a map from bucket → counts. We accumulate {caught,missed,timeout}
# in associative arrays keyed by bucket name.
declare -A caught_count
declare -A missed_count
declare -A timeout_count
declare -A buckets

# A surviving mutant outcome name lives one per line under each .txt
# file. Iterate, extract file, find bucket, increment the right counter.
count_outcomes() {
    local kind="$1"
    local file="$MUTANTS_DIR/${kind}.txt"
    [ -s "$file" ] || return 0
    # `|| [ -n "$line" ]` handles a final line without a trailing newline.
    # Without it, the last entry is silently dropped — and cargo-mutants
    # output may or may not have a trailing newline depending on version.
    while IFS= read -r line || [ -n "$line" ]; do
        [ -z "$line" ] && continue
        local src bucket
        src=$(echo "$line" | extract_file)
        bucket=$(bucket_for "$src")
        buckets[$bucket]=1
        case "$kind" in
            caught)  caught_count[$bucket]=$(( ${caught_count[$bucket]:-0} + 1 )) ;;
            missed)  missed_count[$bucket]=$(( ${missed_count[$bucket]:-0} + 1 )) ;;
            timeout) timeout_count[$bucket]=$(( ${timeout_count[$bucket]:-0} + 1 )) ;;
        esac
    done < "$file"
}

count_outcomes caught
count_outcomes missed
count_outcomes timeout

# ----------------------------------------------------------------------
# Per-PR inline annotations (GitHub workflow commands).
#
# When run in CI with GITHUB_ANNOTATIONS=1, emit `::error file=...,line=...`
# for every surviving mutant. GitHub Actions surfaces these as inline
# annotations on the PR diff, satisfying the "PR inline comments for
# surviving mutants" acceptance criterion of #1003.
# ----------------------------------------------------------------------

emit_github_annotations() {
    local missed="$MUTANTS_DIR/missed.txt"
    [ -s "$missed" ] || return 0
    # `|| [ -n "$line" ]` handles a final line without a trailing newline.
    # Without it, the last entry is silently dropped — and cargo-mutants
    # output may or may not have a trailing newline depending on version.
    #
    # Parse once with bash's =~ regex (single in-process operation) instead
    # of spawning four `sed` subprocesses per line; on a 1000-line missed.txt
    # that's 4000 fewer fork/exec pairs.
    local line_re='^(.+\.rs):([0-9]+):([0-9]+):[[:space:]]*(.*)$'
    while IFS= read -r line || [ -n "$line" ]; do
        [ -z "$line" ] && continue
        if [[ ! "$line" =~ $line_re ]]; then
            continue
        fi
        local file="${BASH_REMATCH[1]}"
        local lineno="${BASH_REMATCH[2]}"
        local col="${BASH_REMATCH[3]}"
        local rest="${BASH_REMATCH[4]}"
        # GitHub annotation format. Newlines in the message are escaped
        # as %0A per the workflow command spec.
        printf '::warning file=%s,line=%s,col=%s,title=Mutant survived::%s%%0A%%0AThis mutation was not caught by any test. Either tighten a test or annotate with #[mutants::skip] (with a reason).\n' \
            "$file" "$lineno" "$col" "$rest"
    done < "$missed"
}

if [ "$GITHUB_ANNOTATIONS" = "1" ]; then
    emit_github_annotations
fi

# ----------------------------------------------------------------------
# Report
# ----------------------------------------------------------------------

echo "=== Per-plugin mutation testing report ==="
echo ""
echo "Floor: ≤${MUTATION_FLOOR}% survival rate per plugin"
echo "(survival rate = missed / (caught + missed + timeout); unviable mutants excluded)"
echo ""
printf '%-32s %8s %8s %9s %10s   %s\n' "Plugin" "Caught" "Missed" "Timeout" "Survival" "Status"
printf '%-32s %8s %8s %9s %10s   %s\n' \
    "--------------------------------" "------" "------" "-------" "--------" "------"

fail=0
plugin_count=0
plugin_pass=0
plugin_fail=0
fail_list=""

# Sort buckets so real plugins appear first (alphabetically), then
# `_infrastructure` last. Floor enforcement applies only to real plugins.
sorted_buckets=$(
    for b in "${!buckets[@]}"; do
        if [ "$b" = "_infrastructure" ]; then
            echo "1 $b"
        else
            echo "0 $b"
        fi
    done | sort | awk '{print $2}'
)

for bucket in $sorted_buckets; do
    c=${caught_count[$bucket]:-0}
    m=${missed_count[$bucket]:-0}
    t=${timeout_count[$bucket]:-0}
    total=$((c + m + t))
    if [ $total -eq 0 ]; then
        survival="N/A"
    else
        # Print with 1 decimal of precision via awk float math.
        survival_dec=$(awk -v m="$m" -v t="$total" 'BEGIN { printf "%.1f", (m * 100.0) / t }')
        survival="${survival_dec}%"
    fi

    status="✅"
    if [ "$bucket" = "_infrastructure" ]; then
        # Reported but not enforced.
        status="(not enforced)"
    elif [ $total -eq 0 ]; then
        status="(no mutants)"
    # Cross-multiplication avoids lossy integer division: instead of
    # `(m * 100 / total) > floor`, which truncates 10.89% to 10 and
    # incorrectly passes, compare `m * 100 > floor * total` directly.
    # This is strictly greater (any value > floor fails).
    elif [ $((m * 100)) -gt $((MUTATION_FLOOR * total)) ]; then
        status="❌ exceeds ${MUTATION_FLOOR}% floor"
        fail=1
        plugin_fail=$((plugin_fail + 1))
        fail_list="$fail_list $bucket"
    else
        plugin_pass=$((plugin_pass + 1))
    fi
    if [ "$bucket" != "_infrastructure" ]; then
        plugin_count=$((plugin_count + 1))
    fi

    printf '%-32s %8d %8d %9d %10s   %s\n' "$bucket" "$c" "$m" "$t" "$survival" "$status"
done

echo ""
echo "Summary:"
echo "  Plugins evaluated: $plugin_count"
echo "  Pass: $plugin_pass"
echo "  Fail: $plugin_fail"
if [ -n "$fail_list" ]; then
    echo "  Failed plugins:$fail_list"
fi
echo ""

if [ "$MUTATION_FLOOR" = "0" ]; then
    echo "MUTATION_FLOOR=0: enforcement disabled (report-only mode)"
    exit 0
fi

if [ $fail -eq 1 ]; then
    echo "=== FAILED: $plugin_fail plugin(s) exceed ${MUTATION_FLOOR}% survival rate ==="
    echo ""
    echo "Each surviving mutant means a code change that no test caught. To fix:"
    echo "  1. Tighten the relevant test to fail under the mutated code, OR"
    echo "  2. Annotate the function with #[mutants::skip] and a leading"
    echo "     '// reason: …' comment. See CONTRIBUTING.md → Mutation testing."
    echo ""
    echo "See mutants.out/missed.txt for the full list."
    exit 1
fi

echo "=== All plugins pass the ${MUTATION_FLOOR}% survival floor ==="
