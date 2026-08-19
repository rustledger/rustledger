#!/usr/bin/env bash
# Assert the profiling workloads still measure what they claim to.
#
# The workloads exist to stop a profile drifting away from what rledger is
# actually asked to do. That drift is exactly what happened before: the sole
# workload contained no `{`, `^` or `#` anywhere, so it never booked a lot and
# never entered the three whole-tree error passes those characters gate. Every
# profile taken against it measured the cheapest path through the parser.
#
# Two properties have to hold, and neither is self-evident from reading the
# generator:
#
#   1. Each shape LOADS CLEANLY. A workload with errors profiles the
#      diagnostic paths instead of the pipeline — a different program.
#   2. Each shape CONTAINS the feature it exists for. A generator can keep
#      emitting syntactically valid ledgers long after a change stops it
#      emitting cost specs, and nothing else would notice.
#
# Usage: scripts/check-profile-workloads.sh [path-to-rledger]
set -euo pipefail

RLEDGER="${1:-./target/release/rledger}"
GEN="$(dirname "$0")/gen-profile-workload.py"
TXNS=200
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

if [ ! -x "$RLEDGER" ]; then
    echo "error: rledger not found at $RLEDGER" >&2
    echo "       build it first: cargo build --release --bin rledger" >&2
    exit 2
fi

# shape:regex — the feature whose ABSENCE would make the shape pointless.
declare -A REQUIRED=(
    # Dated lot reference, not a bare cost: `investment` names the lot it is
    # selling by cost AND acquisition date. Costs collide across thousands of
    # buys, so naming the cost alone matched two lots and STRICT rejected it
    # (#2097) — the date is load-bearing, and this asserts it stays.
    [investment]='\{[0-9.]+ USD, [0-9]{4}-[0-9]{2}-[0-9]{2}\}'
    [tagged]='#[a-z]'
    [multicurrency]='^[0-9-]+ price '
    # Bare braces: the whole point of `fifo` is that the booking method picks
    # the lot. An explicit cost here would collapse it into `investment`.
    [fifo]='\{\} @'
)
# `simple` deliberately has no required feature: it is the floor, kept to show
# what the cheapest path costs. It is asserted to load, nothing more.

failed=0
# `fifo` was absent from this list for as long as it has existed, so the shape
# added because ordered selection was unprofiled was itself unchecked.
for shape in simple investment tagged multicurrency fifo; do
    file="$TMP/$shape.beancount"
    if ! python3 "$GEN" "$shape" "$TXNS" > "$file" 2>"$TMP/$shape.gen.err"; then
        echo "FAIL $shape: generator failed"
        sed 's/^/     /' "$TMP/$shape.gen.err"
        failed=1
        continue
    fi

    if ! "$RLEDGER" check "$file" > "$TMP/$shape.check.out" 2>&1; then
        echo "FAIL $shape: does not load cleanly — a profile of this measures error paths"
        head -5 "$TMP/$shape.check.out" | sed 's/^/     /'
        failed=1
        continue
    fi

    want="${REQUIRED[$shape]:-}"
    if [ -n "$want" ] && ! grep -qE "$want" "$file"; then
        echo "FAIL $shape: no match for /$want/ — the shape stopped emitting its own feature"
        failed=1
        continue
    fi

    printf 'ok   %-14s loads clean%s\n' "$shape" \
        "${want:+, contains /$want/}"
done

# Cross-check against Python where it is available. `investment` spent months
# loading cleanly here while bean-check rejected it outright (#2097), which
# made it useless as an input for any rustledger-vs-beancount comparison and
# hid a real divergence. Optional, so this script still runs without a Python
# beancount installed.
if command -v bean-check >/dev/null 2>&1; then
    for shape in simple investment tagged multicurrency fifo; do
        file="$TMP/$shape.beancount"
        [ -f "$file" ] || continue
        if bean-check "$file" > "$TMP/$shape.bean.out" 2>&1; then
            printf 'ok   %-14s loads under bean-check too\n' "$shape"
        else
            echo "FAIL $shape: bean-check rejects it — the shape is rledger-only"
            head -3 "$TMP/$shape.bean.out" | sed 's/^/     /'
            failed=1
        fi
    done
else
    echo "note: bean-check not on PATH; skipped the Python cross-check"
fi

# The floor must stay the floor: if `simple` ever grows these features it
# stops being the cheap-path baseline the others are compared against.
if grep -qE '\{|\^|#' "$TMP/simple.beancount"; then
    echo "FAIL simple: gained a cost spec, link or tag — it exists to be the FLOOR"
    failed=1
fi

exit "$failed"
