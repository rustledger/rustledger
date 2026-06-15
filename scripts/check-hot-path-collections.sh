#!/usr/bin/env bash
#
# Forbid std SipHash collections in hot-path modules.
#
# `rustc_hash::FxHashMap`/`FxHashSet` were adopted on hot paths as a perf win
# (#1076): the std `HashMap`/`HashSet` default to `SipHash`, which is much
# slower for the small integer/short-string keys these paths use. Nothing at
# the compiler level stops a new `std::collections::HashMap` from creeping
# into a hot path and silently regressing that. This is the ratchet.
#
# Opt-in, not blanket: a module marks itself a hot path with
#
#     // ratchet: fxhash-only
#
# near the top. This script finds every marked file and fails if its
# non-test code uses `std::collections::HashMap`/`HashSet`. `BTreeMap` and
# other collections are unaffected — only the SipHash maps are forbidden.
#
# Same lightweight, named-CI-status pattern as `check-unsafe-invariant.sh`,
# and deliberately a grep ratchet rather than a `dylint` lint so it needs no
# extra (nightly) toolchain.
#
# Escape hatch: append `// ratchet-allow: std-collections <reason>` to a line
# that genuinely needs a std map (e.g. one relied on for a specific property).
#
# Exit codes
# ----------
#   0  all marked files are clean
#   1  a marked file uses a forbidden std collection
#   2  invocation error (no marked files found)
#
# Usage
# -----
#   ./scripts/check-hot-path-collections.sh

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

marker='ratchet: fxhash-only'
forbidden='std::collections::(\{[^}]*)?(HashMap|HashSet)'

# Files that opt in to the ratchet.
mapfile -t marked < <(grep -rlE "$marker" crates/*/src --include='*.rs' 2>/dev/null | sort)

if [ "${#marked[@]}" -eq 0 ]; then
    echo "error: no files carry the '$marker' marker — the ratchet would be vacuous." >&2
    echo "       Did a marked module lose its marker?" >&2
    exit 2
fi

violations=""
for f in "${marked[@]}"; do
    # Drop everything from the first top-level `#[cfg(test)]` onward: std maps
    # in unit-test modules are harmless. (Test modules sit at file end by
    # convention here.)
    code="$(awk '/#\[cfg\(test\)\]/{exit} {print}' "$f")"
    hits="$(printf '%s\n' "$code" | grep -nE "$forbidden" | grep -v 'ratchet-allow: std-collections' || true)"
    if [ -n "$hits" ]; then
        violations+="$f:"$'\n'"$(printf '%s\n' "$hits" | sed 's/^/    /')"$'\n'
    fi
done

if [ -n "$violations" ]; then
    echo "error: std SipHash collection(s) in hot-path (fxhash-only) modules." >&2
    echo "       Use rustc_hash::FxHashMap / FxHashSet instead (see #1076)." >&2
    echo "       If a std map is genuinely required, append" >&2
    echo "         // ratchet-allow: std-collections <reason>" >&2
    echo "       to the line." >&2
    echo >&2
    printf '%s' "$violations" >&2
    exit 1
fi

echo "ok: ${#marked[@]} hot-path module(s) are free of std SipHash collections."
