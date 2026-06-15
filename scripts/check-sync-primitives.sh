#!/usr/bin/env bash
#
# Forbid `std::sync::Mutex` / `std::sync::RwLock` in library source.
#
# `parking_lot` was adopted as a performance quick win (#1076): its locks are
# smaller, faster, and do not poison. Nothing at the compiler level prevents a
# new `std::sync::Mutex`/`RwLock` from creeping back in, which would silently
# regress that decision. This script is the ratchet — the same lightweight,
# named-CI-status pattern as `check-unsafe-invariant.sh`, deliberately chosen
# over a `dylint` lint so it needs no extra (nightly) toolchain.
#
# Scope: `crates/*/src/` only, and within those files only non-test code —
# `#[cfg(test)] mod ...` blocks are skipped (std locks in unit tests are
# harmless, matching #1237's "excluding #[cfg(test)]" intent). Integration
# tests / benches / examples live outside `src/` and aren't scanned.
#
# Escape hatch: append `// ratchet-allow: std-sync <reason>` to the offending
# line for a legitimate exception (none exist today).
#
# Exit codes
# ----------
#   0  no forbidden std::sync locks found
#   1  one or more forbidden usages found
#
# Usage
# -----
#   ./scripts/check-sync-primitives.sh

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

# Matches `std::sync::Mutex`/`RwLock` and the brace-import form
# `std::sync::{... Mutex ...}`. The trailing `\b` excludes the guard types
# (`MutexGuard`, `RwLockReadGuard`, `RwLockWriteGuard`), which are type
# references, not lock constructions.
forbidden='std::sync::(\{[^}]*)?(Mutex|RwLock)\b'

# Print a file's non-test code: everything up to the trailing
# `#[cfg(test)]`-attributed `mod`. A `#[cfg(test)]` that precedes anything
# other than a module (e.g. a test-only `use`/`fn` near the top) does NOT
# truncate scanning — only the conventional trailing test module does.
strip_test_module() {
    awk '
        /#\[cfg\(test\)\]/ { pending = 1; print; next }
        pending && /^[[:space:]]*$/ { print; next }              # blank lines between attr and mod
        pending && /^[[:space:]]*(pub[[:space:]]+)?mod[[:space:]]/ { exit }
        { pending = 0; print }
    ' "$1"
}

violations=""
while IFS= read -r f; do
    hits="$(strip_test_module "$f" | grep -nE "$forbidden" | grep -v 'ratchet-allow: std-sync' || true)"
    if [ -n "$hits" ]; then
        violations+="$f:"$'\n'"$(printf '%s\n' "$hits" | sed 's/^/    /')"$'\n'
    fi
done < <(grep -rlE "$forbidden" crates/*/src --include='*.rs' 2>/dev/null | sort)

if [ -n "$violations" ]; then
    echo "error: forbidden std::sync lock(s) found in non-test library code." >&2
    echo "       Use parking_lot::Mutex / parking_lot::RwLock instead (see #1076)." >&2
    echo "       If a std lock is genuinely required, append" >&2
    echo "         // ratchet-allow: std-sync <reason>" >&2
    echo "       to the line." >&2
    echo >&2
    printf '%s' "$violations" >&2
    exit 1
fi

echo "ok: no std::sync::Mutex / RwLock in non-test library source."
