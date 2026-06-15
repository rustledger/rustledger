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
# Scope: `crates/*/src/` only (library code). Tests, benches, and examples are
# not checked — std locks there are harmless.
#
# Escape hatch: append `// ratchet-allow: std-sync <reason>` to the offending
# line for a legitimate exception (none exist today).
#
# Exit codes
# ----------
#   0  no forbidden std::sync locks found
#   1  one or more forbidden usages found
#   2  invocation error
#
# Usage
# -----
#   ./scripts/check-sync-primitives.sh

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

# Matches `std::sync::Mutex`, `std::sync::RwLock`, and the brace-import form
# `std::sync::{... Mutex ...}` / `{... RwLock ...}`.
pattern='std::sync::(\{[^}]*)?(Mutex|RwLock)'

if ! command -v rg >/dev/null 2>&1; then
    grep_cmd() { grep -rnE "$pattern" crates/*/src --include='*.rs' 2>/dev/null || true; }
else
    grep_cmd() { rg -n --no-heading -e "$pattern" -g 'crates/*/src/**/*.rs' 2>/dev/null || true; }
fi

# Collect hits, dropping any line that carries the explicit allow marker.
hits="$(grep_cmd | grep -v 'ratchet-allow: std-sync' || true)"

if [ -n "$hits" ]; then
    echo "error: forbidden std::sync lock(s) found in library code." >&2
    echo "       Use parking_lot::Mutex / parking_lot::RwLock instead (see #1076)." >&2
    echo "       If a std lock is genuinely required, append" >&2
    echo "         // ratchet-allow: std-sync <reason>" >&2
    echo "       to the line." >&2
    echo >&2
    echo "$hits" >&2
    exit 1
fi

echo "ok: no std::sync::Mutex / RwLock in library source."
