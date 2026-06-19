#!/usr/bin/env bash
# CI gate (#1395): a change to the Component-Model WIT contract
# (`crates/rustledger-ffi-component/wit/world.wit`) MUST be accompanied by a
# package-version bump, so a wire-shape change cannot ship without a conscious,
# visible version decision.
#
# The Component Model replaced the hand-parsed FFI-WASI JSON wire format as the
# primary embedding surface (#1384). Its `world.wit` *is* the diffable contract,
# but the version (`package rustledger:ledger@X.Y.Z;`) is still hand-maintained
# with nothing tying it to a contract change. This gate is that tie.
#
# "Change" means a change to the WIT *interface*: comments (`// ...`) and blank
# lines are ignored, so doc-only edits don't force a bump. On any interface
# change, the package version must differ from the base.
#
# Usage: check-wit-version-bump.sh [base-ref]   (default: origin/main)
set -euo pipefail

BASE_REF="${1:-origin/main}"
WIT="crates/rustledger-ffi-component/wit/world.wit"

if ! git rev-parse --verify --quiet "${BASE_REF}^{commit}" >/dev/null; then
    echo "check-wit-version-bump: base ref '${BASE_REF}' not found; skipping." >&2
    exit 0
fi

# New file (not present on base) — nothing to compare against.
if ! git cat-file -e "${BASE_REF}:${WIT}" 2>/dev/null; then
    echo "check-wit-version-bump: '${WIT}' is new on this branch; skipping." >&2
    exit 0
fi

# Semantic content = drop line comments and blank/whitespace-only lines.
semantic() {
    sed -E 's://.*$::' | sed -E 's/[[:space:]]+$//' | grep -vE '^[[:space:]]*$' || true
}

old_iface="$(git show "${BASE_REF}:${WIT}" | semantic)"
new_iface="$(semantic <"${WIT}")"

if [ "${old_iface}" = "${new_iface}" ]; then
    echo "check-wit-version-bump: no WIT interface change (comments/whitespace only). OK."
    exit 0
fi

ver_re='package rustledger:ledger@[0-9]+\.[0-9]+\.[0-9]+'
old_ver="$(git show "${BASE_REF}:${WIT}" | grep -oE "${ver_re}" || true)"
new_ver="$(grep -oE "${ver_re}" "${WIT}" || true)"

if [ -n "${new_ver}" ] && [ "${old_ver}" != "${new_ver}" ]; then
    echo "check-wit-version-bump: WIT interface changed and version bumped (${old_ver} -> ${new_ver}). OK."
    exit 0
fi

cat >&2 <<EOF
ERROR: ${WIT} interface changed but the package version was not bumped.

  current: ${new_ver:-<none>}
  base:    ${old_ver:-<none>}

The Component-Model wire contract is versioned (#1395). A shape change must bump
'package rustledger:ledger@X.Y.Z;' (and the mirrored API_VERSION const in
crates/rustledger-ffi-component/src/lib.rs):
  - additive / backwards-compatible change -> bump MINOR  (X.Y+1.0)
  - breaking change                        -> bump MAJOR  (X+1.0.0)

If you believe this is a no-op interface change, it should not appear in the
semantic diff (only comments/whitespace differ); re-check the edit.
EOF
exit 1
