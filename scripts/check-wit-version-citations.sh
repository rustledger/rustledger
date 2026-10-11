#!/usr/bin/env bash
# CI gate (#2508): prose that cites the Component-Model contract version must
# not drift from `crates/rustledger-ffi-component/wit/world.wit`.
#
# Docs cited `rustledger:ledger@3.0.0` through thirteen minor bumps, because
# nothing tied the citations to the `package` line. This check does: every
# `rustledger:ledger@<version>` in a tracked file must be either
#   - the exact current version (`@3.14.0`), or
#   - the current major with a wildcard (`@3.x`), which is what prose should
#     use, so a minor bump does not touch it.
# Anything else (an old exact version, an old major, `@3.13`) fails.
#
# CHANGELOG files are history and are not checked; world.wit is the source.
#
# Usage: check-wit-version-citations.sh
set -euo pipefail

WIT="crates/rustledger-ffi-component/wit/world.wit"

current="$(grep -oE '^package rustledger:ledger@[0-9]+\.[0-9]+\.[0-9]+' "${WIT}" | sed 's/.*@//' || true)"
if [ -z "${current}" ]; then
    echo "ERROR: ${WIT} has no 'package rustledger:ledger@X.Y.Z;' line." >&2
    exit 1
fi
major="${current%%.*}"

# `git grep` reads tracked files only, so build output and caches never match.
# A citation is the package name followed by `@` and a version-like token.
hits="$(git grep -nIoE 'rustledger:ledger@[0-9][0-9A-Za-z.]*' -- \
    ':!*CHANGELOG*.md' ":!${WIT}" || true)"

bad=""
while IFS= read -r hit; do
    [ -z "${hit}" ] && continue
    cited="${hit##*@}"
    cited="${cited%.}" # a citation ending a sentence: `@3.x.`
    if [ "${cited}" = "${current}" ] || [ "${cited}" = "${major}.x" ]; then
        continue
    fi
    bad="${bad}  ${hit}"$'\n'
done <<<"${hits}"

if [ -n "${bad}" ]; then
    cat >&2 <<EOF
ERROR: stale Component-Model version citations. ${WIT} is
rustledger:ledger@${current}; cite it as \`rustledger:ledger@${major}.x\` (preferred,
survives minor bumps) or as the exact \`@${current}\`:

${bad}
EOF
    exit 1
fi

echo "check-wit-version-citations: every citation matches rustledger:ledger@${current} (or @${major}.x). OK."
