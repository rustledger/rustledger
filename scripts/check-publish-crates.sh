#!/usr/bin/env bash
# Guardrail: keep the crates.io publish list in sync with the workspace.
#
# `release-publish.yml` publishes a hand-maintained `CRATES=( ... )` array to
# crates.io. If a new publishable crate is added to the workspace but not to
# that array, the release silently skips it — and any crate that depends on it
# then fails to publish ("failed to select a version for <crate>"). That is
# exactly what broke the v0.16.0 release (rustledger-completion was missing).
#
# This script fails if the set of publishable workspace crates does not match
# the CRATES array. Run it in CI on every PR so the drift is caught at review
# time, not mid-release.
set -euo pipefail

WORKFLOW=".github/workflows/release-publish.yml"

# Publishable workspace crates (everything except `publish = false`), sorted.
publishable=$(
  cargo metadata --format-version 1 --no-deps \
    | python3 -c 'import json,sys
m = json.load(sys.stdin)
for p in m["packages"]:
    if p.get("publish") != []:  # [] means publish = false
        print(p["name"])' \
    | sort
)

# Crate names inside the CRATES=( ... ) array, sorted.
listed=$(
  awk '/CRATES=\(/{f=1;next} /\)/{f=0} f' "$WORKFLOW" \
    | tr -d ' ' \
    | grep . \
    | sort
)

missing=$(comm -23 <(printf '%s\n' "$publishable") <(printf '%s\n' "$listed"))
extra=$(comm -13 <(printf '%s\n' "$publishable") <(printf '%s\n' "$listed"))

status=0
if [ -n "$missing" ]; then
  echo "::error::Publishable crate(s) missing from the CRATES array in ${WORKFLOW}:"
  printf '%s\n' "$missing" | sed 's/^/  - /'
  echo ""
  echo "Add each one to the array IN DEPENDENCY ORDER (dependencies before dependents)."
  echo "If a crate is brand-new to crates.io, its FIRST publish must be done MANUALLY"
  echo "  cargo login <token> && cargo publish -p <crate>"
  echo "and trusted publishing must be configured at"
  echo "  https://crates.io/crates/<crate>/settings"
  echo "OIDC cannot create a crate or push to one without trusted publishing set up."
  status=1
fi
if [ -n "$extra" ]; then
  echo "::error::CRATES array lists name(s) that are not publishable workspace crates:"
  printf '%s\n' "$extra" | sed 's/^/  - /'
  echo "Remove them, or fix the crate's publish setting."
  status=1
fi

if [ "$status" -eq 0 ]; then
  echo "✓ crates.io publish list matches all $(printf '%s\n' "$publishable" | grep -c .) publishable crates"
fi
exit "$status"
