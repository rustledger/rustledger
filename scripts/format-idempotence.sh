#!/usr/bin/env bash
# Format idempotence check (#1323).
#
# `rledger format` must be a fixed point: re-formatting an
# already-formatted file must produce byte-identical output. This
# catches whole classes of formatter bugs that the small golden cases in
# `crates/rustledger-parser/tests/format_compat/cases/` miss - e.g.
# #1321, where header `#tag` / `^link` migrated to continuation lines for
# every transaction after the first.
#
# Runs over the fetched compatibility corpus (the ~800 real-world
# `.beancount` files the compat workflow already downloads), exercising
# far more shapes than the golden cases. Files that do not format cleanly
# (parse errors, unsupported constructs) are out of scope and skipped.
#
# Usage:   scripts/format-idempotence.sh [CORPUS_DIR]
# Env:     RLEDGER  path to the rledger binary (default ./target/release/rledger)
#          STRICT   if "0", report non-idempotent files but exit 0 (default: strict, exit 1 on any)
#
# Note: `-e` is intentionally omitted. The loop must survive a `diff` (which
# exits 1 on the very differences we are reporting) and per-file `rledger`
# failures without aborting; correctness comes from explicit return-code
# checks and the `fail` accumulator, not from `-e`. Setup commands that
# must not fail silently (mktemp) are guarded individually below.
set -uo pipefail

RLEDGER="${RLEDGER:-./target/release/rledger}"
CORPUS="${1:-tests/compatibility/files}"
STRICT="${STRICT:-1}"

if ! command -v "$RLEDGER" >/dev/null 2>&1 && [ ! -x "$RLEDGER" ]; then
  echo "error: rledger binary not found/executable at '$RLEDGER'" >&2
  exit 2
fi
if [ ! -d "$CORPUS" ]; then
  echo "error: corpus directory not found: '$CORPUS'" >&2
  exit 2
fi

once=$(mktemp) || { echo "error: mktemp failed" >&2; exit 2; }
twice=$(mktemp) || { echo "error: mktemp failed" >&2; exit 2; }
trap 'rm -f "$once" "$twice"' EXIT

checked=0
skipped=0
fail=0
failed_files=()

while IFS= read -r -d '' f; do
  # Format once. Skip files rledger can't format (out of scope here).
  if ! "$RLEDGER" format "$f" >"$once" 2>/dev/null; then
    skipped=$((skipped + 1))
    continue
  fi
  checked=$((checked + 1))

  # Re-format the formatted output; it must be byte-identical.
  if ! "$RLEDGER" format "$once" >"$twice" 2>/dev/null; then
    echo "FAIL (rledger format errored on its own output): $f"
    failed_files+=("$f")
    fail=$((fail + 1))
    continue
  fi
  if ! cmp -s "$once" "$twice"; then
    echo "FAIL (not idempotent): $f"
    diff "$once" "$twice" | head -20
    failed_files+=("$f")
    fail=$((fail + 1))
  fi
done < <(find "$CORPUS" -name '*.beancount' -type f -print0)

echo "----"
echo "format idempotence: checked=$checked skipped=$skipped non_idempotent=$fail"

if [ "$fail" -gt 0 ]; then
  {
    echo "non-idempotent files:"
    printf '  %s\n' "${failed_files[@]}"
  } >&2
  if [ "$STRICT" != "0" ]; then
    exit 1
  fi
fi
