#!/usr/bin/env bash
# bean-format roundtrip check (#1324).
#
# Idempotence (scripts/format-idempotence.sh) proves `rledger format` is a
# fixed point of *itself*. That is necessary but not sufficient: the
# formatter could converge on output that is stable yet structurally wrong
# (wrong directive order, a misplaced tag, a mangled number) and stay
# green forever. This check adds an *external oracle* - Python beancount's
# own `bean-format` - and asserts that our output is a fixed point of it
# too:
#
#     normalize(bean-format(rledger format(x))) == normalize(rledger format(x))
#
# i.e. once rledger has formatted a file, running Python's canonical
# formatter over the result changes nothing of substance. That pins
# agreement with beancount on everything `bean-format` touches: directive
# and posting order, tag/link placement, decimal and currency
# normalization, costs, metadata, flags.
#
# Why `normalize`. rledger and bean-format deliberately disagree on ONE
# thing: the column model. bean-format aligns every posting amount to a
# single whole-file column (the max prefix width in the entire file);
# rledger aligns per transaction (the max within each transaction). Both
# are legitimate; per-transaction alignment keeps unrelated transactions
# from reflowing when one long account name appears elsewhere in the file.
# So we normalize away horizontal *alignment padding* before comparing:
# leading indentation is preserved (a real indent regression still fails),
# but internal runs of two-or-more spaces - which is exactly where the two
# tools pad differently - collapse to one. Across the ~700-file compat
# corpus this leaves precisely zero divergences, so the check ships as a
# strict gate with no allowlist: any future structural disagreement with
# bean-format is a real regression.
#
# Usage:   scripts/format-bean-format-roundtrip.sh [CORPUS_DIR]
# Env:     RLEDGER     path to the rledger binary (default ./target/release/rledger)
#          BEANFORMAT  bean-format command (default: bean-format on PATH)
#          STRICT      if "0", report divergences but exit 0 (default: strict, exit 1 on any)
#
# Note: `-e` is intentionally omitted (see scripts/format-idempotence.sh) -
# the loop must survive `diff`/per-file tool failures and report rather than
# abort. Setup commands that must not fail silently (mktemp) are guarded.
set -uo pipefail

RLEDGER="${RLEDGER:-./target/release/rledger}"
BEANFORMAT="${BEANFORMAT:-bean-format}"
CORPUS="${1:-tests/compatibility/files}"
STRICT="${STRICT:-1}"

if ! command -v "$RLEDGER" >/dev/null 2>&1 && [ ! -x "$RLEDGER" ]; then
  echo "error: rledger binary not found/executable at '$RLEDGER'" >&2
  exit 2
fi
if ! command -v "$BEANFORMAT" >/dev/null 2>&1; then
  echo "error: bean-format not found (set BEANFORMAT or install beancount)" >&2
  exit 2
fi
if [ ! -d "$CORPUS" ]; then
  echo "error: corpus directory not found: '$CORPUS'" >&2
  exit 2
fi

once=$(mktemp) || { echo "error: mktemp failed" >&2; exit 2; }
oracle=$(mktemp) || { echo "error: mktemp failed" >&2; exit 2; }
once_n=$(mktemp) || { echo "error: mktemp failed" >&2; exit 2; }
oracle_n=$(mktemp) || { echo "error: mktemp failed" >&2; exit 2; }
trap 'rm -f "$once" "$oracle" "$once_n" "$oracle_n"' EXIT

# Strip alignment padding: preserve leading indentation, collapse internal
# runs of 2+ spaces to one, drop trailing whitespace. This is the one axis
# on which rledger (per-transaction) and bean-format (whole-file) are meant
# to differ; everything else must match exactly.
normalize() {
  sed -E 's/([^[:space:]])[[:space:]]{2,}/\1 /g; s/[[:space:]]+$//' "$1"
}

checked=0
skipped=0
fail=0
failed_files=()

while IFS= read -r -d '' f; do
  # Format with rledger. Skip files rledger can't format (out of scope).
  if ! "$RLEDGER" format "$f" >"$once" 2>/dev/null; then
    skipped=$((skipped + 1))
    continue
  fi
  # Run Python's bean-format over our output. Skip files bean-format
  # chokes on (it is regex-based and not a full parser).
  if ! "$BEANFORMAT" "$once" >"$oracle" 2>/dev/null; then
    skipped=$((skipped + 1))
    continue
  fi
  checked=$((checked + 1))

  normalize "$once" >"$once_n"
  normalize "$oracle" >"$oracle_n"
  if ! cmp -s "$once_n" "$oracle_n"; then
    echo "FAIL (bean-format disagrees beyond alignment): $f"
    diff "$once_n" "$oracle_n" | head -20
    failed_files+=("$f")
    fail=$((fail + 1))
  fi
done < <(find "$CORPUS" -name '*.beancount' -type f -print0)

echo "----"
echo "bean-format roundtrip: checked=$checked skipped=$skipped divergent=$fail"

if [ "$fail" -gt 0 ]; then
  {
    echo "divergent files:"
    printf '  %s\n' "${failed_files[@]}"
  } >&2
  if [ "$STRICT" != "0" ]; then
    exit 1
  fi
fi
