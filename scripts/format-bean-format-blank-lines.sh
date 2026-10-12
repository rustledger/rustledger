#!/usr/bin/env bash
# bean-format blank-line agreement check (#2506).
#
# `rledger format` must keep the author's blank lines exactly where
# bean-format keeps them: between directives, around comments, and at the
# very start and end of a file. The roundtrip check
# (scripts/format-bean-format-roundtrip.sh) cannot see this. It compares
# bean-format(rledger format(x)) against rledger format(x), so a blank line
# rledger deleted is gone from both sides. This check is anchored on the
# INPUT instead: it formats x with both tools and compares where the blank
# lines fall.
#
# What is compared is the "blank-line shape": each run of blank lines
# (lines with no non-whitespace character), with every run of non-blank
# lines between them collapsed to one marker. So alignment, number
# formatting and a tag line rledger splits in two do not count; a blank line
# added, dropped or moved does.
#
# Usage:   scripts/format-bean-format-blank-lines.sh [CORPUS_DIR]
# Env:     RLEDGER     path to the rledger binary (default ./target/release/rledger)
#          BEANFORMAT  bean-format command (default: bean-format on PATH)
#          STRICT      if "0", report divergences but exit 0 (default: strict)
#
# `-e` is intentionally omitted, as in the sibling format scripts: the loop
# must survive per-file tool failures and report rather than abort.
set -uo pipefail

RLEDGER="${RLEDGER:-./target/release/rledger}"
BEANFORMAT="${BEANFORMAT:-bean-format}"
CORPUS="${1:-tests/compatibility/files}"
STRICT="${STRICT:-1}"

# Files whose difference is not about blank lines, with the reason.
ALLOW=(
  # The whole file is one tab with no newline. bean-format echoes it;
  # rledger drops trailing whitespace, and with no newline there is no
  # line left to keep.
  "parser-lima/test-cases_ParserComplete.IndentEOF.beancount"
)

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

ours=$(mktemp) || { echo "error: mktemp failed" >&2; exit 2; }
theirs=$(mktemp) || { echo "error: mktemp failed" >&2; exit 2; }
trap 'rm -f "$ours" "$theirs"' EXIT

shape() {
  awk '{ if ($0 ~ /^[[:space:]]*$/) print "B"; else print "L" }' "$1" \
    | uniq -c | awk '$2 == "L" { print "L"; next } { print $1 "B" }'
}

allowed() {
  local f=$1 a
  for a in "${ALLOW[@]}"; do
    [[ "$f" == *"/$a" ]] && return 0
  done
  return 1
}

checked=0
skipped=0
allowed_n=0
fail=0
failed_files=()

while IFS= read -r -d '' f; do
  if ! "$RLEDGER" format "$f" >"$ours" 2>/dev/null; then
    skipped=$((skipped + 1))
    continue
  fi
  if ! "$BEANFORMAT" "$f" >"$theirs" 2>/dev/null; then
    skipped=$((skipped + 1))
    continue
  fi
  checked=$((checked + 1))
  if ! cmp -s <(shape "$ours") <(shape "$theirs"); then
    if allowed "$f"; then
      allowed_n=$((allowed_n + 1))
      continue
    fi
    echo "FAIL (blank lines differ from bean-format): $f"
    diff <(shape "$ours") <(shape "$theirs") | head -10
    failed_files+=("$f")
    fail=$((fail + 1))
  fi
done < <(find "$CORPUS" -name '*.beancount' -type f -print0)

echo "----"
echo "bean-format blank lines: checked=$checked skipped=$skipped allowlisted=$allowed_n divergent=$fail"

if [ "$fail" -gt 0 ]; then
  {
    echo "divergent files:"
    printf '  %s\n' "${failed_files[@]}"
  } >&2
  if [ "$STRICT" != "0" ]; then
    exit 1
  fi
fi
