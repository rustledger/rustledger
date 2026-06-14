#!/usr/bin/env bash
# Comment-preservation check (#1332).
#
# `rledger format` must never DELETE the author's comment-only LINES (a line
# whose only content is a `;`/`%` comment). Same-line *trailing* comments are
# out of scope for this count-based metric — they live on content lines, so
# they aren't counted; #1332/#1335/#1337 were all about whole comment lines
# vanishing, which is what this catches.
#
# The format idempotence and bean-format roundtrip checks both miss this
# class: a formatter that drops comments converges on a stable, self-
# consistent output (idempotence stays green), and bean-format applied to that
# already-stripped output preserves the absence (the roundtrip stays green
# too). Both compare the formatter against ITS OWN output; neither compares
# against the original input, so content loss slips through. #1332 was
# exactly this — body-internal comment lines silently deleted.
#
# The naive external-oracle alternative — `normalize(bean-format(x)) ==
# normalize(rledger format(x))` on the original `x` — is too noisy to gate
# on: rledger canonicalizes number forms (thousands separators, decimals,
# spacing) that bean-format deliberately leaves untouched, so they diverge
# on most files for reasons that have nothing to do with content loss.
#
# This check is the focused invariant instead: a comment-only line
# (`;` or `%`, optionally indented) must never be dropped by formatting.
# We count comment-only lines in the input and in `rledger format`'s output
# and fail if the output has fewer.
#
# Usage:   scripts/format-preserves-comments.sh [CORPUS_DIR]
# Env:     RLEDGER  path to the rledger binary (default ./target/release/rledger)
#          STRICT   if "0", report but exit 0 (default: strict, exit 1 on any)
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

formatted=$(mktemp) || { echo "error: mktemp failed" >&2; exit 2; }
trap 'rm -f "$formatted"' EXIT

# A comment-only line: leading whitespace then `;` or `%`.
count_comment_lines() { grep -cE '^[[:space:]]*[;%]' "$1" 2>/dev/null || true; }

checked=0
skipped=0
fail=0
failed_files=()

while IFS= read -r -d '' f; do
  if ! "$RLEDGER" format "$f" >"$formatted" 2>/dev/null; then
    skipped=$((skipped + 1))
    continue
  fi
  checked=$((checked + 1))

  before=$(count_comment_lines "$f")
  after=$(count_comment_lines "$formatted")
  if [ "$after" -lt "$before" ]; then
    echo "FAIL (dropped comments: $before -> $after): $f"
    failed_files+=("$f")
    fail=$((fail + 1))
  fi
done < <(find "$CORPUS" -name '*.beancount' -type f -print0)

echo "----"
echo "comment preservation: checked=$checked skipped=$skipped dropped_comments_in=$fail"

if [ "$fail" -gt 0 ]; then
  {
    echo "files where formatting dropped comment lines:"
    printf '  %s\n' "${failed_files[@]}"
  } >&2
  if [ "$STRICT" != "0" ]; then
    exit 1
  fi
fi
