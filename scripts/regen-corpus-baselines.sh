#!/usr/bin/env bash
# Regenerate the parser-output and formatter-output baseline manifests
# under tests/baselines/.
#
# When to run:
#   - An intentional parser change shifts output bytes on some corpus
#     files. CI's baseline gate fails; you regenerate, review the diff,
#     and commit.
#   - The compat corpus changes (a new source added to
#     scripts/fetch-compat-test-files.sh). The new files have no
#     baseline yet; you regenerate, review, and commit.
#
# When NOT to run:
#   - Casually before commit, "to make CI green." The whole point of
#     the baseline is to catch unexpected output drift. If the baseline
#     is failing, look at the diff before regenerating.
#
# See tests/baselines/README.md for the full contract.

set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

# Require a meaningfully-populated corpus before regenerating. The
# repo commits 3 in-tree plugin fixtures, so a plain non-empty check
# would let regen proceed on a fresh checkout, overwriting the
# committed multi-hundred-entry manifests with 3-entry versions and
# silently zeroing out the baseline gate.
#
# 100 matches the minimum the test/CI workflow uses; well below the
# real corpus size (~700) so partial fetches still trigger this guard.
MIN_CORPUS_SIZE=100

if [ ! -d tests/compatibility/files ]; then
  echo "error: tests/compatibility/files/ does not exist." >&2
  echo "       Run scripts/fetch-compat-test-files.sh first." >&2
  exit 1
fi

# Deliberately do NOT swallow find's stderr (memory rule: never use
# 2>/dev/null). Two failure paths to be precise about under
# `set -euo pipefail`:
# - find itself fails (permission denied on a subdir, stale FUSE
#   mount): pipefail propagates the non-zero exit, the `$(...)`
#   assignment fails, and `set -e` aborts the script here. The user
#   sees find's stderr explaining what broke. Good.
# - find succeeds, prints zero matches: corpus_size=0, falls through
#   to the explicit error below. Good.
# Either way the user gets an actionable diagnostic; the silencer
# would have collapsed both into a confusing "0 files" message.
corpus_size=$(find tests/compatibility/files -name '*.beancount' | wc -l)

if [ "$corpus_size" -lt "$MIN_CORPUS_SIZE" ]; then
  echo "error: compat corpus has $corpus_size .beancount files (need at least $MIN_CORPUS_SIZE)." >&2
  echo "       Run scripts/fetch-compat-test-files.sh first; without the full corpus" >&2
  echo "       the regenerated manifest would only cover a tiny subset and would" >&2
  echo "       overwrite the committed manifests." >&2
  exit 1
fi

echo "=== Regenerating parser-output baseline ==="
BASELINE_UPDATE=1 cargo test -p rustledger-parser --test corpus_baseline parser_output_matches_baseline

echo ""
echo "=== Regenerating formatter-output baseline ==="
BASELINE_UPDATE=1 cargo test -p rustledger-parser --test corpus_baseline_format formatter_output_matches_baseline

echo ""
echo "Done. Review the diff:"
echo "  git diff tests/baselines/"
echo ""
echo "If the diff looks correct, stage and commit:"
echo "  git add tests/baselines/"
echo "  git commit -m 'chore(baselines): regenerate parser+format manifests'"
