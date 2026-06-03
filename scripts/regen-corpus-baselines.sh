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

if [ ! -d tests/compatibility/files ] || [ -z "$(find tests/compatibility/files -name '*.beancount' -print -quit)" ]; then
  echo "error: compat corpus is empty. Run scripts/fetch-compat-test-files.sh first." >&2
  echo "       (Without it the regenerated manifest would only cover the 3 in-tree fixtures." >&2
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
