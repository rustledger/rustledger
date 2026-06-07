#!/usr/bin/env bash
# Sync guard for compat-treesitter.sh — verify the three
# directive-kind lists stay aligned:
#
#   1. `directive_kind_label` match arms in
#      crates/rustledger-parser/examples/dump_top_level_directives.rs
#   2. `(<name>) @directive` lines in scripts/compat-treesitter.sh's
#      tree-sitter query (TS_QUERY_FILE heredoc)
#   3. `kinds=(...)` bash array in scripts/compat-treesitter.sh
#      (decoder for tree-sitter pattern indices)
#
# The three lists MUST be exactly equal (same set of names, in the
# same order — query indices feed `${kinds[i]}` and the example's
# label is the source-of-truth). This script fails fast when any
# pair diverges.
#
# Run on-demand or wire into pre-push / CI. Exit code 0 on sync,
# non-zero on drift.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
DUMP_EXAMPLE="${REPO_ROOT}/crates/rustledger-parser/examples/dump_top_level_directives.rs"
COMPAT_SCRIPT="${REPO_ROOT}/scripts/compat-treesitter.sh"

# Extract the labels from `directive_kind_label`'s match arms:
# lines like `        SyntaxKind::OPEN_DIRECTIVE => Some("open"),`
# capture group 1 = the label.
example_labels="$(
  grep -oE 'Some\("[a-z_]+"\)' "${DUMP_EXAMPLE}" \
    | grep -oE '"[a-z_]+"' \
    | tr -d '"'
)"

# Extract the query-side `(kind)` names from the heredoc block.
query_kinds="$(
  awk '/<<.EOF/{flag=1; next} /^EOF/{flag=0} flag' "${COMPAT_SCRIPT}" \
    | grep -oE '\([a-z_]+\) @directive' \
    | grep -oE '\([a-z_]+\)' \
    | tr -d '()'
)"

# Extract the bash decoder array entries (space-separated, possibly
# across continuation lines).
bash_kinds="$(
  awk '/^  kinds=\(/{flag=1} flag {print} /\)$/{flag=0}' "${COMPAT_SCRIPT}" \
    | sed -e 's/^  kinds=(//' -e 's/)$//' -e 's/\\$//' \
    | tr -s ' \n' '\n' \
    | grep -v '^$'
)"

# Compare. Pretty-print all 3 lists side by side so divergence is
# easy to spot.
if [ "${example_labels}" = "${query_kinds}" ] \
   && [ "${query_kinds}" = "${bash_kinds}" ]; then
  count="$(echo "${example_labels}" | wc -l)"
  echo "OK — ${count} directive kinds in sync across all 3 sources"
  exit 0
fi

echo "DRIFT detected between compat-treesitter sources:" >&2
echo >&2
echo "--- directive_kind_label (example) ---" >&2
echo "${example_labels}" >&2
echo >&2
echo "--- (kind) @directive (query)        ---" >&2
echo "${query_kinds}" >&2
echo >&2
echo "--- kinds=(...) (bash decoder)        ---" >&2
echo "${bash_kinds}" >&2
echo >&2
echo "All three lists must contain the same names in the same" >&2
echo "order. Tree-sitter pattern indices flow query → kinds → diff." >&2
exit 1
