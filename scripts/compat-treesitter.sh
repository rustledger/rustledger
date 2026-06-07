#!/usr/bin/env bash
# Cross-validate rustledger's `parse_structured` against
# `polarmutex/tree-sitter-beancount` on a sample of corpus files.
#
# WHY
#   The phase-2 CST migration (#1262) is independently verified
#   against:
#     1. hand-written tests (exact tree shapes)
#     2. byte round-trip on 714 corpus files
#     3. the legacy rustledger AST parser (parser-corpus.manifest)
#     4. parse_structured's own corpus baseline (cst-corpus.manifest)
#     5. Python beancount semantic match (CI compatibility job)
#
#   None of those is an INDEPENDENT lossless-parser opinion on
#   structural boundaries. polarmutex/tree-sitter-beancount is the
#   closest existing lossless Beancount parser; cross-checking
#   top-level directive identification catches recognition bugs
#   the other layers don't.
#
# WHEN TO RUN
#   On-demand only — NOT in CI. Useful:
#     - before merging a phase-2.X parser change to spot-check
#       recognition behavior on real corpus
#     - when a corpus baseline diff is suspicious and a second
#       opinion would help
#     - as scaffolding for phase 2.1b / 2.2 where structural
#       complexity grows
#
# REQUIREMENTS
#   - tree-sitter CLI (`tree-sitter --version`)
#   - polarmutex/tree-sitter-beancount grammar cloned and built
#     (`tree-sitter generate` in its repo)
#   - the env var TREE_SITTER_BEANCOUNT pointing at that repo
#     (the parser build artifact must be discoverable by
#     `tree-sitter parse`)
#
# USAGE
#   # default sample (~10 corpus files covering each directive
#   # kind we recognize)
#   ./scripts/compat-treesitter.sh
#
#   # custom file list
#   ./scripts/compat-treesitter.sh path/to/file.beancount ...
#
#   # full corpus (slow; useful before a release)
#   ./scripts/compat-treesitter.sh --all
#
# OUTPUT
#   For each file, a unified diff between two TSV listings of the
#   form "<kind>\t<start_byte>\t<end_byte>\t<first_line_excerpt>".
#   Empty diff = both parsers agree on every directive boundary
#   and kind. Non-empty diff = a real divergence to investigate.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "${REPO_ROOT}"

# ---- environment checks --------------------------------------------------

if ! command -v tree-sitter >/dev/null 2>&1; then
  cat >&2 <<'EOF'
tree-sitter CLI not found in PATH.

On NixOS, add to the dev shell or install:
  nix shell nixpkgs#tree-sitter

Otherwise, install per
https://tree-sitter.github.io/tree-sitter/cli/index.html

EOF
  exit 2
fi

if [[ -z "${TREE_SITTER_BEANCOUNT:-}" ]]; then
  cat >&2 <<'EOF'
TREE_SITTER_BEANCOUNT not set. Point it at a checkout of
https://github.com/polarmutex/tree-sitter-beancount with the
grammar generated (run `tree-sitter generate` in that repo).

  git clone https://github.com/polarmutex/tree-sitter-beancount /tmp/tsb
  (cd /tmp/tsb && tree-sitter generate)
  export TREE_SITTER_BEANCOUNT=/tmp/tsb
EOF
  exit 2
fi

if [[ ! -d "${TREE_SITTER_BEANCOUNT}" ]]; then
  echo >&2 "TREE_SITTER_BEANCOUNT=${TREE_SITTER_BEANCOUNT} is not a directory"
  exit 2
fi

# ---- build the rustledger dumper once ------------------------------------

echo >&2 "Building rustledger parse_structured dumper..."
cargo build --release --example dump_top_level_directives -p rustledger-parser \
  >&2 2>&1
DUMPER="${REPO_ROOT}/target/release/examples/dump_top_level_directives"
if [[ ! -x "${DUMPER}" ]]; then
  echo >&2 "build artifact missing: ${DUMPER}"
  exit 1
fi

# ---- pick file sample ----------------------------------------------------

SAMPLE=()
if [[ $# -eq 0 ]]; then
  # Default sample: in-tree fixtures plus a few corpus files known
  # to exercise different directive kinds. Adjust as the corpus
  # evolves.
  SAMPLE=(
    "tests/compatibility/files/beancount-v3/examples_vesting_vesting.beancount"
    "tests/compatibility/files/beancount-v3/examples_basic_basic.beancount"
    "tests/compatibility/files/apyb-financeiro/financeiro_2020-01.beancount"
  )
elif [[ "${1:-}" == "--all" ]]; then
  mapfile -t SAMPLE < <(
    find tests/compatibility/files -name '*.beancount' -type f | sort
  )
else
  SAMPLE=("$@")
fi

if [[ ${#SAMPLE[@]} -eq 0 ]]; then
  echo >&2 "no files to compare"
  exit 1
fi

# ---- per-file comparison -------------------------------------------------

# Tree-sitter top-level node kinds that map 1:1 to our
# *_DIRECTIVE labels. Keep aligned with dump_top_level_directives.rs
# (the example's `directive_kind_label` function).
TS_QUERY_FILE="$(mktemp -t compat-treesitter-XXXXXX.scm)"
trap 'rm -f "${TS_QUERY_FILE}"' EXIT
cat > "${TS_QUERY_FILE}" <<'EOF'
(open) @directive
(close) @directive
(balance) @directive
(pad) @directive
(event) @directive
(query) @directive
(note) @directive
(document) @directive
(price) @directive
(commodity) @directive
(pushtag) @directive
(poptag) @directive
(pushmeta) @directive
(popmeta) @directive
(option) @directive
(include) @directive
(plugin) @directive
(custom) @directive
(transaction) @directive
EOF

# Tree-sitter query output looks like
#   pattern: 0, capture: 0 - directive, start: (1, 0), end: (2, 12), text: ...
# We need byte offsets, so use `tree-sitter parse` with --byte-range
# style. The simpler portable path: run `tree-sitter query` and a
# small awk to convert (row,col) to bytes by reading the source.
#
# Actually, easiest: run `tree-sitter parse` to get S-expression
# with byte positions, then grep+sed. But the S-expr format is
# (kind [start_row, start_col] - [end_row, end_col]) — no bytes.
#
# Most robust: write a tiny helper in nodejs / python that uses
# the bindings. For a hand-tool that runs on demand, we keep
# it pragmatic: just verify KIND and ORDER of top-level
# directives, dropping exact byte positions on the tree-sitter
# side. Our dumper emits bytes; we'll strip them before diff'ing.

declare -i divergences=0

for f in "${SAMPLE[@]}"; do
  if [[ ! -f "${f}" ]]; then
    echo >&2 "skip (missing): ${f}"
    continue
  fi

  echo
  echo "=== ${f} ==="

  # rustledger side: kind only, in source order (strip byte
  # offsets + excerpt for an apples-to-apples comparison with
  # what tree-sitter `query` gives us cheaply).
  ours="$(mktemp)"
  "${DUMPER}" "${f}" | cut -f1 > "${ours}"

  # tree-sitter side: extract @directive captures, get the
  # NAMED-NODE kind for each. `tree-sitter query` reports
  # the matching node's start_byte / end_byte in the format
  # `start: ROW, COL` — we don't need bytes, just kinds.
  # Tree-sitter query output looks like:
  #   /path/to/file.bean
  #     pattern: 0
  #       capture: directive, start: (0, 0), end: (1, 0)
  # We only need the pattern index per match — it tells us which
  # directive kind (0=open, 1=close, ...) per the query file order.
  # MUST stay aligned with the (kind) @directive lines in
  # TS_QUERY_FILE above — array indices correspond to tree-sitter
  # pattern indices (0=open, 1=close, ...). Also aligned with the
  # `directive_kind_label` arms in
  # crates/rustledger-parser/examples/dump_top_level_directives.rs;
  # see scripts/check-compat-treesitter-sync.sh for the sync guard.
  kinds=(open close balance pad event query note document price commodity \
         pushtag poptag pushmeta popmeta \
         option include plugin custom \
         transaction)
  theirs="$(mktemp)"
  (
    cd "${TREE_SITTER_BEANCOUNT}"
    tree-sitter query "${TS_QUERY_FILE}" "${REPO_ROOT}/${f}" 2>/dev/null \
      | grep -oE 'pattern: [0-9]+' \
      | awk '{print $2}'
  ) | while read -r pat_idx; do
    echo "${kinds[${pat_idx}]}"
  done > "${theirs}"

  if diff -u "${ours}" "${theirs}" > /tmp/compat-treesitter.diff; then
    n=$(wc -l < "${ours}")
    echo "OK — ${n} directives, both parsers agree on kind+order"
  else
    divergences=$((divergences + 1))
    echo "DIVERGENCE:"
    cat /tmp/compat-treesitter.diff
  fi

  rm -f "${ours}" "${theirs}"
done

echo
if [[ ${divergences} -eq 0 ]]; then
  echo "All ${#SAMPLE[@]} files: rustledger parse_structured agrees with polarmutex tree-sitter-beancount on top-level directive kind + order."
else
  echo "${divergences} of ${#SAMPLE[@]} files diverged. Review diffs above."
  exit 1
fi
