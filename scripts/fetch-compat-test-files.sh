#!/usr/bin/env bash
set -e

# Fetch Beancount Test Files from Multiple Sources
# Run inside: nix develop --command ./scripts/fetch-compat-test-files.sh
#
# This script downloads .beancount files from various open source projects
# to create a comprehensive compatibility test suite.
#
# Target: 800+ unique beancount files from 70+ diverse sources (after deduplication)

DEST="tests/compatibility/files"
TMPDIR="/tmp/beancount-fetch-$$"

# Per-repo clone failures are tolerated (each repo is a best-effort
# source), but we surface stderr and count failures so a substantially
# broken fetch doesn't silently produce a partial corpus. The parser-
# baseline workflow's corpus-floor (manifest entries minus slack=50)
# catches partial fetches downstream; this counter catches them HERE
# with a more actionable diagnostic.
FETCH_FAILURES=0
# Above this many clone failures the script gives up. Keeps a single
# transient network blip from masquerading as success while still
# catching a half-broken auth or rate-limit storm.
MAX_FETCH_FAILURES=15

echo "=== Fetching Beancount Test Files ==="
echo ""

mkdir -p "$TMPDIR"
mkdir -p "$DEST"

cleanup() {
  rm -rf "$TMPDIR"
}
trap cleanup EXIT

# Helper function to fetch and extract beancount files.
# Clone failures are tolerated per repo (each source is best-effort)
# but stderr is NOT silenced — see the FETCH_FAILURES counter at the
# top of the script for the abort threshold. `cp` failures are also
# surfaced (silently dropping a per-file copy can produce a partial
# corpus, which is exactly what the baseline gate is trying to
# detect upstream).
fetch_repo() {
  local name="$1"
  local repo="$2" # GitHub repo in "owner/repo" format
  local branch="${3:-}"
  local subdir="$DEST/$name"

  mkdir -p "$subdir"
  echo "Fetching $name..."

  local clone_args=(-- --depth=1)
  if [ -n "$branch" ]; then
    clone_args+=(--branch="$branch")
  fi

  if ! gh repo clone "$repo" "$TMPDIR/$name" "${clone_args[@]}"; then
    echo "  Warning: Failed to clone $name (see stderr above)"
    FETCH_FAILURES=$((FETCH_FAILURES + 1))
    if [ "$FETCH_FAILURES" -ge "$MAX_FETCH_FAILURES" ]; then
      echo ""
      echo "ERROR: $FETCH_FAILURES clone failures reached the abort threshold ($MAX_FETCH_FAILURES)." >&2
      echo "Check gh auth status, network, and rate limits before retrying." >&2
      exit 1
    fi
    return 0
  fi

  # Find and copy all .beancount files, preserving some path info in filename
  find "$TMPDIR/$name" -name "*.beancount" -type f | while read -r f; do
    # Create a unique filename based on relative path
    relpath="${f#$TMPDIR/$name/}"
    safename=$(echo "$relpath" | tr '/' '_')
    if ! cp "$f" "$subdir/$safename"; then
      echo "  Warning: failed to copy $relpath" >&2
    fi
  done

  count=$(find "$subdir" -name "*.beancount" | wc -l | tr -d ' ')
  echo "  Found $count files"
}

# 1. beancount v2 - most comprehensive test data
# Skip beancount v2 - uses plugins removed in v3
# fetch_repo "beancount-v2" "beancount/beancount" "v2"

# 2. beancount v3
fetch_repo "beancount-v3" "beancount/beancount" "v3"

# 2b. beancount v1 (legacy, may have different test cases)
fetch_repo "beancount-v1" "beancount/beancount" "v1"

# 3. fava - web interface with test data
fetch_repo "fava" "beancount/fava"

# 4. beangulp - importer framework
fetch_repo "beangulp" "beancount/beangulp"

# 5. ledger2beancount - conversion tool tests
fetch_repo "ledger2beancount" "beancount/ledger2beancount"

# 6. beancount-import - import web UI
fetch_repo "beancount-import" "jbms/beancount-import"

# 7. LaunchPlatform parser - standalone parser tests
fetch_repo "launchplatform" "LaunchPlatform/beancount-parser"

# 8. smart_importer - ML importers
fetch_repo "smart-importer" "beancount/smart_importer"

# 9. beancount_reds_importers
fetch_repo "reds-importers" "redstreet/beancount_reds_importers"

# 10. Community examples
fetch_repo "community-wileykestner" "wileykestner/beancount-example"

# 11. Parser Lima - comprehensive parser test suite (246 files)
fetch_repo "parser-lima" "tesujimath/beancount-parser-lima"

# 12. Fava Investor - investment tracking plugin
fetch_repo "fava-investor" "redstreet/fava_investor"

# 13. Fava Dashboards
fetch_repo "fava-dashboards" "andreasgerstmayr/fava-dashboards"

# 14. Beancern (tariochbctools)
fetch_repo "beancern" "tarioch/beancern"

# 15. double-entry-generator - Chinese accounting tool
fetch_repo "double-entry-generator" "deb-sig/double-entry-generator"

# 16. beanahead - forward-looking beancount entries
fetch_repo "beanahead" "maread99/beanahead"

# 17. beancount-boilerplate-cn - Chinese beancount examples
fetch_repo "beancount-boilerplate-cn" "mckelvin/beancount-boilerplate-cn"

# 18. gnucash-to-beancount converter tests
fetch_repo "gnucash-to-beancount" "andrewstein/gnucash-to-beancount"

# === Official Beancount Org ===
fetch_repo "beancount2ledger" "beancount/beancount2ledger"
fetch_repo "beangrow" "beancount/beangrow"
fetch_repo "fava-plugins" "beancount/fava-plugins"

# === Plugins ===
fetch_repo "autobean" "SEIAROTg/autobean"
fetch_repo "beancount-lazy-plugins" "Evernight/beancount-lazy-plugins"
fetch_repo "beancount-plugins-metadata" "seltzered/beancount-plugins-metadata-spray"
fetch_repo "beancount-portfolio-alloc" "ghislainbourgeois/beancount_portfolio_allocation"
fetch_repo "reds-plugins" "redstreet/beancount_reds_plugins"
fetch_repo "michaelbull-plugins" "michaelbull/beancount-plugins"
fetch_repo "davidastephens-plugins" "davidastephens/beancount-plugins"
fetch_repo "fkarg-plugins" "fkarg/beancount-plugins"

# === Fava Extensions ===
fetch_repo "fava-envelope" "polarmutex/fava-envelope"
fetch_repo "fava-portfolio-returns" "andreasgerstmayr/fava-portfolio-returns"
fetch_repo "fava-portfolio-summary" "PhracturedBlue/fava-portfolio-summary"
fetch_repo "fava-classy-portfolio" "seltzered/fava-classy-portfolio"
fetch_repo "fava-tax-loss" "redstreet/fava_tax_loss_harvester"
fetch_repo "fava-budget-freedom" "Leon2xiaowu/fava_budget_freedom"

# === Importers - Germany ===
fetch_repo "beancount-commerzbank" "siddhantgoel/beancount-commerzbank"
fetch_repo "beancount-dkb" "siddhantgoel/beancount-dkb"
fetch_repo "beancount-ing" "siddhantgoel/beancount-ing"
fetch_repo "beancount-n26" "siddhantgoel/beancount-n26"
fetch_repo "beancount-volksbank" "Fjanks/beancount-importer-volksbank"

# === Importers - France ===
fetch_repo "beancount-ce" "ArthurFDLR/beancount-ce"
fetch_repo "beancount-mytools" "grostim/Beancount-myTools"
fetch_repo "vrischmann-importers" "vrischmann/beancount-importers"

# === Importers - India ===
fetch_repo "beancount-india" "dumbPy/beancount-importers-india"
fetch_repo "prabusw-india" "prabusw/beancount-importers-india"

# === Importers - Netherlands ===
fetch_repo "beancount-abnamro" "deepakg/beancount-abnamro"

# === Importers - Switzerland ===
fetch_repo "beancounttools" "tarioch/beancounttools"
fetch_repo "drnuke-bean" "Dr-Nuke/drnuke-bean"

# === Importers - UK ===
fetch_repo "evernight-importers" "Evernight/beancount-importers"

# === Importers - US ===
fetch_repo "beancount-capitalone" "mtlynch/beancount-capitalone"
fetch_repo "beancount-chase-bank" "mtlynch/beancount-chase-bank"
fetch_repo "beancount-chase" "ArthurFDLR/beancount-chase"
fetch_repo "beancount-mercury" "mtlynch/beancount-mercury"

# === Converters ===
fetch_repo "csv2beancount" "PaNaVTEC/csv2beancount"
fetch_repo "henriquebastos-gnucash" "henriquebastos/gnucash-to-beancount"
fetch_repo "dtrai2-gnucash" "dtrai2/gnucash-to-beancount"
fetch_repo "glasserc-ledger" "glasserc/ledger-to-beancount"
fetch_repo "quicken2beancount" "mortisj/quicken2beancount"

# === Tools ===
fetch_repo "beancount-black" "LaunchPlatform/beancount-black"
fetch_repo "beancount-categorizer" "bratekarate/beancount-categorizer"
fetch_repo "lazy-beancount" "Evernight/lazy-beancount"
fetch_repo "beancount-ynab" "hoostus/beancount-ynab"

# === Bots/UI ===
fetch_repo "beancount-bot-tg" "LucaBernstein/beancount-bot-tg"
fetch_repo "beancount-telegram-bot" "blinkstu/beancount-telegram-bot"
fetch_repo "beancount-mobile" "xuhcc/beancount-mobile"

# === Editor/Language Support ===
fetch_repo "beancount-language-server" "polarmutex/beancount-language-server"
fetch_repo "tree-sitter-beancount" "polarmutex/tree-sitter-beancount"
fetch_repo "vscode-beancount" "Lencerf/vscode-beancount"
fetch_repo "vim-beancount" "nathangrigg/vim-beancount"

# === Examples/Tutorials ===
fetch_repo "awesome-beancount-wzyboy" "wzyboy/awesome-beancount"
fetch_repo "awesome-beancount-siddhant" "siddhantgoel/awesome-beancount"
fetch_repo "donearm-ledger" "Donearm/ledger"

# === Misc ===
fetch_repo "jbeancount" "jbeancount/jbeancount"
fetch_repo "beanpost" "gerdemb/beanpost"
fetch_repo "portfolio-returns" "hoostus/portfolio-returns"

# === Alternative Parsers/Implementations ===
fetch_repo "twilco-beancount" "twilco/beancount"
fetch_repo "jcornaz-parser" "jcornaz/beancount-parser"
fetch_repo "intellij-beancount" "Ramblurr/intellij-beancount"
fetch_repo "jord1e-jbeancount" "jord1e/jbeancount"

# === More Official ===
fetch_repo "beanprice" "beancount/beanprice"
fetch_repo "finance-dl" "jbms/finance-dl"

# === Chinese Tools ===
fetch_repo "beancount-gs" "BaoXuebin/beancount-gs"
fetch_repo "beancount-chinese-manual" "maonx/Beancount-Chinese-User-Manual"
fetch_repo "homemade-importers" "heyeshuang/beancount-homemade-importers"

# === More Community ===
fetch_repo "beancount-mode" "beancount/beancount-mode"
fetch_repo "sublime-beancount" "norseghost/sublime-beancount"
fetch_repo "zed-beancount" "zed-extensions/beancount"
fetch_repo "beancount-exporter" "LaunchPlatform/beancount-exporter"
fetch_repo "beanhub-forms" "LaunchPlatform/beanhub-forms"
fetch_repo "beanhub-web-react" "LaunchPlatform/beanhub-web-react"
fetch_repo "beancount-extract" "LaunchPlatform/beancount-extract"
fetch_repo "beancount-exchangerates" "xuhcc/beancount-exchangerates"
fetch_repo "beancount-cryptoassets" "xuhcc/beancount-cryptoassets"

# === Forks with Test Data ===
fetch_repo "iocoop-beancount" "iocoop/beancount"
fetch_repo "beancount-valuation" "Evernight/beancount-valuation"

# === More Converters ===
fetch_repo "ofxtools" "csingley/ofxtools"
fetch_repo "beancount-bot" "StdioA/beancount-bot"
fetch_repo "zhangzhishan-importer" "zhangzhishan/beancount_importer"

# === More Regional Importers ===
fetch_repo "jamatute-importer" "jamatute/beancount-importer"
fetch_repo "balancechange" "daniel-wells/beancount_balancechange"
fetch_repo "beancount-balexpr" "w1ndy/beancount_balexpr"
fetch_repo "checkclosed" "daniel-wells/beancount_checkclosed"

# === More LSP/Editor Tools ===
fetch_repo "fengkx-lsp" "fengkx/beancount-lsp"
fetch_repo "matze-ls" "matze/beancount-language-server"
fetch_repo "vscode-beancount-langserver" "polarmutex/vscode-beancount-langserver"
fetch_repo "beanquery-mcp" "vanto/beanquery-mcp"

# === More from GitHub Topics ===
fetch_repo "beancount-fava-gtk" "johannesjh/fava-gtk"
fetch_repo "autobean-format" "SEIAROTg/autobean-format"
fetch_repo "autobean-refactor" "SEIAROTg/autobean-refactor"

# === From GitHub Code Search ===
fetch_repo "beanbot" "dumbPy/beanbot"
fetch_repo "pynomina" "WolfgangFahl/pynomina"
fetch_repo "beancount-blog-examples" "LalitMaganti/beancount-blog-examples"
fetch_repo "beancount-staging" "jakobhellermann/beancount-staging"
fetch_repo "pinto-reports" "sjoblomj/pinto-reports"
fetch_repo "portfolio-eidorb" "eidorb/portfolio"
fetch_repo "apyb-financeiro" "apyb/financeiro"
fetch_repo "cookbook-beancount-llm" "David-Barnes-Data-Imaginations/cookbook-beancount-llm"

# === Fix short plugin names ===
# Some test files use short plugin names that only work in specific Python environments.
# Replace them with full module paths for compatibility testing.
echo ""
echo "=== Fixing short plugin names ==="

# Fix beancount_reds_plugins capital_gains_classifier short names
find "$DEST" -name "*.beancount" -type f -exec grep -l 'plugin "gain_loss"' {} \; 2>/dev/null | while read -r file; do
  sed -i 's/plugin "gain_loss"/plugin "beancount_reds_plugins.capital_gains_classifier.gain_loss"/' "$file"
  echo "  Fixed: $(basename "$file")"
done

find "$DEST" -name "*.beancount" -type f -exec grep -l 'plugin "long_short"' {} \; 2>/dev/null | while read -r file; do
  sed -i 's/plugin "long_short"/plugin "beancount_reds_plugins.capital_gains_classifier.long_short"/' "$file"
  echo "  Fixed: $(basename "$file")"
done

# Fix beanahead rx_txn_plugin short name
find "$DEST" -name "*.beancount" -type f -exec grep -l 'plugin "rx_txn_plugin"' {} \; 2>/dev/null | while read -r file; do
  sed -i 's/plugin "rx_txn_plugin"/plugin "beanahead.plugins.rx_txn_plugin"/' "$file"
  echo "  Fixed: $(basename "$file")"
done

# Fix plugins.redstreet.zerosum path to beancount_reds_plugins.zerosum
find "$DEST" -name "*.beancount" -type f -exec grep -l 'plugins.redstreet.zerosum' {} \; 2>/dev/null | while read -r file; do
  sed -i 's/plugins\.redstreet\.zerosum/beancount_reds_plugins.zerosum/' "$file"
  echo "  Fixed: $(basename "$file")"
done

# === Deduplication ===
# Remove duplicate files based on content hash to avoid testing the same content twice
echo ""
echo "=== Deduplicating files by content hash ==="

# Build hash index: hash -> first file with that hash
declare -A seen_hashes
duplicates_removed=0

# Process all .beancount files
while IFS= read -r -d '' file; do
  hash=$(sha256sum "$file" | cut -d' ' -f1)
  if [[ -n ${seen_hashes[$hash]:-} ]]; then
    # Duplicate found - remove it
    rm "$file"
    duplicates_removed=$((duplicates_removed + 1))
  else
    seen_hashes[$hash]="$file"
  fi
done < <(find "$DEST" -name "*.beancount" -type f -print0 | sort -z)

echo "  Removed $duplicates_removed duplicate files"

# Summary
echo ""
echo "=== Summary ==="
echo ""

total=0
for dir in "$DEST"/*/; do
  if [ -d "$dir" ]; then
    count=$(find "$dir" -name "*.beancount" | wc -l | tr -d ' ')
    dirname=$(basename "$dir")
    printf "  %-25s %4d files\n" "$dirname:" "$count"
    total=$((total + count))
  fi
done

# Also count top-level files
top_count=$(find "$DEST" -maxdepth 1 -name "*.beancount" | wc -l | tr -d ' ')
if [ "$top_count" -gt 0 ]; then
  printf "  %-25s %4d files\n" "(top-level):" "$top_count"
  total=$((total + top_count))
fi

echo ""
echo "Total: $total beancount files"
if [ "$FETCH_FAILURES" -gt 0 ]; then
  echo "Note: $FETCH_FAILURES repository clone(s) failed (under the abort threshold of $MAX_FETCH_FAILURES). The corpus may be slightly smaller than usual."
fi
echo ""
echo "Files saved to: $DEST"
