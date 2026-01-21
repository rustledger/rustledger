#!/usr/bin/env bash
set -e

# Fetch Beancount Test Files from Multiple Sources
# Run inside: nix develop --command ./scripts/fetch-compat-test-files.sh
#
# This script downloads .beancount files from various open source projects
# to create a comprehensive compatibility test suite.
#
# Target: ~800+ real beancount files from diverse sources

DEST="tests/compat-full"
TMPDIR="/tmp/beancount-fetch-$$"

echo "=== Fetching Beancount Test Files ==="
echo ""

mkdir -p "$TMPDIR"
mkdir -p "$DEST"

cleanup() {
    rm -rf "$TMPDIR"
}
trap cleanup EXIT

# Helper function to fetch and extract beancount files
fetch_repo() {
    local name="$1"
    local url="$2"
    local branch="${3:-}"
    local subdir="$DEST/$name"
    
    mkdir -p "$subdir"
    echo "Fetching $name..."
    
    if [ -n "$branch" ]; then
        git clone --depth=1 --branch="$branch" "$url" "$TMPDIR/$name" 2>/dev/null || {
            echo "  Warning: Failed to clone $name (branch: $branch)"
            return 0
        }
    else
        git clone --depth=1 "$url" "$TMPDIR/$name" 2>/dev/null || {
            echo "  Warning: Failed to clone $name"
            return 0
        }
    fi
    
    # Find and copy all .beancount files, preserving some path info in filename
    find "$TMPDIR/$name" -name "*.beancount" -type f | while read -r f; do
        # Create a unique filename based on relative path
        relpath="${f#$TMPDIR/$name/}"
        safename=$(echo "$relpath" | tr '/' '_')
        cp "$f" "$subdir/$safename" 2>/dev/null || true
    done
    
    count=$(find "$subdir" -name "*.beancount" | wc -l | tr -d ' ')
    echo "  Found $count files"
}

# 1. beancount v2 - most comprehensive test data
fetch_repo "beancount-v2" "https://github.com/beancount/beancount" "v2"

# 2. beancount v3
fetch_repo "beancount-v3" "https://github.com/beancount/beancount" "v3"

# 3. fava - web interface with test data
fetch_repo "fava" "https://github.com/beancount/fava"

# 4. beangulp - importer framework
fetch_repo "beangulp" "https://github.com/beancount/beangulp"

# 5. ledger2beancount - conversion tool tests
fetch_repo "ledger2beancount" "https://github.com/beancount/ledger2beancount"

# 6. beancount-import - import web UI
fetch_repo "beancount-import" "https://github.com/jbms/beancount-import"

# 7. LaunchPlatform parser - standalone parser tests
fetch_repo "launchplatform" "https://github.com/LaunchPlatform/beancount-parser"

# 8. smart_importer - ML importers
fetch_repo "smart-importer" "https://github.com/beancount/smart_importer"

# 9. beancount_reds_importers
fetch_repo "reds-importers" "https://github.com/redstreet/beancount_reds_importers"

# 10. Community examples
fetch_repo "community-wileykestner" "https://github.com/wileykestner/beancount-example"

# Copy existing curated files
if [ -d "tests/compat/files" ]; then
    echo "Copying existing curated files..."
    cp -r tests/compat/files/* "$DEST/" 2>/dev/null || true
fi

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
echo ""
echo "Files saved to: $DEST"
