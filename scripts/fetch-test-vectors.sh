#!/bin/bash
# fetch-test-vectors.sh
# Downloads golden test vectors from upstream sources

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
FIXTURES_DIR="$PROJECT_ROOT/spec/fixtures"

echo "=== Fetching Beancount Test Vectors ==="
echo "Target: $FIXTURES_DIR"
echo

# Create directories
mkdir -p "$FIXTURES_DIR/lima-tests"
mkdir -p "$FIXTURES_DIR/examples"
mkdir -p "$FIXTURES_DIR/python-tests"

# 1. Fetch beancount-parser-lima test cases (220 files)
echo "[1/3] Fetching beancount-parser-lima test cases..."
if [ -d "/tmp/beancount-parser-lima" ]; then
    rm -rf /tmp/beancount-parser-lima
fi

git clone --depth 1 https://github.com/tesujimath/beancount-parser-lima.git /tmp/beancount-parser-lima

cp -r /tmp/beancount-parser-lima/test-cases/* "$FIXTURES_DIR/lima-tests/"
echo "  -> Copied $(ls -1 "$FIXTURES_DIR/lima-tests" | wc -l) test files"

# 2. Fetch Python beancount examples
echo "[2/3] Fetching Python beancount examples..."
if [ -d "/tmp/beancount" ]; then
    rm -rf /tmp/beancount
fi

git clone --depth 1 --branch v2 https://github.com/beancount/beancount.git /tmp/beancount

cp -r /tmp/beancount/examples/* "$FIXTURES_DIR/examples/"
echo "  -> Copied examples directory"

# 3. Copy Python test files (for reference)
echo "[3/3] Copying Python test references..."
cp /tmp/beancount/beancount/parser/*_test.py "$FIXTURES_DIR/python-tests/" 2>/dev/null || true
echo "  -> Copied Python test files for reference"

# Cleanup
rm -rf /tmp/beancount-parser-lima /tmp/beancount

echo
echo "=== Summary ==="
echo "Lima tests:     $(find "$FIXTURES_DIR/lima-tests" -name "*.beancount" | wc -l) files"
echo "Examples:       $(find "$FIXTURES_DIR/examples" -name "*.beancount" | wc -l) files"
echo "Python tests:   $(ls -1 "$FIXTURES_DIR/python-tests" | wc -l) files"
echo
echo "Done! Test vectors are in: $FIXTURES_DIR"
