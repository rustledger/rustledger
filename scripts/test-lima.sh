#!/usr/bin/env bash
# Test parser against lima test vectors
#
# Usage: ./scripts/test-lima.sh [rledger-binary]
#
# Downloads test vectors first if not present (run fetch-test-vectors.sh).

set -uo pipefail

RLEDGER="${1:-./target/release/rledger}"

# Build if binary doesn't exist
if [ ! -f "$RLEDGER" ]; then
    echo "Building rledger..."
    cargo build --release -p rustledger --quiet
    RLEDGER="./target/release/rledger"
fi

TESTS_DIR="tests/fixtures/lima-tests"
if [ ! -d "$TESTS_DIR" ] || [ -z "$(ls -A "$TESTS_DIR" 2>/dev/null)" ]; then
    echo "Lima test vectors not found. Run: ./scripts/fetch-test-vectors.sh"
    exit 1
fi

failed=0
passed=0
total=0

for f in "$TESTS_DIR"/*.beancount; do
    total=$((total+1))
    basename=$(basename "$f")

    # Run rledger check and capture both exit code and output
    out=$("$RLEDGER" check "$f" 2>&1) || true
    exit_code=$?

    has_error=false
    if [ $exit_code -ne 0 ] || echo "$out" | grep -qi "syntax error\|parse error\|unexpected"; then
        has_error=true
    fi

    # Files matching these patterns are expected to produce errors
    if [[ "$basename" == SyntaxErrors.* ]] || [[ "$basename" == LexerAndParserErrors.* ]]; then
        if $has_error; then
            passed=$((passed+1))
        else
            echo "FAIL (expected error): $basename"
            failed=$((failed+1))
        fi
    else
        if $has_error; then
            echo "FAIL (unexpected error): $basename"
            failed=$((failed+1))
        else
            passed=$((passed+1))
        fi
    fi
done

echo "---"
echo "Total: $total"
echo "Passed: $passed"
echo "Failed: $failed"

if [ "$failed" -gt 0 ]; then
    exit 1
fi
