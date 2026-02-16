#!/usr/bin/env bash
# Run format regression tests against rledger format
# Usage: ./scripts/test-format-regressions.sh [rledger-binary]
#
# These tests verify that the formatter preserves comments, metadata, and whitespace.
# A test passes if formatting twice produces the same output (idempotent).

set -e

RLEDGER="${1:-./target/release/rledger}"
TESTS_DIR="tests/regressions/format"
PASSED=0
FAILED=0
FAILED_TESTS=""

# Build if binary doesn't exist
if [ ! -f "$RLEDGER" ]; then
    echo "Building rledger..."
    cargo build --release --bin rledger
fi

echo "Running format regression tests..."
echo "Binary: $RLEDGER"
echo "Tests:  $TESTS_DIR"
echo ""

for f in "$TESTS_DIR"/issue-*.beancount; do
    if [ ! -f "$f" ]; then
        echo "No format regression tests found in $TESTS_DIR"
        exit 0
    fi

    BASENAME=$(basename "$f")
    ISSUE_NUM=$(echo "$BASENAME" | sed 's/issue-\([0-9]*\).*/\1/')

    # Create temp files for comparison
    FORMATTED1=$(mktemp)
    FORMATTED2=$(mktemp)
    trap "rm -f $FORMATTED1 $FORMATTED2" EXIT

    # Format once
    "$RLEDGER" format "$f" > "$FORMATTED1" 2>/dev/null

    # Format the formatted output (should be idempotent)
    "$RLEDGER" format "$FORMATTED1" > "$FORMATTED2" 2>/dev/null

    # Check idempotency
    if ! diff -q "$FORMATTED1" "$FORMATTED2" > /dev/null 2>&1; then
        echo "✗ #$ISSUE_NUM FAILED (not idempotent)"
        FAILED=$((FAILED + 1))
        FAILED_TESTS="$FAILED_TESTS #$ISSUE_NUM"
        continue
    fi

    # Check that comments are preserved
    ORIG_COMMENTS=$(grep -c "^;" "$f" || true)
    FMT_COMMENTS=$(grep -c "^;" "$FORMATTED1" || true)
    if [ "$ORIG_COMMENTS" -ne "$FMT_COMMENTS" ]; then
        echo "✗ #$ISSUE_NUM FAILED (comments lost: $ORIG_COMMENTS -> $FMT_COMMENTS)"
        FAILED=$((FAILED + 1))
        FAILED_TESTS="$FAILED_TESTS #$ISSUE_NUM"
        continue
    fi

    # Check that metadata is preserved (lines with key: value pattern indented)
    # Note: formatter uses 4-space indent for metadata by default
    ORIG_META=$(grep -cE "^[[:space:]]+[a-z]+:" "$f" || true)
    FMT_META=$(grep -cE "^[[:space:]]+[a-z]+:" "$FORMATTED1" || true)
    if [ "$ORIG_META" -ne "$FMT_META" ]; then
        echo "✗ #$ISSUE_NUM FAILED (metadata lost: $ORIG_META -> $FMT_META)"
        FAILED=$((FAILED + 1))
        FAILED_TESTS="$FAILED_TESTS #$ISSUE_NUM"
        continue
    fi

    echo "✓ #$ISSUE_NUM passed (comments: $ORIG_COMMENTS, metadata: $ORIG_META)"
    PASSED=$((PASSED + 1))
done

echo ""
echo "Results: $PASSED passed, $FAILED failed"

if [ $FAILED -gt 0 ]; then
    echo "Failed tests:$FAILED_TESTS"
    exit 1
fi
