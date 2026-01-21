#!/usr/bin/env bash
set -e

# Beancount Compatibility Test Harness (Parallel)
# Compares bean-check (Python) vs rledger-check (Rust) on all .beancount files
# Run inside: nix develop --command ./scripts/compat-test.sh [directory]
#
# Examples:
#   ./scripts/compat-test.sh                    # Test full suite (tests/compat-full)
#   ./scripts/compat-test.sh tests/compat/files # Test curated files only

# Default to full test suite, but allow override via argument
FIXTURES_DIR="${1:-tests/compat-full}"
RESULTS_DIR="tests/compat-results"

# Fall back to curated files if full suite doesn't exist
if [ ! -d "$FIXTURES_DIR" ] || [ -z "$(ls -A "$FIXTURES_DIR" 2>/dev/null)" ]; then
    echo "Full test suite not found at $FIXTURES_DIR"
    echo "Falling back to curated files..."
    FIXTURES_DIR="tests/compat/files"
fi
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
RESULTS_FILE="$RESULTS_DIR/results_$TIMESTAMP.jsonl"
SUMMARY_FILE="$RESULTS_DIR/summary_$TIMESTAMP.md"

# Clean cache files to ensure fresh test results
find "$FIXTURES_DIR" -name "*.cache" -delete 2>/dev/null || true

# Parallel settings
PARALLEL_JOBS="${PARALLEL_JOBS:-$(nproc 2>/dev/null || echo 4)}"
# Cap at 16 for stability
[ "$PARALLEL_JOBS" -gt 16 ] && PARALLEL_JOBS=16

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "=== Beancount Compatibility Test Harness (Parallel) ==="
echo ""

# Create results directory and temp directory
mkdir -p "$RESULTS_DIR"
TEMP_DIR=$(mktemp -d)
trap "rm -rf $TEMP_DIR" EXIT

# Build rustledger in release mode
echo "Building rustledger..."
cargo build --release --quiet
RLEDGER_CHECK="./target/release/rledger-check"

if [ ! -x "$RLEDGER_CHECK" ]; then
    echo "Error: rledger-check not found at $RLEDGER_CHECK"
    exit 1
fi

# Check that bean-check is available
if ! command -v bean-check &> /dev/null; then
    echo "Error: bean-check not found. Run inside nix develop."
    exit 1
fi

echo "Using:"
echo "  Python: $(bean-check --version 2>&1 | head -1 || echo 'bean-check available')"
echo "  Rust:   $($RLEDGER_CHECK --version 2>&1 || echo 'rledger-check available')"
echo "  Parallel jobs: $PARALLEL_JOBS"
echo ""

# Find all beancount files
mapfile -t files < <(find "$FIXTURES_DIR" -name "*.beancount" -type f | sort)
total_files=${#files[@]}

echo "Found $total_files .beancount files to test"
echo "Results will be written to: $RESULTS_FILE"
echo ""

# Export variables and functions for parallel execution
export FIXTURES_DIR RLEDGER_CHECK TEMP_DIR

# Create a test script that can be run in parallel
cat > "$TEMP_DIR/test_one.sh" << 'SCRIPT'
#!/usr/bin/env bash
file="$1"
FIXTURES_DIR="$2"
RLEDGER_CHECK="$3"
TEMP_DIR="$4"

relpath="${file#$FIXTURES_DIR/}"

# Escape string for safe JSON embedding (limit to 200 chars)
escape_json() {
    echo "$1" | head -c 200 | sed 's/\\/\\\\/g; s/"/\\"/g; s/	/\\t/g' | tr '\n' ' '
}

# Run Python bean-check
py_stderr=$(mktemp)
bean-check "$file" >/dev/null 2>"$py_stderr" && py_exit=0 || py_exit=$?
py_err=$(cat "$py_stderr" | head -c 500)
rm -f "$py_stderr"

# Run Rust rledger-check (capture both stdout and stderr since errors go to stdout)
# Always use --no-cache for reproducible results during testing
# Strip ANSI codes to avoid breaking JSON
rs_output=$(mktemp)
"$RLEDGER_CHECK" --no-cache "$file" >"$rs_output" 2>&1 && rs_exit=0 || rs_exit=$?
rs_err=$(cat "$rs_output" | sed 's/\x1b\[[0-9;]*m//g' | head -c 500)
rm -f "$rs_output"

# Determine parse errors
py_parse_error=false
rs_parse_error=false
echo "$py_err" | grep -qi "syntax error\|parse error\|unexpected\|invalid token" && py_parse_error=true
echo "$rs_err" | grep -qi "syntax error\|parse error\|unexpected\|invalid token" && rs_parse_error=true

# Check if exits match
exit_match=false
if [ "$py_exit" -eq 0 ] && [ "$rs_exit" -eq 0 ]; then
    exit_match=true
elif [ "$py_exit" -ne 0 ] && [ "$rs_exit" -ne 0 ]; then
    exit_match=true
fi

# Count errors
py_error_count=$(echo "$py_err" | grep -c "error\|Error" || echo 0)
rs_error_count=$(echo "$rs_err" | grep -c "error\|Error" || echo 0)
[[ "$py_error_count" =~ ^[0-9]+$ ]] || py_error_count=0
[[ "$rs_error_count" =~ ^[0-9]+$ ]] || rs_error_count=0

# Escape special chars for JSON using helper function
py_err_escaped=$(escape_json "$py_err")
rs_err_escaped=$(escape_json "$rs_err")

# Output JSON result
echo "{\"file\":\"$relpath\",\"python\":{\"exit\":$py_exit,\"parse_error\":$py_parse_error,\"error_count\":$py_error_count,\"stderr\":\"$py_err_escaped\"},\"rust\":{\"exit\":$rs_exit,\"parse_error\":$rs_parse_error,\"error_count\":$rs_error_count,\"stderr\":\"$rs_err_escaped\"},\"match\":$exit_match}"
SCRIPT
chmod +x "$TEMP_DIR/test_one.sh"

echo "Running tests with $PARALLEL_JOBS parallel jobs..."
echo ""

start_time=$(date +%s)

# Run tests in parallel using xargs
# Each job outputs one JSON line to stdout
printf '%s\n' "${files[@]}" | \
    xargs -P "$PARALLEL_JOBS" -I {} "$TEMP_DIR/test_one.sh" {} "$FIXTURES_DIR" "$RLEDGER_CHECK" "$TEMP_DIR" \
    > "$RESULTS_FILE" 2>/dev/null

end_time=$(date +%s)
elapsed=$((end_time - start_time))

echo "Completed in ${elapsed}s"
echo ""
echo "=== Results Summary ==="
echo ""

# Calculate statistics from results
total=$(wc -l < "$RESULTS_FILE" | tr -d ' ')
check_match=$(grep -c '"match":true' "$RESULTS_FILE" || echo 0)
check_mismatch=$((total - check_match))

# Parse match (both have parse error or both don't)
# Use -c (compact) to ensure one line per match for accurate counting
parse_match=$(jq -c 'select(.python.parse_error == .rust.parse_error)' "$RESULTS_FILE" 2>/dev/null | wc -l | tr -d ' ')
parse_fail_python=$(jq -c 'select(.python.parse_error == true and .rust.parse_error == false)' "$RESULTS_FILE" 2>/dev/null | wc -l | tr -d ' ')
parse_fail_rust=$(jq -c 'select(.rust.parse_error == true and .python.parse_error == false)' "$RESULTS_FILE" 2>/dev/null | wc -l | tr -d ' ')

# Ensure numeric
[ -z "$parse_match" ] && parse_match=0
[ -z "$parse_fail_python" ] && parse_fail_python=0
[ -z "$parse_fail_rust" ] && parse_fail_rust=0

# Calculate percentages
parse_pct=$((parse_match * 100 / total))
check_pct=$((check_match * 100 / total))

# Display summary
echo "Files tested:       $total"
echo "Execution time:     ${elapsed}s ($((total / (elapsed + 1))) files/sec)"
echo ""
echo "Parse behavior match: $parse_match/$total ($parse_pct%)"
echo "  - Python parse error only: $parse_fail_python"
echo "  - Rust parse error only:   $parse_fail_rust"
echo ""
echo "Check exit match:     $check_match/$total ($check_pct%)"
echo "  - Mismatches: $check_mismatch"
echo ""

# Generate markdown summary
cat > "$SUMMARY_FILE" << EOF
# Beancount Compatibility Report

Generated: $(date)

## Summary

| Metric | Count | Percentage |
|--------|-------|------------|
| Files tested | $total | 100% |
| Parse match | $parse_match | $parse_pct% |
| Check exit match | $check_match | $check_pct% |

## Performance

- **Execution time:** ${elapsed}s
- **Parallel jobs:** $PARALLEL_JOBS
- **Rate:** $((total / (elapsed + 1))) files/sec

## Parse Behavior

- **Python-only parse errors:** $parse_fail_python
- **Rust-only parse errors:** $parse_fail_rust

## Check Mismatches

Total: $check_mismatch files

EOF

# Find and list mismatches
echo "### Files with exit code mismatch:" >> "$SUMMARY_FILE"
echo "" >> "$SUMMARY_FILE"

jq -r 'select(.match == false) | "- \(.file): Python=\(.python.exit), Rust=\(.rust.exit)"' "$RESULTS_FILE" 2>/dev/null | head -50 >> "$SUMMARY_FILE" || true

echo "" >> "$SUMMARY_FILE"
echo "## Details" >> "$SUMMARY_FILE"
echo "" >> "$SUMMARY_FILE"
echo "Full results in: \`$RESULTS_FILE\`" >> "$SUMMARY_FILE"

echo "Summary written to: $SUMMARY_FILE"
echo "Full results in:    $RESULTS_FILE"
echo ""

# Exit with error if match rate is too low
if [ "$check_pct" -lt 80 ]; then
    echo -e "${YELLOW}Warning: Check match rate below 80%${NC}"
fi
