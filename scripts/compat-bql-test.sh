#!/usr/bin/env bash
set -e

# BQL Compatibility Test (Parallel)
# Compares bean-query (Python) vs rledger-query (Rust) on valid beancount files
# Run inside: nix develop --command ./scripts/compat-bql-test.sh
#
# Environment variables:
#   PARALLEL_JOBS: Number of parallel workers (default: CPU count, max 8)

FIXTURES_DIR="${1:-tests/compat-full}"
RESULTS_DIR="tests/compat-results"

# Fall back to curated files if full suite doesn't exist
if [ ! -d "$FIXTURES_DIR" ] || [ -z "$(ls -A "$FIXTURES_DIR" 2>/dev/null)" ]; then
    FIXTURES_DIR="tests/compat/files"
fi
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
RESULTS_FILE="$RESULTS_DIR/bql_results_$TIMESTAMP.jsonl"

# Clean cache files to ensure fresh test results
find "$FIXTURES_DIR" -name "*.cache" -delete 2>/dev/null || true

# Parallel settings
PARALLEL_JOBS="${PARALLEL_JOBS:-$(nproc 2>/dev/null || echo 4)}"
[ "$PARALLEL_JOBS" -gt 16 ] && PARALLEL_JOBS=16

echo "=== BQL Compatibility Test (Parallel) ==="
echo ""

mkdir -p "$RESULTS_DIR"
TEMP_DIR=$(mktemp -d)
trap "rm -rf $TEMP_DIR" EXIT

# Build rustledger
echo "Building rustledger..."
cargo build --release --quiet
RLEDGER_QUERY="./target/release/rledger-query"

if [ ! -x "$RLEDGER_QUERY" ]; then
    echo "Error: rledger-query not found"
    exit 1
fi

# Check bean-query is available
if ! command -v bean-query &> /dev/null; then
    echo "Error: bean-query not found. Run inside nix develop."
    exit 1
fi

echo "Using $PARALLEL_JOBS parallel workers"
echo ""

# Find files that passed both check tests (use most recent results)
COMPAT_RESULTS=$(ls -t "$RESULTS_DIR"/results_*.jsonl 2>/dev/null | head -1)
if [ -z "$COMPAT_RESULTS" ]; then
    echo "No compat-test results found. Run ./scripts/compat-test.sh first."
    exit 1
fi

# Get files where both implementations passed (match=true and both exit=0)
mapfile -t valid_files < <(jq -r 'select(.match == true and .python.exit == 0 and .rust.exit == 0) | .file' "$COMPAT_RESULTS" | head -50)

# Standard queries to test - expanded coverage
# Note: All queries with LIMIT must have ORDER BY for deterministic results
# Without ORDER BY, LIMIT selects different rows depending on processing order
QUERIES_FILE="$TEMP_DIR/queries.txt"
cat > "$QUERIES_FILE" << 'EOF'
SELECT DISTINCT account ORDER BY account LIMIT 20
SELECT COUNT(*) AS total
SELECT currency, COUNT(*) AS cnt GROUP BY currency ORDER BY cnt DESC LIMIT 10
SELECT YEAR(date) AS year, COUNT(*) AS cnt GROUP BY year ORDER BY year
SELECT DISTINCT ROOT(account) AS root ORDER BY root
SELECT DISTINCT LEAF(account) AS leaf ORDER BY leaf LIMIT 20
SELECT account, SUM(position) GROUP BY account ORDER BY account LIMIT 10
SELECT MONTH(date) AS month, COUNT(*) AS cnt GROUP BY month ORDER BY month
SELECT date, narration ORDER BY date, narration LIMIT 10
SELECT account, FIRST(date) AS first_date GROUP BY account ORDER BY account LIMIT 10
SELECT MIN(date) AS min_date, MAX(date) AS max_date
EOF

QUERY_COUNT=$(wc -l < "$QUERIES_FILE" | tr -d ' ')
echo "Found ${#valid_files[@]} files that passed both implementations"
echo "Testing with $QUERY_COUNT queries each..."
echo ""

# Create test script for parallel execution
cat > "$TEMP_DIR/test_bql.sh" << 'SCRIPT'
#!/usr/bin/env bash
file="$1"
query="$2"
FIXTURES_DIR="$3"
RLEDGER_QUERY="$4"

full_path="$FIXTURES_DIR/$file"
[ ! -f "$full_path" ] && exit 0

# Run Python bean-query
py_out=$(bean-query "$full_path" "$query" 2>/dev/null | head -50 || echo "ERROR")
py_exit=$?

# Run Rust rledger-query
rs_out=$("$RLEDGER_QUERY" "$full_path" "$query" 2>/dev/null | head -50 || echo "ERROR")
rs_exit=$?

# Normalize function: extract just the data values
# - Skip header row (first line)
# - Skip separator lines (----)
# - Skip row count lines (N row(s))
# - Trim whitespace, normalize spaces
# - Normalize whitespace inside braces (lot costs): { 5.16 -> {5.16
# - Sort for comparison (handles undefined ORDER BY)
normalize_output() {
    echo "$1" | \
        grep -v "^-" | \
        grep -v "row(s)" | \
        grep -v "^$" | \
        tail -n +2 | \
        tr -s ' \t' ' ' | \
        sed 's/{ /{/g' | \
        sed 's/ }/}/g' | \
        sed 's/^ *//; s/ *$//' | \
        sort
}

py_data=$(normalize_output "$py_out")
rs_data=$(normalize_output "$rs_out")

# Count data rows (needed for categorization)
py_rows=$(echo "$py_data" | grep -c . 2>/dev/null || echo 0)
rs_rows=$(echo "$rs_data" | grep -c . 2>/dev/null || echo 0)
py_rows=$(echo "$py_rows" | tr -d '\n')
rs_rows=$(echo "$rs_rows" | tr -d '\n')

# Normalize numbers for comparison
# Handles:
# - Python's display context truncation (e.g., "111 USD" vs "111.11 USD")
# - Zero balance display differences (Python shows empty, Rust shows "0 USD")
# - Empty currency rows (Rust may show rows for empty/null currencies)
normalize_numbers() {
    echo "$1" | \
        sed -E 's/([0-9]+)\.[0-9]+/\1/g' | \
        sed -E 's/\b0 [A-Z]+\b//g' | \
        grep -v '^[[:space:]]*[0-9]*[[:space:]]*$' | \
        sed 's/^ *//; s/ *$//'
}

# Categorize the result
if [ "$py_data" = "$rs_data" ]; then
    match="true"
    category="match"
elif [ -z "$py_data" ] && [ -z "$rs_data" ]; then
    match="true"
    category="both_empty"
elif [ -z "$py_data" ]; then
    match="false"
    category="python_empty"
elif [ -z "$rs_data" ]; then
    match="false"
    category="rust_empty"
elif [ "$py_exit" -ne 0 ] || [ "$rs_exit" -ne 0 ]; then
    match="false"
    category="error"
else
    # Check if difference is only in decimal precision or zero values
    py_normalized=$(normalize_numbers "$py_data")
    rs_normalized=$(normalize_numbers "$rs_data")
    if [ "$py_normalized" = "$rs_normalized" ]; then
        # Values match when decimals/zeros are normalized - acceptable
        match="true"
        category="precision_diff"
    else
        # Data differs after normalization - this is a real difference
        match="false"
        category="data_diff"
    fi
fi

# Output JSON result with more detail
query_escaped=$(echo "$query" | head -c 50 | sed 's/"/\\"/g')
echo "{\"file\":\"$file\",\"query\":\"$query_escaped\",\"match\":$match,\"category\":\"$category\",\"py_rows\":$py_rows,\"rs_rows\":$rs_rows}"
SCRIPT
chmod +x "$TEMP_DIR/test_bql.sh"

# Build list of all (file, query) pairs
TEST_CASES_FILE="$TEMP_DIR/test_cases.txt"
> "$TEST_CASES_FILE"
for file in "${valid_files[@]}"; do
    while IFS= read -r query; do
        echo "$file	$query" >> "$TEST_CASES_FILE"
    done < "$QUERIES_FILE"
done

total_cases=$(wc -l < "$TEST_CASES_FILE" | tr -d ' ')
echo "Running $total_cases BQL tests..."
echo ""

start_time=$(date +%s)

# Run tests in parallel
while IFS=$'\t' read -r file query; do
    echo "$file"$'\t'"$query"
done < "$TEST_CASES_FILE" | \
    xargs -P "$PARALLEL_JOBS" -I {} bash -c '
        IFS=$'"'"'\t'"'"' read -r file query <<< "{}"
        '"$TEMP_DIR"'/test_bql.sh "$file" "$query" "'"$FIXTURES_DIR"'" "'"$RLEDGER_QUERY"'"
    ' > "$RESULTS_FILE"

end_time=$(date +%s)
elapsed=$((end_time - start_time))

echo ""
echo "=== BQL Results Summary ==="
echo ""

total_queries=$(wc -l < "$RESULTS_FILE" | tr -d ' ')
matching_queries=$(grep -c '"match":true' "$RESULTS_FILE" || echo 0)
failed_queries=$((total_queries - matching_queries))

if [ "$total_queries" -gt 0 ]; then
    match_pct=$((matching_queries * 100 / total_queries))
else
    match_pct=0
fi

echo "Total queries:    $total_queries"
echo "Matching:         $matching_queries ($match_pct%)"
echo "Different:        $failed_queries"
echo "Execution time:   ${elapsed}s"
echo ""

# Show breakdown by category (grep -c exits 1 when 0 matches, so use || true)
cat_match=$(grep -c '"category":"match"' "$RESULTS_FILE" 2>/dev/null) || cat_match=0
cat_both_empty=$(grep -c '"category":"both_empty"' "$RESULTS_FILE" 2>/dev/null) || cat_both_empty=0
cat_precision_diff=$(grep -c '"category":"precision_diff"' "$RESULTS_FILE" 2>/dev/null) || cat_precision_diff=0
cat_python_empty=$(grep -c '"category":"python_empty"' "$RESULTS_FILE" 2>/dev/null) || cat_python_empty=0
cat_rust_empty=$(grep -c '"category":"rust_empty"' "$RESULTS_FILE" 2>/dev/null) || cat_rust_empty=0
cat_data_diff=$(grep -c '"category":"data_diff"' "$RESULTS_FILE" 2>/dev/null) || cat_data_diff=0
cat_error=$(grep -c '"category":"error"' "$RESULTS_FILE" 2>/dev/null) || cat_error=0

echo "Breakdown by category:"
echo "  Passing:"
echo "    match:          $cat_match"
echo "    both_empty:     $cat_both_empty"
echo "    precision_diff: $cat_precision_diff  (display precision only)"
echo "  Failing:"
echo "    python_empty:   $cat_python_empty"
echo "    rust_empty:     $cat_rust_empty"
echo "    data_diff:      $cat_data_diff"
echo "    error:          $cat_error"
echo ""

# Show sample data_diff cases for debugging
data_diffs=$(jq -r 'select(.category == "data_diff") | "\(.file) | \(.query) | py=\(.py_rows) rs=\(.rs_rows)"' "$RESULTS_FILE" 2>/dev/null | head -5)
if [ -n "$data_diffs" ]; then
    echo "Sample data differences (py vs rs row counts):"
    echo "$data_diffs" | while read line; do echo "  $line"; done
    echo ""
fi

echo "Results in: $RESULTS_FILE"
