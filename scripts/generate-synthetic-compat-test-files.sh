#!/usr/bin/env bash
echo "Generating synthetic test files..."
    
mkdir -p tests/compatibility/files/synthetic

# Use rledger doctor to generate synthetic files with manifest
./target/release/rledger doctor generate-synthetic \
    --output tests/compatibility/files/synthetic \
    --count 50 \
    --seed 12345 \
    --manifest \
    --skip-validation
echo "Generated $(find tests/compatibility/synthetic -name '*.beancount' 2>/dev/null | wc -l) synthetic files"

# Also generate bean-example files if available
if command -v bean-example &> /dev/null; then
    echo "Generating bean-example files..."
    for seed in 1 42 123; do
        end_date=$(date +%Y-%m-%d)
        start_date=$(date -d "$end_date - 1 year" +%Y-%m-%d 2>/dev/null || date -v-1y +%Y-%m-%d)
        output="tests/compatibility/files/synthetic/bean-example_seed${seed}.beancount"
        bean-example --seed "$seed" --date-begin "$start_date" --date-end "$end_date" --output "$output" 2>/dev/null || true
    done
    echo "Generated $(find tests/compatibility/synthetic/bean-example -name '*.beancount' 2>/dev/null | wc -l) bean-example files"
fi
