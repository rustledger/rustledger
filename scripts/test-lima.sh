#!/bin/bash
# Test parser against lima test vectors

failed=0
passed=0
total=0

for f in spec/fixtures/lima-tests/*.beancount; do
    total=$((total+1))
    basename=$(basename "$f")
    out=$(cargo run --quiet --bin bean-check -- "$f" 2>&1)
    has_syntax_error=false
    if echo "$out" | grep -qi "syntax error"; then
        has_syntax_error=true
    fi

    # SyntaxErrors.* files are expected to produce syntax errors
    if [[ "$basename" == SyntaxErrors.* ]]; then
        if $has_syntax_error; then
            passed=$((passed+1))
        else
            echo "FAIL (expected syntax error): $basename"
            failed=$((failed+1))
        fi
    else
        if $has_syntax_error; then
            echo "FAIL: $basename"
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
