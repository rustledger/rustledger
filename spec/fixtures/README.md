# Test Fixtures

This directory contains `.beancount` files for testing the parser, validator, and booking engine.

## Files

| File | Purpose | Expected Result |
|------|---------|-----------------|
| `syntax-edge-cases.beancount` | Parser edge cases | Should parse successfully |
| `booking-scenarios.beancount` | Booking algorithm scenarios | Should process successfully |
| `validation-errors.beancount` | Intentional errors | Should produce specific errors |

## Usage

### Parser Tests

```rust
#[test]
fn test_parse_edge_cases() {
    let content = include_str!("fixtures/syntax-edge-cases.beancount");
    let result = parse(content);
    assert!(result.is_ok(), "Parser should handle all edge cases");
}
```

### Validation Tests

```rust
#[test]
fn test_validation_errors() {
    let content = include_str!("fixtures/validation-errors.beancount");
    let ledger = parse_and_process(content);

    assert!(ledger.errors.iter().any(|e| e.code == "E1001"));  // Account not opened
    assert!(ledger.errors.iter().any(|e| e.code == "E2001"));  // Balance failed
    // ... etc
}
```

### Compatibility Tests

To verify against Python beancount:

```bash
# Run Python beancount
python -m beancount.scripts.check fixtures/syntax-edge-cases.beancount > python-output.txt

# Run Rust implementation
rustledger check fixtures/syntax-edge-cases.beancount > rust-output.txt

# Compare (should be identical)
diff python-output.txt rust-output.txt
```

## Adding New Fixtures

When adding test cases:

1. Document the purpose with comments
2. Note expected behavior (success/specific errors)
3. Cover one concept per section
4. Include edge cases for that concept
