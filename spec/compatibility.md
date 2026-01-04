# Compatibility Notes

This document tracks compatibility with Python beancount, including intentional differences.

## Compatibility Goal

**100% compatible** with valid beancount files. Any file that Python beancount accepts should produce identical results in rustledger.

## Compatibility Levels

### Level 1: Syntax (Parser)

The parser must accept exactly the same syntax as Python beancount.

**Status**: Target full compatibility

### Level 2: Semantics (Processing)

Interpolation, booking, and validation must produce identical results.

**Status**: Target full compatibility

### Level 3: Output (Formatting)

Error messages, query results, and printed output may differ in formatting.

**Status**: Allowed differences

### Level 4: Performance

Processing order and internal representation may differ as long as results match.

**Status**: Allowed differences

## Known Differences

### Intentional Differences

| Feature | Python Behavior | Rust Behavior | Rationale |
|---------|-----------------|---------------|-----------|
| Plugin system | Python modules | WASM modules | Language independence |
| Error messages | Python format | Rich formatting (ariadne) | Better UX |
| Query output | Python tables | Various formats | Flexibility |

### Accepted Deviations

| Behavior | Python | Rust | Impact |
|----------|--------|------|--------|
| Floating point display | Python repr | Decimal display | Cosmetic only |
| Error ordering | Undefined | By source location | UX improvement |
| Hash/ID generation | Python hash | Different algorithm | Cosmetic only |

## Plugin Compatibility

### Python Plugins (NOT supported)

rustledger does **not** support Python plugins. Users must:

1. Port plugins to WASM (Rust, Go, AssemblyScript, etc.)
2. Use built-in reimplementations of common plugins

### Built-in Plugin Equivalents

| Python Plugin | rustledger Equivalent |
|---------------|-------------------------|
| `beancount.plugins.implicit_prices` | Built-in Rust |
| `beancount.plugins.check_commodity` | Built-in Rust |
| `beancount.plugins.check_closing` | Built-in Rust |
| `beancount.plugins.coherent_cost` | Built-in Rust |

### Plugin Porting Guide

```python
# Python plugin
def process(entries, options_map):
    new_entries = []
    errors = []
    for entry in entries:
        # Transform entry
        new_entries.append(entry)
    return new_entries, errors
```

```rust
// Rust WASM plugin
#[no_mangle]
pub fn process(input: PluginInput) -> PluginOutput {
    let mut directives = input.directives;
    let mut errors = Vec::new();

    for directive in &mut directives {
        // Transform directive
    }

    PluginOutput { directives, errors }
}
```

## BQL Compatibility

### Fully Supported

- SELECT with columns and expressions
- WHERE filtering
- GROUP BY aggregation
- ORDER BY sorting
- LIMIT
- Standard functions (sum, count, first, last, etc.)
- OPEN ON / CLOSE ON / CLEAR

### Partially Supported

| Feature | Python | Rust | Notes |
|---------|--------|------|-------|
| PIVOT BY | Yes | Planned | Phase 2 |
| FLATTEN | Yes | Planned | Phase 2 |
| Sub-selects | Yes | Planned | Phase 3 |

### Differences

| Behavior | Python | Rust |
|----------|--------|------|
| NULL handling | Python None | Rust Option |
| Regex engine | Python re | Rust regex |

## Error Message Compatibility

Error messages will differ in format but convey the same information:

### Python

```
ledger.beancount:42:
  Assets:Unknown is not defined
```

### Rust (ariadne)

```
error[E1001]: Account "Assets:Unknown" is not open
  --> ledger.beancount:42:3
   |
42 |   Assets:Unknown  100 USD
   |   ^^^^^^^^^^^^^^ account used here
   |
   = help: add an `open` directive before line 42
```

## Testing Compatibility

### Comparison Test Suite

```bash
#!/bin/bash
# Run both implementations and compare output

FILE=$1

# Python output
python -m beancount.scripts.check "$FILE" 2>&1 | \
    grep -E '^(error|warning)' | sort > /tmp/python.txt

# Rust output
rustledger check "$FILE" 2>&1 | \
    grep -E '^(error|warning)' | sort > /tmp/rust.txt

# Compare (ignoring formatting)
diff /tmp/python.txt /tmp/rust.txt
```

### Semantic Comparison

Compare computed values rather than output format:

```python
# Python: extract balances
import beancount.loader
entries, errors, options = beancount.loader.load_file('ledger.beancount')
balances = compute_balances(entries)
print(json.dumps(balances))
```

```bash
# Rust: extract balances
rustledger query ledger.beancount \
    "SELECT account, sum(position) GROUP BY 1" \
    --format json
```

```bash
# Compare JSON outputs
diff <(python extract.py | jq -S .) <(rustledger ... | jq -S .)
```

## Reporting Compatibility Issues

When you find a compatibility issue:

1. **Create minimal reproducer**: Smallest beancount file that shows the difference
2. **Document both behaviors**: Python output vs Rust output
3. **Classify**: Is this a bug or intentional difference?
4. **File issue**: Include reproducer and classification

### Issue Template

```markdown
## Compatibility Issue

**File**: minimal.beancount
```beancount
2024-01-01 open Assets:Cash
2024-01-15 * "Test"
  Assets:Cash  100 USD
  ; <-- specific issue here
```

**Python behavior**:
```
[output]
```

**Rust behavior**:
```
[output]
```

**Expected**: [Python/Rust/Neither] is correct because [reason]
```

## Version Compatibility

### Beancount Versions

| Python Version | Compatibility |
|----------------|---------------|
| v2.x (current) | Full target |
| v3.x (future) | Track changes |

### Syntax Changes

We track the beancount syntax changelog and update accordingly:

| Change | Version | rustledger Status |
|--------|---------|---------------------|
| (none currently) | | |

## Migration Guide

### From Python Beancount

1. **Run compatibility check**:
   ```bash
   rustledger compat-check ledger.beancount
   ```

2. **Address plugin dependencies**:
   - List used plugins: `grep "^plugin" ledger.beancount`
   - Find WASM equivalents or port

3. **Update query scripts**:
   - Replace `bean-query` with `rustledger query`
   - Check for BQL feature usage

4. **Run parallel validation**:
   ```bash
   # Verify identical results
   diff <(bean-check ledger.beancount) <(rustledger check ledger.beancount)
   ```

### Gradual Migration

Use rustledger for read-only operations first:

1. **Phase 1**: Use for validation (`rustledger check`)
2. **Phase 2**: Use for queries (`rustledger query`)
3. **Phase 3**: Use for reporting
4. **Phase 4**: Full replacement
