# Plan: Fix Formatter to Preserve Comments, Metadata, and Whitespace

## Issue
The `rledger format` command strips comments, metadata, and blank lines from beancount files.

## Root Cause Analysis

### Python beancount approach (bean-format)
Uses a **regex-based, line-by-line approach**:
1. Reads file as raw text (not parsed AST)
2. Uses regex to identify lines containing amounts
3. Only reformats those specific lines for alignment
4. Leaves ALL other lines completely unchanged
5. Has assertion: `assert old_stripped == new_stripped` (only whitespace changes)

**Key insight**: Python doesn't parse-then-print; it does surgical edits on specific lines.

### rustledger approach (current)
Uses a **parse-then-print approach**:
1. Parses file into full AST via `Loader`
2. Iterates through parsed `Directive` objects only
3. Regenerates text using `format_directive()`

**Problems identified**:

| Issue | Location | Details |
|-------|----------|---------|
| Comments lost | Parser | Standalone comments (`;`) not captured in AST |
| Inline comments lost | Parser | Comments at end of lines not captured |
| Blank lines lost | Parser/Formatter | No tracking of whitespace between directives |
| Metadata not output | `format/*.rs` | Only `format_transaction()` outputs metadata; `format_open()`, `format_balance()`, etc. ignore the `meta` field |

## Proposed Solution

### Option A: Regex-based approach (like Python)
Rewrite formatter to work line-by-line:
- Read file as lines
- Use regex to identify posting lines with amounts
- Reformat only those lines for alignment
- Pass through all other lines unchanged

**Pros**: Simple, preserves everything automatically, matches Python behavior exactly
**Cons**: Less intelligent, can't do structural reformatting

### Option B: AST-preserving approach (improve current)
Enhance parser and formatter:
1. Parser captures comments as `Directive::Comment` or attaches to directives
2. Parser tracks blank lines / source spans
3. All directive formatters output their `meta` field
4. Reconstruct with original whitespace where possible

**Pros**: More powerful, enables intelligent formatting
**Cons**: Significant parser changes, complex implementation

### Option C: Hybrid approach (Recommended)
**Phase 1** (Quick fix): Regex-based alignment only
- Match Python's behavior exactly
- Minimal code changes
- Ship quickly to fix the bug

**Phase 2** (Future): Intelligent formatting
- Add `--rewrite` flag for full AST-based formatting
- Keep default as regex-based (safe)
- Gradually improve AST to capture more metadata

## Implementation Plan (Phase 1)

### Step 1: Create new regex-based formatter module
Create `crates/rustledger/src/format_regex.rs`:

```rust
use regex::Regex;
use lazy_static::lazy_static;

lazy_static! {
    // Match posting lines with amounts: "  Account:Name  123.45 USD"
    static ref POSTING_RE: Regex = Regex::new(
        r"^(\s+)([A-Z][A-Za-z0-9:-]+)(\s+)([-+]?\d[\d,]*\.?\d*)\s+([A-Z][A-Z0-9]{2,})(.*)$"
    ).unwrap();
}

pub fn align_beancount(content: &str, currency_column: usize) -> String {
    // 1. Parse lines and identify those with amounts
    // 2. Calculate max widths
    // 3. Reformat only amount lines
    // 4. Return with all other lines unchanged
}
```

### Step 2: Update format command
Modify `crates/rustledger/src/cmd/format.rs`:
- Replace AST-based formatting with regex-based
- Keep syntax validation (still parse to check for errors)
- Only reformat if file parses successfully

### Step 3: Add tests
- Test that comments are preserved
- Test that metadata is preserved
- Test that blank lines are preserved
- Test alignment still works

### Step 4: Verify Python compatibility
Run both formatters on same files, compare output.

## Files to Modify

| File | Changes |
|------|---------|
| `crates/rustledger/src/format_regex.rs` | New file - regex-based formatter |
| `crates/rustledger/src/cmd/format.rs` | Use regex formatter instead of AST |
| `crates/rustledger/src/lib.rs` | Export new module |

## Testing

```bash
# Create test file
cat > /tmp/test.beancount << 'EOF'
; Header comment

option "operating_currency" "USD"

2024-01-01 open Assets:Bank
  description: "Main checking"

; Section comment
2024-01-15 * "Store" "Groceries" #food
  Expenses:Food    50.00 USD
  Assets:Bank

; Footer
EOF

# Test
rledger format /tmp/test.beancount

# Should preserve ALL content, only align amounts
```

## Timeline
- Phase 1: 1-2 days (regex-based, quick fix)
- Phase 2: Future enhancement (AST improvements)

## References
- Python beancount format.py: https://github.com/beancount/beancount/blob/master/beancount/scripts/format.py
- Issue #364: Formatter does not preserve comments, metadata, whitespaces
