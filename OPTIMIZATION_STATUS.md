# Performance Optimization Status

## ✅ Already Implemented

| Optimization | Status | Impact | Location |
|--------------|--------|--------|----------|
| **String Interning** | ✅ Done | +6% | `InternedStr` for accounts, currencies, payees, narration, tags, links |
| **LTO (Thin)** | ✅ Done | +5-15% | `Cargo.toml: lto = "thin"` |
| **LTO (Fat - Linux)** | ✅ Done | +10-20% | `Cargo.toml: [profile.release-linux] lto = "fat"` |
| **PGO** | ✅ Done | +13% | Documented in performance-roadmap.md |
| **Binary Cache (rkyv)** | ✅ Done | 2.3x on cache hit | `crates/rustledger-loader/src/cache.rs` |
| **Parallel Validation** | ✅ Done | +5% | `rayon` in `rustledger-validate`, `rustledger-query` |
| **Logos Lexer** | ✅ Done | SIMD-accelerated | `crates/rustledger-parser/src/logos_lexer.rs` |
| **Winnow Parser** | ✅ Done | Replaced Chumsky | `crates/rustledger-parser/src/winnow_parser.rs` |
| **Regex Cache** | ✅ Done | 10-20% | `crates/rustledger-query/src/executor/mod.rs` |
| **Vec::with_capacity** | ✅ Done | ~80% fewer allocs | Parser, booking, validate, query, loader, plugin |
| **#[must_use] attributes** | ✅ Done | API safety | Added across all crates |
| **thiserror for errors** | ✅ Done | Consistency | All library crates |

---

## 🔮 Future Opportunities

### High Priority (10-30% improvement)

#### 1. **Bumpalo Arena Allocator** ⭐⭐⭐
**Status:** Not implemented
**Expected:** +20% parsing speed

```rust
// Use bumpalo for AST allocation during parsing
use bumpalo::collections::String;

let arena = bumpalo::Arena::new();
let directives = parse_with_arena(source, &arena);
// Mass deallocation: just reset bump pointer
```

**Files to modify:**
- `crates/rustledger-parser/src/winnow_parser.rs`
- `crates/rustledger-parser/src/Cargo.toml` (add bumpalo)

**Why:** Only 11 instructions per allocation vs ~100 for malloc

---

#### 2. **SIMD Text Processing** ⭐⭐
**Status:** Partial (Logos has SIMD)
**Expected:** +10-20% for string operations

**Already using:**
- ✅ Logos lexer (SIMD DFA)

**Could add:**
- `simdutf8` - SIMD UTF-8 validation
- `memchr` - SIMD string search
- `aho-corasick` - SIMD multi-pattern matching

**Files to modify:**
- `crates/rustledger-parser/src/logos_lexer.rs`
- `crates/rustledger-loader/src/lib.rs` (file reading)

---

#### 3. **Incremental Parsing (LSP)** ⭐⭐⭐
**Status:** Planned in LSP
**Expected:** 5-10x faster for LSP operations

**Current:** Full reparse on every change
**Future:** Only reparse changed regions

**Files to modify:**
- `crates/rustledger-lsp/src/db/mod.rs` (already planned)
- `crates/rustledger-parser/src/winnow_parser.rs`

---

### Medium Priority (5-10% improvement)

#### 4. **Struct Field Reordering** ⭐⭐
**Status:** Not done
**Expected:** 5-10% memory reduction, better cache hits

**Check:** `Posting`, `Transaction`, `Directive` structs for padding

```rust
// Verify with: cargo +nightly clippy -- -Z layout-suggestions
```

---

#### 5. **Memory-Mapped Files** ⭐
**Status:** Not implemented
**Expected:** 10-20% for files >100MB

**Add:** Optional mmap for large files
```rust
use memmap2::Mmap;

// Only for files > 50MB threshold
if file_size > 50 * 1024 * 1024 {
    let mmap = Mmap::open(file)?;
    // Zero-copy file access
}
```

**Files to modify:**
- `crates/rustledger-loader/src/lib.rs`
- `crates/rustledger-loader/Cargo.toml` (add memmap2)

---

### Low Priority (<5% improvement)

#### 6. **More String Interning** ⭐
**Status:** Partial (payee, narration done)
**Expected:** 5-10% fewer allocations

**Already interned:** ✅
- Account names
- Currency codes
- Payee names
- Narration
- Tags
- Links

**Could add:**
- Commodity names (if frequently repeated)
- Metadata keys (if standardized set)

---

#### 7. **SmallVec Re-evaluation** ⭐
**Status:** ❌ Previously reverted (-27% slower)
**Expected:** May help with newer Rust versions

**Previous attempt:** Phase 2 in performance-roadmap.md
**Result:** 27% slower (reverted)

**Re-evaluate with:**
- Newer SmallVec versions
- Different size parameters
- Specific use cases (metadata entries, not postings)

---

## Performance Summary

### Current State (January 2026)

| Benchmark | rustledger | beancount | Speedup |
|-----------|------------|-----------|---------|
| Validation (10K txn) | 35ms | 754ms | **22x** |
| Balance report | 118ms | 1280ms | **11x** |
| Cache hit (repeated) | 13ms | N/A | **instant** |

### Scaling

| Transactions | rustledger | Speedup vs beancount |
|--------------|------------|---------------------|
| 1K | 4.5ms | **33x** |
| 10K | 30.4ms | **24x** |
| 100K | 304ms | **10x** |

**Throughput:** ~330K transactions/second (after warmup)

---

## Recommended Next Steps

### 1. **Bumpalo Arena** (Highest impact remaining)
- **Effort:** Medium (2-3 days)
- **Impact:** +20% parsing
- **Risk:** Low (isolated to parser)

### 2. **Incremental Parsing** (Best for LSP)
- **Effort:** High (1-2 weeks)
- **Impact:** 5-10x LSP speed
- **Risk:** Medium (complexity)

### 3. **SIMD String Ops** (Quick win)
- **Effort:** Low (1 day)
- **Impact:** +10-20% string ops
- **Risk:** Low (additive)

---

## What NOT to Do

Based on previous measurements:

❌ **SmallVec for postings** - 27% slower (reverted)
❌ **Rc for closures** - 25% slower (reverted)

These added overhead that outweighed benefits.

---

## Measurement Plan

Before implementing any optimization:

```bash
# Baseline
cargo bench -p rustledger-parser --bench parser_bench
cargo bench -p rustledger-core --bench inventory_bench

# After change
cargo bench -p rustledger-parser --bench parser_bench

# Compare
# Expected: >5% improvement to justify complexity
```

---

## References

- **Performance roadmap:** `docs/development/performance-roadmap.md`
- **Benchmarks:** `BENCHMARKS.md`
- **rust-skills rules:** `.opencode/skills/rust-skills/`
---

## Bumpalo Arena Experiment Results (April 2026)

**Status:** ❌ Not beneficial with current API

**Implementation:** Used bumpalo::collections::Vec for temporary parsing collections
**Result:** No significant performance improvement (12-19ms vs baseline 12ms on 340K file)

**Why it didn't help:**
1. Data must be copied from arena to heap when returning ParseResult
2. Most strings already use InternedStr (Arc<str>) which is efficient
3. Arena benefit (fast allocation + bulk deallocation) is lost when copying out

**To make bumpalo effective would require:**
- API changes to return arena-borrowed references (breaking change)
- Keeping parsed data in arena for entire lifetime (not feasible for CLI)
- Much larger files where allocation overhead dominates (>10MB)

**Conclusion:** Bumpalo is not worth pursuing without architectural changes. Focus on other optimizations.

