# Rustledger Performance Optimization Roadmap

## Current Performance

| Metric | Value |
|--------|-------|
| rustledger | 160ms |
| Python beancount | 863ms |
| Current speedup | **5.4x** |

## Target

Push the speedup from 5x to **10-20x** through systematic optimization.

---

## Phase 1: Parser Quick Wins (Week 1)

**Goal**: Eliminate unnecessary allocations in the parser
**Expected Impact**: 20-30% faster
**Breaking Changes**: None

### 1.1 Remove `.to_string()` in Parser Primitives
- **File**: `crates/rustledger-parser/src/parser.rs`
- **Lines**: 622, 886, 922, 934, 942
- **Change**: Return `&str` slices instead of allocating String
- **Impact**: ~15% improvement

### 1.2 Fix Vector Cloning
- **File**: `crates/rustledger-parser/src/parser.rs`
- **Lines**: 1055, 1080
- **Change**: Use `.into_iter()` instead of `.clone().into_iter()`
- **Impact**: ~5% improvement

### 1.3 Use Rc for Metadata in Closures
- **File**: `crates/rustledger-parser/src/parser.rs`
- **Lines**: 1271, 1305, 1329, etc.
- **Change**: Wrap metadata in `Rc<Metadata>` to avoid cloning
- **Impact**: ~10% improvement

---

## Phase 2: Collection Optimizations (Week 2)

**Goal**: Reduce heap allocations for small collections
**Expected Impact**: 15-25% faster
**Breaking Changes**: Library API (see below)

### 2.1 Add SmallVec Dependency
```toml
# crates/rustledger-core/Cargo.toml
smallvec = "1.11"
```

### 2.2 Convert Small Vectors
```rust
// crates/rustledger-core/src/directive.rs
pub tags: SmallVec<[String; 4]>,      // was Vec<String>
pub links: SmallVec<[String; 2]>,     // was Vec<String>
pub postings: SmallVec<[Posting; 4]>, // was Vec<Posting>
```

### 2.3 Pre-allocate HashMaps
- Add `.with_capacity()` calls in validation and query execution
- **Files**: `rustledger-validate/src/lib.rs`, `rustledger-query/src/executor.rs`

### Breaking Change Impact
**Who is affected**: Rust library users (crate consumers)
**CLI users**: Not affected
**What changes**:
- Type signature of `Transaction::postings` changes from `Vec<Posting>` to `SmallVec<[Posting; 4]>`
- Code iterating over postings still works (SmallVec implements Iterator)
- Code doing `transaction.postings = vec![...]` needs update

---

## Phase 3: String Interning (Week 3-4)

**Goal**: Deduplicate strings across entire ledger
**Expected Impact**: 10-20% faster, 30-50% less memory
**Breaking Changes**: Library API

### 3.1 Extend InternedStr Usage
```rust
// crates/rustledger-core/src/directive.rs
pub struct Transaction {
    pub payee: Option<InternedStr>,    // was Option<String>
    pub narration: InternedStr,        // was String
    pub tags: SmallVec<[InternedStr; 4]>,
    pub links: SmallVec<[InternedStr; 2]>,
}
```

### 3.2 Intern at Parse Time
- Pass `StringInterner` to parser
- Intern strings immediately when parsed
- Share interner across all parsed files

---

## Phase 4: Parallelization (Week 5-6)

**Goal**: Use multiple CPU cores
**Expected Impact**: 2-4x faster on multi-core
**Breaking Changes**: None (internal)

### 4.1 Add Rayon Dependency
```toml
# crates/rustledger-validate/Cargo.toml
rayon = "1.8"
```

### 4.2 Parallel Transaction Processing
- Interpolate transactions in parallel
- Validate independent checks in parallel
- Keep sorting single-threaded (required for correctness)

---

## Phase 5: Lexer Rewrite (Future)

**Goal**: Replace parser combinators with fast lexer
**Expected Impact**: 30-50% faster parsing
**Breaking Changes**: None (internal)

### 5.1 Implement Logos-based Lexer
- Use `logos` crate for fast tokenization
- Enable existing `lexer.rs` (currently disabled)
- Separate tokenization from parsing

---

## Roadmap Summary

| Phase | Work | Impact | Breaking | Timeline |
|-------|------|--------|----------|----------|
| 1 | Parser quick wins | +25% | No | Week 1 |
| 2 | SmallVec | +20% | Yes* | Week 2 |
| 3 | Full interning | +15% | Yes* | Week 3-4 |
| 4 | Parallelization | +100% | No | Week 5-6 |
| 5 | Lexer rewrite | +40% | No | Future |

*Breaking for library users only, not CLI users

## Projected Performance

| After Phase | Speedup vs Python |
|-------------|-------------------|
| Current | 5.4x |
| Phase 1 | ~7x |
| Phase 2 | ~8-9x |
| Phase 3 | ~10x |
| Phase 4 | ~15-20x |
| Phase 5 | ~25x+ |

---

## Measurement Plan

Each phase should be benchmarked:

```bash
# Before/after each phase
cargo bench --bench pipeline_bench

# Nightly CI comparison (already set up)
# Results in benchmarks branch
```

---

## Decision Points

1. **After Phase 1**: Evaluate if quick wins are sufficient
2. **Before Phase 2**: Decide if breaking API changes are acceptable
3. **Before Phase 4**: Profile to see if parallelization is worthwhile
4. **Phase 5**: Only if still not meeting performance targets
