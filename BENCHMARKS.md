# Rustledger Performance Benchmarks

## Baseline Measurements (Pre-Optimization)

Benchmarks run on: Linux, rustc 1.85.0

---

## Parser Benchmarks (`rustledger-parser`)

### Tokenize Scaling

| Size | Time (µs) | Throughput (MiB/s) |
|------|-----------|-------------------|
| 100 bytes | 24.32 | 432.07 |
| 500 bytes | 122.54 | 425.96 |
| 1000 bytes | 227.56 | 467.35 |

### Tokenize vs Parse

| Operation | Time (µs/ms) | Throughput (MiB/s) |
|-----------|--------------|-------------------|
| Tokenize only | 229.85 µs | 451.84 |
| Full parse | 1.2372 ms | 84.441 |

**Observations:**
- Tokenization is ~5x faster than full parsing
- Throughput remains consistent across sizes (420-470 MiB/s)
- Outliers detected (2-12%) - may indicate GC or scheduling variance

---

## Inventory Benchmarks (`rustledger-core`)

### Reduce LIFO (Lot Matching)

| Positions | Time (µs/ms) |
|-----------|--------------|
| 100 | 295.55 µs |
| 500 | 7.0606 ms |

**Scaling:** O(n²) expected for LIFO with 500 positions

### Reduce STRICT

| Positions | Time (µs) |
|-----------|-----------|
| 10 | 660.92 ns |
| 100 | 2.8460 µs |
| 500 | 12.437 µs |

**Scaling:** Linear O(n) - excellent performance

### Inventory Merge

| Positions | Time (µs) |
|-----------|-----------|
| 10 | 860.69 ns |
| 100 | 6.2651 µs |
| 500 | 31.825 µs |

**Scaling:** Linear O(n) - good for portfolio consolidation

---

## Validation Benchmarks (`rustledger-validate`)

### Validate With Errors

| Elements | Time (ms) | Throughput (Kelem/s) |
|----------|-----------|---------------------|
| 1000 | 1.3708 | 744.82 |

### Validate Balance Assertions

| Assertions | Time (µs) | Throughput (Kelem/s) |
|------------|-----------|---------------------|
| 10 | 15.221 | 664.22 |
| 50 | 60.729 | 869.55 |
| 100 | 139.51 | 724.34 |

**Observations:**
- Validation throughput: 650-870 Kelem/s (thousand elements per second)
- Slight performance variation at different scales
- Outliers (3-10%) present in all benchmarks

---

## Optimization Impact (Expected)

### Parser Optimizations (PR #754, #766)
- **Vec::with_capacity()**: ~10-20% reduction in allocations
- **36 new tests**: Coverage from 40.88% → 51.13%

### Booking Optimizations (PR #756)
- **Inventory cloning**: O(txn accounts) vs O(all accounts)
- Expected: 50-80% faster for large ledgers (100+ accounts)

### Core Memory Fixes (PR #755)
- **Formatting allocations**: ~40-60% fewer allocations
- Expected: Minor speedup (1-5%) in display operations

### Query/Plugin/Loader/Validate (PR #761-763, #759)
- **Inline hints**: Hot function optimization
- **Capacity hints**: Minor allocation reduction
- Expected: 1-3% improvement in respective operations

---

## Recommendations

### 1. Run Post-Optimization Benchmarks
After PRs merge, run same benchmarks to measure actual improvement:
```bash
cargo bench -p rustledger-parser --bench parser_bench
cargo bench -p rustledger-core --bench inventory_bench
cargo bench -p rustledger-validate --bench validate_bench
```

### 2. Add CI Benchmarks
Consider adding benchmark CI to track performance regressions:
```yaml
- name: Benchmarks
  run: cargo bench --all-features
```

### 3. Profile Hot Paths
Use `cargo-llvm-cov` to identify remaining hot paths:
```bash
cargo llvm-cov --lib --all-features --html
```

### 4. Compare with Python Beancount
Benchmark against Python beancount for real-world comparison:
```bash
# Python
bean-check test.beancount

# Rust
rledger check test.beancount
```

---

## Benchmark Files

| Crate | File | Purpose |
|-------|------|---------|
| parser | `benches/parser_bench.rs` | Tokenize and parse performance |
| core | `benches/inventory_bench.rs` | Inventory operations (reduce, merge) |
| validate | `benches/validate_bench.rs` | Validation performance |
| query | `benches/query_bench.rs` | BQL query execution |
| rustledger | `benches/pipeline_bench.rs` | Full pipeline (load + validate) |

---

## Next Steps

1. **Wait for PRs to merge**
2. **Run post-optimization benchmarks**
3. **Compare before/after metrics**
4. **Update this document with results**