# Performance Targets and Benchmarks

This document defines performance targets for rustledger.

## Performance Goals

### Primary Target

**10x faster than Python beancount** for typical workloads.

| Metric | Python Beancount | rustledger Target |
|--------|------------------|---------------------|
| Parse + validate (10K txns) | 4-6 seconds | < 500ms |
| Parse + validate (100K txns) | 40-60 seconds | < 5 seconds |
| Memory usage (10K txns) | ~500 MB | < 100 MB |
| Startup time | ~1 second | < 50ms |

### Secondary Targets

- **Incremental re-parse**: < 100ms for single file change
- **Query execution**: < 100ms for typical queries
- **WASM bundle size**: < 2 MB (gzipped)

## Benchmark Scenarios

### B1: Parse Only

Parse a file to AST without processing:

```rust
#[bench]
fn bench_parse_10k_transactions(b: &mut Bencher) {
    let source = generate_ledger(10_000);
    b.iter(|| {
        parse(&source).unwrap()
    });
}
```

**Target**: 50ms for 10K transactions

### B2: Full Processing

Parse, interpolate, book, validate:

```rust
#[bench]
fn bench_full_process_10k(b: &mut Bencher) {
    let source = generate_ledger(10_000);
    b.iter(|| {
        Ledger::load_from_string(&source).unwrap()
    });
}
```

**Target**: 500ms for 10K transactions

### B3: Query Execution

Execute BQL query on loaded ledger:

```rust
#[bench]
fn bench_query_sum_expenses(b: &mut Bencher) {
    let ledger = load_test_ledger();
    b.iter(|| {
        ledger.query("SELECT account, sum(position) WHERE account ~ 'Expenses' GROUP BY 1")
    });
}
```

**Target**: 50ms for 10K transactions

### B4: Memory Usage

Peak memory during processing:

```rust
#[test]
fn test_memory_usage_10k() {
    let before = get_memory_usage();
    let ledger = load_test_ledger(10_000);
    let after = get_memory_usage();

    assert!(after - before < 100 * 1024 * 1024);  // < 100 MB
}
```

**Target**: < 10 KB per transaction

### B5: Startup Time

Time from process start to ready:

```bash
$ time rustledger --version
real    0m0.010s  # Target: < 50ms
```

### B6: WASM Size

Compressed bundle size for browser:

```bash
$ wasm-pack build --target web
$ gzip -c pkg/beancount_wasm_bg.wasm | wc -c
# Target: < 2 MB
```

## Complexity Bounds

### Time Complexity

| Operation | Complexity | Notes |
|-----------|------------|-------|
| Parse | O(n) | Linear in input size |
| Sort directives | O(n log n) | Stable sort |
| Interpolation | O(n × p) | n transactions, p postings each |
| Booking (FIFO/LIFO) | O(n × l) | n reductions, l lots average |
| Booking (STRICT) | O(n × l) | Usually l = 1 |
| Balance check | O(n) | Linear scan |
| Query (full scan) | O(n) | All transactions |
| Query (with GROUP BY) | O(n log g) | g groups |

### Space Complexity

| Data Structure | Complexity | Notes |
|----------------|------------|-------|
| AST | O(n) | Linear in input |
| Inventories | O(a × l) | a accounts, l lots each |
| String interner | O(s) | s unique strings |
| Source map | O(f) | f files |

## Optimization Strategies

### 1. String Interning

Intern account names and currencies to reduce memory and enable fast comparison:

```rust
// Before: 24 bytes per account reference
account: String

// After: 4 bytes per account reference
account: StringId  // index into interner
```

**Expected impact**: 50% memory reduction

### 2. Arena Allocation

Allocate AST nodes in arena for cache-friendly access:

```rust
// All directives in contiguous memory
let arena = Arena::new();
for directive in parse(&source) {
    arena.alloc(directive);
}
```

**Expected impact**: 2x parse speed improvement

### 3. Parallel Parsing

Parse included files in parallel:

```rust
let files: Vec<_> = collect_includes(&main_file);
let asts: Vec<_> = files.par_iter()
    .map(|f| parse_file(f))
    .collect();
```

**Expected impact**: Nx speedup for N files on N cores

### 4. Lazy Inventory Computation

Compute inventories on-demand rather than eagerly:

```rust
impl Ledger {
    pub fn inventory(&self, account: &str, date: NaiveDate) -> Inventory {
        // Compute only up to requested date
        self.compute_inventory_at(account, date)
    }
}
```

**Expected impact**: Faster bean-check for partial validation

### 5. SIMD for Decimal Arithmetic

Use SIMD for batch decimal operations:

```rust
// Sum many amounts at once
fn sum_amounts_simd(amounts: &[Amount]) -> Decimal {
    // Use portable_simd when stable
}
```

**Expected impact**: 2-4x for heavy aggregation queries

## Profiling

### CPU Profiling

```bash
# With perf
perf record --call-graph dwarf ./target/release/rustledger check large.beancount
perf report

# With flamegraph
cargo flamegraph -- check large.beancount
```

### Memory Profiling

```bash
# With heaptrack
heaptrack ./target/release/rustledger check large.beancount
heaptrack_gui heaptrack.*.gz

# With valgrind massif
valgrind --tool=massif ./target/release/rustledger check large.beancount
ms_print massif.out.*
```

### Benchmarking

```bash
# Run all benchmarks
cargo bench

# Run specific benchmark
cargo bench --bench parse

# Compare against baseline
cargo bench -- --save-baseline main
git checkout feature-branch
cargo bench -- --baseline main
```

## Regression Prevention

### CI Benchmarks

Run benchmarks in CI to catch regressions:

```yaml
# .github/workflows/bench.yml
- name: Run benchmarks
  run: cargo bench -- --save-baseline ci

- name: Check for regression
  run: |
    cargo bench -- --baseline ci --threshold 10
    # Fail if >10% regression
```

### Benchmark Database

Track benchmark results over time:

```bash
# Save results to JSON
cargo bench -- --format json > bench-results.json

# Upload to tracking service
curl -X POST https://bench.example.com/upload -d @bench-results.json
```

## Real-World Test Files

### Small (< 1K transactions)
- Personal monthly ledger
- Target: < 50ms

### Medium (1K - 10K transactions)
- Personal yearly ledger
- Small business books
- Target: < 500ms

### Large (10K - 100K transactions)
- Multi-year personal finance
- Medium business books
- Target: < 5 seconds

### Very Large (> 100K transactions)
- Enterprise accounting
- Decade of personal finance
- Target: < 30 seconds

## Comparison Benchmark

Compare against Python beancount on same file:

```bash
#!/bin/bash
FILE=$1

echo "Python beancount:"
time python -m beancount.scripts.check "$FILE"

echo ""
echo "rustledger:"
time rustledger check "$FILE"
```

Expected output:
```
Python beancount:
real    0m4.523s
user    0m4.312s
sys     0m0.198s

rustledger:
real    0m0.342s
user    0m0.298s
sys     0m0.043s
```
