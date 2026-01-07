# Justfile for beancount-rs
# https://github.com/casey/just

# Default recipe - show help
default:
    @just --list

# ============================================================================
# BUILD
# ============================================================================

# Build in debug mode
build:
    cargo build --all-targets

# Build in release mode
build-release:
    cargo build --release --all-targets

# Build WASM target
build-wasm:
    cargo build --target wasm32-unknown-unknown --release -p beancount-wasm

# Build with wasm-pack (for npm)
build-wasm-pack:
    wasm-pack build --target web crates/beancount-wasm

# ============================================================================
# TEST
# ============================================================================

# Run all tests
test:
    cargo nextest run

# Run tests with standard cargo test
test-cargo:
    cargo test --all-targets

# Run tests with coverage
test-cov:
    cargo llvm-cov --all-features --lcov --output-path lcov.info
    cargo llvm-cov report --html

# Run property tests with more iterations
test-prop iterations="10000":
    PROPTEST_CASES={{iterations}} cargo test --features proptest

# Run specific test
test-one name:
    cargo nextest run {{name}}

# ============================================================================
# LINT & FORMAT
# ============================================================================

# Run clippy
clippy:
    cargo clippy --all-targets --all-features -- -D warnings

# Format code
fmt:
    treefmt

# Check formatting without changes
fmt-check:
    treefmt --fail-on-change

# Run all lints
lint: clippy fmt-check
    cargo doc --no-deps --all-features
    @echo "✓ All lints passed"

# ============================================================================
# CHECK
# ============================================================================

# Run all checks (like CI)
check:
    nix flake check

# Quick check
check-quick:
    cargo check --all-targets

# Audit dependencies for security
audit:
    cargo audit

# Check dependency licenses
deny:
    cargo deny check

# Check for unused dependencies
udeps:
    cargo +nightly udeps --all-targets

# ============================================================================
# BENCHMARK
# ============================================================================

# Run benchmarks
bench:
    cargo bench

# Run specific benchmark
bench-one name:
    cargo bench -- {{name}}

# Compare against baseline
bench-compare baseline="main":
    cargo bench -- --baseline {{baseline}}

# ============================================================================
# FUZZ
# ============================================================================

# List fuzz targets
fuzz-list:
    cargo +nightly fuzz list

# Run fuzzer (requires nightly)
fuzz target duration="60":
    cargo +nightly fuzz run {{target}} -- -max_total_time={{duration}}

# ============================================================================
# TLA+
# ============================================================================

# Download TLA+ tools if not present
tla-setup:
    @if [ ! -f tools/tla2tools.jar ]; then \
        mkdir -p tools && \
        echo "Downloading TLA+ tools..." && \
        wget -q https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar \
            -O tools/tla2tools.jar && \
        echo "Downloaded tools/tla2tools.jar"; \
    else \
        echo "TLA+ tools already present"; \
    fi

# Run TLA+ model checker on Inventory spec
tla-inventory: tla-setup
    java -XX:+UseParallelGC -Xmx4g -jar tools/tla2tools.jar \
        -config spec/tla/Inventory.cfg \
        -workers auto \
        -deadlock \
        spec/tla/Inventory.tla

# Run TLA+ model checker on BookingMethods spec
tla-booking: tla-setup
    java -XX:+UseParallelGC -Xmx4g -jar tools/tla2tools.jar \
        -config spec/tla/BookingMethods.cfg \
        -workers auto \
        -deadlock \
        spec/tla/BookingMethods.tla

# Run TLA+ model checker on TransactionBalance spec
tla-balance: tla-setup
    java -XX:+UseParallelGC -Xmx4g -jar tools/tla2tools.jar \
        -config spec/tla/TransactionBalance.cfg \
        -workers auto \
        -deadlock \
        spec/tla/TransactionBalance.tla

# Run all TLA+ specs
tla-all: tla-inventory tla-booking tla-balance
    @echo "All TLA+ specifications verified"

# Run specific TLA+ spec by name
tla-check spec:
    java -XX:+UseParallelGC -Xmx4g -jar tools/tla2tools.jar \
        -config spec/tla/{{spec}}.cfg \
        -workers auto \
        -deadlock \
        spec/tla/{{spec}}.tla

# ============================================================================
# COMPATIBILITY
# ============================================================================

# Fetch test vectors from upstream
fetch-tests:
    ./scripts/fetch-test-vectors.sh

# Run compatibility tests against Python beancount
compat:
    ./tests/compat/run.sh

# ============================================================================
# DOCS
# ============================================================================

# Build documentation
doc:
    cargo doc --no-deps --all-features --open

# Build mdbook documentation
doc-book:
    mdbook build docs/

# Serve mdbook with live reload
doc-serve:
    mdbook serve docs/

# ============================================================================
# DEV
# ============================================================================

# Watch and rebuild on changes
watch:
    bacon

# Watch and run tests
watch-test:
    bacon test

# Clean build artifacts
clean:
    cargo clean
    rm -rf result result-*

# Update dependencies
update:
    cargo update
    nix flake update

# Generate changelog
changelog:
    git cliff --unreleased --prepend CHANGELOG.md

# Count lines of code
loc:
    tokei --exclude spec/fixtures

# Show dependency tree
deps:
    cargo tree

# Show outdated dependencies
outdated:
    cargo outdated

# ============================================================================
# RELEASE
# ============================================================================

# Prepare for release
release-prep version:
    @echo "Preparing release {{version}}"
    cargo set-version {{version}}
    just changelog
    just lint
    just test
    @echo "Ready for release {{version}}"

# Create release build
release-build:
    cargo build --release
    @echo "Binary at: target/release/beancount-rs"
    @ls -lh target/release/beancount-rs
