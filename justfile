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

# Run TLA+ model checker on AccountLifecycle spec
tla-lifecycle: tla-setup
    java -XX:+UseParallelGC -Xmx4g -jar tools/tla2tools.jar \
        -config spec/tla/AccountLifecycle.cfg \
        -workers auto \
        -deadlock \
        spec/tla/AccountLifecycle.tla

# Run TLA+ model checker on DirectiveOrdering spec
tla-ordering: tla-setup
    java -XX:+UseParallelGC -Xmx4g -jar tools/tla2tools.jar \
        -config spec/tla/DirectiveOrdering.cfg \
        -workers auto \
        -deadlock \
        spec/tla/DirectiveOrdering.tla

# Run TLA+ model checker on ValidationErrors spec
tla-validate: tla-setup
    java -XX:+UseParallelGC -Xmx4g -jar tools/tla2tools.jar \
        -config spec/tla/ValidationErrors.cfg \
        -workers auto \
        -deadlock \
        spec/tla/ValidationErrors.tla

# Run TLA+ model checker on PriceDatabase spec
tla-price: tla-setup
    java -XX:+UseParallelGC -Xmx4g -jar tools/tla2tools.jar \
        -config spec/tla/PriceDatabase.cfg \
        -workers auto \
        -deadlock \
        spec/tla/PriceDatabase.tla

# Run all TLA+ specs
tla-all: tla-inventory tla-booking tla-balance tla-lifecycle tla-ordering tla-validate tla-price
    @echo "All TLA+ specifications verified"

# Run specific TLA+ spec by name
tla-check spec:
    java -XX:+UseParallelGC -Xmx4g -jar tools/tla2tools.jar \
        -config spec/tla/{{spec}}.cfg \
        -workers auto \
        -deadlock \
        spec/tla/{{spec}}.tla

# ============================================================================
# TLA+ PROOFS (TLAPS)
# ============================================================================

# Check TLAPS proofs for Inventory
tla-prove-inventory:
    @echo "Checking InventoryProofs.tla..."
    @if command -v tlapm > /dev/null 2>&1; then \
        tlapm --threads 4 spec/tla/InventoryProofs.tla; \
    else \
        echo "TLAPS not installed. Install from: https://tla.msr-inria.inria.fr/tlaps/"; \
        echo "Skipping proof verification."; \
    fi

# Check TLAPS proofs for BookingMethods
tla-prove-booking:
    @echo "Checking BookingMethodsProofs.tla..."
    @if command -v tlapm > /dev/null 2>&1; then \
        tlapm --threads 4 spec/tla/BookingMethodsProofs.tla; \
    else \
        echo "TLAPS not installed. Install from: https://tla.msr-inria.inria.fr/tlaps/"; \
        echo "Skipping proof verification."; \
    fi

# Check TLAPS proofs for ValidationErrors
tla-prove-validate:
    @echo "Checking ValidationErrorsProofs.tla..."
    @if command -v tlapm > /dev/null 2>&1; then \
        tlapm --threads 4 spec/tla/ValidationErrorsProofs.tla; \
    else \
        echo "TLAPS not installed. Install from: https://tla.msr-inria.inria.fr/tlaps/"; \
        echo "Skipping proof verification."; \
    fi

# Check all TLAPS proofs
tla-prove-all: tla-prove-inventory tla-prove-booking tla-prove-validate
    @echo "All TLAPS proofs checked"

# ============================================================================
# REFINEMENT CHECKING
# ============================================================================

# Check Inventory refinement (Rust → TLA+)
tla-refine-inventory: tla-setup
    java -XX:+UseParallelGC -Xmx4g -jar tools/tla2tools.jar \
        -config spec/tla/InventoryRefinement.cfg \
        -workers auto \
        -deadlock \
        spec/tla/InventoryRefinement.tla

# Check Booking refinement (Rust → TLA+)
tla-refine-booking: tla-setup
    java -XX:+UseParallelGC -Xmx4g -jar tools/tla2tools.jar \
        -config spec/tla/BookingRefinement.cfg \
        -workers auto \
        -deadlock \
        spec/tla/BookingRefinement.tla

# Check all refinements
tla-refine-all: tla-refine-inventory tla-refine-booking
    @echo "All refinement checks passed"

# ============================================================================
# APALACHE (Symbolic Model Checking)
# ============================================================================

# Setup Apalache (download if not present)
apalache-setup:
    @if [ ! -f tools/apalache/bin/apalache-mc ]; then \
        mkdir -p tools && \
        echo "Downloading Apalache..." && \
        curl -sL https://github.com/informalsystems/apalache/releases/download/v0.44.2/apalache-0.44.2.tgz | \
            tar -xz -C tools && \
        mv tools/apalache-0.44.2 tools/apalache && \
        echo "Downloaded tools/apalache"; \
    else \
        echo "Apalache already present"; \
    fi

# Run Apalache on Inventory spec
apalache-inventory: apalache-setup
    tools/apalache/bin/apalache-mc check \
        --config=spec/tla/Inventory.cfg \
        spec/tla/Inventory.tla

# Run Apalache on BookingMethods spec
apalache-booking: apalache-setup
    tools/apalache/bin/apalache-mc check \
        --config=spec/tla/BookingMethods.cfg \
        spec/tla/BookingMethods.tla

# Run Apalache on ValidationErrors spec
apalache-validate: apalache-setup
    tools/apalache/bin/apalache-mc check \
        --config=spec/tla/ValidationErrors.cfg \
        spec/tla/ValidationErrors.tla

# Run Apalache on specific spec
apalache-check spec: apalache-setup
    tools/apalache/bin/apalache-mc check \
        --config=spec/tla/{{spec}}.cfg \
        spec/tla/{{spec}}.tla

# Run Apalache on all specs
apalache-all: apalache-inventory apalache-booking apalache-validate
    @echo "All Apalache checks complete"

# ============================================================================
# TLA+ TRACE TO TEST
# ============================================================================

# Run TLC and capture counterexample trace as JSON
tla-trace spec: tla-setup
    @mkdir -p traces
    java -XX:+UseParallelGC -Xmx4g -jar tools/tla2tools.jar \
        -config spec/tla/{{spec}}.cfg \
        -workers auto \
        -deadlock \
        spec/tla/{{spec}}.tla 2>&1 | \
        python3 scripts/tla_trace_to_json.py --spec {{spec}} > traces/{{spec}}_trace.json || true
    @if [ -s traces/{{spec}}_trace.json ]; then \
        echo "Trace saved to traces/{{spec}}_trace.json"; \
    else \
        echo "No counterexample found (spec passed)"; \
        rm -f traces/{{spec}}_trace.json; \
    fi

# Generate Rust test from trace JSON
tla-gen-test trace_file:
    python3 scripts/trace_to_rust_test.py {{trace_file}}

# Generate Rust tests from all traces
tla-gen-all-tests:
    @if ls traces/*.json 1> /dev/null 2>&1; then \
        python3 scripts/trace_to_rust_test.py traces/*.json; \
    else \
        echo "No trace files found in traces/"; \
    fi

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
