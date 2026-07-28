# Justfile for rustledger
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
    cargo build --target wasm32-unknown-unknown --release -p rustledger-wasm

# Build with wasm-pack (for npm)
build-wasm-pack:
    wasm-pack build --target web crates/rustledger-wasm

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

# Run tests only for crates with uncommitted changes (fast pre-push check)
test-changed:
    #!/usr/bin/env bash
    set -eo pipefail
    changed_crates=$(git diff --name-only HEAD 2>/dev/null | grep '^crates/' | cut -d/ -f2 | sort -u || true)
    if [ -z "$changed_crates" ]; then
        echo "No crate changes detected."
        exit 0
    fi
    failed=0
    for crate in $changed_crates; do
        pkg="rustledger-${crate#rustledger-}"
        # Normalize: if crate dir is already "rustledger-foo", don't double-prefix
        if [[ "$crate" == rustledger-* ]]; then
            pkg="$crate"
        elif [[ "$crate" == "rustledger" ]]; then
            pkg="rustledger"
        fi
        # Check if the package exists before trying to test it
        if ! cargo pkgid -p "$pkg" > /dev/null 2>&1; then
            echo "  (skipped: $pkg not a cargo package)"
            continue
        fi
        echo "==> Testing $pkg"
        if ! cargo test -p "$pkg" --all-features; then
            failed=1
        fi
    done
    if [ "$failed" -ne 0 ]; then
        echo ""
        echo "Some tests failed!"
        exit 1
    fi

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

#
# These recipes are the local counterpart to the scheduled `Mutation
# Testing` workflow (.github/workflows/mutation.yml); see issue #1238.
# `--all-features` mirrors that job so local results match CI (e.g. the
# `fuzz`-gated constructors in rustledger-core are mutated). Filtering
# config lives in .cargo/mutants.toml.

# Mutation-testing audit on the curated crates (rustledger-core +
# rustledger-parser). Slow: ~10-60 min/crate. Surviving ("missed") mutants
# are reviewed by hand — add a test, or annotate why un-killable. Pass extra
# cargo-mutants args through, e.g. `just mutants --file src/inventory/booking.rs`.
mutants *ARGS:
    cargo mutants --package rustledger-core --package rustledger-parser {{ARGS}} -- --all-features

# Same audit scoped to a single crate, e.g. `just mutants-crate rustledger-core`.
mutants-crate package *ARGS:
    cargo mutants --package {{package}} {{ARGS}} -- --all-features

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

# Run specific TLA+ spec by name
tla-check spec:
    java -XX:+UseParallelGC -Xmx4g -jar tools/tla2tools.jar \
        -config spec/tla/{{spec}}.cfg \
        -workers auto \
        -deadlock \
        spec/tla/{{spec}}.tla

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

# Run Apalache on specific spec
apalache-check spec: apalache-setup
    tools/apalache/bin/apalache-mc check \
        --config=spec/tla/{{spec}}.cfg \
        spec/tla/{{spec}}.tla

# ============================================================================
# TLA+ TRACE TO TEST
# ============================================================================

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
    @echo "Binaries at: target/release/rledger-*"
    @ls -lh target/release/rledger-*

# ============================================================================
# PACKAGING
# ============================================================================

# Test AUR PKGBUILD locally (requires Docker)
test-aur:
    ./packaging/arch/test-pkgbuild.sh

# Push PKGBUILD to AUR (after testing!)
push-aur:
    #!/usr/bin/env bash
    set -euo pipefail
    cd /tmp
    rm -rf aur-rustledger-push
    git clone ssh://aur@aur.archlinux.org/rustledger.git aur-rustledger-push
    cp "$OLDPWD/packaging/arch/rustledger/PKGBUILD" aur-rustledger-push/
    cd aur-rustledger-push
    makepkg --printsrcinfo > .SRCINFO 2>/dev/null || echo "Warning: makepkg not available, .SRCINFO not updated"
    git add -A
    git diff --cached --stat
    echo ""
    read -p "Push to AUR? [y/N] " -n 1 -r
    echo
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        git commit -m "Update to $(grep pkgver= PKGBUILD | cut -d= -f2)"
        git push origin master
        echo "✓ Pushed to AUR"
    else
        echo "Aborted"
    fi
