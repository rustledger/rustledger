# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).


## [0.9.1](https://github.com/rustledger/rustledger/compare/v0.9.0...v0.9.1) - 2026-02-18

### Bug Fixes

- address PR review comments

### Features

- *(ci)* add per-platform status badges to README

## [0.8.8](https://github.com/rustledger/rustledger/compare/v0.8.7...v0.8.8) - 2026-02-14

### Bug Fixes

- *(docs)* address Copilot review feedback on PR #351

### Documentation

- comprehensive documentation overhaul

## [0.8.7](https://github.com/rustledger/rustledger/compare/v0.8.6...v0.8.7) - 2026-02-14

### Bug Fixes

- batch request per-element error handling & add unit tests
- address Copilot review feedback on JSON-RPC implementation

### Features

- *(ffi-wasi)* convert to JSON-RPC 2.0 protocol

## [0.8.6](https://github.com/rustledger/rustledger/compare/v0.8.5...v0.8.6) - 2026-02-09

### Miscellaneous

- update Cargo.lock dependencies

## [0.8.5](https://github.com/rustledger/rustledger/compare/v0.8.4...v0.8.5) - 2026-02-08

### Bug Fixes

- *(ffi)* revert display_precision clone due to FxHashMap type mismatch
- *(ffi)* address review feedback

### Features

- *(ffi)* add missing options and entry fields to FFI output

## [0.8.4](https://github.com/rustledger/rustledger/compare/v0.8.3...v0.8.4) - 2026-02-06

### Bug Fixes

- *(ffi-wasi)* use HashMap for FFI Posting meta field

### Performance

- optimize hash maps, add parallel query execution, improve test coverage

## [0.8.3](https://github.com/rustledger/rustledger/compare/v0.8.2...v0.8.3) - 2026-02-05

### Miscellaneous

- update Cargo.lock dependencies

## [0.8.0](https://github.com/rustledger/rustledger/releases/tag/v0.8.0) - 2026-01-28

### Bug Fixes

- *(balance)* propagate tolerance options and preserve total costs/prices

### Style

- fix clippy warnings after MSRV alignment

## [0.7.5](https://github.com/rustledger/rustledger/compare/v0.7.4...v0.7.5) - 2026-01-26

### Miscellaneous

- update Cargo.lock dependencies

## [0.7.4](https://github.com/rustledger/rustledger/compare/v0.7.3...v0.7.4) - 2026-01-26

### Miscellaneous

- update Cargo.lock dependencies

## [0.7.2](https://github.com/rustledger/rustledger/compare/v0.7.1...v0.7.2) - 2026-01-25

### Performance

- box heavy Value variants and avoid balance prefix alloc

## [0.7.0](https://github.com/rustledger/rustledger/releases/tag/v0.7.0) - 2026-01-25

### Bug Fixes

- *(ffi-wasi)* add Metadata and Interval Value variant handling
- *(ffi,wasm)* remove duplicate "Query parse error" prefix
- *(booking,ffi)* run booking in FFI and normalize total prices
- *(ffi-wasi)* match beancount clamp_opt behavior
- push benchmark results to separate branch

### Documentation

- update install options in README
- fix documentation inconsistencies and add crate READMEs
- streamline README
- replace install dropdown with scannable table
- document all installation channels in README
- fix README accuracy issues
- fix plugin count (20 not 14) and mention Python support
- show complete lists for booking methods and plugins
- redesign README for clarity and scannability
- use npm 'next' tag for prerelease badge
- remove static badges, keep only dynamic ones
- add distribution channel badges to README
- add Nix installation to README
- add cargo binstall to README
- add all installation methods to README
- comprehensive README improvements
- use cargo add instead of hardcoded versions

### Features

- *(ffi-wasi)* add clamp-entries command for JSON input
- comprehensive benchmark infrastructure overhaul
- enhance compatibility CI with comprehensive testing
- add Scoop bucket for Windows
- add AUR packaging
- add Docker distribution
- *(core)* implement string interning for performance

### Miscellaneous

- add CLA and commercial licensing notice
- update AUR checksums and remove version from README
- migrate to semver 0.x.y versioning
- *(release)* improve release assets

### Refactoring

- consolidate rledger-* binaries into single rledger binary
- *(ffi-wasi)* split commands into separate modules
- *(ffi-wasi)* split main.rs into modular structure
- rename rustledger-ffi-py to rustledger-ffi-wasi
- *(bench)* fair benchmarks with two separate charts

### Ci

- add benchmark history tracking and chart generation
- add nightly benchmark comparison vs Python beancount

### Style

- apply cargo fmt
