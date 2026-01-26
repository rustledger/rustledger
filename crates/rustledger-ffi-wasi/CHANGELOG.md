# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).


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
