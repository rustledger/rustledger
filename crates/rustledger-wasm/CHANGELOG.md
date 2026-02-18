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

## [0.8.0](https://github.com/rustledger/rustledger/releases/tag/v0.8.0) - 2026-01-28

### Miscellaneous

- reorganize test fixtures and cleanup

### Style

- fix clippy warnings after MSRV alignment

## [0.7.4](https://github.com/rustledger/rustledger/compare/v0.7.3...v0.7.4) - 2026-01-26

### Bug Fixes

- *(ffi,wasm)* remove duplicate "Query parse error" prefix

### Features

- *(ffi-py)* add Fava integration APIs and BQL improvements
- *(bql)* add CREATE TABLE, INSERT, interval(), and SELECT FROM table

### Refactoring

- consolidate rledger-* binaries into single rledger binary
- *(wasm)* split lib.rs into focused modules
- *(wasm)* split editor.rs into modular structure

### Testing

- *(wasm)* add comprehensive editor coverage tests

### Style

- apply cargo fmt

## [0.7.0](https://github.com/rustledger/rustledger/releases/tag/v0.7.0) - 2026-01-25

### Bug Fixes

- *(ffi,wasm)* remove duplicate "Query parse error" prefix

### Features

- *(ffi-py)* add Fava integration APIs and BQL improvements
- *(bql)* add CREATE TABLE, INSERT, interval(), and SELECT FROM table

### Refactoring

- consolidate rledger-* binaries into single rledger binary
- *(wasm)* split lib.rs into focused modules
- *(wasm)* split editor.rs into modular structure

### Testing

- *(wasm)* add comprehensive editor coverage tests

### Style

- apply cargo fmt

## [0.6.0](https://github.com/rustledger/rustledger/releases/tag/v0.6.0) - 2026-01-23

### Bug Fixes

- address Copilot review feedback
- push benchmark results to separate branch
- add nontrapping-float-to-int flag to wasm-opt
- add bulk-memory flag to wasm-opt for newer Rust
- correctly apply interpolation result in WASM bindings
- add interpolation to WASM validate and query

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

- comprehensive benchmark infrastructure overhaul
- enhance compatibility CI with comprehensive testing
- [**breaking**] upgrade to Rust 2024 edition and MSRV 1.85
- add editor_references tool (find all references)
- *(wasm)* add LSP-like editor integration
- add Scoop bucket for Windows
- add AUR packaging
- add Docker distribution
- *(core)* implement string interning for performance
- add shell completions, refactor WASM module, add release workflow
- add format, pads, plugins to WASM module

### Miscellaneous

- add CLA and commercial licensing notice
- update AUR checksums and remove version from README
- migrate to semver 0.x.y versioning
- *(release)* improve release assets

### Performance

- *(lsp,wasm)* add caching and optimize position lookups
- add binary cache and full string interning

### Refactoring

- *(bench)* fair benchmarks with two separate charts
- *(wasm)* improve module with best practices

### Ci

- add benchmark history tracking and chart generation
- add nightly benchmark comparison vs Python beancount

### Style

- fix all import ordering for CI rustfmt

## [0.5.2](https://github.com/rustledger/rustledger/compare/v0.5.1...v0.5.2) - 2026-01-20

### Bug Fixes

- address Copilot review feedback
- push benchmark results to separate branch
- add nontrapping-float-to-int flag to wasm-opt
- add bulk-memory flag to wasm-opt for newer Rust
- correctly apply interpolation result in WASM bindings
- add interpolation to WASM validate and query

### Documentation

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

- [**breaking**] upgrade to Rust 2024 edition and MSRV 1.85
- add editor_references tool (find all references)
- *(wasm)* add LSP-like editor integration
- add Scoop bucket for Windows
- add AUR packaging
- add Docker distribution
- *(core)* implement string interning for performance
- add shell completions, refactor WASM module, add release workflow
- add format, pads, plugins to WASM module

### Miscellaneous

- add CLA and commercial licensing notice
- update AUR checksums and remove version from README
- migrate to semver 0.x.y versioning
- *(release)* improve release assets

### Performance

- *(lsp,wasm)* add caching and optimize position lookups
- add binary cache and full string interning

### Refactoring

- *(bench)* fair benchmarks with two separate charts
- *(wasm)* improve module with best practices

### Ci

- add benchmark history tracking and chart generation
- add nightly benchmark comparison vs Python beancount

### Style

- fix all import ordering for CI rustfmt

## [0.5.1](https://github.com/rustledger/rustledger/compare/v0.5.0...v0.5.1) - 2026-01-19

### Bug Fixes

- address Copilot review feedback
- push benchmark results to separate branch
- add nontrapping-float-to-int flag to wasm-opt
- add bulk-memory flag to wasm-opt for newer Rust
- correctly apply interpolation result in WASM bindings
- add interpolation to WASM validate and query

### Documentation

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

- [**breaking**] upgrade to Rust 2024 edition and MSRV 1.85
- add editor_references tool (find all references)
- *(wasm)* add LSP-like editor integration
- add Scoop bucket for Windows
- add AUR packaging
- add Docker distribution
- *(core)* implement string interning for performance
- add shell completions, refactor WASM module, add release workflow
- add format, pads, plugins to WASM module

### Miscellaneous

- add CLA and commercial licensing notice
- update AUR checksums and remove version from README
- migrate to semver 0.x.y versioning
- *(release)* improve release assets

### Performance

- *(lsp,wasm)* add caching and optimize position lookups
- add binary cache and full string interning

### Refactoring

- *(bench)* fair benchmarks with two separate charts
- *(wasm)* improve module with best practices

### Ci

- add benchmark history tracking and chart generation
- add nightly benchmark comparison vs Python beancount

### Style

- fix all import ordering for CI rustfmt

## [0.5.0](https://github.com/rustledger/rustledger/compare/v0.4.0...v0.5.0) - 2026-01-19

### Bug Fixes

- address Copilot review feedback
- push benchmark results to separate branch
- add nontrapping-float-to-int flag to wasm-opt
- add bulk-memory flag to wasm-opt for newer Rust
- correctly apply interpolation result in WASM bindings
- add interpolation to WASM validate and query

### Documentation

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

- [**breaking**] upgrade to Rust 2024 edition and MSRV 1.85
- add editor_references tool (find all references)
- *(wasm)* add LSP-like editor integration
- add Scoop bucket for Windows
- add AUR packaging
- add Docker distribution
- *(core)* implement string interning for performance
- add shell completions, refactor WASM module, add release workflow
- add format, pads, plugins to WASM module

### Miscellaneous

- add CLA and commercial licensing notice
- update AUR checksums and remove version from README
- migrate to semver 0.x.y versioning
- *(release)* improve release assets

### Performance

- *(lsp,wasm)* add caching and optimize position lookups
- add binary cache and full string interning

### Refactoring

- *(bench)* fair benchmarks with two separate charts
- *(wasm)* improve module with best practices

### Ci

- add benchmark history tracking and chart generation
- add nightly benchmark comparison vs Python beancount

### Style

- fix all import ordering for CI rustfmt

## [0.4.0](https://github.com/rustledger/rustledger/releases/tag/v0.4.0) - 2026-01-18

### Bug Fixes

- address Copilot review feedback
- push benchmark results to separate branch
- add nontrapping-float-to-int flag to wasm-opt
- add bulk-memory flag to wasm-opt for newer Rust
- correctly apply interpolation result in WASM bindings
- add interpolation to WASM validate and query

### Documentation

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

- add editor_references tool (find all references)
- *(wasm)* add LSP-like editor integration
- add Scoop bucket for Windows
- add AUR packaging
- add Docker distribution
- *(core)* implement string interning for performance
- add shell completions, refactor WASM module, add release workflow
- add format, pads, plugins to WASM module

### Miscellaneous

- add CLA and commercial licensing notice
- update AUR checksums and remove version from README
- migrate to semver 0.x.y versioning
- *(release)* improve release assets

### Performance

- *(lsp,wasm)* add caching and optimize position lookups
- add binary cache and full string interning

### Refactoring

- *(bench)* fair benchmarks with two separate charts
- *(wasm)* improve module with best practices

### Ci

- add benchmark history tracking and chart generation
- add nightly benchmark comparison vs Python beancount

### Style

- fix all import ordering for CI rustfmt
