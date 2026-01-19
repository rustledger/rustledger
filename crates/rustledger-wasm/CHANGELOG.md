# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).


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
