# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Features

- `ParseErrorEntry.kind_code` exposes the stable numeric discriminant
  from `rustledger_parser::ParseError::kind_code()`. Codes 1-26
  documented in `openrpc.json`'s `ParseErrorEntry` schema. Notably,
  `kind_code === 26` is `BomInDirectiveBody` (mid-file UTF-8 BOM
  detected). RPC clients can detect this structurally and surface a
  'Remove BOM' fix-it action without regex-matching the message body.
- `ParseErrorEntry.hint` carries the actionable suggestion attached at
  the parser emission site (e.g., 'Remove the U+FEFF byte…' for the
  BOM diagnostic). Render below `message` as a help/fix-it line.
- `ParseErrorEntry.span` carries the byte range of the failed entry
  for source-location-aware UX (highlight, navigate-to).

### Breaking Changes

- **Wire shape (major bump 1.0 → 2.0):** `error.data.errors` on
  `beancount_parse_error` (-32000) responses is now
  `ParseErrorEntry[]` (per-error object with `message`, `kind_code`,
  `hint`, `span`) instead of the previous `string[]` of rendered
  messages. Bump `API_VERSION` to `2.0` per the major-on-break policy
  documented on `API_VERSION` in `src/lib.rs` (round-19 correction:
  this change shipped briefly as 1.1, which violated the policy).
  Clients negotiate via `api_version` on every response payload; v1.x
  clients that parse errors as `string[]` should refuse to talk to a
  v2.x server. Migration recipe for cross-version clients that want
  to bridge both:
  ```js
  errors.map(e => typeof e === 'string'
    ? { message: e, kind_code: null, hint: null, span: null }
    : e)
  ```
  The `ParseErrorEntry` schema allows `null` for
  `kind_code`/`hint`/`span` so legacy entries bridged through the
  recipe above still validate; 2.0+ servers always emit the
  integer/object form. See `README.md` for the full
  `ParseErrorEntry` shape and an example.

## [0.13.0](https://github.com/rustledger/rustledger/compare/v0.12.0...v0.13.0) - 2026-04-21

### Bug Fixes

- address review comments on chrono-to-jiff migration
- clippy, formatting, and cast precedence issues
- add NaiveDate import and fix mangled parse in FFI WASI
- resolve Rust 1.95 clippy warnings and remaining jiff issues

### Refactoring

- remove more dead code found in second pass
- migrate remaining crates from chrono to jiff

## [0.12.0](https://github.com/rustledger/rustledger/compare/v0.11.0...v0.12.0) - 2026-04-11

### Bug Fixes

- *(booking)* apply per-account methods across all consumers

### Documentation

- clarify phase field documentation on Error struct

### Features

- add phase field to JSON diagnostics for parse/validate separation

### Testing

- add unit tests for diagnostic phase field

## [0.11.0](https://github.com/rustledger/rustledger/compare/v0.10.1...v0.11.0) - 2026-04-02

### Bug Fixes

- *(ffi-wasi)* handle Value::Set variant in convert.rs
- address PR review comments
- update sha2 usage in ffi-wasi for MSRV 1.90 compatibility

## [0.10.1](https://github.com/rustledger/rustledger/compare/v0.10.0...v0.10.1) - 2026-03-12

### Documentation

- comprehensive documentation audit and corrections

## [0.10.0](https://github.com/rustledger/rustledger/compare/v0.9.0...v0.10.0) - 2026-02-18

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

- consolidate rledger-\* binaries into single rledger binary
- *(ffi-wasi)* split commands into separate modules
- *(ffi-wasi)* split main.rs into modular structure
- rename rustledger-ffi-py to rustledger-ffi-wasi
- *(bench)* fair benchmarks with two separate charts

### Ci

- add benchmark history tracking and chart generation
- add nightly benchmark comparison vs Python beancount

### Style

- apply cargo fmt
