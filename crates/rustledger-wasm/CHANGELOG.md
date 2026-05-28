# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### ⚠ BREAKING CHANGES

- **Wire shape of `Custom.values`** is now a tagged union
  `{type, value}` instead of raw values (closes #1207). Pre-fix WASM
  emitted each `MetaValue` as its bare JSON form, which made
  `Date`/`String`/`Account`/`Tag`/`Link`/`Number` indistinguishable on
  the wire (all collapsed to JSON strings). Post-fix the shape mirrors
  `rustledger-ffi-wasi`'s `TypedValue`, e.g.
  `{type: "date", value: "2024-03-31"}`. The new `TypedValue` interface
  is exported from the TypeScript declarations. JS consumers reading
  positional values from `custom` directives must branch on `.type`
  and read `.value`.

- **Transaction `payee` and `narration` shape change** (closes
  #1221). Pre-fix: WASM emitted `"payee": null` when the transaction
  had no payee, and `"narration": ""` when the narration was empty.
  Post-fix: both fields are absent on the wire in their respective
  empty cases, matching FFI-WASI's `skip_serializing_if`-driven
  shape. JS consumers using `"payee" in t` (now `false` instead of
  `true` when absent) or `t.narration === ""` (now `undefined`
  instead of `""` when empty) must update. The hand-written `.d.ts`
  files are updated to `payee?: string` and `narration?: string`.

- **TypeScript declarations consolidated into a single generated file**
  (closes #1218 Phase 1, ADR-0004). The two hand-maintained files
  `beancount.d.ts` and `beancount_wasm.d.ts` are deleted and replaced
  by `crates/rustledger-wasm/bindings/index.d.ts`, generated from the
  Rust DTOs via `ts-rs` (run `scripts/regen-bindings.sh` after any
  wire-format change). Type *shapes* are equivalent or narrower; the
  file layout is the breaking change. Consumers importing from the
  old paths must update to import from the single bundle. CI fails
  the PR if a DTO changes without regenerating the bundle.

  Type name changes in the process:
  - The per-variant directive interfaces (`TransactionDirective`,
    `BalanceDirective`, ...) are gone; the discriminated union is
    inlined on `DirectiveJson`. Use `Extract<DirectiveJson, { type:
    "transaction" }>` for the per-variant type.
  - `Amount` is now `AmountValue` (the Rust DTO name); narrow via a
    type alias on the consumer side if you want the old name.
  - `Posting` is now `PostingJson`; `Directive` is now `DirectiveJson`.
  - `Error` is now `BeancountError` (avoiding the JS-builtin
    `Error` shadow). All other public types -- Severity,
    ParseResult, Ledger, LedgerOptions, ValidationResult,
    QueryResult, CellValue, PositionValue, CostValue, FormatResult,
    PadResult, plus the plugin types (PluginResult, PluginInfo),
    BQL completion types (CompletionJson, CompletionResultJson),
    and the LSP-like editor types (EditorCompletion, CompletionKind,
    EditorCompletionResult, EditorHoverInfo, EditorRange,
    EditorLocation, EditorDocumentSymbol, SymbolKind, ReferenceKind,
    EditorReference, EditorReferencesResult) -- keep their Rust
    names. 34 types in the bundle.

- **TypeScript surfaces fully converged** (closes #1224, ADR-0004
  Phase 2). The inline `typescript_custom_section` DTO block in
  `src/lib.rs` (~300 lines of hand-maintained types) is replaced by
  `include_str!("../bindings/index.d.ts")`, so the wasm-bindgen-
  generated `pkg/*.d.ts` and the importable `bindings/index.d.ts` are
  now the **same** types -- no duplication, no drift. JS consumers
  using only the wasm-bindgen-generated `.d.ts` now see the same new
  names that direct-bundle consumers got in Phase 1
  (`DirectiveJson`, `PostingJson`, etc.). One additional rename: the
  Rust DTO `Ledger` now emits `LedgerJson` on the TS side to avoid
  colliding with the wasm-bindgen `Ledger` class (the runtime
  wrapper). `LedgerJson` is the wire shape returned by `parse(...)`
  and stored on `ParseResult.ledger`; `Ledger` is the class
  instantiated via `Ledger.fromFiles(...)`.

  Remaining inline TS in `src/lib.rs`: only the wasm-bindgen-managed
  surface that **can't** go in the bundle -- the `ParsedLedger` and
  `Ledger` classes, the `FileMap` utility type, and the standalone
  function signatures (`parseMultiFile`, `validateMultiFile`,
  `queryMultiFile`, `hashSources`). ~150 lines of necessary glue,
  down from ~480.

## [0.13.0](https://github.com/rustledger/rustledger/compare/v0.12.0...v0.13.0) - 2026-04-21

### Bug Fixes

- resolve Rust 1.95 clippy warnings and remaining jiff issues

### Features

- expose option warnings (E7001–E7006) in LSP and WASM

### Refactoring

- fix false-positive dead_code suppression, narrow WASM visibility
- *(core)* replace chrono with jiff in rustledger-core
- migrate remaining crates from chrono to jiff

## [0.12.0](https://github.com/rustledger/rustledger/compare/v0.11.0...v0.12.0) - 2026-04-11

### Bug Fixes

- *(wasm)* run booking engine in query and validation paths
- *(wasm)* sort directives by date and use Strict booking method
- *(wasm)* address Copilot review feedback
- *(wasm)* store multi-file errors as validation_errors, not parse_errors
- address Copilot review feedback on WASM cache
- *(booking)* apply per-account methods across all consumers

### Documentation

- *(wasm)* update README and crate docs for Ledger class

### Features

- *(wasm)* add ParsedLedger.fromFiles() for multi-file ledgers
- *(wasm)* enable completions on multi-file ParsedLedger
- *(wasm)* add serialize/fromCache for browser ledger caching

### Refactoring

- *(wasm)* rename load_and_interpolate to load_and_book
- *(wasm)* use shared process() pipeline from rustledger-loader
- *(wasm)* split into ParsedLedger (single-file) and Ledger (multi-file)
- *(core)* deduplicate extract_accounts/currencies/payees
- extract reintern_directive helper for plain and Spanned usage

### Testing

- add roundtrip tests and CHANGELOG for WASM cache

### Features

- Add `serialize`/`fromCache` for browser ledger caching (OPFS/IndexedDB)
- Add `hashSources` for SHA-256 cache-invalidation fingerprinting

## [0.11.0](https://github.com/rustledger/rustledger/compare/v0.10.1...v0.11.0) - 2026-04-02

### Bug Fixes

- address PR review comments

### Features

- *(bql)* support numeric and mixed-type sets in IN operator
- *(wasm)* add multi-file API for include resolution

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

- consolidate rledger-\* binaries into single rledger binary
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

- consolidate rledger-\* binaries into single rledger binary
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
- \[**breaking**\] upgrade to Rust 2024 edition and MSRV 1.85
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

- \[**breaking**\] upgrade to Rust 2024 edition and MSRV 1.85
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

- \[**breaking**\] upgrade to Rust 2024 edition and MSRV 1.85
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

- \[**breaking**\] upgrade to Rust 2024 edition and MSRV 1.85
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
