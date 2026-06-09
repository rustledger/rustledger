# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Breaking Changes

- `ParseResult`, `ParseError`, and `ParseErrorKind` are now `#[non_exhaustive]`.
  Downstream consumers that pattern-match on these types must add a wildcard arm:
  ```rust
  // Before - compiled exhaustively pre-this-release:
  match err.kind {
      ParseErrorKind::UnexpectedEof => ...,
      ParseErrorKind::SyntaxError(_) => ...,
      // ... every variant listed
  }

  // After - wildcard arm required:
  match err.kind {
      ParseErrorKind::UnexpectedEof => ...,
      ParseErrorKind::SyntaxError(_) => ...,
      _ => /* fallback for future variants */,
  }
  ```
  Rationale: SemVer-hygiene. Adding a new error variant in a future release is
  no longer a breaking change for consumers that use a wildcard arm.

- `ParseErrorKind::BomInDirectiveBody` is a new structural variant for the
  "BOM byte appears mid-directive" diagnostic (kind_code 26). Previously this
  was reported as a generic `SyntaxError` with a string-matched message; the
  dedicated variant lets downstream tooling (LSP quick-fix, FFI structural
  error reporting) detect the case by `matches!()` rather than substring
  search of the message.

### Features

- `ParseResult::has_leading_bom` records whether the source had a leading UTF-8
  BOM that the parser stripped before tokenization. The formatter uses this
  to round-trip the BOM verbatim, so `format(parse(source))` preserves a
  Windows-encoded file's leading byte sequence even though the parser sees
  BOM-free coordinates.

- Mid-file BOM recovery (round 17): a BOM token at the start of a directive
  position is now consumed and reported as a focused single-BOM diagnostic,
  **without** consuming the following directive into the error span. Previous
  behavior silently dropped the directive immediately after a mid-file BOM
  from `result.directives` - a regression caught by extending the
  `test_mid_file_bom_produces_error` assertion to require both directives
  surviving.

- `ParseError::every_kind_sample()` (doc-hidden, `#[non_exhaustive]`-aware)
  returns one `ParseError` per `ParseErrorKind` variant via an exhaustive
  `match`. Used by integration tests (notably `openrpc_kind_code_sync.rs`)
  to enforce that downstream wire schemas (openrpc.json) list every kind_code
  the parser can emit; compiler-enforced because the inner match is
  exhaustive on `&ParseErrorKind`.

- Crate-root re-exports for the `rowan` types CST consumers need:
  `Direction`, `NodeOrToken`, `TextRange`, `TextSize`, `TokenAtOffset`,
  `WalkEvent`. Downstream crates (notably `rustledger-lsp`) can walk the
  CST through these aliases without taking a direct dependency on `rowan`,
  keeping the dep graph anchored at this crate. `GreenNode` is deliberately
  NOT re-exported - the cursor API is the supported way to traverse.
  **Stability**: these aliases are versioned in lockstep with this crate,
  not with `rowan` directly; a rowan minor bump that touches any of them
  requires a coordinated bump here.

- `ParseResult::account_occurrences`: every `ACCOUNT` token the parser
  consumed (outside `ERROR_NODE` regions), paired with its interned
  value and source-byte range. Mirrors the existing `currency_occurrences`
  field. Populated during the `walk_descendants_once` pass (no extra
  parser traversal pass; one `Account::new` interner call per ACCOUNT
  token in the source). The LSP **rename** handler (phase 5.4) consumes
  this index to emit exact-span edits without resorting to per-directive
  substring search, which used to produce false positives wherever an
  account-name fragment appeared inside a payee string, a STRING-typed
  metadata value, or a comment. ACCOUNT-typed metadata values (e.g.
  `counterparty: Assets:Bank`) DO produce an ACCOUNT token and ARE
  correctly captured / renamed. The sibling LSP handlers (references,
  document_highlight, linked_editing) still walk the typed AST with
  substring search for accounts; migrating them is tracked as a
  phase 5.5+ follow-up. Same `#[non_exhaustive]`-safe addition pattern
  as previous fields.

  **Operational note.** Adding the new field to
  `__baseline_canonical_payload` changes the parser-corpus baseline hash
  for every source containing any ACCOUNT token (i.e., essentially every
  real Beancount file). Downstream consumers caching the canonical
  payload bytes (rkyv archives, content-addressed parser-output caches)
  should refresh after this release. The committed
  `tests/baselines/parser-corpus.manifest` was regenerated as part of
  this change.

## [0.13.0](https://github.com/rustledger/rustledger/compare/v0.12.0...v0.13.0) - 2026-04-21

### Bug Fixes

- rephrase allocation comments to be factual, not empirical
- eliminate redundant contains check in number parsing
- support full Unicode in account names
- address Copilot review - tighten validator, fix Options, update docs
- remove unused NaiveDate imports

### Performance

- avoid allocating empty tag/link/comment Vecs in parser
- fast-path string escape processing for common case
- intern accounts/currencies during parsing to deduplicate allocations
- fast-path number and date parsing to avoid unnecessary allocations
- fast-path decimal parsing for simple beancount numbers
- zero-copy string parsing with Cow for narration/payee

### Refactoring

- *(core)* replace chrono with jiff in rustledger-core
- migrate remaining crates from chrono to jiff

## [0.12.0](https://github.com/rustledger/rustledger/compare/v0.11.0...v0.12.0) - 2026-04-11

### Bug Fixes

- *(parser)* reject 7 invalid inputs per beancount v3 spec
- address Copilot review feedback on parser strict
- align error message wording with Python beancount
- address Copilot review feedback on error message wording
- *(parser)* allow Unicode letters after ASCII start in account names

### Features

- migrate from archived ariadne to miette for error diagnostics

### Testing

- *(parser)* Add 36 new tests for untested functions
- fix 14 fake-coverage tests flagged by Copilot review on #766

## [0.11.0](https://github.com/rustledger/rustledger/compare/v0.10.0...v0.11.0) - 2026-04-02

### Bug Fixes

- support single-character commodity names (e.g., T, V, F)

## [0.10.0](https://github.com/rustledger/rustledger/compare/v0.9.0...v0.10.0) - 2026-02-18

### Bug Fixes

- *(parser)* handle division by zero in expression parser
- address PR review comments

### Features

- *(ci)* add per-platform status badges to README

### Testing

- *(parser)* add regression test for division by zero

## [0.8.8](https://github.com/rustledger/rustledger/compare/v0.8.7...v0.8.8) - 2026-02-14

### Bug Fixes

- *(docs)* address Copilot review feedback on PR #351

### Documentation

- comprehensive documentation overhaul

## [0.8.6](https://github.com/rustledger/rustledger/compare/v0.8.5...v0.8.6) - 2026-02-09

### Bug Fixes

- *(security)* update bytes to 1.11.1 (CVE-2026-25541)

## [0.8.4](https://github.com/rustledger/rustledger/compare/v0.8.3...v0.8.4) - 2026-02-06

### Performance

- optimize hash maps, add parallel query execution, improve test coverage

## [0.8.3](https://github.com/rustledger/rustledger/compare/v0.8.2...v0.8.3) - 2026-02-05

### Bug Fixes

- *(parser)* parse metadata for custom and query directives

### Performance

- *(parser)* add winnow-based parser for ~3x performance improvement

### Refactoring

- *(parser)* address Copilot review suggestions

## [0.8.2](https://github.com/rustledger/rustledger/compare/v0.8.1...v0.8.2) - 2026-02-02

### Bug Fixes

- *(parser)* lower posting metadata indent threshold from 4 to 3 spaces

## [0.8.0](https://github.com/rustledger/rustledger/releases/tag/v0.8.0) - 2026-01-28

### Miscellaneous

- reorganize test fixtures and cleanup

### Style

- fix clippy warnings after MSRV alignment

## [0.7.2](https://github.com/rustledger/rustledger/compare/v0.7.1...v0.7.2) - 2026-01-25

### Performance

- avoid intermediate allocations in parser tag/meta handling

## [0.7.0](https://github.com/rustledger/rustledger/releases/tag/v0.7.0) - 2026-01-25

### Features

- *(test)* add synthetic beancount file generation for compat testing

### Miscellaneous

- update remaining references to single rledger binary

### Refactoring

- consolidate rledger-\* binaries into single rledger binary
- address PR review comments

## [0.6.0](https://github.com/rustledger/rustledger/releases/tag/v0.6.0) - 2026-01-23

### Bug Fixes

- address review comments
- remove broken doc link to SourceMap
- address PR review comments and clippy warnings

### Documentation

- update install options in README

### Features

- add infrastructure for validation error line numbers
- support unicode and emoji in account names
- comprehensive benchmark infrastructure overhaul
- achieve 100% BQL query compatibility with Python beancount
- enhance compatibility CI with comprehensive testing

## [0.5.2](https://github.com/rustledger/rustledger/compare/v0.5.1...v0.5.2) - 2026-01-20

### Miscellaneous

- update Cargo.toml dependencies

## [0.5.1](https://github.com/rustledger/rustledger/compare/v0.5.0...v0.5.1) - 2026-01-19

### Miscellaneous

- update Cargo.toml dependencies

## [0.5.0](https://github.com/rustledger/rustledger/compare/v0.4.0...v0.5.0) - 2026-01-19

### Bug Fixes

- *(parser)* support logos 0.16 greedy pattern warnings

### Features

- \[**breaking**\] upgrade to Rust 2024 edition and MSRV 1.85
