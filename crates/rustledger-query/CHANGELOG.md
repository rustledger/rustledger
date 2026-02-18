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

## [0.8.4](https://github.com/rustledger/rustledger/compare/v0.8.3...v0.8.4) - 2026-02-06

### Bug Fixes

- *(query)* handle RwLock poisoning gracefully, add parallel execution tests

### Performance

- optimize hash maps, add parallel query execution, improve test coverage

## [0.8.2](https://github.com/rustledger/rustledger/compare/v0.8.1...v0.8.2) - 2026-02-02

### Bug Fixes

- *(bql)* use latest price in convert() when no date specified
- *(bql)* handle NULL in regex, add type column, remove zero postings

## [0.8.0](https://github.com/rustledger/rustledger/releases/tag/v0.8.0) - 2026-01-28

### Documentation

- reorganize documentation and add TLA+ references

### Features

- *(testing)* add comprehensive TLA+ verification infrastructure
- *(ci)* add fuzzing infrastructure (Phase 2)

### Style

- fix clippy warnings after MSRV alignment
- fix clippy warnings in TLA+ proptests

## [0.7.2](https://github.com/rustledger/rustledger/compare/v0.7.1...v0.7.2) - 2026-01-25

### Bug Fixes

- *(validate)* derive balance tolerance from transaction amounts

### Performance

- box heavy Value variants and avoid balance prefix alloc

## [0.7.0](https://github.com/rustledger/rustledger/releases/tag/v0.7.0) - 2026-01-25

### Bug Fixes

- *(query)* NUMBER returns NULL for multi-currency inventories
- *(query)* support ORDER BY with GROUP BY expressions not in SELECT
- add missing imports for tests after refactor
- *(ffi,wasm)* remove duplicate "Query parse error" prefix
- *(query)* SUM now works on integer columns (day, month, year)
- *(bql)* improve robustness and add comprehensive tests

### Features

- *(query)* support nested aggregate functions for holdings reports
- *(ffi-py)* add Fava integration APIs and BQL improvements
- *(bql)* add CREATE TABLE, INSERT, interval(), and SELECT FROM table
- *(bql)* add nested function calls, getprice(), and only() functions

### Miscellaneous

- *(query)* remove unused imports from executor modules

### Refactoring

- *(query)* split executor into focused modules
- *(query)* split executor eval functions into category modules
- *(query)* split executor.rs into module with types.rs

### Testing

- add coverage tests for nested aggregate functions
- remove misleading duplicate test
- *(query)* add comprehensive BQL executor coverage tests

### Style

- remove unnecessary raw string hashes
- apply cargo fmt
- apply cargo fmt
- apply cargo fmt

## [0.6.0](https://github.com/rustledger/rustledger/releases/tag/v0.6.0) - 2026-01-23

### Bug Fixes

- resolve CI failures for Clippy, Semver Check, and CodeQL
- *(ci)* pin GitHub Actions to SHA in bench-pr.yml

### Documentation

- update install options in README

### Features

- comprehensive benchmark infrastructure overhaul
- achieve 100% BQL query compatibility with Python beancount
- enhance compatibility CI with comprehensive testing

## [0.5.2](https://github.com/rustledger/rustledger/compare/v0.5.1...v0.5.2) - 2026-01-20

## [0.5.1](https://github.com/rustledger/rustledger/releases/tag/v0.5.1) - 2026-01-20

### Features

- [**breaking**] upgrade to Rust 2024 edition and MSRV 1.85

## [0.5.0](https://github.com/rustledger/rustledger/compare/v0.4.0...v0.5.0) - 2026-01-19

### Features

- [**breaking**] upgrade to Rust 2024 edition and MSRV 1.85
