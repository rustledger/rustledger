# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).


## [0.7.0](https://github.com/rustledger/rustledger/releases/tag/v0.7.0) - 2026-01-24

### Bug Fixes

- add missing imports for tests after refactor
- *(ffi,wasm)* remove duplicate "Query parse error" prefix
- *(query)* SUM now works on integer columns (day, month, year)
- *(bql)* improve robustness and add comprehensive tests

### Features

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

- *(query)* add comprehensive BQL executor coverage tests

### Style

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
