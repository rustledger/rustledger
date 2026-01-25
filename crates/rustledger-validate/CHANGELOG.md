# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).


## [0.7.2](https://github.com/rustledger/rustledger/compare/v0.7.1...v0.7.2) - 2026-01-25

### Bug Fixes

- *(validate)* apply 2x tolerance multiplier for balance assertions

## [0.7.1](https://github.com/rustledger/rustledger/compare/v0.7.0...v0.7.1) - 2026-01-25

### Bug Fixes

- *(validate)* apply 2x tolerance multiplier for balance assertions

## [0.7.0](https://github.com/rustledger/rustledger/releases/tag/v0.7.0) - 2026-01-25

### Bug Fixes

- add missing imports for tests after refactor

### Refactoring

- consolidate rledger-* binaries into single rledger binary
- *(validate)* split validators into focused modules
- *(validate)* extract error types to error.rs

### Style

- apply cargo fmt

## [0.6.0](https://github.com/rustledger/rustledger/releases/tag/v0.6.0) - 2026-01-23

### Bug Fixes

- address review comments
- remove broken doc link to SourceMap
- *(ci)* pin GitHub Actions to SHA in bench-pr.yml
- address PR review comments and clippy warnings

### Documentation

- update install options in README

### Features

- *(validate)* add validate_spanned_with_options for location tracking
- add infrastructure for validation error line numbers
- support unicode and emoji in account names
- comprehensive benchmark infrastructure overhaul
- achieve 100% BQL query compatibility with Python beancount
- enhance compatibility CI with comprehensive testing

### Testing

- add tests for validate_spanned_with_options()

## [0.5.2](https://github.com/rustledger/rustledger/compare/v0.5.1...v0.5.2) - 2026-01-20

## [0.5.1](https://github.com/rustledger/rustledger/releases/tag/v0.5.1) - 2026-01-20

### Features

- [**breaking**] upgrade to Rust 2024 edition and MSRV 1.85

## [0.5.0](https://github.com/rustledger/rustledger/compare/v0.4.0...v0.5.0) - 2026-01-19

### Features

- [**breaking**] upgrade to Rust 2024 edition and MSRV 1.85
