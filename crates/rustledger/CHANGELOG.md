# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).


## [0.9.1](https://github.com/rustledger/rustledger/compare/v0.9.0...v0.9.1) - 2026-02-18

### Bug Fixes

- *(tests)* handle missing rledger binary in fixture_tests.rs
- *(tests)* gracefully handle missing rledger binary in CLI tests
- *(tests)* use CARGO_BIN_EXE for CLI tests

## [0.8.8](https://github.com/rustledger/rustledger/compare/v0.8.7...v0.8.8) - 2026-02-14

### Bug Fixes

- address review feedback on comments and error messages

### Features

- *(cli)* add completions subcommand for shell completion generation

## [0.8.6](https://github.com/rustledger/rustledger/compare/v0.8.5...v0.8.6) - 2026-02-09

### Miscellaneous

- update Cargo.lock dependencies

## [0.8.4](https://github.com/rustledger/rustledger/compare/v0.8.3...v0.8.4) - 2026-02-06

### Miscellaneous

- update Cargo.lock dependencies

## [0.8.3](https://github.com/rustledger/rustledger/compare/v0.8.2...v0.8.3) - 2026-02-05

### Miscellaneous

- update Cargo.lock dependencies

## [0.8.2](https://github.com/rustledger/rustledger/compare/v0.8.1...v0.8.2) - 2026-02-02

### Bug Fixes

- address PR review feedback

### Features

- *(loader)* add central orchestration API matching Python's loader.load_file()
- *(plugin)* enable Python plugin execution via WASM sandbox

### Style

- fix clippy warnings and formatting

## [0.8.0](https://github.com/rustledger/rustledger/releases/tag/v0.8.0) - 2026-01-28

### Bug Fixes

- *(balance)* propagate tolerance options and preserve total costs/prices
- *(check)* don't cache files with option validation warnings
- *(query)* tolerate parse errors like bean-query does
- line #s

### Miscellaneous

- reorganize test fixtures and cleanup

### Style

- fix clippy warnings after MSRV alignment

## [0.7.5](https://github.com/rustledger/rustledger/compare/v0.7.4...v0.7.5) - 2026-01-26

### Miscellaneous

- update Cargo.lock dependencies

## [0.7.4](https://github.com/rustledger/rustledger/compare/v0.7.3...v0.7.4) - 2026-01-26

### Miscellaneous

- update Cargo.lock dependencies

## [0.7.2](https://github.com/rustledger/rustledger/compare/v0.7.1...v0.7.2) - 2026-01-25

### Bug Fixes

- *(booking)* sort directives by date before lot matching

### Performance

- box heavy Value variants and avoid balance prefix alloc

### Style

- apply cargo fmt

## [0.7.1](https://github.com/rustledger/rustledger/compare/v0.7.0...v0.7.1) - 2026-01-25

### Bug Fixes

- *(doctor)* convert byte offsets to line numbers in context command

## [0.7.0](https://github.com/rustledger/rustledger/releases/tag/v0.7.0) - 2026-01-25

### Bug Fixes

- *(test)* handle broken pipe gracefully in stdin test
- *(booking)* run booking before interpolation in check command

### Features

- *(synthetic)* add rledger-doctor generate-synthetic subcommand
- *(ffi-py)* add Fava integration APIs and BQL improvements
- *(bql)* add CREATE TABLE, INSERT, interval(), and SELECT FROM table

### Miscellaneous

- update remaining references to single rledger binary

### Refactoring

- consolidate rledger-* binaries into single rledger binary
- *(cli)* split doctor.rs into command modules
- *(cli)* split report_cmd into focused modules

### Testing

- *(cli)* add comprehensive CLI command integration tests

### Style

- apply cargo fmt
- apply cargo fmt
- apply cargo fmt

## [0.6.0](https://github.com/rustledger/rustledger/releases/tag/v0.6.0) - 2026-01-23

### Bug Fixes

- add TTY detection for colored output
- address PR review comments and clippy warnings

### Documentation

- update install options in README

### Features

- *(validate)* add validate_spanned_with_options for location tracking
- add infrastructure for validation error line numbers
- add DisplayContext for consistent number formatting
- comprehensive benchmark infrastructure overhaul
- achieve 100% BQL query compatibility with Python beancount
- enhance compatibility CI with comprehensive testing
- add beancount compatibility testing framework
- [**breaking**] upgrade to Rust 2024 edition and MSRV 1.85

## [0.5.2](https://github.com/rustledger/rustledger/compare/v0.5.1...v0.5.2) - 2026-01-20

### Miscellaneous

- update Cargo.lock dependencies

## [0.5.1](https://github.com/rustledger/rustledger/compare/v0.5.0...v0.5.1) - 2026-01-19

### Miscellaneous

- update Cargo.lock dependencies

## [0.5.0](https://github.com/rustledger/rustledger/compare/v0.4.0...v0.5.0) - 2026-01-19

### Features

- [**breaking**] upgrade to Rust 2024 edition and MSRV 1.85
