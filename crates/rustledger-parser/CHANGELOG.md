# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).


## [0.7.6](https://github.com/rustledger/rustledger/compare/v0.7.5...v0.7.6) - 2026-01-28

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

- consolidate rledger-* binaries into single rledger binary
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

- [**breaking**] upgrade to Rust 2024 edition and MSRV 1.85
