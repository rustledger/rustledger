# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).


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

## [0.8.4](https://github.com/rustledger/rustledger/compare/v0.8.3...v0.8.4) - 2026-02-06

### Performance

- optimize hash maps, add parallel query execution, improve test coverage

## [0.8.2](https://github.com/rustledger/rustledger/compare/v0.8.1...v0.8.2) - 2026-02-02

### Bug Fixes

- *(plugin)* prevent duplicate Open directives in zerosum and Python compat
- *(python)* use CostSpec format for posting cost serialization
- *(python)* add beancount.core.getters and flags modules to compat layer
- *(python)* fix WASI directory mapping for Python runtime
- address PR review feedback

### Documentation

- clarify valuation plugin implementation status
- clarify intentional module discovery behavior

### Features

- *(plugin)* implement native valuation plugin with FIFO cost tracking
- *(loader)* add central orchestration API matching Python's loader.load_file()
- *(plugin)* enable Python plugin execution via WASM sandbox

### Testing

- add coverage for Python plugin execution

### Style

- address PR review suggestions
- fix clippy warnings and formatting

## [0.8.0](https://github.com/rustledger/rustledger/releases/tag/v0.8.0) - 2026-01-28

### Features

- *(testing)* add comprehensive TLA+ verification infrastructure

### Style

- fix clippy warnings after MSRV alignment
- fix clippy warnings in TLA+ proptests

## [0.7.5](https://github.com/rustledger/rustledger/compare/v0.7.4...v0.7.5) - 2026-01-26

### Miscellaneous

- update Cargo.toml dependencies

## [0.7.0](https://github.com/rustledger/rustledger/releases/tag/v0.7.0) - 2026-01-25

### Bug Fixes

- add missing imports for tests after refactor
- *(plugin)* deterministic ordering for auto_accounts plugin
- *(plugin)* preserve typed values in custom directives
- *(plugin)* serialize custom directive values without debug format
- *(plugin)* preserve user-defined metadata through plugin processing
- *(plugin)* preserve source locations through plugin processing

### Features

- *(plugin)* implement beancount-compatible entry sorting

### Refactoring

- consolidate rledger-* binaries into single rledger binary
- *(plugin)* split convert.rs into to_wrapper and from_wrapper modules
- *(plugin)* split native plugins into individual files
- *(wasm)* split editor.rs into modular structure
- *(plugin)* split native.rs into native/ module

### Testing

- *(plugin)* add comprehensive plugin manager coverage tests

### Style

- apply cargo fmt

## [0.6.0](https://github.com/rustledger/rustledger/releases/tag/v0.6.0) - 2026-01-23

### Bug Fixes

- address PR review comments and clippy warnings

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
