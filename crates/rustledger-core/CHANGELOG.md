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

### Performance

- optimize hash maps, add parallel query execution, improve test coverage

## [0.8.0](https://github.com/rustledger/rustledger/releases/tag/v0.8.0) - 2026-01-28

### Bug Fixes

- *(kani)* exclude i64::MIN before calling .abs() in proofs
- *(ci)* add cfg(kani) to check-cfg and fix formatting

### Documentation

- reorganize documentation and add TLA+ references

### Features

- *(testing)* add comprehensive TLA+ verification infrastructure
- *(formal)* add Kani verification and TLA+ trace automation (Phase 4)

### Refactoring

- *(kani)* rewrite proofs to verify TLA+ invariants

### Style

- fix clippy warnings after MSRV alignment

## [0.7.2](https://github.com/rustledger/rustledger/compare/v0.7.1...v0.7.2) - 2026-01-25

### Bug Fixes

- *(validate)* derive balance tolerance from transaction amounts

### Performance

- reduce allocations in validation and booking loops
- avoid intermediate allocations in parser tag/meta handling
- add units cache to Inventory for O(1) lookups
- optimize booking hot path and validation sorting

## [0.7.0](https://github.com/rustledger/rustledger/releases/tag/v0.7.0) - 2026-01-25

### Bug Fixes

- add missing imports for tests after refactor
- address all clippy warnings in synthetic_generation tests
- address warnings in synthetic_generation tests

### Features

- *(synthetic)* add rledger-doctor generate-synthetic subcommand
- *(test)* add synthetic beancount file generation for compat testing

### Refactoring

- consolidate rledger-* binaries into single rledger binary
- *(plugin)* split convert.rs into to_wrapper and from_wrapper modules
- *(core)* split inventory booking methods into module
- *(core)* split format.rs into focused modules

### Testing

- *(core)* add comprehensive inventory and format coverage tests

### Style

- apply cargo fmt
- apply cargo fmt

## [0.6.0](https://github.com/rustledger/rustledger/releases/tag/v0.6.0) - 2026-01-23

### Bug Fixes

- *(ci)* pin GitHub Actions to SHA in bench-pr.yml
- address Copilot review suggestions
- achieve 100% BQL compatibility with Python beancount
- address PR review comments and clippy warnings

### Documentation

- update install options in README

### Features

- add DisplayContext for consistent number formatting
- comprehensive benchmark infrastructure overhaul
- achieve 100% BQL query compatibility with Python beancount
- enhance compatibility CI with comprehensive testing

### Performance

- *(inventory)* replace HashMap with boolean flags for sign tracking
- *(inventory)* restore O(1) add for augmentations with costed_signs tracking

### Testing

- *(inventory)* add tests for buy/sell cancellation in add()

## [0.5.2](https://github.com/rustledger/rustledger/compare/v0.5.1...v0.5.2) - 2026-01-20

## [0.5.1](https://github.com/rustledger/rustledger/releases/tag/v0.5.1) - 2026-01-20

### Features

- [**breaking**] upgrade to Rust 2024 edition and MSRV 1.85

## [0.5.0](https://github.com/rustledger/rustledger/compare/v0.4.0...v0.5.0) - 2026-01-19

### Features

- [**breaking**] upgrade to Rust 2024 edition and MSRV 1.85
