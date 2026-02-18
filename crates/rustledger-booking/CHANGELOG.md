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

## [0.8.6](https://github.com/rustledger/rustledger/compare/v0.8.5...v0.8.6) - 2026-02-09

### Bug Fixes

- *(booking)* preserve cost spec scale in interpolation

## [0.8.4](https://github.com/rustledger/rustledger/compare/v0.8.3...v0.8.4) - 2026-02-06

### Performance

- optimize hash maps, add parallel query execution, improve test coverage

## [0.8.2](https://github.com/rustledger/rustledger/compare/v0.8.1...v0.8.2) - 2026-02-02

### Bug Fixes

- *(interpolate)* preserve precision when rounding would make residual zero
- *(bql)* handle NULL in regex, add type column, remove zero postings
- *(booking)* track inventory state across multiple postings in same transaction
- *(interpolate)* infer currency from cost spec for zero-cost postings
- *(interpolate)* infer currency from cost basis for balanced transactions

### Refactoring

- *(interpolate)* extract round_interpolated helper function

### Testing

- *(booking)* add regression test for multi-posting lot boundary crossing
- *(interpolate)* add coverage for cost currency inference edge cases

### Style

- apply rustfmt formatting

## [0.8.1](https://github.com/rustledger/rustledger/compare/v0.8.0...v0.8.1) - 2026-01-29

### Bug Fixes

- *(interpolate)* round interpolated amounts to match currency precision

## [0.8.0](https://github.com/rustledger/rustledger/releases/tag/v0.8.0) - 2026-01-28

### Bug Fixes

- *(balance)* propagate tolerance options and preserve total costs/prices
- *(balance)* use BigDecimal for precise residual checking and fix tolerance defaults

### Documentation

- reorganize documentation and add TLA+ references

### Features

- *(testing)* add comprehensive TLA+ verification infrastructure

### Style

- rustfmt
- fix clippy warnings after MSRV alignment
- fix clippy warnings in TLA+ proptests

## [0.7.5](https://github.com/rustledger/rustledger/compare/v0.7.4...v0.7.5) - 2026-01-26

### Bug Fixes

- *(booking)* infer cost currency from other postings

## [0.7.2](https://github.com/rustledger/rustledger/compare/v0.7.1...v0.7.2) - 2026-01-25

### Bug Fixes

- *(validate)* derive balance tolerance from transaction amounts

### Performance

- skip redundant residual recalculation and add HashMap capacity hints
- optimize booking posting expansion and loader file handling
- optimize booking hot path and validation sorting
- *(booking)* lazy evaluation for cost currency inference

## [0.7.1](https://github.com/rustledger/rustledger/compare/v0.7.0...v0.7.1) - 2026-01-25

### Bug Fixes

- *(booking)* infer cost currency from other postings

### Documentation

- document currency inference priority order

## [0.7.0](https://github.com/rustledger/rustledger/releases/tag/v0.7.0) - 2026-01-25

### Bug Fixes

- *(booking,ffi)* run booking in FFI and normalize total prices

### Refactoring

- consolidate rledger-* binaries into single rledger binary

## [0.6.0](https://github.com/rustledger/rustledger/releases/tag/v0.6.0) - 2026-01-23

### Bug Fixes

- preserve full precision in cost calculations for total cost syntax
- address Copilot review suggestions
- achieve 100% BQL compatibility with Python beancount
- address PR review comments and clippy warnings

### Documentation

- update install options in README

### Features

- comprehensive benchmark infrastructure overhaul
- achieve 100% BQL query compatibility with Python beancount
- enhance compatibility CI with comprehensive testing

### Testing

- add coverage for book() with total cost syntax
- *(booking)* add tests to improve code coverage

## [0.5.2](https://github.com/rustledger/rustledger/compare/v0.5.1...v0.5.2) - 2026-01-20

## [0.5.1](https://github.com/rustledger/rustledger/releases/tag/v0.5.1) - 2026-01-20

### Features

- [**breaking**] upgrade to Rust 2024 edition and MSRV 1.85

## [0.5.0](https://github.com/rustledger/rustledger/compare/v0.4.0...v0.5.0) - 2026-01-19

### Features

- [**breaking**] upgrade to Rust 2024 edition and MSRV 1.85
