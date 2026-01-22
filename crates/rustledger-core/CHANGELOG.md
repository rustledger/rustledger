# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).


## [0.5.3](https://github.com/rustledger/rustledger/compare/v0.5.2...v0.5.3) - 2026-01-22

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
