# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).


## [0.7.0](https://github.com/rustledger/rustledger/releases/tag/v0.7.0) - 2026-01-24

### Bug Fixes

- *(plugin)* deterministic ordering for auto_accounts plugin
- *(plugin)* preserve typed values in custom directives
- *(plugin)* serialize custom directive values without debug format
- *(plugin)* preserve user-defined metadata through plugin processing
- *(plugin)* preserve source locations through plugin processing

### Features

- *(plugin)* implement beancount-compatible entry sorting

### Testing

- *(plugin)* add comprehensive plugin manager coverage tests

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
