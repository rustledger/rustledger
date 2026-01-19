# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).


## [0.5.0](https://github.com/rustledger/rustledger/compare/v0.4.0...v0.5.0) - 2026-01-19

### Bug Fixes

- *(lsp)* address PR review comments

### Documentation

- add comprehensive PR review policy

### Features

- [**breaking**] upgrade to Rust 2024 edition and MSRV 1.85
- *(lsp)* add resolve handlers and file watching
- *(lsp)* add execute command and completion resolve
- *(lsp)* add call hierarchy and signature help
- *(lsp)* add code lens, document color, goto declaration
- *(lsp)* add document highlight, linked editing, on-type formatting
- *(lsp)* add type hierarchy for account navigation
- *(lsp)* add find references for accounts, currencies, payees
- *(lsp)* add range formatting, document links, inlay hints, selection range
- *(lsp)* add workspace symbols, rename, formatting, folding
- *(lsp)* add code actions for quick fixes
- *(lsp)* add semantic tokens for syntax highlighting
- *(lsp)* add Phase 5 - document symbols (outline view)
- *(lsp)* add Phase 4 - navigation features (definition, hover)
- *(lsp)* add Phase 3 - autocompletion support
- *(lsp)* implement Phase 1 & 2 - main loop with diagnostics
- *(lsp)* add rustledger-lsp crate skeleton (WIP)

### Performance

- *(lsp,wasm)* add caching and optimize position lookups

### Refactoring

- remove dead code and fix duplication

## [0.4.0](https://github.com/rustledger/rustledger/releases/tag/v0.4.0) - 2026-01-18

### Bug Fixes

- *(lsp)* address PR review comments

### Documentation

- add comprehensive PR review policy

### Features

- *(lsp)* add resolve handlers and file watching
- *(lsp)* add execute command and completion resolve
- *(lsp)* add call hierarchy and signature help
- *(lsp)* add code lens, document color, goto declaration
- *(lsp)* add document highlight, linked editing, on-type formatting
- *(lsp)* add type hierarchy for account navigation
- *(lsp)* add find references for accounts, currencies, payees
- *(lsp)* add range formatting, document links, inlay hints, selection range
- *(lsp)* add workspace symbols, rename, formatting, folding
- *(lsp)* add code actions for quick fixes
- *(lsp)* add semantic tokens for syntax highlighting
- *(lsp)* add Phase 5 - document symbols (outline view)
- *(lsp)* add Phase 4 - navigation features (definition, hover)
- *(lsp)* add Phase 3 - autocompletion support
- *(lsp)* implement Phase 1 & 2 - main loop with diagnostics
- *(lsp)* add rustledger-lsp crate skeleton (WIP)

### Performance

- *(lsp,wasm)* add caching and optimize position lookups

### Refactoring

- remove dead code and fix duplication
