# Documentation Validation Plan

## Overview

Systematic review of ALL rustledger documentation to ensure 100% accuracy.

## Documentation Sources

### 1. Website (rustledger.github.io/docs/)

| File | Validation Method | Status |
|------|-------------------|--------|
| **Getting Started** | | |
| `getting-started/installation.md` | Test all install commands | ⬜ |
| `getting-started/quick-start.md` | Run all examples | ⬜ |
| `getting-started/configuration.md` | Verify config options against code | ⬜ |
| **Commands** | | |
| `commands/check.md` | Test all flags against `--help` | ⬜ |
| `commands/query.md` | Test all flags against `--help` | ⬜ |
| `commands/format.md` | Test all flags against `--help` | ⬜ |
| `commands/extract.md` | Test all flags against `--help` | ⬜ |
| `commands/report.md` | Test all flags against `--help` | ⬜ |
| `commands/price.md` | Test all flags against `--help` | ⬜ |
| `commands/doctor.md` | Test all flags against `--help` | ⬜ |
| **Guides** | | |
| `guides/editor-integration.md` | Verify each editor config works | ⬜ |
| `guides/importing.md` | Test import examples | ⬜ |
| `guides/multi-file.md` | Test include examples | ⬜ |
| `guides/common-queries.md` | Run all BQL examples | ⬜ |
| `guides/cookbook.md` | Run all examples | ⬜ |
| `guides/budgeting.md` | Run all examples | ⬜ |
| `guides/shell-aliases.md` | Verify aliases work | ⬜ |
| **Reference** | | |
| `reference/bql.md` | Test all BQL syntax examples | ⬜ |
| `reference/syntax.md` | Parse all syntax examples | ⬜ |
| `reference/options.md` | Verify against code | ⬜ |
| `reference/plugins.md` | Verify plugin list against code | ⬜ |
| `reference/errors.md` | Verify error codes against code | ⬜ |
| `reference/compatibility.md` | Verify claims | ⬜ |
| **Migration** | | |
| `migration/from-beancount.md` | Verify migration steps | ⬜ |
| `migration/from-ledger.md` | Verify migration steps | ⬜ |
| `migration/from-hledger.md` | Verify migration steps | ⬜ |

### 2. Crate READMEs

| File | Validation Method | Status |
|------|-------------------|--------|
| `crates/rustledger-lsp/README.md` | Test all editor configs | ⬜ |
| `crates/rustledger-wasm/README.md` | Test WASM examples | ⬜ |
| `crates/rustledger-importer/README.md` | Test import examples | ⬜ |
| `crates/rustledger-query/README.md` | Test BQL examples | ⬜ |
| `crates/rustledger-plugin/README.md` | Test plugin examples | ⬜ |
| `crates/rustledger-ffi-wasi/README.md` | Test FFI examples | ⬜ |
| `crates/rustledger/README.md` | Test CLI examples | ⬜ |
| `packages/mcp-server/README.md` | Test MCP examples | ⬜ |

### 3. Root README

| File | Validation Method | Status |
|------|-------------------|--------|
| `README.md` | Test all examples, verify claims | ⬜ |

## Validation Methods

### A. Command Validation
- Extract documented flags/options
- Compare against `rledger <cmd> --help`
- Flag any mismatches

### B. Code Example Validation
- Extract code blocks from docs
- Run them against test fixtures
- Verify output matches documented output

### C. Configuration Validation
- Extract config options from docs
- Compare against actual config parsing code
- Verify defaults match

### D. Editor Integration Validation
- VS Code: Test with actual extension
- Neovim: Test nvim-lspconfig setup
- Helix: Test languages.toml config
- Zed: Test settings.json config
- Emacs: Test lsp-mode/eglot config
- Sublime: Test LSP config

### E. BQL Validation
- Extract all BQL examples
- Run each query
- Verify syntax is valid

### F. Plugin Validation
- Extract plugin list from docs
- Compare against `NativePluginRegistry`
- Verify plugin names/descriptions

## Priority Order

1. **HIGH** - User-facing getting started docs (installation, quick-start)
2. **HIGH** - Editor integration (LSP README, editor-integration guide)
3. **HIGH** - Command docs (most used daily)
4. **MEDIUM** - BQL reference (complex, error-prone)
5. **MEDIUM** - Import/extract docs
6. **LOW** - Migration guides
7. **LOW** - Architecture/ADR docs

## Execution Plan

1. Build validation scripts where possible (automated)
2. Manual testing for editor integrations
3. Document all findings as issues
4. Fix docs in batches by category
