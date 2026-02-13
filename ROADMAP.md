# Roadmap

This document outlines the development roadmap for rustledger.

## Current Status (v0.8.x)

rustledger is a **production-ready** Beancount-compatible accounting tool with:

- ✅ **99.86% compatibility** with Python beancount on 694 test files
- ✅ **10-30x faster** than Python beancount
- ✅ **100% BQL query compatibility** with Python beancount
- ✅ 20 native plugins matching Python behavior
- ✅ 7 booking methods (FIFO, LIFO, HIFO, etc.)
- ✅ Multi-platform binaries (Linux, macOS, Windows, ARM64)
- ✅ WebAssembly build for browser/JS use
- ✅ Language Server Protocol (LSP) implementation
- ✅ **Python plugin execution** via CPython-WASI sandbox
- ✅ **MCP server** for AI assistant integration (Claude, Cursor, etc.)
- ✅ **Import framework** (`rledger extract` for CSV/OFX)
- ✅ **WASM plugins** for cross-platform plugin distribution

## Near-Term (v0.9.x)

### Editor Integration
- [ ] **VS Code extension**: Bundle `rledger-lsp` for zero-config editing
- [ ] **mason.nvim registry**: Easy LSP installation for Neovim users
- [ ] **Helix/Zed support**: Configuration guides and testing

### Performance
- [ ] **Parallel parsing**: Multi-threaded file loading for large ledgers
- [ ] **Incremental updates**: Only re-process changed portions of files

### Fava Integration
- [ ] **Full Fava compatibility**: Complete Python FFI for fava use
- [ ] **Fava performance mode**: Use rustledger as fava's backend

## Medium-Term (v0.10.x - v1.0)

### New Features
- [ ] **Web UI**: Lightweight alternative to fava (Rust + WASM)
- [ ] **Forecasting**: Built-in transaction forecasting and projection

### Query Enhancements
- [ ] **Query caching**: Cache parsed queries and results
- [ ] **Custom functions**: User-defined BQL functions

### Plugin System
- [ ] **Plugin marketplace**: Registry for community plugins
- [ ] **Plugin templates**: Scaffolding for new plugin development

## Long-Term Vision (v1.0+)

### Ecosystem
- [ ] **PTA Spec participation**: Contribute to Plain Text Accounting standardization
- [ ] **Multi-format support**: Optional ledger/hledger syntax parsing
- [ ] **Migration tools**: Automated conversion from other PTA tools

### Enterprise Features
- [ ] **Multi-user support**: Concurrent editing with conflict resolution
- [ ] **Audit logging**: Track all changes for compliance
- [ ] **API server**: REST/GraphQL API for integrations

### Distribution
- [ ] **Homebrew core**: Get into homebrew-core (not just tap)
- [x] **AUR**: Arch User Repository packages (`rustledger`, `rustledger-bin`)
- [x] **Nix**: Available in flake and via `nix run`
- [x] **COPR**: Fedora/RHEL packages
- [ ] **Linux packages**: .deb, .rpm for Debian/Ubuntu
- [ ] **Chocolatey**: Windows package manager

## Non-Goals

These are explicitly **not** planned:

- **GUI desktop app**: Use VS Code + extension or web UI instead
- **Cloud service**: rustledger is local-first; no hosted version planned
- **Breaking Beancount compatibility**: We follow beancount syntax strictly

## Detailed Roadmaps

For implementation details, see these focused roadmaps:

- **[Performance Roadmap](docs/PERFORMANCE_ROADMAP.md)** - Optimization phases, benchmarks, cache implementation
- **[Testing Roadmap](docs/TESTING_ROADMAP.md)** - Testing infrastructure, fuzzing, formal verification
- **[TLA+ Status](spec/tla/ROADMAP.md)** - Formal specification coverage and verification status

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for how to contribute. Priority areas:

1. **Testing**: More real-world beancount files for compatibility testing
2. **Documentation**: Tutorials, guides, examples
3. **Editor plugins**: VS Code, Neovim, Emacs configurations
4. **Importers**: Bank statement importers for various institutions

## Versioning

We follow [Semantic Versioning](https://semver.org/):

- **Patch** (0.5.x): Bug fixes, performance improvements
- **Minor** (0.x.0): New features, backward-compatible
- **Major** (x.0.0): Breaking changes (none planned before 1.0)
