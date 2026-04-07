//! Beancount CLI tools.
//!
//! This crate provides command-line tools for working with Beancount files:
//!
//! - `rledger check` / `bean-check`: Validate a beancount file
//! - `rledger format` / `bean-format`: Format a beancount file
//! - `rledger query` / `bean-query`: Query with BQL
//! - `rledger report` / `bean-report`: Generate reports
//! - `rledger doctor` / `bean-doctor`: Debugging tools
//!
//! # Example Usage
//!
//! ```bash
//! rledger check ledger.beancount
//! rledger format ledger.beancount
//! rledger query ledger.beancount "SELECT account, SUM(position)"
//! ```
//!
//! # Related Crates
//!
//! rustledger is a workspace with several crates:
//!
//! | Crate | Description |
//! |-------|-------------|
//! | [`rustledger-core`](https://docs.rs/rustledger-core) | Core types (Amount, Position, Inventory, Directives) |
//! | [`rustledger-parser`](https://docs.rs/rustledger-parser) | Lexer and parser with error recovery |
//! | [`rustledger-loader`](https://docs.rs/rustledger-loader) | File loading, includes, options |
//! | [`rustledger-booking`](https://docs.rs/rustledger-booking) | Interpolation and booking engine |
//! | [`rustledger-validate`](https://docs.rs/rustledger-validate) | Validation with error reporting |
//! | [`rustledger-query`](https://docs.rs/rustledger-query) | BQL query engine |
//! | [`rustledger-plugin`](https://docs.rs/rustledger-plugin) | Native and WASM plugin system |
//! | [`rustledger-wasm`](https://docs.rs/rustledger-wasm) | WebAssembly library target |
//! | [`rustledger-importer`](https://docs.rs/rustledger-importer) | Import framework for bank statements |
//! | [`rustledger-lsp`](https://docs.rs/rustledger-lsp) | Language Server Protocol implementation |
//! | [`rustledger-ffi-wasi`](https://docs.rs/rustledger-ffi-wasi) | FFI via WASI for embedding |

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod cmd;
pub mod config;
pub mod format;
pub mod pager;
pub mod report;
