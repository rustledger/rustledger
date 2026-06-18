//! Rustledger FFI via WASI - JSON-RPC 2.0 API for embedding in any language.
//!
//! **Legacy/fallback surface.** The typed `rustledger-ffi-component`
//! (wasip2 / Component Model, #1384) is now the default embedding path;
//! new integrators should target it. This JSON-RPC surface is slated for
//! removal in Phase 5 (#1419).
//!
//! This is a WASI module that can be run via wasmtime (or any WASI runtime).
//!
//! # Usage
//!
//! Send JSON-RPC 2.0 requests via stdin:
//!
//! ```bash
//! echo '{"jsonrpc":"2.0","method":"ledger.validate","params":{"source":"..."},"id":1}' | \
//!     wasmtime rustledger-ffi-wasi.wasm
//! ```
//!
//! Batch requests are supported:
//!
//! ```bash
//! echo '[{"jsonrpc":"2.0","method":"util.version","id":1},{"jsonrpc":"2.0","method":"util.version","id":2}]' | \
//!     wasmtime rustledger-ffi-wasi.wasm
//! ```
//!
//! # Available Methods
//!
//! - `ledger.load`, `ledger.loadFile`, `ledger.validate`, `ledger.validateFile`
//! - `query.execute`, `query.executeFile`, `query.batch`, `query.batchFile`
//! - `format.source`, `format.file`, `format.entry`, `format.entries`
//! - `entry.create`, `entry.createBatch`, `entry.filter`, `entry.clamp`
//! - `util.version`, `util.types`, `util.isEncrypted`, `util.getAccountType`

use rustledger_ffi_wasi::jsonrpc;

fn main() {
    let exit_code = jsonrpc::process_stdin();
    std::process::exit(exit_code);
}
