//! Language Server Protocol implementation for Beancount.
//!
//! This crate provides an LSP server for Beancount files, enabling IDE features like:
//! - Real-time syntax error diagnostics
//! - Autocompletion for accounts, currencies, payees
//! - Go-to-definition for accounts
//! - Hover information
//! - Document symbols (outline view)
//!
//! # Architecture
//!
//! The server follows rust-analyzer's architecture:
//! - **Main loop**: Handles LSP messages, applies changes, dispatches requests
//! - **Query database**: Salsa-inspired incremental computation
//! - **Handlers**: Process LSP requests against immutable snapshots
//!
//! # Example
//!
//! ```ignore
//! use rustledger_lsp::Server;
//!
//! #[tokio::main]
//! async fn main() {
//!     Server::new().run().await;
//! }
//! ```

#![warn(missing_docs)]
#![warn(clippy::all)]

use lsp_types::Uri;
use std::path::PathBuf;

pub mod db;
pub mod handlers;
pub mod ledger_state;
pub mod main_loop;

/// Convert an LSP URI to a file path.
///
/// Handles both Unix and Windows paths, as well as percent-encoded characters.
#[cfg(not(windows))]
pub fn uri_to_path(uri: &Uri) -> Option<PathBuf> {
    let path_str = uri.as_str().strip_prefix("file://")?;
    // Decode percent-encoded characters (e.g., %20 -> space)
    let decoded = percent_decode(path_str);
    Some(PathBuf::from(decoded))
}

/// Convert an LSP URI to a file path (Windows version).
#[cfg(windows)]
pub fn uri_to_path(uri: &Uri) -> Option<PathBuf> {
    let path_str = uri.as_str().strip_prefix("file://")?;
    // Handle Windows paths like file:///C:/...
    let path_str = path_str.strip_prefix('/').unwrap_or(path_str);
    // Decode percent-encoded characters (e.g., %20 -> space)
    let decoded = percent_decode(path_str);
    Some(PathBuf::from(decoded))
}

/// Decode percent-encoded characters in a string.
fn percent_decode(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    let mut chars = s.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '%' {
            // Try to read two hex digits
            let hex: String = chars.by_ref().take(2).collect();
            if hex.len() == 2
                && let Ok(byte) = u8::from_str_radix(&hex, 16)
            {
                result.push(byte as char);
                continue;
            }
            // Failed to decode, keep original
            result.push('%');
            result.push_str(&hex);
        } else {
            result.push(c);
        }
    }
    result
}

mod server;
mod snapshot;
mod vfs;

pub use ledger_state::{LedgerState, LspConfig, SharedLedgerState, new_shared_ledger_state};
pub use main_loop::run_main_loop;
pub use server::{Server, start_stdio};
pub use snapshot::Snapshot;
pub use vfs::Vfs;

/// LSP server version.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
