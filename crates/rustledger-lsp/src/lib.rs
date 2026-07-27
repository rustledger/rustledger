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
//! fn main() -> std::process::ExitCode {
//!     rustledger_lsp::start_stdio().map(|()| std::process::ExitCode::SUCCESS)
//!         .unwrap_or(std::process::ExitCode::FAILURE)
//! }
//! ```

#![warn(missing_docs)]
#![warn(clippy::all)]

pub mod handlers;
pub mod ledger_state;
pub mod main_loop;

mod server;
mod snapshot;
mod vfs;

/// Why a URI and a path could not be converted into one another.
///
/// A named reason rather than `None`. Both directions used to return `Option`,
/// so a malformed URI became a feature that silently did nothing — no link, no
/// definition, no diagnostic, and nothing in the log saying why. rust-analyzer's
/// equivalent returns an error for the same reason.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PathUriError {
    /// Not parseable as a URI at all.
    NotAUri,
    /// A URI, but not one naming a file on this machine: a scheme other than
    /// `file` (`untitled:` for an unsaved buffer, `git:`/`fugitive:` for a
    /// history view), or a host this platform cannot reach as a local path.
    ///
    /// The scheme half must be checked explicitly. `Url::to_file_path` looks at
    /// the host and not the scheme, so it will happily turn
    /// `fugitive:///home/rob/main.beancount` into a real path.
    NotALocalFile,
    /// A relative path has no `file:` URI. Inventing one would resolve it
    /// against whatever the process's working directory happens to be.
    NotAbsolute,
    /// The encoded path is not a URI `lsp-types` will accept.
    Unencodable,
    /// A segment that percent-decodes into path syntax: named `.` or `..`, or
    /// containing a separator. The URI claims one structure and denotes
    /// another, so it names a file outside the segments it appears to name.
    DeceptiveSegment,
}

impl std::fmt::Display for PathUriError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::NotAUri => "not a URI",
            Self::NotALocalFile => "not a local file URI",
            Self::NotAbsolute => "path is not absolute",
            Self::Unencodable => "path has no representable file URI",
            Self::DeceptiveSegment => "a path segment decodes into path syntax",
        })
    }
}

impl std::error::Error for PathUriError {}

/// An absolute path for tests, spelled the way THIS platform spells one.
///
/// `/home/user/ledger` is absolute on Unix and relative on Windows, so a test
/// hard-coding it does not assert a weaker thing on Windows — it asserts
/// nothing, because `path_to_uri` correctly refuses a relative path and the
/// test panics before reaching its subject. Six tests failed that way the first
/// time this crate's suite ran on Windows.
///
/// Prefixing a drive keeps each test asserting what it was written to assert on
/// both platforms, which is the point of running them there at all. Tests whose
/// SUBJECT is a POSIX-specific spelling belong in a `cfg(unix)` block instead.
#[cfg(test)]
pub(crate) fn test_abs(relative: &str) -> std::path::PathBuf {
    if cfg!(windows) {
        std::path::PathBuf::from(format!("C:\\{}", relative.replace('/', "\\")))
    } else {
        std::path::PathBuf::from(format!("/{relative}"))
    }
}

pub mod abs_path;
pub mod proto;
pub use abs_path::AbsPathBuf;
pub use ledger_state::{LedgerState, LspConfig, SharedLedgerState, new_shared_ledger_state};
pub use main_loop::{run_main_loop, run_main_loop_with_exit_action};
pub use proto::{path_to_uri, uri_to_path};
pub use server::{Server, start_stdio};
pub use snapshot::Snapshot;
pub use vfs::Vfs;

/// LSP server version.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
