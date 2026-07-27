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

use lsp_types::Uri;
use std::path::PathBuf;

pub mod handlers;
pub mod ledger_state;
pub mod main_loop;

/// Convert an LSP URI to a file path.
///
/// Delegates to [`url::Url`], which is the only implementation in this tree
/// that gets the whole job right. `lsp-types` 0.97 swapped `url::Url` for
/// `fluent_uri::Uri`, a generic RFC 3986 parser with no file-path conversion
/// and no feature flag to restore it, so every call site here had been
/// hand-written and each had drifted:
///
/// - The decoder rebuilt UTF-8 one byte at a time (`result.push(byte as char)`),
///   so a ledger under `Facturé/` resolved to `FacturÃ©/` and every feature that
///   takes a path silently looked in a directory that does not exist.
/// - `file://` was stripped literally, leaving `/C:/x` on Windows, where the
///   drive colon also arrives as `%3A` (issue #1866).
///
/// rust-analyzer and taplo both keep a `url::Url`-based URI type deliberately
/// rather than reimplement this; `url` carries its own test suite for the
/// platform behavior our CI cannot exercise.
#[must_use]
pub fn uri_to_path(uri: &Uri) -> Option<PathBuf> {
    url::Url::parse(uri.as_str()).ok()?.to_file_path().ok()
}

/// Convert a file path to an LSP URI.
///
/// The inverse of [`uri_to_path`], and the one place a `file:` URI is built.
/// `format!("file://{}", path.display())` was used at eight call sites and
/// percent-encoded nothing, so any path containing a space, `#`, or a non-ASCII
/// character produced a URI the editor could not open. On Windows it also
/// produced `file://C:/x`, which needs three slashes, and left the platform's
/// backslashes in place.
#[must_use]
pub fn path_to_uri(path: &std::path::Path) -> Option<Uri> {
    url::Url::from_file_path(path)
        .ok()?
        .as_str()
        .parse::<Uri>()
        .ok()
}

mod server;
mod snapshot;
mod vfs;

pub use ledger_state::{LedgerState, LspConfig, SharedLedgerState, new_shared_ledger_state};
pub use main_loop::{run_main_loop, run_main_loop_with_exit_action};
pub use server::{Server, start_stdio};
pub use snapshot::Snapshot;
pub use vfs::Vfs;

/// LSP server version.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

#[cfg(test)]
mod uri_conversion_tests {
    use super::*;
    use std::str::FromStr;

    fn uri(s: &str) -> Uri {
        Uri::from_str(s).expect("valid uri")
    }

    /// A percent-encoded path decodes to the bytes the filesystem actually has.
    ///
    /// The old decoder rebuilt UTF-8 one byte at a time — `%C3%A9` became two
    /// chars rather than one — so a ledger under `Facturé/` resolved to
    /// `FacturÃ©/` and every feature taking a path looked in a directory that
    /// does not exist. `uri_to_path` has a dozen call sites, so this was not
    /// confined to one feature.
    #[test]
    fn a_non_ascii_path_survives_the_round_trip() {
        for (encoded, want) in [
            (
                "file:///home/a/Factur%C3%A9/x.bean",
                "/home/a/Facturé/x.bean",
            ),
            ("file:///home/a/B%C3%BCcher/x.bean", "/home/a/Bücher/x.bean"),
            (
                "file:///home/a/%E4%BC%9A%E8%A8%88/x.bean",
                "/home/a/会計/x.bean",
            ),
            (
                "file:///tmp/re%20pro/main.beancount",
                "/tmp/re pro/main.beancount",
            ),
            ("file:///home/a/%23hash/x.bean", "/home/a/#hash/x.bean"),
        ] {
            assert_eq!(
                uri_to_path(&uri(encoded)).expect(encoded),
                std::path::PathBuf::from(want),
                "{encoded}"
            );
        }
    }

    /// Both directions agree, which is what a URI a handler hands back to the
    /// editor depends on.
    #[test]
    fn path_and_uri_round_trip() {
        for p in [
            "/tmp/plain.bean",
            "/tmp/a b/space.bean",
            "/tmp/Facturé/accented.bean",
            "/tmp/会計/cjk.bean",
            "/tmp/#hash/punct.bean",
        ] {
            let path = std::path::Path::new(p);
            let u = path_to_uri(path).unwrap_or_else(|| panic!("to uri: {p}"));
            assert!(
                !u.as_str().contains(' '),
                "a raw space makes a URI the editor cannot open: {}",
                u.as_str()
            );
            assert_eq!(uri_to_path(&u).unwrap_or_else(|| panic!("back: {p}")), path);
        }
    }

    /// A relative path has no `file:` URI. Saying so beats inventing one that
    /// resolves against whatever the process's working directory happens to be.
    #[test]
    fn a_relative_path_has_no_uri() {
        assert_eq!(path_to_uri(std::path::Path::new("relative/x.bean")), None);
    }

    /// A non-`file:` URI is not a path, and must not be coerced into one.
    #[test]
    fn a_non_file_uri_is_not_a_path() {
        assert_eq!(uri_to_path(&uri("untitled:Untitled-1")), None);
        assert_eq!(uri_to_path(&uri("https://example.com/x.bean")), None);
    }
}
