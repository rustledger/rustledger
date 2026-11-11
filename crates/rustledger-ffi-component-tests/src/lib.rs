//! Parity harness for the WIT / Component-Model surface (#1384).
//!
//! The actual tests live in `tests/parity.rs`, which instantiates the built
//! `rustledger-ffi-component` wasip2 component in a `wasmtime` host and asserts
//! agreement with the `rustledger-ffi-wasi` JSON-RPC path. A `tests/`-only
//! package reports "no targets specified in the manifest" on some toolchains,
//! so this lib target exists; it also holds the one place both test files
//! resolve the component artifact from (#2933).

use std::ffi::OsStr;
use std::path::{Path, PathBuf};

/// Path of the debug wasip2 component inside a cargo target directory.
const COMPONENT_IN_TARGET_DIR: &str = "wasm32-wasip2/debug/rustledger_ffi_component.wasm";

/// The prefix of the message printed when a test skips for a missing
/// component. CI's `component-parity` job greps for it, so keep it stable.
pub const SKIP_MARKER: &str = "skip: component wasm not built";

/// The workspace root (two levels above this crate's manifest).
#[must_use]
pub fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Resolve the component artifact path for a given `CARGO_TARGET_DIR` value.
///
/// - unset or empty: `<workspace_root>/target`
/// - absolute: used as is
/// - relative: taken against `workspace_root`, where cargo is normally run
///   from (the test binary's own cwd is the crate directory, so the original
///   invocation directory is not known here)
#[must_use]
pub fn resolve_component_path(target_dir: Option<&OsStr>, workspace_root: &Path) -> PathBuf {
    let target_dir = match target_dir {
        Some(dir) if !dir.is_empty() => {
            let dir = Path::new(dir);
            if dir.is_absolute() {
                dir.to_path_buf()
            } else {
                workspace_root.join(dir)
            }
        }
        _ => workspace_root.join("target"),
    };
    target_dir.join(COMPONENT_IN_TARGET_DIR)
}

/// Where the built component is expected, honoring `CARGO_TARGET_DIR`.
#[must_use]
pub fn component_path() -> PathBuf {
    resolve_component_path(
        std::env::var_os("CARGO_TARGET_DIR").as_deref(),
        &workspace_root(),
    )
}

/// Whether the component has been built. When it has not, prints
/// [`SKIP_MARKER`] with the exact path that was checked, so a skipped run says
/// where it looked rather than passing in silence.
#[must_use]
pub fn component_built() -> bool {
    let path = component_path();
    if path.exists() {
        return true;
    }
    eprintln!(
        "{SKIP_MARKER} (looked for {}; build it with \
         `cargo build -p rustledger-ffi-component --target wasm32-wasip2`)",
        path.display()
    );
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    const ARTIFACT: &str = "wasm32-wasip2/debug/rustledger_ffi_component.wasm";

    #[test]
    fn test_resolve_component_path_env_unset_uses_workspace_target() {
        let root = Path::new("/ws");
        assert_eq!(
            resolve_component_path(None, root),
            Path::new("/ws/target").join(ARTIFACT)
        );
    }

    #[test]
    fn test_resolve_component_path_env_empty_uses_workspace_target() {
        let root = Path::new("/ws");
        assert_eq!(
            resolve_component_path(Some(OsStr::new("")), root),
            Path::new("/ws/target").join(ARTIFACT)
        );
    }

    #[test]
    fn test_resolve_component_path_env_absolute_is_used_as_is() {
        let root = Path::new("/ws");
        // `temp_dir()` is absolute on every platform, unlike a literal `/x`
        // (which Windows treats as relative to the current drive).
        let abs = std::env::temp_dir().join("elsewhere-tgt");
        assert!(abs.is_absolute());
        assert_eq!(
            resolve_component_path(Some(abs.as_os_str()), root),
            abs.join(ARTIFACT)
        );
    }

    #[test]
    fn test_resolve_component_path_env_relative_is_under_workspace_root() {
        let root = Path::new("/ws");
        assert_eq!(
            resolve_component_path(Some(OsStr::new(".cargo-target")), root),
            Path::new("/ws/.cargo-target").join(ARTIFACT)
        );
    }
}
