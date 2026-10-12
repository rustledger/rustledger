//! Python plugin support via CPython-WASI.
//!
//! This module enables running Python beancount plugins in a sandboxed WASM
//! environment. The Python runtime (`CPython` compiled to WASI) is downloaded
//! on first use and cached locally.
//!
//! # Features
//!
//! - Runs unmodified Python beancount plugins
//! - Fully sandboxed (no filesystem or network access)
//! - Downloaded on first use (~50MB)
//! - Compatible with most pure-Python plugins
//!
//! # Limitations
//!
//! - No C extensions (numpy, scikit-learn, etc.)
//! - No filesystem access for plugins
//! - No network access for plugins
//! - 10-100x slower than native Rust plugins
//!
//! # Example
//!
//! ```ignore
//! use rustledger_plugin::python::PythonRuntime;
//!
//! let runtime = PythonRuntime::new()?;
//! let output = runtime.execute_plugin(
//!     "beancount.plugins.check_commodity",
//!     &input,
//! )?;
//! ```

mod compat;
mod download;
mod runtime;

pub use compat::BEANCOUNT_COMPAT_PY;
pub use runtime::{
    PythonRuntime, builtin_python_plugin, is_python_available, is_python_plugin_file_ref,
    suggest_module_path,
};

/// Python plugin error types.
#[derive(Debug, thiserror::Error)]
pub enum PythonError {
    /// Failed to download Python runtime.
    #[error("failed to download Python runtime: {0}")]
    Download(String),

    /// Checksum mismatch after download.
    #[error("checksum mismatch: expected {expected}, got {actual}")]
    ChecksumMismatch {
        /// Expected checksum.
        expected: String,
        /// Actual checksum.
        actual: String,
    },

    /// Failed to execute Python code.
    #[error("Python execution failed: {0}")]
    Execution(String),

    /// Failed to serialize/deserialize data.
    #[error("serialization error: {0}")]
    Serialization(String),

    /// IO error.
    ///
    /// This and [`Self::Wasm`] name their cause in the message, so it is not
    /// also the `source()`: a `{:#}` chain would print it twice (#2574).
    /// `From` is implemented by hand below (`#[from]` implies `#[source]`).
    #[error("IO error: {0}")]
    Io(std::io::Error),

    /// WASM runtime error. `{0:#}` prints the whole `wasmtime::Error` chain,
    /// which the `source()` used to carry.
    #[error("WASM runtime error: {0:#}")]
    Wasm(wasmtime::Error),

    /// Plugin module not found on the system.
    #[error("Python plugin module not found: {0}")]
    ModuleNotFound(String),

    /// Plugin is a C extension (not supported in WASI sandbox).
    #[error("Python plugin '{0}' is a C extension and cannot run in WASI sandbox")]
    CExtensionNotSupported(String),

    /// Python runtime not available (Python interpreter not found).
    #[error("Python runtime unavailable: {0}")]
    RuntimeUnavailable(String),
}

impl From<std::io::Error> for PythonError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

impl From<wasmtime::Error> for PythonError {
    fn from(e: wasmtime::Error) -> Self {
        Self::Wasm(e)
    }
}

#[cfg(test)]
mod error_chain_tests {
    use super::PythonError;

    /// The `{:#}`-style chain: the message, then each `source()` in turn.
    fn chain(e: &dyn std::error::Error) -> String {
        let mut out = e.to_string();
        let mut cur = e.source();
        while let Some(s) = cur {
            out.push_str(": ");
            out.push_str(&s.to_string());
            cur = s.source();
        }
        out
    }

    /// #2574: `PythonError::Io` and `::Wasm` name their cause in the message
    /// and used to return it from `source()` as well, so a `{:#}` chain
    /// printed it twice. `Wasm` prints the whole `wasmtime::Error` chain in
    /// its message, so the inner cause the `source()` carried is kept.
    #[test]
    fn io_and_wasm_errors_name_their_cause_once_2574() {
        let io = PythonError::from(std::io::Error::other("INNER-IO"));
        assert_eq!(chain(&io), io.to_string());
        assert_eq!(chain(&io), "IO error: INNER-IO");

        let wasm = PythonError::from(wasmtime::Error::msg("INNER-CAUSE").context("OUTER-CONTEXT"));
        let chained = chain(&wasm);
        assert_eq!(chained, wasm.to_string(), "the message is the whole chain");
        assert_eq!(chained, "WASM runtime error: OUTER-CONTEXT: INNER-CAUSE");
    }
}
