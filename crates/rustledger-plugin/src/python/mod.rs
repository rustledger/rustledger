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

pub use runtime::PythonRuntime;

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
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    /// WASM runtime error.
    #[error("WASM runtime error: {0}")]
    Wasm(#[from] anyhow::Error),
}
