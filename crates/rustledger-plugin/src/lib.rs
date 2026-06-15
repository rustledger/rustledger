//! Beancount WASM Plugin Runtime.
//!
//! This crate provides a plugin system for extending Beancount's functionality.
//! Plugins can be written in any language that compiles to WebAssembly, or as
//! native Rust code for maximum performance.
//!
//! # Architecture
//!
//! The plugin system uses wasmtime as the WASM runtime with `MessagePack`
//! serialization for passing data across the WASM boundary.
//!
//! # Plugin Types
//!
//! - **WASM Plugins**: Sandboxed plugins loaded from `.wasm` files
//! - **Native Plugins**: Built-in plugins implemented in Rust
//!
//! # Built-in Plugins (31)
//!
//! See the [plugin reference](https://rustledger.github.io/docs/reference/plugins) for the full list.
//!
//! # Example
//!
//! ```ignore
//! use rustledger_plugin::{PluginManager, PluginInput, PluginOptions};
//!
//! let mut manager = PluginManager::new();
//! manager.load(Path::new("my_plugin.wasm"))?;
//!
//! let input = PluginInput {
//!     directives: vec![],
//!     options: PluginOptions::default(),
//!     config: None,
//! };
//!
//! let output = manager.execute_all(input)?;
//! ```

// Note: unsafe is needed for wasmtime Module::deserialize (caching compiled modules)
#![deny(unsafe_code)]
#![warn(missing_docs)]

pub mod convert;
pub mod native;
#[cfg(feature = "python-plugins")]
pub mod python;
#[cfg(feature = "wasm-runtime")]
pub mod runtime;
#[cfg(feature = "wasm-runtime")]
pub mod sandbox;
pub mod test_helpers;
pub mod types;
#[cfg(feature = "wasm-runtime")]
pub mod wasm_dir_scan;

pub use convert::{
    ConversionError, directive_to_wrapper, directive_to_wrapper_with_location,
    directives_to_wrappers, wrapper_to_directive, wrappers_to_directives,
};
pub use native::{
    AUTO_ACCOUNTS_NAME, DOCUMENT_DISCOVERY_NAME, NativePlugin, NativePluginRegistry, RegularPlugin,
    SynthPlugin, document_discovery_config,
};
#[cfg(feature = "wasm-runtime")]
pub use runtime::{
    Plugin, PluginManager, RuntimeConfig, WasmPluginDirScanReport, WatchingPluginManager,
    validate_plugin_module,
};
pub use types::{
    DirectiveWrapper, PluginError, PluginErrorSeverity, PluginInput, PluginOp, PluginOptions,
    PluginOutput,
};
