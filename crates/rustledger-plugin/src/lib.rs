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
//! # Built-in Plugins (14)
//!
//! - `implicit_prices`: Generates price entries from transaction costs/prices
//! - `check_commodity`: Verifies all commodities are declared
//! - `auto_accounts`: Auto-generates Open directives for used accounts
//! - `auto_tag`: Auto-tag transactions by account patterns
//! - `leafonly`: Errors on postings to non-leaf accounts
//! - `noduplicates`: Hash-based duplicate transaction detection
//! - `onecommodity`: Enforces single commodity per account
//! - `unique_prices`: One price per day per currency pair
//! - `check_closing`: Zero balance assertion on account closing
//! - `close_tree`: Closes descendant accounts automatically
//! - `coherent_cost`: Enforces cost OR price (not both) consistency
//! - `sellgains`: Cross-checks capital gains against sales
//! - `pedantic`: Enables all strict validation rules
//! - `unrealized`: Calculates unrealized gains/losses
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

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod convert;
pub mod native;
pub mod runtime;
pub mod types;

pub use convert::{
    directive_to_wrapper, directives_to_wrappers, wrapper_to_directive, wrappers_to_directives,
    ConversionError,
};
pub use native::{NativePlugin, NativePluginRegistry};
pub use runtime::{validate_plugin_module, Plugin, PluginManager, RuntimeConfig, WatchingPluginManager};
pub use types::{
    PluginError, PluginErrorSeverity, PluginInput, PluginOptions, PluginOutput,
};
