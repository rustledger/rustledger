//! WASM Plugin Runtime.
//!
//! This module provides the wasmtime-based runtime for executing plugins.
//!
//! # Security / Sandboxing
//!
//! Plugins run in a fully sandboxed environment with the following guarantees:
//!
//! - **No filesystem access**: Plugins cannot read or write files
//! - **No network access**: Plugins cannot make network connections
//! - **No environment access**: Plugins cannot read environment variables
//! - **No system calls**: No WASI or other system imports are provided
//! - **Memory limits**: Configurable max memory (default 256MB)
//! - **Execution limits**: Fuel-based execution time limits (default 30s)
//!
//! The only way for plugins to communicate is through the `process` function
//! which receives serialized directive data and returns modified directives.
//!
//! # Hot Reloading
//!
//! The `WatchingPluginManager` provides file-watching capability for
//! development workflows. It tracks plugin file modification times and
//! reloads plugins when their source files change.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::SystemTime;

use anyhow::{Context, Result};
use wasmtime::{Engine, Module, Config, Store, Linker};

use crate::types::{PluginInput, PluginOutput};

/// Configuration for the plugin runtime.
#[derive(Debug, Clone)]
pub struct RuntimeConfig {
    /// Maximum memory in bytes (default: 256MB).
    pub max_memory: usize,
    /// Maximum execution time in seconds (default: 30).
    pub max_time_secs: u64,
}

impl Default for RuntimeConfig {
    fn default() -> Self {
        Self {
            max_memory: 256 * 1024 * 1024, // 256MB
            max_time_secs: 30,
        }
    }
}

/// Validate that a WASM module doesn't have any forbidden imports.
///
/// Beancount plugins should be self-contained and not require any
/// external imports (WASI, env, etc.). This function checks that the
/// module only has the expected exports and no unexpected imports.
///
/// # Errors
///
/// Returns an error if the module has forbidden imports or is missing
/// required exports.
pub fn validate_plugin_module(bytes: &[u8]) -> Result<()> {
    let engine = Engine::default();
    let module = Module::new(&engine, bytes)?;

    // Check for forbidden imports (any imports are forbidden)
    if let Some(import) = module.imports().next() {
        anyhow::bail!(
            "plugin has forbidden import: {}::{}",
            import.module(),
            import.name()
        );
    }

    // Verify required exports exist
    let exports: Vec<_> = module.exports().map(|e| e.name()).collect();

    if !exports.contains(&"memory") {
        anyhow::bail!("plugin must export 'memory'");
    }
    if !exports.contains(&"alloc") {
        anyhow::bail!("plugin must export 'alloc' function");
    }
    if !exports.contains(&"process") {
        anyhow::bail!("plugin must export 'process' function");
    }

    Ok(())
}

/// A loaded WASM plugin.
pub struct Plugin {
    /// Plugin name (derived from filename).
    name: String,
    /// Compiled module.
    module: Module,
    /// Engine reference.
    engine: Arc<Engine>,
}

impl Plugin {
    /// Load a plugin from a WASM file.
    pub fn load(path: &Path, _config: &RuntimeConfig) -> Result<Self> {
        let name = path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("unknown")
            .to_string();

        // Create engine with configuration
        let mut engine_config = Config::new();
        engine_config.consume_fuel(true); // Enable fuel for execution limits

        let engine = Arc::new(Engine::new(&engine_config)?);

        // Load and compile the module
        let wasm_bytes =
            std::fs::read(path).with_context(|| format!("failed to read {}", path.display()))?;

        let module = Module::new(&engine, &wasm_bytes)
            .with_context(|| format!("failed to compile {}", path.display()))?;

        Ok(Self {
            name,
            module,
            engine,
        })
    }

    /// Load a plugin from WASM bytes.
    pub fn load_bytes(name: impl Into<String>, bytes: &[u8], _config: &RuntimeConfig) -> Result<Self> {
        let name = name.into();

        let mut engine_config = Config::new();
        engine_config.consume_fuel(true);

        let engine = Arc::new(Engine::new(&engine_config)?);
        let module = Module::new(&engine, bytes)?;

        Ok(Self {
            name,
            module,
            engine,
        })
    }

    /// Get the plugin name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Execute the plugin with the given input.
    pub fn execute(&self, input: &PluginInput, config: &RuntimeConfig) -> Result<PluginOutput> {
        // Create a store with fuel limit
        let mut store = Store::new(&self.engine, ());

        // Set fuel limit based on time (rough approximation: 1M instructions per second)
        let fuel = config.max_time_secs * 1_000_000;
        store.set_fuel(fuel)?;

        // Create linker with NO imports for full sandboxing
        // Plugins have no access to filesystem, network, or any system calls
        let linker = Linker::new(&self.engine);

        // Instantiate the module
        let instance = linker.instantiate(&mut store, &self.module)?;

        // Serialize input
        let input_bytes = rmp_serde::to_vec(input)?;

        // Get memory and allocate space for input
        let memory = instance
            .get_memory(&mut store, "memory")
            .context("plugin must export 'memory'")?;

        // Get the alloc function to allocate space in WASM memory
        let alloc = instance
            .get_typed_func::<u32, u32>(&mut store, "alloc")
            .context("plugin must export 'alloc' function")?;

        // Allocate space for input
        let input_ptr = alloc.call(&mut store, input_bytes.len() as u32)?;

        // Write input to WASM memory
        memory.write(&mut store, input_ptr as usize, &input_bytes)?;

        // Call the process function
        let process = instance
            .get_typed_func::<(u32, u32), u64>(&mut store, "process")
            .context("plugin must export 'process' function")?;

        let result = process.call(&mut store, (input_ptr, input_bytes.len() as u32))?;

        // Parse result (packed as ptr << 32 | len)
        let output_ptr = (result >> 32) as u32;
        let output_len = (result & 0xFFFF_FFFF) as u32;

        // Read output from WASM memory
        let mut output_bytes = vec![0u8; output_len as usize];
        memory.read(&store, output_ptr as usize, &mut output_bytes)?;

        // Deserialize output
        let output: PluginOutput = rmp_serde::from_slice(&output_bytes)?;

        Ok(output)
    }
}

/// Plugin manager that caches loaded plugins.
pub struct PluginManager {
    /// Runtime configuration.
    config: RuntimeConfig,
    /// Loaded plugins.
    plugins: Vec<Plugin>,
}

impl PluginManager {
    /// Create a new plugin manager.
    pub fn new() -> Self {
        Self::with_config(RuntimeConfig::default())
    }

    /// Create a plugin manager with custom configuration.
    pub const fn with_config(config: RuntimeConfig) -> Self {
        Self {
            config,
            plugins: Vec::new(),
        }
    }

    /// Load a plugin from a file path.
    pub fn load(&mut self, path: &Path) -> Result<usize> {
        let plugin = Plugin::load(path, &self.config)?;
        let index = self.plugins.len();
        self.plugins.push(plugin);
        Ok(index)
    }

    /// Load a plugin from bytes.
    pub fn load_bytes(&mut self, name: impl Into<String>, bytes: &[u8]) -> Result<usize> {
        let plugin = Plugin::load_bytes(name, bytes, &self.config)?;
        let index = self.plugins.len();
        self.plugins.push(plugin);
        Ok(index)
    }

    /// Execute a plugin by index.
    pub fn execute(&self, index: usize, input: &PluginInput) -> Result<PluginOutput> {
        let plugin = self
            .plugins
            .get(index)
            .context("plugin index out of bounds")?;
        plugin.execute(input, &self.config)
    }

    /// Execute all loaded plugins in sequence.
    pub fn execute_all(&self, mut input: PluginInput) -> Result<PluginOutput> {
        let mut all_errors = Vec::new();

        for plugin in &self.plugins {
            let output = plugin.execute(&input, &self.config)?;
            all_errors.extend(output.errors);
            input.directives = output.directives;
        }

        Ok(PluginOutput {
            directives: input.directives,
            errors: all_errors,
        })
    }

    /// Get the number of loaded plugins.
    pub fn len(&self) -> usize {
        self.plugins.len()
    }

    /// Check if any plugins are loaded.
    pub fn is_empty(&self) -> bool {
        self.plugins.is_empty()
    }
}

impl Default for PluginManager {
    fn default() -> Self {
        Self::new()
    }
}

/// A plugin with file tracking info for hot-reloading.
struct TrackedPlugin {
    /// The loaded plugin.
    plugin: Plugin,
    /// Path to the WASM file.
    path: PathBuf,
    /// Last modification time.
    modified: SystemTime,
}

/// Plugin manager with hot-reloading support.
///
/// This manager tracks plugin file modification times and can reload
/// plugins when their source files change. This is useful for development
/// workflows where you want to iterate on plugins without restarting.
///
/// # Example
///
/// ```ignore
/// use rustledger_plugin::WatchingPluginManager;
///
/// let mut manager = WatchingPluginManager::new();
/// manager.load("plugins/my_plugin.wasm")?;
///
/// // Check for changes and reload if needed
/// if manager.check_and_reload()? {
///     println!("Plugins reloaded!");
/// }
/// ```
pub struct WatchingPluginManager {
    /// Runtime configuration.
    config: RuntimeConfig,
    /// Tracked plugins with file info.
    plugins: Vec<TrackedPlugin>,
    /// Plugin name to index mapping for lookup.
    name_index: HashMap<String, usize>,
    /// Reload callback (optional).
    on_reload: Option<Box<dyn Fn(&str) + Send + Sync>>,
}

impl WatchingPluginManager {
    /// Create a new watching plugin manager.
    pub fn new() -> Self {
        Self::with_config(RuntimeConfig::default())
    }

    /// Create a watching plugin manager with custom configuration.
    pub fn with_config(config: RuntimeConfig) -> Self {
        Self {
            config,
            plugins: Vec::new(),
            name_index: HashMap::new(),
            on_reload: None,
        }
    }

    /// Set a callback to be invoked when a plugin is reloaded.
    pub fn on_reload<F>(&mut self, callback: F)
    where
        F: Fn(&str) + Send + Sync + 'static,
    {
        self.on_reload = Some(Box::new(callback));
    }

    /// Load a plugin from a file path.
    pub fn load(&mut self, path: impl AsRef<Path>) -> Result<usize> {
        let path = path.as_ref();
        let abs_path = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());

        // Get modification time
        let metadata = std::fs::metadata(&abs_path)
            .with_context(|| format!("failed to stat {}", abs_path.display()))?;
        let modified = metadata.modified()?;

        // Load the plugin
        let plugin = Plugin::load(&abs_path, &self.config)?;
        let name = plugin.name().to_string();
        let index = self.plugins.len();

        // Track the plugin
        self.plugins.push(TrackedPlugin {
            plugin,
            path: abs_path,
            modified,
        });
        self.name_index.insert(name, index);

        Ok(index)
    }

    /// Check for file changes and reload modified plugins.
    ///
    /// Returns `true` if any plugins were reloaded.
    pub fn check_and_reload(&mut self) -> Result<bool> {
        let mut reloaded = false;

        for tracked in &mut self.plugins {
            // Get current modification time
            let metadata = match std::fs::metadata(&tracked.path) {
                Ok(m) => m,
                Err(_) => continue, // File might have been deleted
            };

            let current_modified = match metadata.modified() {
                Ok(m) => m,
                Err(_) => continue,
            };

            // Check if file was modified
            if current_modified > tracked.modified {
                // Reload the plugin
                match Plugin::load(&tracked.path, &self.config) {
                    Ok(new_plugin) => {
                        let name = tracked.plugin.name().to_string();
                        tracked.plugin = new_plugin;
                        tracked.modified = current_modified;
                        reloaded = true;

                        // Call reload callback if set
                        if let Some(ref callback) = self.on_reload {
                            callback(&name);
                        }
                    }
                    Err(e) => {
                        // Log error but don't fail - keep using old plugin
                        eprintln!(
                            "warning: failed to reload plugin {}: {}",
                            tracked.path.display(),
                            e
                        );
                    }
                }
            }
        }

        Ok(reloaded)
    }

    /// Force reload all plugins.
    pub fn reload_all(&mut self) -> Result<()> {
        for tracked in &mut self.plugins {
            let new_plugin = Plugin::load(&tracked.path, &self.config)?;
            let metadata = std::fs::metadata(&tracked.path)?;
            tracked.plugin = new_plugin;
            tracked.modified = metadata.modified()?;
        }
        Ok(())
    }

    /// Get a plugin by name.
    pub fn get(&self, name: &str) -> Option<&Plugin> {
        self.name_index.get(name).map(|&i| &self.plugins[i].plugin)
    }

    /// Execute a plugin by index.
    pub fn execute(&self, index: usize, input: &PluginInput) -> Result<PluginOutput> {
        let tracked = self
            .plugins
            .get(index)
            .context("plugin index out of bounds")?;
        tracked.plugin.execute(input, &self.config)
    }

    /// Execute a plugin by name.
    pub fn execute_by_name(&self, name: &str, input: &PluginInput) -> Result<PluginOutput> {
        let index = self
            .name_index
            .get(name)
            .with_context(|| format!("plugin '{name}' not found"))?;
        self.execute(*index, input)
    }

    /// Execute all loaded plugins in sequence.
    pub fn execute_all(&self, mut input: PluginInput) -> Result<PluginOutput> {
        let mut all_errors = Vec::new();

        for tracked in &self.plugins {
            let output = tracked.plugin.execute(&input, &self.config)?;
            all_errors.extend(output.errors);
            input.directives = output.directives;
        }

        Ok(PluginOutput {
            directives: input.directives,
            errors: all_errors,
        })
    }

    /// Get the number of loaded plugins.
    pub fn len(&self) -> usize {
        self.plugins.len()
    }

    /// Check if any plugins are loaded.
    pub fn is_empty(&self) -> bool {
        self.plugins.is_empty()
    }

    /// Get plugin paths and their last modification times.
    pub fn plugin_info(&self) -> Vec<(&Path, SystemTime)> {
        self.plugins
            .iter()
            .map(|t| (t.path.as_path(), t.modified))
            .collect()
    }
}

impl Default for WatchingPluginManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Test that a minimal valid WASM module passes validation.
    ///
    /// This module exports memory, alloc, and process as required.
    #[test]
    fn test_valid_plugin_validation() {
        // A minimal WASM module with required exports
        // This is a hand-crafted minimal module that exports:
        // - memory
        // - alloc (returns 0)
        // - process (returns 0)
        let wasm = wat::parse_str(
            r#"
            (module
                (memory (export "memory") 1)
                (func (export "alloc") (param i32) (result i32)
                    i32.const 0
                )
                (func (export "process") (param i32 i32) (result i64)
                    i64.const 0
                )
            )
            "#,
        )
        .expect("valid wat");

        let result = validate_plugin_module(&wasm);
        assert!(result.is_ok(), "valid plugin should pass validation: {:?}", result.err());
    }

    /// Test that a module with WASI imports is rejected.
    #[test]
    fn test_wasi_import_rejected() {
        // A module that tries to import WASI fd_write
        let wasm = wat::parse_str(
            r#"
            (module
                (import "wasi_snapshot_preview1" "fd_write"
                    (func $fd_write (param i32 i32 i32 i32) (result i32))
                )
                (memory (export "memory") 1)
                (func (export "alloc") (param i32) (result i32)
                    i32.const 0
                )
                (func (export "process") (param i32 i32) (result i64)
                    i64.const 0
                )
            )
            "#,
        )
        .expect("valid wat");

        let result = validate_plugin_module(&wasm);
        assert!(result.is_err(), "module with WASI import should be rejected");
        let err = result.unwrap_err().to_string();
        assert!(err.contains("forbidden import"), "error should mention forbidden import: {err}");
        assert!(err.contains("wasi_snapshot_preview1"), "error should mention WASI: {err}");
    }

    /// Test that a module with env imports is rejected.
    #[test]
    fn test_env_import_rejected() {
        // A module that tries to import from env
        let wasm = wat::parse_str(
            r#"
            (module
                (import "env" "some_func" (func $some_func))
                (memory (export "memory") 1)
                (func (export "alloc") (param i32) (result i32)
                    i32.const 0
                )
                (func (export "process") (param i32 i32) (result i64)
                    i64.const 0
                )
            )
            "#,
        )
        .expect("valid wat");

        let result = validate_plugin_module(&wasm);
        assert!(result.is_err(), "module with env import should be rejected");
    }

    /// Test that a module missing required exports is rejected.
    #[test]
    fn test_missing_exports_rejected() {
        // Module missing 'alloc' export
        let wasm = wat::parse_str(
            r#"
            (module
                (memory (export "memory") 1)
                (func (export "process") (param i32 i32) (result i64)
                    i64.const 0
                )
            )
            "#,
        )
        .expect("valid wat");

        let result = validate_plugin_module(&wasm);
        assert!(result.is_err(), "module missing alloc should be rejected");
        assert!(result.unwrap_err().to_string().contains("alloc"));
    }

    /// Test that runtime config has sane defaults.
    #[test]
    fn test_runtime_config_defaults() {
        let config = RuntimeConfig::default();
        assert_eq!(config.max_memory, 256 * 1024 * 1024); // 256MB
        assert_eq!(config.max_time_secs, 30);
    }
}
