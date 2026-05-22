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
use wasmtime::{Engine, Linker, Module};

use crate::sandbox;
use crate::types::{DirectiveWrapper, PluginInput, PluginOp, PluginOutput};

/// Materialize a plugin's `ops` against its input directive list,
/// producing the resulting flat list of wrappers.
///
/// Used by `execute_all` to chain plugin outputs back into the next
/// plugin's input. The loader uses a more elaborate version
/// (`apply_plugin_ops` in `rustledger-loader`) that also validates the
/// ops protocol invariants and preserves source spans; here we just
/// need the materialized list.
fn materialize_ops(input: &[DirectiveWrapper], output: &PluginOutput) -> Vec<DirectiveWrapper> {
    let mut out = Vec::with_capacity(output.ops.len());
    for op in &output.ops {
        match op {
            PluginOp::Keep(i) => {
                if let Some(w) = input.get(*i) {
                    out.push(w.clone());
                }
            }
            PluginOp::Modify(_, w) | PluginOp::Insert(w) => out.push(w.clone()),
            PluginOp::Delete(_) => {}
        }
    }
    out
}

/// Configuration for the plugin runtime.
///
/// **Applied at `Plugin::execute` time, not at load.** `Plugin::load`
/// and `Plugin::load_bytes` accept a `&RuntimeConfig` for API
/// symmetry but ignore it — only the per-call execution caps
/// (`max_memory`, `max_time_secs`) are meaningful, and those flow
/// into the per-`Store` setup that `execute` builds.
#[derive(Debug, Clone)]
pub struct RuntimeConfig {
    /// Maximum memory in bytes (default: 256MB). Enforced at
    /// `Plugin::execute` via [`crate::sandbox::make_sandboxed_store`].
    pub max_memory: usize,
    /// Maximum execution time in seconds (default: 30). Clamped to
    /// `≥1` and `saturating_mul`'d to fuel units; see
    /// [`crate::sandbox::make_sandboxed_store`].
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
    // Use the workspace sandbox config — same feature flags the
    // runtime applies at load. Otherwise `validate_plugin_module`
    // could say "Ok" against vanilla wasmtime features but the
    // actual `Plugin::load_bytes` would reject the same module
    // because (e.g.) it uses `wasm_threads`.
    let engine = Engine::new(&sandbox::sandbox_config())?;
    let module = Module::new(&engine, bytes)?;
    validate_loaded_module(&module)
}

/// Inner validator that operates on an already-compiled [`Module`].
/// Used by both [`validate_plugin_module`] (the public bytes-taking
/// helper) and `Plugin::load`/`load_bytes` so the module is only
/// compiled once during load instead of twice.
fn validate_loaded_module(module: &Module) -> Result<()> {
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

        // Process-wide shared engine with the workspace's locked-down
        // wasm-feature config (see `sandbox::sandbox_config` for the
        // list). One Engine per process amortizes JIT/cache cost
        // across all loaded plugins.
        let engine = sandbox::shared_engine();

        // Load and compile the module
        let wasm_bytes =
            std::fs::read(path).with_context(|| format!("failed to read {}", path.display()))?;

        let module = Module::new(&engine, &wasm_bytes)
            .map_err(anyhow::Error::from)
            .with_context(|| format!("invalid plugin {}", path.display()))?;

        // Validate imports + required exports at load time so failures
        // surface here (with a clear "must export" message) rather than
        // deeper in `execute()` where they look like signature mismatches.
        validate_loaded_module(&module)
            .with_context(|| format!("invalid plugin {}", path.display()))?;

        Ok(Self {
            name,
            module,
            engine,
        })
    }

    /// Load a plugin from WASM bytes.
    pub fn load_bytes(
        name: impl Into<String>,
        bytes: &[u8],
        _config: &RuntimeConfig,
    ) -> Result<Self> {
        let name = name.into();
        let engine = sandbox::shared_engine();
        let module = Module::new(&engine, bytes)
            .map_err(anyhow::Error::from)
            .with_context(|| format!("invalid plugin `{name}`"))?;
        // Same load-time validation as `load` — see that method's
        // comment for rationale.
        validate_loaded_module(&module).with_context(|| format!("invalid plugin `{name}`"))?;

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
        // Workspace-shared sandboxed store: wires the MemoryLimiter
        // (enforcing `config.max_memory` on initial allocation +
        // `memory.grow`) and the fuel budget (clamped ≥1 + saturating
        // to avoid zero-fuel starvation and u64 overflow). Mirrors the
        // WASM importer host so per-call enforcement is consistent
        // across the workspace.
        let mut store =
            sandbox::make_sandboxed_store(&self.engine, config.max_memory, config.max_time_secs)?;

        // Create linker with NO imports for full sandboxing
        // Plugins have no access to filesystem, network, or any system calls
        let linker = Linker::new(&self.engine);

        // Instantiate the module
        let instance = linker.instantiate(&mut store, &self.module)?;

        // Serialize input. The serializer choice (default-mode
        // `to_vec`, not `to_vec_named`) is pinned by the
        // cross-boundary wire-format tests in
        // `rustledger-plugin-types/tests/cost_number_wire_format.rs`.
        // If you change this call to a different rmp_serde entry
        // point, update those tests to match — otherwise plugins
        // built against the old wire shape silently break.
        let input_bytes = rmp_serde::to_vec(input)?;

        // `validate_loaded_module` proved `memory` presence at load
        // time — an absent export here is unreachable in practice.
        let memory = instance
            .get_memory(&mut store, "memory")
            .expect("validate_loaded_module verified `memory` export at load");

        // Same reasoning: presence is guaranteed by load-time
        // validation, so any `get_typed_func` failure here is a
        // signature mismatch (e.g. plugin declared `alloc(i64) -> i64`
        // instead of `alloc(u32) -> u32`), not absence.
        let alloc = instance
            .get_typed_func::<u32, u32>(&mut store, "alloc")
            .map_err(anyhow::Error::from)
            // wasmtime's error already names the expected vs found
            // signature — our context just labels what was being
            // looked up. Avoids drift if the ABI ever changes.
            .context("plugin export `alloc` has wrong signature")?;

        // Allocate space for input
        let input_ptr = alloc.call(&mut store, input_bytes.len() as u32)?;

        // Write input to WASM memory
        memory.write(&mut store, input_ptr as usize, &input_bytes)?;

        // Call the process function
        let process = instance
            .get_typed_func::<(u32, u32), u64>(&mut store, "process")
            .map_err(anyhow::Error::from)
            .context("plugin export `process` has wrong signature")?;

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

/// Result of [`PluginManager::register_wasm_dir`].
///
/// Splits successfully-loaded plugin names from per-file failures so
/// callers can log/report both. A single broken module in a dir with
/// 19 good ones leaves the 19 registered; the broken one's path + error
/// land in [`Self::failures`]. Mirrors `rustledger_importer::WasmDirScanReport`.
#[derive(Debug, Default)]
pub struct WasmPluginDirScanReport {
    /// Plugin names of each successfully-loaded module, in load order
    /// (lexicographic by file path). Name is the file stem — the path's
    /// final component without the `.wasm` extension.
    pub loaded: Vec<String>,
    /// Per-file load failures. Each entry is the `.wasm` path plus the
    /// underlying error. Per-entry I/O errors (rare — broken symlinks,
    /// permission denied on a single inode) appear here tagged with
    /// the dir path since the inode's name isn't known.
    pub failures: Vec<(PathBuf, anyhow::Error)>,
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

    /// Scan `dir` for `*.wasm` files (one level only — no recursion)
    /// and register each as a plugin.
    ///
    /// Files are loaded in sorted order so multi-plugin pipelines have
    /// deterministic ordering across filesystems and platforms.
    /// Extension matching is case-insensitive — `foo.wasm` and
    /// `BAR.WASM` are both picked up.
    ///
    /// Loading is **skip-and-collect**: every loadable module is
    /// registered; failures are accumulated in
    /// [`WasmPluginDirScanReport::failures`] so the caller can decide
    /// whether to log them, abort, or ignore. A single broken module
    /// in a dir with 19 good ones doesn't prevent the 19 from
    /// loading. Mirrors `ImporterRegistry::register_wasm_dir` in
    /// `rustledger-importer`.
    ///
    /// Non-`.wasm` files (a `README.md` or `.gitignore`) and
    /// subdirectories are silently skipped. Entries whose metadata
    /// can't be read at all (broken symlinks; the file existed in
    /// `read_dir`'s listing but `path.is_file()` returns false) are
    /// also silently skipped — `std::fs::DirEntry::path().is_file()`
    /// swallows the underlying I/O error. If that matters for your
    /// use case, walk the dir yourself with explicit
    /// `symlink_metadata` checks.
    ///
    /// # Errors
    ///
    /// The outer `Result` reports an I/O error reading `dir` itself
    /// (dir doesn't exist, permission denied on the dir). Per-file
    /// load failures land inside the report's `failures` vec so the
    /// caller can surface them without aborting the rest of the scan.
    pub fn register_wasm_dir(&mut self, dir: impl AsRef<Path>) -> Result<WasmPluginDirScanReport> {
        let dir = dir.as_ref();
        // Listing/filtering/sorting is shared with `ImporterRegistry::register_wasm_dir`
        // in `rustledger-importer` — see `crate::wasm_dir_scan` for the
        // common helper. Caller-side: dir-level error context + the
        // per-file load fn + the per-entry error wrapping.
        let scan = crate::wasm_dir_scan::collect_wasm_paths(dir)
            .with_context(|| format!("failed to read plugin dir {}", dir.display()))?;
        let mut report = WasmPluginDirScanReport::default();
        // Forward per-entry I/O failures wrapped in anyhow.
        for (path, source) in scan.entry_failures {
            report.failures.push((path, anyhow::Error::new(source)));
        }
        for path in scan.sorted_paths {
            match self.load(&path) {
                Ok(index) => {
                    // Read the name back from the registered Plugin so
                    // `report.loaded` exactly matches `Plugin::name()`
                    // for all subsequent calls — including the
                    // non-UTF-8-filename edge case where `Plugin::load`
                    // falls back to `"unknown"`.
                    let name = self.plugins[index].name().to_string();
                    report.loaded.push(name);
                }
                Err(e) => report.failures.push((path, e)),
            }
        }
        Ok(report)
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
    ///
    /// Note: because the ops protocol references the **plugin's** input
    /// indices and `execute_all` chains plugins by materializing each
    /// stage's ops before feeding the next, the final ops returned
    /// here describe the result relative to the original input as a
    /// **rebuild**: every output directive is encoded as
    /// [`PluginOp::Insert`] and every original input is encoded as
    /// [`PluginOp::Delete`]. Loader callers don't go through this
    /// path — they apply ops one plugin at a time — so this simplifies
    /// the multi-plugin WASM-runtime case to "here's the resulting
    /// directive list" without losing the protocol's invariants.
    pub fn execute_all(&self, mut input: PluginInput) -> Result<PluginOutput> {
        let mut all_errors = Vec::new();
        let n_original = input.directives.len();

        for plugin in &self.plugins {
            let output = plugin.execute(&input, &self.config)?;
            // Materialize this plugin's ops to feed the next plugin.
            input.directives = materialize_ops(&input.directives, &output);
            all_errors.extend(output.errors);
        }

        // Rebuild-style ops: Delete every original input, Insert every
        // final directive. Order: deletes first so the protocol
        // invariant (each input index appears once) is satisfied.
        let mut ops: Vec<PluginOp> = (0..n_original).map(PluginOp::Delete).collect();
        for w in input.directives {
            ops.push(PluginOp::Insert(w));
        }

        Ok(PluginOutput {
            ops,
            errors: all_errors,
        })
    }

    /// Get the number of loaded plugins.
    pub const fn len(&self) -> usize {
        self.plugins.len()
    }

    /// Check if any plugins are loaded.
    pub const fn is_empty(&self) -> bool {
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
        // Canonicalize path, or use original if it fails (e.g., symlink issues)
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
    ///
    /// See [`PluginManager::execute_all`] for the rebuild-style
    /// (Delete-all-Insert-all) op encoding rationale.
    pub fn execute_all(&self, mut input: PluginInput) -> Result<PluginOutput> {
        let mut all_errors = Vec::new();
        let n_original = input.directives.len();

        for tracked in &self.plugins {
            let output = tracked.plugin.execute(&input, &self.config)?;
            input.directives = materialize_ops(&input.directives, &output);
            all_errors.extend(output.errors);
        }

        let mut ops: Vec<PluginOp> = (0..n_original).map(PluginOp::Delete).collect();
        for w in input.directives {
            ops.push(PluginOp::Insert(w));
        }

        Ok(PluginOutput {
            ops,
            errors: all_errors,
        })
    }

    /// Get the number of loaded plugins.
    pub const fn len(&self) -> usize {
        self.plugins.len()
    }

    /// Check if any plugins are loaded.
    pub const fn is_empty(&self) -> bool {
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
    use crate::types::PluginOptions;

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
        assert!(
            result.is_ok(),
            "valid plugin should pass validation: {:?}",
            result.err()
        );
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
        assert!(
            result.is_err(),
            "module with WASI import should be rejected"
        );
        let err = result.unwrap_err().to_string();
        assert!(
            err.contains("forbidden import"),
            "error should mention forbidden import: {err}"
        );
        assert!(
            err.contains("wasi_snapshot_preview1"),
            "error should mention WASI: {err}"
        );
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

    /// Test that a module missing memory export is rejected.
    #[test]
    fn test_missing_memory_rejected() {
        let wasm = wat::parse_str(
            r#"
            (module
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
        assert!(result.is_err(), "module missing memory should be rejected");
        assert!(result.unwrap_err().to_string().contains("memory"));
    }

    /// Test that a module missing process export is rejected.
    #[test]
    fn test_missing_process_rejected() {
        let wasm = wat::parse_str(
            r#"
            (module
                (memory (export "memory") 1)
                (func (export "alloc") (param i32) (result i32)
                    i32.const 0
                )
            )
            "#,
        )
        .expect("valid wat");

        let result = validate_plugin_module(&wasm);
        assert!(result.is_err(), "module missing process should be rejected");
        assert!(result.unwrap_err().to_string().contains("process"));
    }

    /// Test that invalid WASM bytes are rejected.
    #[test]
    fn test_invalid_wasm_rejected() {
        let invalid = b"not valid wasm bytes";
        let result = validate_plugin_module(invalid);
        assert!(result.is_err(), "invalid WASM should be rejected");
    }

    /// Test that runtime config can be customized.
    #[test]
    fn test_runtime_config_custom() {
        let config = RuntimeConfig {
            max_memory: 512 * 1024 * 1024, // 512MB
            max_time_secs: 60,
        };
        assert_eq!(config.max_memory, 512 * 1024 * 1024);
        assert_eq!(config.max_time_secs, 60);
    }

    // ====================================================================
    // Phase 3: Additional Coverage Tests for Plugin Managers
    // ====================================================================

    #[test]
    fn test_plugin_manager_new() {
        let manager = PluginManager::new();
        assert!(manager.is_empty());
        assert_eq!(manager.len(), 0);
    }

    #[test]
    fn test_plugin_manager_with_config() {
        let config = RuntimeConfig {
            max_memory: 128 * 1024 * 1024,
            max_time_secs: 10,
        };
        let manager = PluginManager::with_config(config);
        assert!(manager.is_empty());
    }

    #[test]
    fn test_plugin_manager_default() {
        let manager = PluginManager::default();
        assert!(manager.is_empty());
        assert_eq!(manager.len(), 0);
    }

    #[test]
    fn test_watching_plugin_manager_new() {
        let manager = WatchingPluginManager::new();
        assert!(manager.is_empty());
        assert_eq!(manager.len(), 0);
        assert!(manager.plugin_info().is_empty());
    }

    #[test]
    fn test_watching_plugin_manager_with_config() {
        let config = RuntimeConfig {
            max_memory: 64 * 1024 * 1024,
            max_time_secs: 5,
        };
        let manager = WatchingPluginManager::with_config(config);
        assert!(manager.is_empty());
    }

    #[test]
    fn test_watching_plugin_manager_default() {
        let manager = WatchingPluginManager::default();
        assert!(manager.is_empty());
        assert_eq!(manager.len(), 0);
    }

    #[test]
    fn test_watching_plugin_manager_get_unknown() {
        let manager = WatchingPluginManager::new();
        assert!(manager.get("nonexistent").is_none());
    }

    #[test]
    fn test_plugin_manager_execute_out_of_bounds() {
        let manager = PluginManager::new();
        let input = crate::types::PluginInput {
            directives: vec![],
            options: crate::types::PluginOptions::default(),
            config: None,
        };
        let result = manager.execute(0, &input);
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("out of bounds"));
    }

    #[test]
    fn test_watching_plugin_manager_execute_out_of_bounds() {
        let manager = WatchingPluginManager::new();
        let input = crate::types::PluginInput {
            directives: vec![],
            options: crate::types::PluginOptions::default(),
            config: None,
        };
        let result = manager.execute(0, &input);
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("out of bounds"));
    }

    #[test]
    fn test_watching_plugin_manager_execute_by_name_unknown() {
        let manager = WatchingPluginManager::new();
        let input = crate::types::PluginInput {
            directives: vec![],
            options: crate::types::PluginOptions::default(),
            config: None,
        };
        let result = manager.execute_by_name("unknown", &input);
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("not found"));
    }

    #[test]
    fn test_plugin_manager_execute_all_empty() {
        let manager = PluginManager::new();
        let input = crate::types::PluginInput {
            directives: vec![],
            options: crate::types::PluginOptions::default(),
            config: None,
        };
        let result = manager.execute_all(input);
        assert!(result.is_ok());
        let output = result.unwrap();
        assert!(output.ops.is_empty());
        assert!(output.errors.is_empty());
    }

    #[test]
    fn test_watching_plugin_manager_execute_all_empty() {
        let manager = WatchingPluginManager::new();
        let input = crate::types::PluginInput {
            directives: vec![],
            options: crate::types::PluginOptions::default(),
            config: None,
        };
        let result = manager.execute_all(input);
        assert!(result.is_ok());
        let output = result.unwrap();
        assert!(output.ops.is_empty());
        assert!(output.errors.is_empty());
    }

    #[test]
    fn test_watching_plugin_manager_check_reload_empty() {
        let mut manager = WatchingPluginManager::new();
        let result = manager.check_and_reload();
        assert!(result.is_ok());
        assert!(!result.unwrap()); // No plugins reloaded
    }

    #[test]
    fn test_watching_plugin_manager_reload_all_empty() {
        let mut manager = WatchingPluginManager::new();
        let result = manager.reload_all();
        assert!(result.is_ok()); // Should succeed with empty manager
    }

    #[test]
    fn test_plugin_load_bytes() {
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

        let config = RuntimeConfig::default();
        let result = Plugin::load_bytes("test_plugin", &wasm, &config);
        assert!(result.is_ok());

        let plugin = result.unwrap();
        assert_eq!(plugin.name(), "test_plugin");
    }

    #[test]
    fn test_plugin_manager_load_bytes() {
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

        let mut manager = PluginManager::new();
        let result = manager.load_bytes("my_plugin", &wasm);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 0); // First plugin index
        assert_eq!(manager.len(), 1);
        assert!(!manager.is_empty());
    }

    #[test]
    fn test_plugin_manager_multiple_plugins() {
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

        let mut manager = PluginManager::new();
        manager.load_bytes("plugin1", &wasm).unwrap();
        manager.load_bytes("plugin2", &wasm).unwrap();
        manager.load_bytes("plugin3", &wasm).unwrap();

        assert_eq!(manager.len(), 3);
    }

    #[test]
    fn test_validate_truncated_wasm() {
        // Start of valid WASM but truncated
        let truncated = &[0x00, 0x61, 0x73, 0x6d]; // Just the magic bytes
        let result = validate_plugin_module(truncated);
        assert!(result.is_err());
    }

    #[test]
    fn test_validate_wrong_magic() {
        let wrong_magic = &[0xFF, 0xFF, 0xFF, 0xFF];
        let result = validate_plugin_module(wrong_magic);
        assert!(result.is_err());
    }

    #[test]
    fn test_validate_empty_wasm() {
        let empty: &[u8] = &[];
        let result = validate_plugin_module(empty);
        assert!(result.is_err());
    }

    #[test]
    fn execute_rejects_initial_memory_above_max_memory_cap() {
        // Plugin declares 5000 pages (320 MiB) initial memory.
        // With max_memory = 64 MiB, instantiation inside execute()
        // must fail via the MemoryLimiter wired by
        // `sandbox::make_sandboxed_store`. Pins the equivalent of
        // the importer's `initial_memory_above_cap_is_rejected_via_limiter_wiring`
        // test for the plugin runtime path — proves the per-Store
        // limiter is actually applied here, not just in the importer.
        let wasm = wat::parse_str(
            r#"
            (module
                (memory (export "memory") 5000)
                (func (export "alloc") (param i32) (result i32) i32.const 0)
                (func (export "process") (param i32 i32) (result i64) i64.const 0)
            )
            "#,
        )
        .expect("WAT parses");
        let plugin = Plugin::load_bytes("bigmem", &wasm, &RuntimeConfig::default())
            .expect("module loads (declared memory size is checked at instantiate, not compile)");
        let tight_config = RuntimeConfig {
            max_memory: 64 * 1024 * 1024,
            max_time_secs: 30,
        };
        let input = PluginInput {
            directives: vec![],
            options: PluginOptions {
                operating_currencies: vec![],
                title: None,
            },
            config: None,
        };
        let err = plugin
            .execute(&input, &tight_config)
            .expect_err("instantiation should fail when initial memory > cap");
        // Check for one of the keywords wasmtime uses when a
        // ResourceLimiter rejects allocation. Wording varies across
        // versions, but at least one of these tokens has appeared
        // in every release we've targeted, so this catches a
        // truly-silent failure (e.g. limiter not wired) while
        // tolerating message rephrasings.
        let msg = format!("{err:#}").to_ascii_lowercase();
        assert!(
            msg.contains("memory") || msg.contains("limit"),
            "expected memory-limit error, got: {msg}"
        );
    }

    #[test]
    fn execute_surfaces_wrong_signature_on_alloc() {
        // Plugin has `alloc(i64) -> i64` instead of the required
        // `alloc(u32) -> u32`. Presence check (validate_loaded_module)
        // passes — the export is there. The signature mismatch
        // surfaces inside `execute()` with the new "wrong signature"
        // context. Pre-PR this would have read "plugin must export
        // 'alloc' function" — misleading, since it DOES export it.
        let wasm = wat::parse_str(
            r#"
            (module
                (memory (export "memory") 1)
                (func (export "alloc") (param i64) (result i64) i64.const 0)
                (func (export "process") (param i32 i32) (result i64) i64.const 0)
            )
            "#,
        )
        .expect("WAT parses");
        let plugin = Plugin::load_bytes("bad-alloc-sig", &wasm, &RuntimeConfig::default())
            .expect("module loads (validate only checks presence by name)");
        let input = PluginInput {
            directives: vec![],
            options: PluginOptions {
                operating_currencies: vec![],
                title: None,
            },
            config: None,
        };
        let err = plugin
            .execute(&input, &RuntimeConfig::default())
            .expect_err("wrong-sig alloc should fail execute");
        let msg = format!("{err:#}");
        assert!(
            msg.contains("alloc") && msg.contains("wrong signature"),
            "expected `alloc` + `wrong signature` in error, got: {msg}"
        );
    }

    #[test]
    fn execute_surfaces_wrong_signature_on_process() {
        // Symmetric to the `alloc` sibling: `process` is declared
        // as `(i32, i32) -> i32` instead of `(u32, u32) -> u64`.
        // Presence check passes; signature mismatch surfaces with
        // the new "wrong signature" context.
        let wasm = wat::parse_str(
            r#"
            (module
                (memory (export "memory") 1)
                (func (export "alloc") (param i32) (result i32) i32.const 0)
                (func (export "process") (param i32 i32) (result i32) i32.const 0)
            )
            "#,
        )
        .expect("WAT parses");
        let plugin = Plugin::load_bytes("bad-process-sig", &wasm, &RuntimeConfig::default())
            .expect("module loads (validate only checks presence by name)");
        let input = PluginInput {
            directives: vec![],
            options: PluginOptions {
                operating_currencies: vec![],
                title: None,
            },
            config: None,
        };
        let err = plugin
            .execute(&input, &RuntimeConfig::default())
            .expect_err("wrong-sig process should fail execute");
        let msg = format!("{err:#}");
        assert!(
            msg.contains("process") && msg.contains("wrong signature"),
            "expected `process` + `wrong signature` in error, got: {msg}"
        );
    }

    /// Minimal passthrough WAT used by the fuel-clamp tests below.
    /// `process` returns `(ptr=0, len=0)` which deserializes to an
    /// empty `PluginOutput` — enough to exercise the full fuel path.
    fn passthrough_wat() -> &'static str {
        r#"
        (module
            (memory (export "memory") 1)
            (func (export "alloc") (param i32) (result i32) i32.const 0)
            (func (export "process") (param i32 i32) (result i64) i64.const 0)
        )
        "#
    }

    fn empty_input() -> PluginInput {
        PluginInput {
            directives: vec![],
            options: PluginOptions {
                operating_currencies: vec![],
                title: None,
            },
            config: None,
        }
    }

    /// Assert that the error from a passthrough-WAT `execute` is the
    /// expected msgpack-decode failure (the WAT returns
    /// `(ptr=0, len=0)`, which can't parse as `PluginOutput`) and not
    /// a fuel-exhaustion trap.
    ///
    /// Reaching the decode step proves WASM execution completed —
    /// any fuel-starvation bug would have trapped before then.
    fn assert_not_fuel_trap(err: &anyhow::Error) {
        let msg = format!("{err:#}").to_ascii_lowercase();
        assert!(
            !msg.contains("fuel") && !msg.contains("trap"),
            "expected msgpack decode error, got fuel/trap: {msg}"
        );
    }

    #[test]
    fn execute_with_zero_max_time_secs_clamps_to_min_fuel() {
        // Regression for the fuel-calc bug fix that landed via
        // `make_sandboxed_store`. Pre-PR, `max_time_secs = 0` caused
        // immediate fuel-exhaustion trap on first instruction. Now
        // clamped to ≥1 second of fuel by the shared helper.
        // Proves the plugin runtime gets the fix, not just the
        // importer.
        let wasm = wat::parse_str(passthrough_wat()).expect("WAT parses");
        let plugin =
            Plugin::load_bytes("fuel-zero", &wasm, &RuntimeConfig::default()).expect("loads");
        let zero_secs = RuntimeConfig {
            max_memory: 256 * 1024 * 1024,
            max_time_secs: 0,
        };
        let err = plugin
            .execute(&empty_input(), &zero_secs)
            .expect_err("passthrough WAT decode-fails by design");
        assert_not_fuel_trap(&err);
    }

    #[test]
    fn execute_with_max_max_time_secs_saturates_fuel() {
        // Regression for the saturating_mul fix. Pre-PR, max_time_secs
        // = u64::MAX would panic in debug and silently wrap in
        // release. Now saturates to u64::MAX fuel via the shared
        // helper.
        let wasm = wat::parse_str(passthrough_wat()).expect("WAT parses");
        let plugin =
            Plugin::load_bytes("fuel-max", &wasm, &RuntimeConfig::default()).expect("loads");
        let max_secs = RuntimeConfig {
            max_memory: 256 * 1024 * 1024,
            max_time_secs: u64::MAX,
        };
        let err = plugin
            .execute(&empty_input(), &max_secs)
            .expect_err("passthrough WAT decode-fails by design");
        assert_not_fuel_trap(&err);
    }

    // ===== register_wasm_dir =====
    //
    // Mirrors `ImporterRegistry::register_wasm_dir`'s skip-and-collect
    // contract. Build a tempdir holding a mix of valid `.wasm`, invalid
    // `.wasm`, non-wasm files, and a subdirectory; assert the loader
    // picks only the top-level `.wasm` files, loads what's valid,
    // collects failures for what isn't, and never aborts the scan.

    fn valid_plugin_wasm() -> Vec<u8> {
        wat::parse_str(
            r#"
            (module
                (memory (export "memory") 1)
                (func (export "alloc") (param i32) (result i32) i32.const 0)
                (func (export "process") (param i32 i32) (result i64) i64.const 0)
            )
            "#,
        )
        .expect("valid wat")
    }

    #[test]
    fn register_wasm_dir_loads_valid_skips_broken_and_non_wasm() {
        let dir = tempfile::tempdir().expect("tempdir");
        let dir_path = dir.path();

        // Two valid plugins — load in sorted order: `a_first`, `b_second`.
        std::fs::write(dir_path.join("b_second.wasm"), valid_plugin_wasm()).unwrap();
        std::fs::write(dir_path.join("a_first.wasm"), valid_plugin_wasm()).unwrap();

        // A broken `.wasm` — failure lands in `failures`, doesn't abort.
        std::fs::write(dir_path.join("broken.wasm"), b"not a wasm module").unwrap();

        // Non-wasm files — silently ignored.
        std::fs::write(dir_path.join("README.md"), "ignore me").unwrap();
        std::fs::write(dir_path.join(".gitignore"), "ignore me too").unwrap();

        // Subdirectory — not recursed into. Even with a `.wasm` inside.
        let subdir = dir_path.join("sub");
        std::fs::create_dir(&subdir).unwrap();
        std::fs::write(subdir.join("recursed.wasm"), valid_plugin_wasm()).unwrap();

        let mut manager = PluginManager::new();
        let report = manager
            .register_wasm_dir(dir_path)
            .expect("dir-level read succeeds");

        // Sorted load order — `a_first` before `b_second`.
        assert_eq!(report.loaded, vec!["a_first", "b_second"]);
        assert_eq!(manager.len(), 2);

        // `broken.wasm` is the only failure.
        assert_eq!(report.failures.len(), 1);
        assert_eq!(
            report.failures[0].0.file_name().and_then(|s| s.to_str()),
            Some("broken.wasm"),
        );
    }

    #[test]
    fn register_wasm_dir_propagates_dir_level_io_error() {
        // Use a tempdir-relative path that's guaranteed not to exist
        // — hard-coding `/this/dir/does/not/exist` could pass on a
        // weird machine where that path happens to be a real dir,
        // and would fail with a different error class on platforms
        // where the syscall behaves differently.
        let tmp = tempfile::tempdir().expect("tempdir");
        let nonexistent = tmp.path().join("does-not-exist");
        let mut manager = PluginManager::new();
        let err = manager
            .register_wasm_dir(&nonexistent)
            .expect_err("nonexistent dir should error at read_dir, not in failures");
        assert!(err.to_string().contains("failed to read plugin dir"));
    }

    #[test]
    fn register_wasm_dir_is_case_insensitive_on_extension() {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(dir.path().join("upper.WASM"), valid_plugin_wasm()).unwrap();
        std::fs::write(dir.path().join("mixed.Wasm"), valid_plugin_wasm()).unwrap();

        let mut manager = PluginManager::new();
        let report = manager
            .register_wasm_dir(dir.path())
            .expect("scan succeeds");
        assert_eq!(report.loaded.len(), 2, "both case variants should load");
        assert!(report.failures.is_empty());
    }
}
