//! CPython-WASI runtime for Python plugin execution.
//!
//! This module provides the runtime for executing Python beancount plugins
//! in a sandboxed WASM environment using `CPython` compiled to WASI.

use super::compat::BEANCOUNT_COMPAT_PY;
use super::download;
use super::PythonError;
use crate::types::{PluginError, PluginErrorSeverity, PluginInput, PluginOutput};
use anyhow::Result;
use std::sync::Arc;
use wasmtime::{Config, Engine, Linker, Module, Store};
use wasmtime_wasi::p1;
use wasmtime_wasi::{DirPerms, FilePerms, WasiCtxBuilder};

/// Python plugin runtime.
///
/// This runtime uses `CPython` compiled to WASI to execute Python beancount
/// plugins. The Python runtime is downloaded on first use.
pub struct PythonRuntime {
    engine: Arc<Engine>,
    module: Module,
    stdlib_path: std::path::PathBuf,
}

impl PythonRuntime {
    /// Create a new Python runtime.
    ///
    /// This will download the CPython-WASI runtime if not already cached.
    pub fn new() -> Result<Self, PythonError> {
        Self::with_options(false)
    }

    /// Create a new Python runtime with options.
    ///
    /// # Arguments
    ///
    /// * `quiet_warning` - If true, suppress the performance warning message.
    #[allow(unsafe_code)] // Module::deserialize is unsafe but we load our own compiled code
    pub fn with_options(quiet_warning: bool) -> Result<Self, PythonError> {
        if !quiet_warning {
            eprintln!("⚠️  Loading Python plugin runtime...");
            eprintln!("⚠️  Python plugins are 10-100x slower than native Rust plugins.");
            eprintln!("⚠️  Consider migrating to native Rust plugins for better performance.");
            eprintln!();
        }

        // Ensure the Python runtime is downloaded
        let python_wasm = download::ensure_runtime()?;
        let stdlib_path = download::python_stdlib_path()?;

        // Create engine with fuel for execution limits
        let mut config = Config::new();
        config.consume_fuel(true);
        let engine = Arc::new(Engine::new(&config).map_err(PythonError::Wasm)?);

        // Try to load precompiled module from cache, or compile and cache it
        let cache_path = python_wasm.with_extension("cwasm");
        let module = if cache_path.exists() {
            // Load precompiled module (fast)
            // SAFETY: We compiled this module ourselves with the same engine config
            unsafe { Module::deserialize_file(&engine, &cache_path).map_err(PythonError::Wasm)? }
        } else {
            // First run: compile and cache
            eprintln!("⚠️  Compiling Python WASM module (first run only, ~30 seconds)...");
            let module = Module::from_file(&engine, &python_wasm).map_err(PythonError::Wasm)?;

            // Cache the compiled module for next time
            if let Ok(bytes) = module.serialize() {
                let _ = std::fs::write(&cache_path, bytes);
            }
            module
        };

        Ok(Self {
            engine,
            module,
            stdlib_path,
        })
    }

    /// Execute a Python plugin.
    ///
    /// # Arguments
    ///
    /// * `plugin_code` - Python code containing the plugin function
    /// * `plugin_func` - Name of the plugin function to call
    /// * `input` - Plugin input with directives and options
    ///
    /// # Returns
    ///
    /// Returns the plugin output with modified directives and any errors.
    pub fn execute_plugin(
        &self,
        plugin_code: &str,
        plugin_func: &str,
        input: &PluginInput,
    ) -> Result<PluginOutput, PythonError> {
        // Serialize input to JSON
        let directives_json = serialize_directives_to_json(&input.directives)?;
        let options_json = serde_json::to_string(&input.options)
            .map_err(|e| PythonError::Serialization(e.to_string()))?;

        let config_arg = input.config.as_ref().map_or_else(
            || "None".to_string(),
            |c| format!("'{}'", c.replace('\'', "\\'")),
        );

        // Build the main Python script
        // Note: We exec() the plugin code in the same namespace as compat
        // so that types like ValidationError, Transaction, etc. are available
        let script = format!(
            r"
import sys
sys.path.insert(0, 'work')

# Load compatibility layer (defines types like ValidationError, Transaction, etc.)
exec(open('work/compat.py').read())

# Load plugin code in same namespace so it has access to compat types
exec(open('work/plugin.py').read())

# Input data
entries_json = '''{entries_json}'''
options_json = '''{options_json}'''

# Run the plugin
config = {config_arg}
entries_out, errors_out = run_plugin({plugin_func}, entries_json, options_json, config)

# Write output to file
with open('work/output.json', 'w') as f:
    f.write(entries_out)
    f.write('\n---SEPARATOR---\n')
    f.write(errors_out)
",
            entries_json = directives_json.replace('\'', "\\'"),
            options_json = options_json.replace('\'', "\\'"),
            plugin_func = plugin_func,
            config_arg = config_arg,
        );

        // Execute Python
        let output = self.run_python(&script, BEANCOUNT_COMPAT_PY, plugin_code)?;

        // Parse output
        parse_plugin_output(&output)
    }

    /// Execute a built-in beancount plugin by module name.
    ///
    /// # Arguments
    ///
    /// * `module_name` - The module name (e.g., "`beancount.plugins.check_commodity`")
    /// * `input` - Plugin input
    pub fn execute_builtin(
        &self,
        module_name: &str,
        input: &PluginInput,
    ) -> Result<PluginOutput, PythonError> {
        // Check if this is one of our implemented built-in plugins
        let plugin_code = match module_name {
            "beancount.plugins.check_commodity" | "check_commodity" => CHECK_COMMODITY_PLUGIN,
            "beancount.plugins.leafonly" | "leafonly" => LEAFONLY_PLUGIN,
            _ => {
                return Err(PythonError::Execution(format!(
                    "built-in plugin '{module_name}' is not available in Python WASI mode. \
                     Use rustledger's native implementation instead."
                )));
            }
        };

        self.execute_plugin(plugin_code, "plugin", input)
    }

    /// Run a Python script and return output via file.
    fn run_python(
        &self,
        script: &str,
        compat_code: &str,
        plugin_code: &str,
    ) -> Result<String, PythonError> {
        // Create a work directory for script and output
        let work_dir = tempfile::tempdir().map_err(PythonError::Io)?;

        // Write the compatibility layer to a file
        let compat_path = work_dir.path().join("compat.py");
        std::fs::write(&compat_path, compat_code)?;

        // Write the user plugin to a file
        let plugin_path = work_dir.path().join("plugin.py");
        std::fs::write(&plugin_path, plugin_code)?;

        // Write the main script to a file
        let script_path = work_dir.path().join("script.py");
        std::fs::write(&script_path, script)?;

        // Build WASI context
        let mut wasi_builder = WasiCtxBuilder::new();

        // Inherit stderr for error messages
        wasi_builder.inherit_stderr();

        // Get the python-wasi root directory (parent of lib)
        let python_root = self.stdlib_path.parent().unwrap_or(&self.stdlib_path);

        // Map the python-wasi directory as "." so Python can find ./lib
        wasi_builder
            .preopened_dir(python_root, ".", DirPerms::READ, FilePerms::READ)
            .map_err(|e: anyhow::Error| PythonError::Wasm(e))?;

        // Set up work directory for script and output (read-write)
        wasi_builder
            .preopened_dir(work_dir.path(), "work", DirPerms::all(), FilePerms::all())
            .map_err(|e: anyhow::Error| PythonError::Wasm(e))?;

        // Set environment for Python - use relative paths
        wasi_builder
            .env("PYTHONHOME", ".")
            .env("PYTHONPATH", "./lib")
            .env("PYTHONDONTWRITEBYTECODE", "1")
            // Set args: python work/script.py (no leading ./)
            .args(&["python", "work/script.py"]);

        let wasi_ctx = wasi_builder.build_p1();

        // Create store with fuel limit (10 minutes worth)
        let mut store: Store<p1::WasiP1Ctx> = Store::new(&self.engine, wasi_ctx);
        store.set_fuel(600_000_000).map_err(PythonError::Wasm)?;

        // Create linker and add WASI
        let mut linker: Linker<p1::WasiP1Ctx> = Linker::new(&self.engine);
        p1::add_to_linker_sync(&mut linker, |ctx| ctx)
            .map_err(|e: anyhow::Error| PythonError::Wasm(e))?;

        // Instantiate and run
        let instance = linker
            .instantiate(&mut store, &self.module)
            .map_err(PythonError::Wasm)?;

        // Get the _start function (WASI entry point)
        let start = instance
            .get_typed_func::<(), ()>(&mut store, "_start")
            .map_err(PythonError::Wasm)?;

        // Run Python
        start
            .call(&mut store, ())
            .map_err(|e| PythonError::Execution(format!("Python execution failed: {e}")))?;

        // Read output from file
        let output_path = work_dir.path().join("output.json");
        std::fs::read_to_string(&output_path).map_err(|e| {
            PythonError::Execution(format!(
                "failed to read Python output: {e}. The plugin may have crashed."
            ))
        })
    }
}

/// Serialize directives to JSON for Python consumption.
fn serialize_directives_to_json(
    directives: &[crate::types::DirectiveWrapper],
) -> Result<String, PythonError> {
    serde_json::to_string(directives).map_err(|e| PythonError::Serialization(e.to_string()))
}

/// Parse the plugin output from the output file.
fn parse_plugin_output(output: &str) -> Result<PluginOutput, PythonError> {
    let separator = "---SEPARATOR---";
    let parts: Vec<&str> = output.split(separator).collect();

    if parts.len() < 2 {
        return Err(PythonError::Execution(format!(
            "unexpected output format from Python plugin: {output}"
        )));
    }

    let entries_json = parts[0].trim();
    let errors_json = parts[1].trim();

    // Parse directives
    let directives: Vec<crate::types::DirectiveWrapper> = serde_json::from_str(entries_json)
        .map_err(|e| PythonError::Serialization(format!("failed to parse entries: {e}")))?;

    // Parse errors
    let json_errors: Vec<serde_json::Value> = serde_json::from_str(errors_json)
        .map_err(|e| PythonError::Serialization(format!("failed to parse errors: {e}")))?;

    let errors: Vec<PluginError> = json_errors
        .into_iter()
        .filter_map(|v| {
            let message = v.get("message")?.as_str()?.to_string();
            Some(PluginError {
                message,
                severity: PluginErrorSeverity::Error,
                source_file: v
                    .get("source_file")
                    .and_then(|v| v.as_str())
                    .map(String::from),
                line_number: v
                    .get("line_number")
                    .and_then(serde_json::Value::as_u64)
                    .map(|n| n as u32),
            })
        })
        .collect();

    Ok(PluginOutput { directives, errors })
}

// =============================================================================
// Built-in plugin implementations
// =============================================================================

/// Python implementation of `check_commodity` plugin.
const CHECK_COMMODITY_PLUGIN: &str = r#"
def plugin(entries, options_map, config=None):
    """Check that all used commodities are declared."""
    errors = []
    declared = set()

    # Collect declared commodities
    for entry in entries:
        if isinstance(entry, Commodity):
            declared.add(entry.currency)
        elif isinstance(entry, Open):
            if entry.currencies:
                declared.update(entry.currencies)

    # Check all used commodities
    for entry in entries:
        if isinstance(entry, Transaction):
            for posting in entry.postings:
                if posting.units and posting.units.currency:
                    if posting.units.currency not in declared:
                        errors.append(ValidationError(
                            entry.meta,
                            f"Commodity '{posting.units.currency}' is not declared",
                            entry
                        ))
                if posting.cost and posting.cost.currency:
                    if posting.cost.currency not in declared:
                        errors.append(ValidationError(
                            entry.meta,
                            f"Commodity '{posting.cost.currency}' is not declared",
                            entry
                        ))
        elif isinstance(entry, Balance):
            if entry.amount and entry.amount.currency:
                if entry.amount.currency not in declared:
                    errors.append(ValidationError(
                        entry.meta,
                        f"Commodity '{entry.amount.currency}' is not declared",
                        entry
                    ))
        elif isinstance(entry, Price):
            if entry.currency and entry.currency not in declared:
                errors.append(ValidationError(
                    entry.meta,
                    f"Commodity '{entry.currency}' is not declared",
                    entry
                ))
            if entry.amount and entry.amount.currency:
                if entry.amount.currency not in declared:
                    errors.append(ValidationError(
                        entry.meta,
                        f"Commodity '{entry.amount.currency}' is not declared",
                        entry
                    ))

    return entries, errors
"#;

/// Python implementation of leafonly plugin.
const LEAFONLY_PLUGIN: &str = r#"
def plugin(entries, options_map, config=None):
    """Check that postings only occur on leaf accounts."""
    errors = []

    # Build account tree
    account_children = {}
    for entry in entries:
        if isinstance(entry, Open):
            parts = entry.account.split(':')
            for i in range(len(parts)):
                parent = ':'.join(parts[:i+1])
                child = ':'.join(parts[:i+2]) if i+1 < len(parts) else None
                if parent not in account_children:
                    account_children[parent] = set()
                if child:
                    account_children[parent].add(child)

    # Check postings
    for entry in entries:
        if isinstance(entry, Transaction):
            for posting in entry.postings:
                if posting.account in account_children and account_children[posting.account]:
                    errors.append(ValidationError(
                        entry.meta,
                        f"Posting to non-leaf account '{posting.account}'",
                        entry
                    ))

    return entries, errors
"#;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_built_in_plugins_exist() {
        assert!(!CHECK_COMMODITY_PLUGIN.is_empty());
        assert!(!LEAFONLY_PLUGIN.is_empty());
    }

    #[test]
    fn test_parse_plugin_output() {
        let output = "[]\n---SEPARATOR---\n[]";
        let result = parse_plugin_output(output).unwrap();
        assert!(result.directives.is_empty());
        assert!(result.errors.is_empty());
    }
}
