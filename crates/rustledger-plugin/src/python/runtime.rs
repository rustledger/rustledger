//! CPython-WASI runtime for Python plugin execution.
//!
//! This module provides the runtime for executing Python beancount plugins
//! in a sandboxed WASM environment using `CPython` compiled to WASI.

use super::PythonError;
use super::compat::BEANCOUNT_COMPAT_PY;
use super::download;
use crate::sandbox::MemoryLimiter;
use crate::types::{PluginError, PluginErrorSeverity, PluginInput, PluginOutput};
use anyhow::Result;
use std::sync::Arc;
use wasmtime::{Config, Engine, Linker, Module, Store};
use wasmtime_wasi::p1;
use wasmtime_wasi::{DirPerms, FilePerms, WasiCtxBuilder};

/// Per-instance linear-memory cap for the Python plugin runtime.
///
/// Aliases [`sandbox::DEFAULT_SANDBOX_MAX_MEMORY`] so this path, the
/// regular WASM-plugin path
/// ([`crate::runtime::RuntimeConfig::default`]), and the WASM
/// importer host all share a single source of truth. `CPython`
/// compiled to WASI is memory-hungry on import and AST compilation;
/// the 256 MiB shared default is generous enough for that workload
/// while small enough to block allocation-spin `DoS` against
/// memory-constrained hosts (issue #1234). Without this cap a single
/// hostile call could allocate up to 4 GiB (the wasm32 linear-memory
/// ceiling), enough to OOM many hosts.
///
/// This value caps **linear memory only**. Tables are capped
/// separately via [`sandbox::MAX_TABLE_ELEMENTS`] (1M ref-typed
/// slots, ~8 MiB worst case), wired into the same `MemoryLimiter`'s
/// [`ResourceLimiter::table_growing`] impl. wasmtime accounts memory
/// and tables as separate resource classes; without the secondary
/// `MAX_TABLE_ELEMENTS` cap, `table.grow` would bypass the
/// `max_memory` ceiling entirely.
///
/// [`sandbox::DEFAULT_SANDBOX_MAX_MEMORY`]: crate::sandbox::DEFAULT_SANDBOX_MAX_MEMORY
/// [`sandbox::MAX_TABLE_ELEMENTS`]: crate::sandbox::MAX_TABLE_ELEMENTS
/// [`ResourceLimiter::table_growing`]: wasmtime::ResourceLimiter::table_growing
const PYTHON_MAX_MEMORY: usize = crate::sandbox::DEFAULT_SANDBOX_MAX_MEMORY;

/// Per-call fuel budget for the Python plugin runtime.
///
/// Roughly "~10 minutes of `CPython` at 1M instructions/second on the
/// reference fixtures". Fuel exhaustion surfaces as a wasmtime trap
/// that the caller in `execute_plugin` translates into a
/// `PythonError::Execution` (the existing error path).
///
/// # Why this isn't [`sandbox::DEFAULT_SANDBOX_MAX_TIME_SECS`]
///
/// The shared sandbox default is 30 seconds (= 30M fuel via the 1M-
/// fuel-per-second convention used by [`sandbox::make_sandboxed_store`]).
/// `CPython` compiled to WASI runs as an interpreter that emits many
/// wasm instructions per Python-source operation, so the same
/// wall-clock budget needs ~10-100x more wasmtime fuel for a Python
/// workload than for equivalent native wasm. Reusing the shared
/// 30-second default would leave Python plugins fuel-starved before
/// `CPython` finished its own startup. The opt-out is principled:
/// interpreter overhead is a structural property of
/// `CPython`-on-wasm, not a budget choice.
///
/// Kept as a module-level `const` rather than a free-floating literal
/// inside [`PythonRuntime::execute_plugin`] so the value is grep-
/// discoverable next to [`PYTHON_MAX_MEMORY`].
///
/// [`sandbox::DEFAULT_SANDBOX_MAX_TIME_SECS`]: crate::sandbox::DEFAULT_SANDBOX_MAX_TIME_SECS
/// [`sandbox::make_sandboxed_store`]: crate::sandbox::make_sandboxed_store
const PYTHON_FUEL: u64 = 600_000_000;

/// Store state for the Python plugin runtime.
///
/// Wraps the WASI preview1 context alongside the [`MemoryLimiter`]
/// that caps `memory.grow` and `table.grow` at [`PYTHON_MAX_MEMORY`].
/// Pre-#1234 the runtime stored the raw `p1::WasiP1Ctx` and installed
/// no limiter, so a buggy or hostile Python plugin could allocate up
/// to 4 GiB per call (the wasm32 linear-memory ceiling, a spec
/// constant), enough to OOM a memory-constrained host. The fuel cap
/// blocked CPU-spin attacks but not allocation-spin attacks
/// (`memory.grow` consumes negligible fuel per allocated page). This
/// struct is the parity counterpart of
/// `rustledger_plugin::sandbox::StoreState` for the WASI-based runtime
/// path.
///
/// The WASI linker that runs on top of this store reaches into
/// `state.wasi` through the closure passed to
/// [`p1::add_to_linker_sync`]; the `Store::limiter` closure reaches
/// into `state.limiter`. The two access paths don't collide because
/// each subsystem holds its own `&mut` to a disjoint field.
struct PythonStoreState {
    wasi: p1::WasiP1Ctx,
    limiter: MemoryLimiter,
}

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

        let engine = Arc::new(Engine::new(&engine_config()).map_err(PythonError::Wasm)?);

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
sys.path.insert(0, '/work')

# Load compatibility layer (defines types like ValidationError, Transaction, etc.)
exec(open('/work/compat.py').read())

# Load plugin code in same namespace so it has access to compat types
exec(open('/work/plugin.py').read())

# Input data
entries_json = '''{entries_json}'''
options_json = '''{options_json}'''

# Run the plugin
config = {config_arg}
entries_out, errors_out = run_plugin({plugin_func}, entries_json, options_json, config)

# Write output to file
with open('/work/output.json', 'w') as f:
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

        // Parse output (pass input length so the Python bridge can
        // encode the opaque rebuild as `Delete(all-input) + Insert(all-output)`).
        parse_plugin_output(&output, input.directives.len())
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

    /// Execute a Python plugin by module name.
    ///
    /// This method discovers the module on the host filesystem (using the host
    /// Python interpreter), reads its source code, and executes it in the WASI
    /// sandbox.
    ///
    /// # Arguments
    ///
    /// * `module_name` - Python module path (e.g., `"my_plugin"` or `"my_package.plugin"`)
    /// * `input` - Plugin input with directives
    /// * `beancount_dir` - Directory containing the beancount file (for relative imports)
    ///
    /// # Errors
    ///
    /// Returns `PythonError::ModuleNotFound` if the module cannot be located.
    /// Returns `PythonError::CExtensionNotSupported` if the module is a C extension.
    pub fn execute_module(
        &self,
        module_name: &str,
        input: &PluginInput,
        beancount_dir: Option<&std::path::Path>,
    ) -> Result<PluginOutput, PythonError> {
        // Discover and read the module source
        let source = discover_module_source(module_name, beancount_dir)?;

        // Execute the plugin using the discovered source
        self.execute_plugin(&source, "plugin", input)
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

        // Map the python-wasi directory as "/" (root) so Python can find /lib
        // This is critical - Python needs absolute paths for PYTHONHOME/PYTHONPATH
        wasi_builder
            .preopened_dir(python_root, "/", DirPerms::READ, FilePerms::READ)
            .map_err(PythonError::Wasm)?;

        // Set up work directory for script and output (read-write)
        wasi_builder
            .preopened_dir(work_dir.path(), "/work", DirPerms::all(), FilePerms::all())
            .map_err(PythonError::Wasm)?;

        // Set environment for Python - use absolute paths from guest perspective
        wasi_builder
            .env("PYTHONHOME", "/")
            .env("PYTHONPATH", "/lib")
            .env("PYTHONDONTWRITEBYTECODE", "1")
            // Set args: python /work/script.py
            .args(&["python", "/work/script.py"]);

        let wasi_ctx = wasi_builder.build_p1();

        // Construct the sandboxed Store via the helper so production
        // and the `make_sandboxed_python_store_caps_memory_growth_via_wasmtime`
        // regression test exercise the same wiring (issue #1234).
        let mut store =
            make_sandboxed_python_store(&self.engine, wasi_ctx).map_err(PythonError::Wasm)?;

        // Create linker and add WASI. The closure reaches through the
        // state wrapper to the inner `p1::WasiP1Ctx` that the WASI
        // syscall implementations expect.
        let mut linker: Linker<PythonStoreState> = Linker::new(&self.engine);
        p1::add_to_linker_sync(&mut linker, |state| &mut state.wasi).map_err(PythonError::Wasm)?;

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

/// Build a `Store<PythonStoreState>` pre-wired with the runtime's
/// resource caps:
///
/// - `Store::limiter` is set so wasmtime's `memory.grow` and
///   `table.grow` checks call back into [`MemoryLimiter`] with the
///   `PYTHON_MAX_MEMORY` ceiling (issue #1234).
/// - `set_fuel(PYTHON_FUEL)` caps per-call CPU consumption.
///
/// Extracted so the production path in
/// [`PythonRuntime::run_python`] and the
/// `make_sandboxed_python_store_caps_memory_growth_via_wasmtime`
/// regression test exercise the SAME wiring. Without a single helper
/// the test could only verify `MemoryLimiter` logic in isolation
/// (which `rustledger_plugin::sandbox` already covers), not the
/// wasmtime-side hookup, so a refactor that accidentally dropped the
/// `store.limiter(...)` call would pass the previous test.
///
/// # Errors
///
/// Returns `wasmtime::Error` if `set_fuel` fails — only when the
/// engine was configured without `consume_fuel(true)`, which
/// [`engine_config`] always sets. The `Result` is defensive: a future
/// refactor flipping the flag surfaces the error rather than silently
/// producing an unmetered Store.
fn make_sandboxed_python_store(
    engine: &Engine,
    wasi: p1::WasiP1Ctx,
) -> wasmtime::Result<Store<PythonStoreState>> {
    let mut store = Store::new(
        engine,
        PythonStoreState {
            wasi,
            limiter: MemoryLimiter::new(PYTHON_MAX_MEMORY),
        },
    );
    store.limiter(|state| &mut state.limiter);
    store.set_fuel(PYTHON_FUEL)?;
    Ok(store)
}

/// Build the wasmtime [`Config`] used for the Python plugin engine.
///
/// Python needs a larger stack for compiling/importing modules: the default
/// `max_wasm_stack` of 512 KiB is too small for `CPython`'s recursive AST
/// visitor, so this raises it to 16 MiB.
///
/// When the `async` feature is compiled in (which it is: `wasmtime`'s
/// `default` feature set includes "async", and the workspace depends on
/// `wasmtime` with default features enabled), wasmtime enforces
/// `max_wasm_stack <= async_stack_size` at [`Engine::new`] time, and the
/// default `async_stack_size` of 2 MiB is smaller than our 16 MiB wasm
/// stack. Without bumping it, engine creation fails with
/// `"max_wasm_stack size cannot exceed the async_stack_size"`.
///
/// `ASYNC_STACK_HEADROOM` is the stack space reserved for host frames
/// running on the async stack: wasmtime's docs state "the amount of stack
/// space guaranteed for host functions is `async_stack_size - max_wasm_stack`,
/// so take care not to set these two values close to one another". We
/// pick 2 MiB to match the stock default difference (default
/// `async_stack_size` 2 MiB minus default `max_wasm_stack` 512 KiB gives
/// ~1.5 MiB of host headroom; rounding up to 2 MiB is comfortable). The
/// Python runtime here is sync-only (it uses [`wasmtime_wasi::p1`], no
/// `.await`), so the async stack is never actually allocated at runtime;
/// this value purely satisfies wasmtime's config validator.
fn engine_config() -> Config {
    const WASM_STACK: usize = 16 * 1024 * 1024;
    const ASYNC_STACK_HEADROOM: usize = 2 * 1024 * 1024;

    let mut config = Config::new();
    config.consume_fuel(true);
    config.max_wasm_stack(WASM_STACK);
    config.async_stack_size(WASM_STACK + ASYNC_STACK_HEADROOM);

    // Apply the full WASM-proposal disable set the regular WASM-plugin
    // path uses, via the shared helper in `sandbox`. Today this is
    // defense-in-depth: the wasm module we execute here is fixed
    // (downloaded `CPython`-WASI, pinned by `download::ensure_runtime`)
    // so the untrusted code runs INSIDE CPython, not as raw wasm. But
    // sharing the disable list with `sandbox_config` means a wasmtime
    // bump that lands a new proposal default-on is caught in ONE place
    // for both paths (per `apply_proposal_disables`'s rustdoc).
    crate::sandbox::apply_proposal_disables(&mut config);

    config
}

/// Discover and read a Python plugin's source code.
///
/// For file-based plugins (`.py` files or paths), reads the file directly.
/// For module-based plugins, returns `ModuleNotFound` error - the caller should
/// use `suggest_module_path()` to provide a helpful hint to the user.
///
/// This intentionally does NOT auto-discover module sources via system Python.
/// We want users to explicitly specify file paths so we can track which plugins
/// need native Rust implementations.
fn discover_module_source(
    module_name: &str,
    beancount_dir: Option<&std::path::Path>,
) -> Result<String, PythonError> {
    use std::path::PathBuf;

    // Handle file-based plugins first
    let is_py_file = std::path::Path::new(module_name)
        .extension()
        .is_some_and(|ext| ext.eq_ignore_ascii_case("py"));
    if is_py_file || module_name.contains(std::path::MAIN_SEPARATOR) {
        let path = if let Some(dir) = beancount_dir {
            dir.join(module_name)
        } else {
            PathBuf::from(module_name)
        };

        if !path.exists() {
            return Err(PythonError::ModuleNotFound(module_name.to_string()));
        }

        return std::fs::read_to_string(&path).map_err(PythonError::Io);
    }

    // Module-based plugins require explicit file paths
    Err(PythonError::ModuleNotFound(module_name.to_string()))
}

/// Try to locate a Python module's file path using the system Python.
///
/// This is used to provide helpful error messages suggesting the user
/// replace module-based plugin references with explicit file paths.
///
/// Returns `Some(path)` if the module was found, `None` otherwise.
pub fn suggest_module_path(module_name: &str) -> Option<String> {
    use std::process::Command;

    let output = Command::new("python3")
        .args([
            "-c",
            r"import sys, importlib.util
spec = importlib.util.find_spec(sys.argv[1])
print(spec.origin if spec and spec.origin and spec.origin.endswith('.py') else '')",
            module_name,
        ])
        .output()
        .ok()?;

    if !output.status.success() {
        return None;
    }

    let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
    if path.is_empty() { None } else { Some(path) }
}

/// Check if Python 3 is available on the system.
pub fn is_python_available() -> bool {
    std::process::Command::new("python3")
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success())
}

/// Serialize directives to JSON for Python consumption.
fn serialize_directives_to_json(
    directives: &[crate::types::DirectiveWrapper],
) -> Result<String, PythonError> {
    serde_json::to_string(directives).map_err(|e| PythonError::Serialization(e.to_string()))
}

/// Parse the plugin output from the output file.
///
/// `input_len` is the length of the **plugin's** input directive list;
/// the Python plugin returns a full replacement list (opaque to us),
/// so we encode the result as a rebuild: `Delete(0..input_len)`
/// followed by `Insert(...)` for every directive Python returned. This
/// satisfies the ops protocol invariant (each input index appears
/// exactly once) without forcing the Python bridge to track which
/// input indices it preserved.
fn parse_plugin_output(output: &str, input_len: usize) -> Result<PluginOutput, PythonError> {
    use crate::types::PluginOp;

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

    let mut ops: Vec<PluginOp> = (0..input_len).map(PluginOp::Delete).collect();
    for w in directives {
        ops.push(PluginOp::Insert(w));
    }

    Ok(PluginOutput { ops, errors })
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

    /// Regression test: `engine_config` must produce a `Config` that satisfies
    /// wasmtime's `max_wasm_stack <= async_stack_size` constraint.
    /// Removing the `async_stack_size` call (or bumping `max_wasm_stack` past
    /// it) would cause `Engine::new` to fail with
    /// `"max_wasm_stack size cannot exceed the async_stack_size"` on every
    /// `PythonRuntime::new()` call.
    #[test]
    fn test_engine_config_satisfies_async_stack_constraint() {
        Engine::new(&engine_config())
            .expect("engine_config must satisfy wasmtime stack constraints");
    }

    /// End-to-end regression for issue #1234: build a real
    /// `Store<PythonStoreState>` via [`make_sandboxed_python_store`],
    /// instantiate a synthetic wasm module that calls `memory.grow`
    /// past the cap, and assert wasmtime reports growth failure (the
    /// `-1` sentinel `memory.grow` returns when the limiter denies the
    /// request). This pins the WIRING between `Store::limiter` and
    /// `MemoryLimiter::memory_growing`, not just the limiter's logic
    /// in isolation (`rustledger_plugin::sandbox` already covers
    /// that). A future refactor that drops the `store.limiter(...)`
    /// line in [`make_sandboxed_python_store`] makes this test fail.
    ///
    /// Pre-#1234 the runtime created the `Store` with a raw
    /// `p1::WasiP1Ctx` and no limiter. The wasm32 linear-memory
    /// ceiling is 4 GiB per `Store` (a spec constant, not policy), so
    /// a single hostile call without our cap could allocate up to
    /// 4 GiB — enough to OOM a memory-constrained host (Docker
    /// container, CI runner). The fuel cap blocked CPU-spin attacks
    /// but not allocation-spin attacks (`memory.grow` consumes
    /// negligible fuel per allocated page).
    ///
    /// We don't instantiate `CPython` here, that pulls the 50+ MiB
    /// runtime download into the test. A 1-page synthetic module is
    /// enough to exercise wasmtime's limiter callback.
    #[test]
    fn make_sandboxed_python_store_caps_memory_growth_via_wasmtime() {
        let engine =
            Engine::new(&engine_config()).expect("engine_config must build a valid Engine");
        let wasi = WasiCtxBuilder::new().build_p1();
        let mut store =
            make_sandboxed_python_store(&engine, wasi).expect("store construction must succeed");

        // `PYTHON_MAX_MEMORY = 256 MiB = 4096 pages` (1 wasm page = 64 KiB).
        // Initial memory is 1 page; request grow by 5000 pages, which
        // would land at 5001 pages = ~328 MiB, past the cap. wasmtime
        // calls `MemoryLimiter::memory_growing` with the desired byte
        // count, the limiter returns `Ok(false)`, and `memory.grow`
        // surfaces `-1` to the wasm caller.
        // Minimal module: 1 page of memory (no export needed; the
        // test never reads it through the host) and a function the
        // test calls. memory.grow defaults to memory 0 when no
        // explicit memidx is given.
        let wat = r#"
            (module
                (memory 1)
                (func (export "try_grow_past_cap") (result i32)
                    i32.const 5000
                    memory.grow))
        "#;
        let module = Module::new(&engine, wat).expect("synthetic wat module must compile");
        let linker = Linker::<PythonStoreState>::new(&engine);
        let instance = linker
            .instantiate(&mut store, &module)
            .expect("instantiation must succeed under the cap");
        let try_grow = instance
            .get_typed_func::<(), i32>(&mut store, "try_grow_past_cap")
            .expect("export must exist");

        let result = try_grow.call(&mut store, ()).expect("call must not trap");
        assert_eq!(
            result, -1,
            "memory.grow past PYTHON_MAX_MEMORY must return -1 (growth rejected). \
             If this fails, the limiter is not wired into the Store — most likely \
             the `store.limiter(|state| &mut state.limiter)` call was removed from \
             `make_sandboxed_python_store`."
        );
    }

    // Pre-architectural-refactor this module had a
    // `python_max_memory_matches_plugin_config_default_cap` test that
    // asserted `PYTHON_MAX_MEMORY == RuntimeConfig::default().max_memory`.
    // Both expressions now reduce to
    // `crate::sandbox::DEFAULT_PLUGIN_MAX_MEMORY` at compile time, so
    // the drift the test was guarding against is unrepresentable. The
    // type system enforces what the runtime assertion used to.

    /// Pin `PYTHON_FUEL` at its documented "~10 minutes of `CPython` at
    /// 1M instructions/second" budget. Hoisted from an inline literal
    /// in #1234; this test makes a future change to the value a
    /// conscious edit. Doesn't pin the wasmtime-side wiring (that's
    /// covered by `make_sandboxed_python_store_caps_memory_growth_via_wasmtime`,
    /// which constructs the store via the helper that sets fuel).
    #[test]
    fn python_fuel_pins_documented_budget() {
        assert_eq!(
            PYTHON_FUEL, 600_000_000,
            "PYTHON_FUEL changed without updating the rustdoc; bumping the budget \
             should also update the \"~10 minutes at 1M instructions/sec\" doc claim."
        );
    }

    #[test]
    fn test_parse_plugin_output() {
        let output = "[]\n---SEPARATOR---\n[]";
        let result = parse_plugin_output(output, 0).unwrap();
        assert!(result.ops.is_empty());
        assert!(result.errors.is_empty());
    }

    #[test]
    fn test_is_python_available() {
        // Just ensure this doesn't panic and returns a bool
        let _available = is_python_available();
    }

    #[test]
    fn test_discover_module_source_file_not_found() {
        let result = discover_module_source("nonexistent.py", None);
        assert!(matches!(result, Err(PythonError::ModuleNotFound(_))));
    }

    #[test]
    fn test_discover_module_source_module_based() {
        // Module-based plugins should return ModuleNotFound
        let result = discover_module_source("beancount.plugins.check_commodity", None);
        assert!(matches!(result, Err(PythonError::ModuleNotFound(_))));
    }

    #[test]
    fn test_discover_module_source_reads_file() {
        use std::io::Write;

        // Create a temp file
        let temp_dir = tempfile::tempdir().unwrap();
        let plugin_path = temp_dir.path().join("test_plugin.py");
        let mut file = std::fs::File::create(&plugin_path).unwrap();
        writeln!(file, "def plugin(entries, options): return entries, []").unwrap();

        // Test reading with absolute path
        let result = discover_module_source(plugin_path.to_str().unwrap(), None);
        assert!(result.is_ok());
        assert!(result.unwrap().contains("def plugin"));
    }

    #[test]
    fn test_discover_module_source_relative_to_beancount_dir() {
        use std::io::Write;

        // Create a temp file
        let temp_dir = tempfile::tempdir().unwrap();
        let plugin_path = temp_dir.path().join("my_plugin.py");
        let mut file = std::fs::File::create(&plugin_path).unwrap();
        writeln!(file, "# my plugin").unwrap();

        // Test reading relative to beancount_dir
        let result = discover_module_source("my_plugin.py", Some(temp_dir.path()));
        assert!(result.is_ok());
        assert!(result.unwrap().contains("# my plugin"));
    }

    #[test]
    fn test_suggest_module_path_returns_option() {
        // Test with a module that likely doesn't exist
        let result = suggest_module_path("nonexistent_module_xyz123");
        assert!(result.is_none());
    }

    #[test]
    fn test_suggest_module_path_finds_known_module() {
        if !is_python_available() {
            return; // Skip if Python not available
        }

        // 'os' is a standard library module that should exist
        let result = suggest_module_path("os");
        // os.py should be found on most systems
        if let Some(path) = result {
            let has_py_ext = std::path::Path::new(&path)
                .extension()
                .is_some_and(|ext| ext.eq_ignore_ascii_case("py"));
            assert!(has_py_ext || path.contains("os"));
        }
    }
}
