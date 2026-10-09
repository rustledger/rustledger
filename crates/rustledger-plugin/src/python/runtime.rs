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
use wasmtime_wasi::p2::pipe::MemoryOutputPipe;
use wasmtime_wasi::{FsPerms, WasiCtxBuilder};

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

/// Fuel for one Python plugin call under a time budget of `max_time_secs`.
///
/// The same conversion as a WASM plugin's
/// ([`sandbox::fuel_for_secs`]), with no Python-specific multiplier,
/// because measurement does not call for one (#2500). Fuel counts wasm
/// operators, and `CPython` compiled to WASI is wasm; measured on an
/// x86-64 host (debug `rledger`, whose dependencies wasmtime and
/// Cranelift are built at `opt-level = 3`), fuel per call is:
///
/// | Workload                                  | Fuel  | CPU time | Sandbox memory |
/// |-------------------------------------------|-------|----------|----------------|
/// | `CPython` startup + passthrough, 3 entries | 1.24G | 0.2 s    | 40 MiB         |
/// | passthrough, 5k transactions              | 3.99G | 0.8 s    | 40 MiB         |
/// | tag every transaction, 5k transactions    | 4.19G | 0.9 s    | 40 MiB         |
/// | passthrough, 20k transactions             | 12.2G | 3.3 s    | 50 MiB         |
/// | tag every transaction, 20k transactions   | 13.0G | 3.7 s    | 58 MiB         |
/// | passthrough, 100k transactions            | 56.7G | 16 s     | 162 MiB        |
/// | tag every transaction, 100k transactions  | 60.0G | 22 s     | 205 MiB        |
/// | passthrough, 200k transactions            | -     | -        | over the 256 MiB cap |
/// | 5M-iteration Python loop                  | 6.81G | 1.1 s    |                |
///
/// (CPU time is the whole `rledger check` process.) That is 3-6G fuel
/// per CPU-second, the range other wasm runs at, so
/// [`sandbox::FUEL_PER_SECOND`]'s conservative 1G keeps its promise
/// for Python too: a budget of N seconds stops the call within N
/// seconds. A multiplier would break that promise without being
/// needed: the default 30 seconds (30G) is 24x `CPython`'s startup and
/// covers a plugin over about 50k transactions (~0.55M fuel each, the
/// cost of moving them through JSON both ways). A larger ledger, or a
/// heavier plugin, needs the host to raise the budget
/// (`[plugins] max_time_secs`, `--plugin-max-time-secs`); the fuel-trap
/// message quotes [`transfer_secs_estimate`] so the user knows by how
/// much. Memory is the harder limit: every entry lives in the sandbox as
/// Python objects (~1.2 KB per transaction), so the 256 MiB cap holds
/// about 180k transactions, whatever the budget.
///
/// Startup costs ~1.2 budget-seconds on every call, so a budget of one
/// second cannot run a Python plugin at all. Before #2500 the budget
/// was a fixed 600M fuel, sized for an assumed 1M fuel per second:
/// half of what `CPython` needs to start, so no Python plugin ran.
///
/// [`sandbox::fuel_for_secs`]: crate::sandbox::fuel_for_secs
/// [`sandbox::FUEL_PER_SECOND`]: crate::sandbox::FUEL_PER_SECOND
const fn python_fuel(max_time_secs: u64) -> u64 {
    crate::sandbox::fuel_for_secs(max_time_secs)
}

/// Measured fuel to start `CPython` and run a passthrough plugin over a
/// tiny ledger (see [`python_fuel`]).
const STARTUP_FUEL: u64 = 1_240_000_000;

/// Measured fuel to move one transaction into Python and back (parse
/// its JSON line, build the namedtuples, write it out again; see
/// [`python_fuel`]), rounded up.
const TRANSFER_FUEL_PER_ENTRY: u64 = 600_000;

/// About how many budget-seconds a Python plugin over `entries` entries
/// spends before doing any work: startup plus moving the entries in and
/// out. A floor for the budget, quoted when a plugin runs out of time.
const fn transfer_secs_estimate(entries: usize) -> u64 {
    let fuel = STARTUP_FUEL.saturating_add(TRANSFER_FUEL_PER_ENTRY.saturating_mul(entries as u64));
    fuel.div_ceil(crate::sandbox::FUEL_PER_SECOND)
}

/// Cap on what a Python plugin's stdout (its result) may hold: twice the
/// input plus 64 MiB, room for a plugin that rewrites every entry and
/// inserts many more, while a plugin cannot use output to exhaust host
/// memory.
const fn output_cap(input_bytes: usize) -> usize {
    input_bytes.saturating_mul(2).saturating_add(64 << 20)
}

/// Cap on a Python plugin's stderr (tracebacks, its prints).
const STDERR_CAP: usize = 4 << 20;

/// Show the guest's stderr on the host's.
fn forward_guest_stderr(bytes: &[u8]) {
    use std::io::Write;
    if !bytes.is_empty() {
        // What the plugin printed, with its control characters escaped
        // (see `crate::untrusted`): it is the plugin's text on the
        // user's terminal.
        let text = String::from_utf8_lossy(bytes);
        let mut err = std::io::stderr().lock();
        let _ = err.write_all(crate::escape_untrusted_text(&text).as_bytes());
        if bytes.len() >= STDERR_CAP {
            let _ = writeln!(
                err,
                "\n(the Python plugin's stderr was cut off at {} MiB)",
                STDERR_CAP >> 20
            );
        }
        let _ = err.flush();
    }
}

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

/// Most WASI resources (open files and directories, streams) a Python
/// plugin may hold at once. Each open file is a host file descriptor, so
/// without a cap (wasmtime's default is a million) a plugin could exhaust
/// the host process's descriptor limit (it reached the 1024 `ulimit -n`
/// in #2500's second review), failing whatever else the host was doing.
/// `CPython` itself holds a handful while importing.
const MAX_GUEST_RESOURCES: usize = 256;

/// How often, in fuel, a running guest yields to the host, so the
/// wall-clock deadline in [`PythonRuntime::run_python`] can stop it
/// (about every few milliseconds of guest work).
const FUEL_YIELD_INTERVAL: u64 = 10_000_000;

/// The script `CPython` runs: load the compat layer, load the plugin file
/// as a module of its own, run it, and write the result.
///
/// Inputs arrive as files in `/work` (see [`PythonRuntime::execute`]), so
/// no value is ever spliced into Python source. The plugin module starts
/// with the compat layer's names (`Transaction`, `ValidationError`, ...)
/// already defined, as when plugin code was exec'd into the compat
/// namespace, but keeps its own namespace, so `__plugins__` and the
/// functions it names are looked up on the module, as beancount does.
const PLUGIN_SCRIPT: &str = r#"
import json
import sys
import types

sys.path.insert(0, '/work')

# The result goes to stdout; anything the plugin prints goes to stderr,
# so it cannot corrupt the result.
_result_out = sys.stdout
sys.stdout = sys.stderr

# Load compatibility layer (defines types like ValidationError, Transaction, etc.)
exec(open('/work/compat.py').read())

with open('/work/invocation.json') as f:
    _invocation = json.load(f)

_plugin_module = types.ModuleType(_invocation['module_name'])
_plugin_module.__dict__.update(
    {k: v for k, v in globals().items() if not (k.startswith('__') and k.endswith('__'))})
_plugin_module.__file__ = '/work/plugin.py'
with open('/work/plugin.py') as f:
    exec(compile(f.read(), '/work/plugin.py', 'exec'), _plugin_module.__dict__)

with open('/work/options.json') as f:
    _options_json = f.read()

entries_out, errors_out = run_plugin(
    _plugin_module,
    _invocation['plugin_name'],
    '/work/entries.jsonl',
    _options_json,
    _invocation['config'],
    _invocation['entry_points'],
)

# `None`: nothing ran, the input stands. The result line goes last: its
# presence tells the host the script finished.
if entries_out is not None:
    dump_entries(entries_out[0], _result_out, entries_out[1])
_result_out.write('{"ran": ' + ('false' if entries_out is None else 'true')
                  + ', "errors": ' + errors_out + '}\n')
_result_out.flush()
"#;

/// Python plugin runtime.
///
/// This runtime uses `CPython` compiled to WASI to execute Python beancount
/// plugins. The Python runtime is downloaded on first use.
pub struct PythonRuntime {
    engine: Arc<Engine>,
    module: Module,
    stdlib_path: std::path::PathBuf,
    max_time_secs: u64,
    max_memory: usize,
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

        let cache_path = compat_cache_path(&engine, &python_wasm);
        let module = load_or_compile_cached_module(&engine, &python_wasm, &cache_path)?;

        Ok(Self {
            engine,
            module,
            stdlib_path,
            max_time_secs: crate::sandbox::DEFAULT_SANDBOX_MAX_TIME_SECS,
            max_memory: PYTHON_MAX_MEMORY,
        })
    }

    /// Set the per-call time budget, in seconds, like a WASM plugin's
    /// [`crate::RuntimeConfig::max_time_secs`]: the host's setting
    /// (`[plugins] max_time_secs`, `--plugin-max-time-secs`,
    /// `LoadOptions::plugin_max_time_secs`), never the ledger's. It becomes
    /// fuel as a WASM plugin's does ([`crate::sandbox::fuel_for_secs`]). The default is
    /// [`sandbox::DEFAULT_SANDBOX_MAX_TIME_SECS`].
    ///
    /// [`sandbox::DEFAULT_SANDBOX_MAX_TIME_SECS`]: crate::sandbox::DEFAULT_SANDBOX_MAX_TIME_SECS
    #[must_use]
    pub const fn with_max_time_secs(mut self, secs: u64) -> Self {
        self.max_time_secs = secs;
        self
    }

    /// Set the sandbox memory cap, in bytes, like a WASM plugin's
    /// [`crate::RuntimeConfig::max_memory`]: the host's setting
    /// (`[plugins] max_memory_mb`, `--plugin-max-memory-mb`,
    /// `LoadOptions::plugin_max_memory_mb`), never the ledger's. The
    /// default is [`crate::sandbox::DEFAULT_SANDBOX_MAX_MEMORY`]; wasm32
    /// cannot address more than 4 GiB.
    #[must_use]
    pub const fn with_max_memory(mut self, bytes: usize) -> Self {
        self.max_memory = bytes;
        self
    }

    /// Execute Python plugin source by calling one named function.
    ///
    /// This bypasses `__plugins__`: `plugin_func` is called directly, with
    /// `(entries, options_map)` plus the config string when there is one.
    /// A `plugin "file.py"` directive goes through [`Self::execute_module`],
    /// which resolves entry points from `__plugins__` the way beancount does.
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
    ///
    /// # Errors
    ///
    /// Returns [`PythonError`] when the interpreter cannot run (including a
    /// fuel trap) or its output cannot be decoded.
    pub fn execute_plugin(
        &self,
        plugin_code: &str,
        plugin_func: &str,
        input: &PluginInput,
    ) -> Result<PluginOutput, PythonError> {
        self.execute(plugin_code, plugin_func, Some(&[plugin_func]), input)
    }

    /// Run `plugin_code` as a module named `plugin_name`.
    ///
    /// `entry_points` names the functions to call; `None` means the
    /// module's `__plugins__`, resolved by the compat layer's `run_plugin`
    /// exactly as beancount's loader does (see its docstring for the two
    /// places it reports where beancount does not).
    fn execute(
        &self,
        plugin_code: &str,
        plugin_name: &str,
        entry_points: Option<&[&str]>,
        input: &PluginInput,
    ) -> Result<PluginOutput, PythonError> {
        // Everything the script needs goes through files, so nothing is
        // spliced into Python source: a narration with a quote or a
        // backslash once broke the JSON embedded in a string literal.
        let entries_jsonl = serialize_directives_to_json_lines(&input.directives)?;
        let options_json = serde_json::to_string(&input.options)
            .map_err(|e| PythonError::Serialization(e.to_string()))?;
        let module_name = std::path::Path::new(plugin_name)
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("plugin");
        let invocation = serde_json::json!({
            "plugin_name": plugin_name,
            "module_name": module_name,
            "config": input.config,
            "entry_points": entry_points,
        })
        .to_string();

        let output = self.run_python(
            &[
                ("script.py", PLUGIN_SCRIPT),
                ("compat.py", BEANCOUNT_COMPAT_PY),
                ("plugin.py", plugin_code),
                ("entries.jsonl", &entries_jsonl),
                ("options.json", &options_json),
                ("invocation.json", &invocation),
            ],
            input.directives.len(),
        )?;
        drop(entries_jsonl);

        // Parse output (pass input length so the Python bridge can
        // encode the opaque rebuild as `Delete(all-input) + Insert(all-output)`).
        parse_plugin_output(output.as_ref(), input.directives.len())
    }

    /// Execute a built-in beancount plugin by module name.
    ///
    /// # Arguments
    ///
    /// * `module_name` - The module name (e.g., "`beancount.plugins.check_commodity`")
    /// * `input` - Plugin input
    ///
    /// # Errors
    ///
    /// As [`Self::execute_plugin`], and [`PythonError::Execution`] for a
    /// module with no Python implementation here.
    pub fn execute_builtin(
        &self,
        module_name: &str,
        input: &PluginInput,
    ) -> Result<PluginOutput, PythonError> {
        let Some(plugin_code) = builtin_python_plugin(module_name) else {
            return Err(PythonError::Execution(format!(
                "built-in plugin '{module_name}' is not available in Python WASI mode. \
                 Use rustledger's native implementation instead."
            )));
        };

        self.execute_module_source(plugin_code, module_name, input)
    }

    /// Execute a Python plugin by module name.
    ///
    /// This method reads the plugin file's source and executes it in the
    /// WASI sandbox, running the functions its `__plugins__` lists, in
    /// order, as beancount's loader does.
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
        self.execute_module_source(&source, module_name, input)
    }

    /// Execute `source` as the module `module_name`, running the functions
    /// its `__plugins__` lists (see [`Self::execute_module`]).
    ///
    /// # Errors
    ///
    /// As [`Self::execute_plugin`].
    pub fn execute_module_source(
        &self,
        source: &str,
        module_name: &str,
        input: &PluginInput,
    ) -> Result<PluginOutput, PythonError> {
        self.execute(source, module_name, None, input)
    }

    /// Run `/work/script.py` with `files` written into `/work` (a fresh
    /// temp dir, deleted when this returns, on every path, including a
    /// trap), and return what it wrote to stdout.
    ///
    /// `entries` is how many directives the input holds, for the
    /// messages when the plugin runs out of time or memory.
    fn run_python(
        &self,
        files: &[(&str, &str)],
        entries: usize,
    ) -> Result<impl AsRef<[u8]> + use<>, PythonError> {
        // Create a work directory for script and output
        // Private to the user (0700 on Unix; the default followed the
        // umask, 0775 here, so other local users could read the ledger's
        // entries while a plugin ran, and after a Ctrl-C, which leaves
        // the directory behind, #2500's third review). Windows' temp
        // directory is per-user already.
        let mut builder = tempfile::Builder::new();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            builder.permissions(std::fs::Permissions::from_mode(0o700));
        }
        let work_dir = builder.tempdir().map_err(PythonError::Io)?;
        for (name, contents) in files {
            std::fs::write(work_dir.path().join(name), contents)?;
        }

        // Build WASI context
        let mut wasi_builder = WasiCtxBuilder::new();

        // The guest writes nothing to the host filesystem: its result goes
        // to stdout, and stdout and stderr go to capped in-memory pipes.
        // A writable `/work` (as before #2500's review) let a plugin write
        // gigabytes of host temp space for almost no fuel (1 GiB cost
        // 0.07G fuel, measured), and an inherited stderr let it flood the
        // host's. A write past a cap traps the call.
        let input_bytes: usize = files.iter().map(|(_, contents)| contents.len()).sum();
        let stdout = MemoryOutputPipe::new(output_cap(input_bytes));
        let stderr = MemoryOutputPipe::new(STDERR_CAP);
        wasi_builder.stdout(stdout.clone());
        wasi_builder.stderr(stderr.clone());

        // Only the standard library, read-only, at `/lib` (PYTHONHOME is
        // `/`). Before #2500's review the whole cache directory was `/`,
        // which also showed the guest `python.wasm` and every cached
        // `.cwasm`; nothing there is secret, but nothing there is needed.
        wasi_builder
            .preopened_dir(&self.stdlib_path, "/lib", FsPerms::ReadOnly)
            .map_err(PythonError::Wasm)?;

        // The inputs, read-only.
        wasi_builder
            .preopened_dir(work_dir.path(), "/work", FsPerms::ReadOnly)
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
        let mut store = make_sandboxed_python_store(
            &self.engine,
            wasi_ctx,
            python_fuel(self.max_time_secs),
            self.max_memory,
        )
        .map_err(PythonError::Wasm)?;

        // Run Python, on a thread of its own under a wall-clock deadline
        // of the time budget. Fuel alone bounds only computation: a guest
        // waiting in WASI (`time.sleep`, `select`) burns none, so before
        // #2500's second review `time.sleep(10**9)` hung the host. The
        // guest runs async (on a fiber, whose stack is sized for
        // `WASM_STACK`), yields every `FUEL_YIELD_INTERVAL`, and is
        // dropped at the deadline. The fiber also means a deep recursion
        // traps in the guest instead of overflowing the host's stack,
        // which aborted the whole process before.
        let deadline = std::time::Duration::from_secs(self.max_time_secs.max(1));
        let outcome = run_start(&self.engine, &self.module, &mut store, deadline)?;
        let Some(outcome) = outcome else {
            forward_guest_stderr(&stderr.contents());
            return Err(PythonError::Execution(format!(
                "the plugin {}; time spent waiting or sleeping counts",
                crate::sandbox::time_budget_exceeded(self.max_time_secs).trim_start_matches("it ")
            )));
        };
        // `exit(0)` is a normal end; the output says whether it is whole.
        let outcome = match outcome {
            Err(e)
                if e.downcast_ref::<wasmtime_wasi::I32Exit>()
                    .is_some_and(|x| x.0 == 0) =>
            {
                Ok(())
            }
            other => other,
        };
        // The interpreter's own diagnostics (a traceback, the plugin's
        // prints) are the user's to see, whatever the outcome.
        forward_guest_stderr(&stderr.contents());
        outcome.map_err(|e| {
            // `PythonError::Execution` already reads "Python execution
            // failed: ", so the message is just the cause.
            let limiter = &store.data().limiter;
            let cause = if e.downcast_ref::<wasmtime::Trap>() == Some(&wasmtime::Trap::OutOfFuel) {
                format!(
                    "the plugin {}; moving {entries} entries into Python and back takes \
                     about {} seconds of it before the plugin does any work: ",
                    crate::sandbox::time_budget_exceeded(self.max_time_secs)
                        .trim_start_matches("it "),
                    transfer_secs_estimate(entries),
                )
            } else if stdout.contents().len() >= output_cap(input_bytes) {
                format!(
                    "the plugin's output exceeded its {} MiB limit: ",
                    output_cap(input_bytes) >> 20
                )
            } else if stderr.contents().len() >= STDERR_CAP {
                format!(
                    "the plugin wrote more than {} MiB to stderr: ",
                    STDERR_CAP >> 20
                )
            } else if limiter.growth_denied() {
                format!(
                    "the plugin {} (Python holds every entry as objects, about 1.2 KB per \
                     transaction; {entries} entries were passed in): ",
                    crate::sandbox::memory_cap_exceeded(limiter.max_memory())
                        .trim_start_matches("it ")
                )
            } else if e.downcast_ref::<wasmtime::Trap>() == Some(&wasmtime::Trap::StackOverflow) {
                "the plugin recursed past the sandbox's call stack: ".to_string()
            } else if format!("{e:#}").contains("resource table has no free keys") {
                format!("the plugin held more than {MAX_GUEST_RESOURCES} files open at once: ")
            } else if let Some(exit) = e.downcast_ref::<wasmtime_wasi::I32Exit>() {
                // An uncaught exception at the top level (an import the
                // compat layer does not provide, a syntax error): its
                // traceback went to stderr above, and its last line names
                // the error.
                let contents = stderr.contents();
                let last = String::from_utf8_lossy(&contents)
                    .lines()
                    .rev()
                    .find(|l| !l.trim().is_empty())
                    .map(|l| l.trim().to_string());
                return PythonError::Execution(match last {
                    Some(last) => format!(
                        "the plugin stopped Python with exit status {}: {last} \
                         (traceback above)",
                        exit.0
                    ),
                    None => format!("the plugin stopped Python with exit status {}", exit.0),
                });
            } else {
                String::new()
            };
            PythonError::Execution(format!("{cause}{e:#}"))
        })?;

        drop(work_dir);
        Ok(stdout.contents())
    }
}

/// Instantiate `module` in `store` and run its `_start`, on a thread of
/// its own with a current-thread tokio runtime, for at most `deadline`.
/// `None` when the deadline passed first.
fn run_start(
    engine: &Engine,
    module: &Module,
    store: &mut Store<PythonStoreState>,
    deadline: std::time::Duration,
) -> Result<Option<wasmtime::Result<()>>, PythonError> {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("rledger-python-plugin".to_string())
            .spawn_scoped(scope, move || {
                // The guest is single-threaded and its file operations run
                // one at a time, so a couple of blocking threads do; the
                // default (512) let one call start dozens.
                let rt = tokio::runtime::Builder::new_current_thread()
                    .max_blocking_threads(2)
                    .enable_all()
                    .build()
                    .map_err(PythonError::Io)?;
                rt.block_on(async move {
                    // Create linker and add WASI. The closure reaches
                    // through the state wrapper to the inner
                    // `p1::WasiP1Ctx` that the WASI syscall
                    // implementations expect.
                    let mut linker: Linker<PythonStoreState> = Linker::new(engine);
                    p1::add_to_linker_async(&mut linker, |state| &mut state.wasi)
                        .map_err(PythonError::Wasm)?;
                    let run = async {
                        let instance = linker.instantiate_async(&mut *store, module).await?;
                        let start = instance.get_typed_func::<(), ()>(&mut *store, "_start")?;
                        start.call_async(&mut *store, ()).await
                    };
                    Ok(tokio::time::timeout(deadline, run).await.ok())
                })
            })
            .map_err(PythonError::Io)?
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

/// Build a `Store<PythonStoreState>` pre-wired with the runtime's
/// resource caps:
///
/// - `Store::limiter` is set so wasmtime's `memory.grow` and
///   `table.grow` checks call back into [`MemoryLimiter`] with the
///   `PYTHON_MAX_MEMORY` ceiling (issue #1234).
/// - `set_fuel(fuel)` caps per-call CPU consumption ([`python_fuel`]).
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
    fuel: u64,
    max_memory: usize,
) -> wasmtime::Result<Store<PythonStoreState>> {
    let mut store = Store::new(
        engine,
        PythonStoreState {
            wasi,
            limiter: MemoryLimiter::new(max_memory),
        },
    );
    store.limiter(|state| &mut state.limiter);
    {
        use wasmtime_wasi::WasiView;
        store
            .data_mut()
            .wasi
            .ctx()
            .table
            .set_max_capacity(MAX_GUEST_RESOURCES);
    }
    store.set_fuel(fuel)?;
    // Yield to the host now and then, so the wall-clock deadline in
    // `run_start` can stop a long computation too.
    store.fuel_async_yield_interval(Some(FUEL_YIELD_INTERVAL))?;
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
/// Python runtime runs async (see [`run_start`]), so the guest runs on a
/// fiber stack of this size: a recursion past `WASM_STACK` traps in the
/// guest rather than overflowing the host thread's stack.
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

/// The `.cwasm` cache path for `source_wasm` under THIS engine, keyed by
/// [`Engine::precompile_compatibility_hash`] (#1809, #1811 review).
///
/// wasmtime guarantees that a serialized module deserializes in another
/// engine *iff* their compatibility hashes match, so embedding the hash in
/// the filename means an artifact written by an incompatible engine (a
/// different wasmtime version, a changed `engine_config`) resolves to a
/// DIFFERENT path and is simply never found — a cache miss that recompiles,
/// never an incompatible artifact handed to the unsafe deserialize. It is
/// what lets [`load_or_compile_cached_module`] uphold its safety contract.
fn compat_cache_path(engine: &Engine, source_wasm: &std::path::Path) -> std::path::PathBuf {
    use std::hash::{Hash, Hasher};
    // `DefaultHasher` has fixed keys (deterministic across runs, unlike
    // `RandomState`); it only has to be stable within one binary and change
    // when the compatibility hash changes, both of which it satisfies.
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    engine.precompile_compatibility_hash().hash(&mut hasher);
    source_wasm.with_extension(format!("{:016x}.cwasm", hasher.finish()))
}

/// Load the compiled CPython-WASI `Module` from `cache_path`, or compile it
/// from `source_wasm` and atomically write the cache.
///
/// The cache exists to skip the ~30s `CPython`-WASI compile on every load;
/// before #1809 a cache that failed to deserialize propagated as a hard
/// `Python runtime unavailable: failed deserialization for .../python.cwasm`,
/// bricking python-plugin loading until the user deleted the file. Now an
/// unusable cache is discarded and recompiled.
///
/// # Safety
///
/// `Module::deserialize_file` is `unsafe` because wasmtime does NOT validate
/// that the bytes are a trustworthy artifact — its own docs warn that
/// deserializing stale/foreign/corrupt bytes "may trick Wasmtime into
/// arbitrary code execution" (it is UB, *not* a guaranteed `Err`). So we
/// never hand it an untrusted file. Two gates make every deserialized file
/// one this code path produced with a compatible engine:
///
/// 1. `cache_path` is keyed by the engine's compatibility hash (see
///    [`compat_cache_path`]), so a cross-version / cross-config artifact
///    resolves to a different path and is never opened here.
/// 2. The SAFE [`Engine::detect_precompiled_file`] header check runs first;
///    anything that is not a precompiled *module* (garbage, a file truncated
///    below its header, a component) is treated as a miss and recompiled,
///    without ever reaching `deserialize_file`.
///
/// Writes go through a temp file + atomic rename ([`write_cache_atomically`]),
/// so a process killed mid-write or a concurrent writer never leaves a
/// partial file at `cache_path`. The residual UB surface — on-disk bit-rot
/// that preserves a valid header AND the matching compatibility hash but
/// corrupts the body — is the irreducible wasmtime caveat shared by all
/// `.cwasm` caching.
#[allow(unsafe_code)]
fn load_or_compile_cached_module(
    engine: &Engine,
    source_wasm: &std::path::Path,
    cache_path: &std::path::Path,
) -> Result<Module, PythonError> {
    // Safe pre-check: does the file look like a precompiled module at all?
    // Returns `Ok(None)` for garbage/truncated-below-header bytes and `Err`
    // for a missing file — both route to recompile without an unsafe call.
    let looks_like_module = matches!(
        Engine::detect_precompiled_file(cache_path),
        Ok(Some(wasmtime::Precompiled::Module))
    );
    if looks_like_module {
        // SAFETY: the file sits at a compatibility-hash-keyed path (so it was
        // produced by a wasmtime-guaranteed-compatible engine) and has passed
        // the safe precompiled-module header check above.
        match unsafe { Module::deserialize_file(engine, cache_path) } {
            Ok(module) => return Ok(module),
            Err(e) => eprintln!(
                "⚠️  Ignoring unreadable Python WASM cache at {} ({e}); recompiling.",
                cache_path.display()
            ),
        }
    } else if cache_path.exists() {
        eprintln!(
            "⚠️  Ignoring foreign/corrupt Python WASM cache at {}; recompiling.",
            cache_path.display()
        );
    } else {
        eprintln!(
            "⚠️  Compiling Python WASM module (~30 seconds; on first use and after a wasmtime upgrade)..."
        );
    }

    let module = Module::from_file(engine, source_wasm).map_err(PythonError::Wasm)?;
    write_cache_atomically(cache_path, &module);
    Ok(module)
}

/// Serialize `module` to `cache_path` via a temp file + atomic rename, so a
/// killed-mid-write or a concurrent writer never leaves a partial `.cwasm`
/// at the path (#1811 review).
///
/// Best-effort: a write failure only costs the next run a recompile — never
/// a load failure — but it IS surfaced (a silently unwritable cache dir would
/// otherwise make every load pay the ~30s recompile with no explanation).
fn write_cache_atomically(cache_path: &std::path::Path, module: &Module) {
    let warn_unwritable = || {
        eprintln!(
            "⚠️  Could not write the Python WASM cache at {} — python-plugin loading will \
             recompile (~30s) every run until this is resolved.",
            cache_path.display()
        );
    };
    let (Ok(bytes), Some(dir)) = (module.serialize(), cache_path.parent()) else {
        warn_unwritable();
        return;
    };
    // Temp name in the SAME directory (rename is only atomic within one
    // filesystem); the pid keeps concurrent writers off each other's temp.
    let file_name = cache_path
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or("python.cwasm");
    let tmp = dir.join(format!("{file_name}.tmp.{}", std::process::id()));
    if std::fs::write(&tmp, &bytes).is_err() {
        let _ = std::fs::remove_file(&tmp);
        warn_unwritable();
        return;
    }
    if std::fs::rename(&tmp, cache_path).is_err() {
        let _ = std::fs::remove_file(&tmp);
        warn_unwritable();
    }
}

/// The source of the built-in Python plugin `name` (with or without the
/// `beancount.plugins.` prefix), if there is one. `plugin "python:<name>"`
/// runs it instead of the native plugin of that name.
#[must_use]
pub fn builtin_python_plugin(name: &str) -> Option<&'static str> {
    match name.strip_prefix("beancount.plugins.").unwrap_or(name) {
        "check_commodity" => Some(CHECK_COMMODITY_PLUGIN),
        "leafonly" => Some(LEAFONLY_PLUGIN),
        _ => None,
    }
}

/// Classify a Python plugin reference as a FILE path vs a dotted module name.
///
/// A file when it ends in `.py` (case-insensitive) or contains a path separator.
/// Forward `/` counts even on Windows (where `MAIN_SEPARATOR` is `\`), so
/// `plugins/foo.py` is never mistaken for a module.
///
/// Single source for the file-vs-module decision across the loader's up-front
/// `#1432` rejection, the loader's runtime dispatch, and `discover_module_source`
/// below — these previously used three non-equivalent criteria (some omitted
/// the forward slash) and could disagree about the same reference.
#[must_use]
pub fn is_python_plugin_file_ref(name: &str) -> bool {
    std::path::Path::new(name)
        .extension()
        .is_some_and(|ext| ext.eq_ignore_ascii_case("py"))
        || name.contains(['/', std::path::MAIN_SEPARATOR])
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
    if is_python_plugin_file_ref(module_name) {
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

/// Serialize directives for Python, one JSON object per line, so the
/// compat layer can parse them one at a time (`load_entries`) instead of
/// holding the whole input as one string beside the objects parsed from it.
/// `serde_json` escapes newlines inside strings, so a line is a directive.
fn serialize_directives_to_json_lines(
    directives: &[crate::types::DirectiveWrapper],
) -> Result<String, PythonError> {
    let mut out = String::new();
    for d in directives {
        out.push_str(
            &serde_json::to_string(d).map_err(|e| PythonError::Serialization(e.to_string()))?,
        );
        out.push('\n');
    }
    Ok(out)
}

/// One output line: an input the plugin returned (possibly rebuilt),
/// or a new entry.
#[derive(serde::Deserialize)]
#[serde(untagged)]
enum OutputEntry {
    Modify {
        modify: usize,
        entry: crate::types::DirectiveWrapper,
    },
    Insert {
        insert: crate::types::DirectiveWrapper,
    },
}

/// Parse the plugin's stdout: one directive per line when it ran, then a
/// last line `{"ran": bool, "errors": [...]}` (written last, so a stream
/// without it means the script died before finishing).
///
/// `input_len` is the length of the **plugin's** input directive list.
/// An output entry the compat layer traced to input `i` (see its
/// `dump_entries`) becomes `Modify(i)`, keeping that input's source
/// location; any other is an `Insert`, and every input index no output
/// claimed is a `Delete`, so each index appears exactly once, as the ops
/// protocol requires. When nothing ran (no `__plugins__`, or an entry
/// point that does not exist) every input is kept as is.
fn parse_plugin_output(output: &[u8], input_len: usize) -> Result<PluginOutput, PythonError> {
    use crate::types::PluginOp;

    let output = std::str::from_utf8(output)
        .map_err(|e| PythonError::Serialization(format!("plugin output is not UTF-8: {e}")))?;
    let mut lines: Vec<&str> = output.lines().filter(|l| !l.trim().is_empty()).collect();
    let result = lines.pop().ok_or_else(|| {
        PythonError::Execution("the plugin wrote no result; it may have crashed".to_string())
    })?;
    let result: serde_json::Value = serde_json::from_str(result)
        .map_err(|e| PythonError::Serialization(format!("failed to parse result: {e}")))?;
    // The compat layer always ends with this line; output without it was
    // cut short (a plugin that exited midway), and before #2500's second
    // review its last entry was read as the result, so the entries were
    // silently kept as they were.
    let ran = result
        .get("ran")
        .and_then(serde_json::Value::as_bool)
        .ok_or_else(|| {
            PythonError::Execution(
                "the plugin's output ends before its result; it may have exited midway".to_string(),
            )
        })?;
    let json_errors = match result.get("errors") {
        Some(serde_json::Value::Array(errors)) => errors.clone(),
        _ => Vec::new(),
    };

    let ops = if ran {
        let mut ops = Vec::with_capacity(input_len.max(lines.len()));
        let mut claimed = vec![false; input_len];
        for line in lines {
            let entry: OutputEntry = serde_json::from_str(line)
                .map_err(|e| PythonError::Serialization(format!("failed to parse entries: {e}")))?;
            match entry {
                OutputEntry::Modify { modify, entry } if modify < input_len && !claimed[modify] => {
                    claimed[modify] = true;
                    ops.push(PluginOp::Modify(modify, entry));
                }
                OutputEntry::Modify { entry, .. } | OutputEntry::Insert { insert: entry } => {
                    ops.push(PluginOp::Insert(entry));
                }
            }
        }
        ops.extend(
            claimed
                .iter()
                .enumerate()
                .filter(|(_, claimed)| !**claimed)
                .map(|(i, _)| PluginOp::Delete(i)),
        );
        ops
    } else {
        (0..input_len).map(PluginOp::Keep).collect()
    };

    let errors: Vec<PluginError> = json_errors
        .into_iter()
        .filter_map(|v| {
            let message = v.get("message")?.as_str()?.to_string();
            let severity =
                if v.get("severity").and_then(serde_json::Value::as_str) == Some("warning") {
                    PluginErrorSeverity::Warning
                } else {
                    PluginErrorSeverity::Error
                };
            Some(PluginError {
                message,
                severity,
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

    Ok(PluginOutput { ops, errors })
}

// =============================================================================
// Built-in plugin implementations
// =============================================================================

/// Python implementation of `check_commodity` plugin.
///
/// Behaves as beancount's `beancount.plugins.check_commodity` (without
/// its config-string ignore map): a currency counts as declared only by
/// a `commodity` directive, and each undeclared one is reported once,
/// with the first account it appears in (in sorted order), or `Price Directive Context`
/// when it appears only in price directives. Before #2500's review this
/// counted an `open`'s currencies as declarations, so it reported
/// nothing for most ledgers that beancount flags.
const CHECK_COMMODITY_PLUGIN: &str = r#"
__plugins__ = ('plugin',)

def plugin(entries, options_map, config=None):
    """Find commodities used without a Commodity directive."""
    declared = set()
    occurrences = set()
    anonymous = set()
    for entry in entries:
        if isinstance(entry, Commodity):
            declared.add(entry.currency)
        elif isinstance(entry, Open):
            for currency in entry.currencies or ():
                occurrences.add((entry.account, currency))
        elif isinstance(entry, Transaction):
            for posting in entry.postings:
                for amount in (posting.units, posting.cost, posting.price):
                    if amount is not None and amount.currency:
                        occurrences.add((posting.account, amount.currency))
        elif isinstance(entry, Balance):
            occurrences.add((entry.account, entry.amount.currency))
        elif isinstance(entry, Price):
            anonymous.add(('Price Directive Context', entry.currency))
            anonymous.add(('Price Directive Context', entry.amount.currency))

    errors = []
    issued = set()
    for context, currency in sorted(occurrences) + sorted(anonymous):
        if currency in declared or currency in issued:
            continue
        errors.append(ValidationError(
            new_metadata('<check_commodity>', 0),
            f"Missing Commodity directive for '{currency}' in '{context}'",
            None))
        issued.add(currency)
    return entries, errors
"#;

/// Python implementation of leafonly plugin.
///
/// Behaves as beancount's `beancount.plugins.leafonly`: one error per
/// account that has child accounts and is posted to by a transaction,
/// located at the account's `open` (beancount reports it there, once).
/// Before #2500's review this reported every posting separately.
const LEAFONLY_PLUGIN: &str = r#"
__plugins__ = ('plugin',)

def plugin(entries, options_map, config=None):
    """Check for non-leaf accounts that have postings on them."""
    accounts = set()
    posted = set()
    opens = {}
    for entry in entries:
        if isinstance(entry, Open):
            accounts.add(entry.account)
            opens.setdefault(entry.account, entry)
        elif isinstance(entry, Balance):
            accounts.add(entry.account)
        elif isinstance(entry, Transaction):
            for posting in entry.postings:
                accounts.add(posting.account)
                posted.add(posting.account)
    parents = set()
    for account in accounts:
        parts = account.split(':')
        for i in range(1, len(parts)):
            parents.add(':'.join(parts[:i]))

    errors = []
    for account in sorted(posted & parents):
        open_entry = opens.get(account)
        errors.append(ValidationError(
            open_entry.meta if open_entry else new_metadata('<leafonly>', 0),
            f"Non-leaf account '{account}' has postings on it",
            open_entry))
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

    /// #1809 / #1811 review: `load_or_compile_cached_module` recovers from an
    /// unusable cache by recompiling — and crucially does so via the SAFE
    /// [`Engine::detect_precompiled_file`] header check, not by feeding
    /// garbage to the unsafe `deserialize_file` and hoping for an `Err`.
    /// Hermetic: a 1-instruction synthetic module, no `CPython` download.
    #[test]
    fn cached_module_recovers_from_unusable_cache_via_safe_precheck() {
        use std::io::Write;

        let engine = Engine::new(&engine_config()).expect("engine builds");
        let dir = tempfile::tempdir().expect("tempdir");
        let source_wasm = dir.path().join("mod.wasm");
        let cache_path = dir.path().join("mod.cwasm");

        // A trivial valid module, written as real `.wasm` bytes so
        // `Module::from_file` (the recompile path) has a source to read.
        let wasm_bytes = wat::parse_str("(module (func (export \"noop\")))")
            .expect("wat compiles to wasm bytes");
        std::fs::write(&source_wasm, &wasm_bytes).expect("write source wasm");

        // 1. Cold cache: compiles from source and atomically writes the cache.
        let module = load_or_compile_cached_module(&engine, &source_wasm, &cache_path)
            .expect("cold path compiles");
        assert!(module.get_export("noop").is_some());
        assert!(cache_path.exists(), "cold path must populate the cache");
        // The written cache must be a detectable precompiled module.
        assert!(
            matches!(
                wasmtime::Engine::detect_precompiled_file(&cache_path),
                Ok(Some(wasmtime::Precompiled::Module))
            ),
            "atomic write must leave a valid precompiled module"
        );

        // 2. Warm cache: the fast deserialize path returns the module.
        load_or_compile_cached_module(&engine, &source_wasm, &cache_path)
            .expect("warm path loads from cache");

        // 3. Garbage at the cache path (a foreign/corrupt-file stand-in). The
        //    SAFE detect precheck rejects it as "not a precompiled module" —
        //    the unsafe `deserialize_file` is never reached — and we recompile.
        {
            let mut f = std::fs::File::create(&cache_path).expect("overwrite cache");
            f.write_all(b"not a valid cwasm header")
                .expect("write garbage");
        }
        // Safe: garbage is NOT classified as a precompiled module (whether
        // detect returns `Ok(None)` or `Err`), so the unsafe `deserialize_file`
        // is never reached for it.
        assert!(
            !matches!(
                wasmtime::Engine::detect_precompiled_file(&cache_path),
                Ok(Some(wasmtime::Precompiled::Module))
            ),
            "garbage must not be seen as a module (no unsafe deserialize)"
        );
        let recovered = load_or_compile_cached_module(&engine, &source_wasm, &cache_path)
            .expect("unusable cache must recompile, not error");
        assert!(
            recovered.get_export("noop").is_some(),
            "recompiled module must be functional"
        );
        // The recompile rewrote the cache with valid bytes, so it's healthy.
        load_or_compile_cached_module(&engine, &source_wasm, &cache_path)
            .expect("cache is healthy again after recompile");
    }

    /// The cache path is keyed by the engine's precompile-compatibility hash
    /// (#1811 review): deterministic for a given engine, and never the bare
    /// `.cwasm` name (so a cross-version artifact can't collide at one path
    /// and reach the unsafe deserialize).
    #[test]
    fn compat_cache_path_is_keyed_and_deterministic() {
        let engine = Engine::new(&engine_config()).expect("engine builds");
        let source = std::path::Path::new("/x/python.wasm");
        let a = compat_cache_path(&engine, source);
        let b = compat_cache_path(&engine, source);
        assert_eq!(a, b, "same engine must yield a stable cache path");
        assert_ne!(
            a,
            source.with_extension("cwasm"),
            "cache path must embed the compatibility hash, not the bare .cwasm"
        );
        assert_eq!(a.extension().and_then(|e| e.to_str()), Some("cwasm"));
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
            make_sandboxed_python_store(&engine, wasi, python_fuel(1), PYTHON_MAX_MEMORY)
                .expect("store construction must succeed");

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
        // The store is set up for async calls (see `run_start`).
        let linker = Linker::<PythonStoreState>::new(&engine);
        let result = tokio::runtime::Builder::new_current_thread()
            .build()
            .expect("tokio runtime")
            .block_on(async {
                let instance = linker
                    .instantiate_async(&mut store, &module)
                    .await
                    .expect("instantiation must succeed under the cap");
                let try_grow = instance
                    .get_typed_func::<(), i32>(&mut store, "try_grow_past_cap")
                    .expect("export must exist");
                try_grow
                    .call_async(&mut store, ())
                    .await
                    .expect("call must not trap")
            });
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

    /// A Python plugin's time budget converts to fuel exactly as a WASM
    /// plugin's does (#2500), so the host's `max_time_secs` means the same
    /// thing for both and a change to one conversion cannot leave the
    /// other behind.
    #[test]
    fn python_fuel_is_the_shared_seconds_conversion() {
        for secs in [
            0,
            1,
            3,
            crate::sandbox::DEFAULT_SANDBOX_MAX_TIME_SECS,
            u64::MAX,
        ] {
            assert_eq!(python_fuel(secs), crate::sandbox::fuel_for_secs(secs));
        }
    }

    /// The default budget covers `CPython`'s startup many times over. The
    /// figure is the startup measured in `python_fuel`'s rustdoc; if the
    /// runtime or the budget changes so this fails, re-measure and update
    /// that table. (The pre-#2500 budget, 600M, fails this: it is half of
    /// one startup.)
    #[test]
    fn default_python_budget_covers_measured_startup() {
        const MEASURED_STARTUP_FUEL: u64 = 1_240_000_000;
        assert!(
            python_fuel(crate::sandbox::DEFAULT_SANDBOX_MAX_TIME_SECS)
                >= 20 * MEASURED_STARTUP_FUEL
        );
    }

    #[test]
    fn test_parse_plugin_output() {
        let result = parse_plugin_output(br#"{"ran": true, "errors": []}"#, 0).unwrap();
        assert!(result.ops.is_empty());
        assert!(result.errors.is_empty());
    }

    /// Output traced to an input is `Modify(i)` (keeping its location),
    /// the rest `Insert`, unclaimed inputs `Delete`, and a second claim on
    /// one input an `Insert` (#2500 review).
    #[test]
    fn parse_plugin_output_traces_entries_to_inputs() {
        use crate::types::PluginOp;
        let entry =
            r#"{"date": "2024-01-01", "type": "close", "account": "Assets:A", "metadata": []}"#;
        let output = format!(
            "{{\"modify\": 2, \"entry\": {entry}}}\n{{\"insert\": {entry}}}\n\
             {{\"modify\": 2, \"entry\": {entry}}}\n{{\"ran\": true, \"errors\": []}}\n"
        );
        let result = parse_plugin_output(output.as_bytes(), 3).unwrap();
        let shape: Vec<String> = result
            .ops
            .iter()
            .map(|op| match op {
                PluginOp::Modify(i, _) => format!("M{i}"),
                PluginOp::Insert(_) => "I".to_string(),
                PluginOp::Delete(i) => format!("D{i}"),
                PluginOp::Keep(i) => format!("K{i}"),
            })
            .collect();
        assert_eq!(shape, ["M2", "I", "I", "D0", "D1"]);
    }

    /// `"ran": false` (nothing ran) keeps every input directive in place,
    /// rather than deleting and re-inserting them; a `"severity":
    /// "warning"` diagnostic stays a warning (#2500).
    #[test]
    fn parse_plugin_output_not_ran_keeps_input_and_warning_severity() {
        use crate::types::PluginOp;
        let output = concat!(
            r#"{"ran": false, "errors": ["#,
            r#"{"message": "ran nothing", "source_file": null, "line_number": null, "severity": "warning"}, "#,
            r#"{"message": "bad", "source_file": null, "line_number": null}]}"#,
            "\n"
        )
        .as_bytes();
        let result = parse_plugin_output(output, 2).unwrap();
        assert!(matches!(
            result.ops.as_slice(),
            [PluginOp::Keep(0), PluginOp::Keep(1)]
        ));
        assert_eq!(result.errors.len(), 2);
        assert_eq!(result.errors[0].severity, PluginErrorSeverity::Warning);
        assert_eq!(result.errors[1].severity, PluginErrorSeverity::Error);
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
