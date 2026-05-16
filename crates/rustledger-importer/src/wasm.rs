//! Host loader for WASM-implemented importers (wave 2.3b).
//!
//! A [`WasmImporter`] wraps a `.wasm` module and implements the
//! [`crate::Importer`] trait by serializing inputs to `MessagePack`,
//! calling into the module via wasmtime, and deserializing outputs.
//!
//! # Sandbox model
//!
//! Mirrors the existing directive-plugin runtime in
//! `rustledger-plugin/src/runtime.rs`:
//!
//! - No imports allowed (rejected at load time)
//! - No WASI / filesystem / network / env / syscalls
//! - Memory limit enforced (default 256 MiB)
//! - Fuel-based execution time limit (default 30 s)
//!
//! The host reads the source file into memory and passes the bytes
//! via [`ImporterInput::content`]; the WASM importer never opens the
//! file itself.
//!
//! # Required WASM exports
//!
//! A WASM importer module must export:
//!
//! - `memory` — the standard linear memory
//! - `alloc(size: u32) -> u32` — allocates `size` bytes, returns pointer
//! - `metadata() -> u64` — packed `(ptr << 32) | len` of `MessagePack`
//!   [`MetadataOutput`]. Called once at load.
//! - `identify(ptr: u32, len: u32) -> u64` — input is msgpack
//!   [`IdentifyInput`], output is msgpack [`IdentifyOutput`].
//! - `extract(ptr: u32, len: u32) -> u64` — input is msgpack
//!   [`ImporterInput`], output is msgpack [`ImporterOutput`].
//! - `extract_enriched(ptr: u32, len: u32) -> u64` — input is msgpack
//!   [`ImporterInput`], output is msgpack [`EnrichedImporterOutput`].

use std::path::{Path, PathBuf};
use std::sync::Arc;

use rustledger_ops::fingerprint::Fingerprint;
use rustledger_plugin_types::{
    EnrichedImporterOutput, IdentifyInput, IdentifyOutput, ImporterInput, ImporterOutput,
    MetadataOutput, PluginError, PluginErrorSeverity,
};
use serde::{Serialize, de::DeserializeOwned};
use wasmtime::{Config, Engine, Linker, Module, ResourceLimiter, Store};

use crate::config::{CsvConfig, ImporterType};
use crate::{EnrichedImportResult, ImportResult, Importer, ImporterConfig};

/// Hard cap on the byte length a WASM importer can return from any
/// entry point. Prevents a malicious or buggy module from triggering a
/// 4 GiB host allocation by returning `(any_ptr, u32::MAX)`. 64 MiB is
/// well above any realistic importer output for a single statement.
const MAX_OUTPUT_BYTES: usize = 64 * 1024 * 1024;

/// Hard cap on the number of elements in any single WASM table.
/// Importers don't typically need indirect-call tables at all, let
/// alone large ones. Each ref-typed slot is pointer-sized (8 bytes on
/// 64-bit), so 1M elements = ~8 MiB worst case — well under the
/// memory cap but enough headroom for any plausible indirect-dispatch
/// pattern. Without this cap, `table.grow` would bypass the memory
/// limiter (`Memory` and `Table` are separate resource classes in
/// wasmtime's accounting).
const MAX_TABLE_ELEMENTS: usize = 1024 * 1024;

/// Configuration for the WASM importer runtime.
#[derive(Debug, Clone, Copy)]
pub struct WasmRuntimeConfig {
    /// Maximum memory in bytes (default 256 MiB).
    pub max_memory: usize,
    /// Maximum execution time in seconds (default 30). Converted to a
    /// fuel budget at roughly 1M instructions per second.
    pub max_time_secs: u64,
}

impl Default for WasmRuntimeConfig {
    fn default() -> Self {
        Self {
            max_memory: 256 * 1024 * 1024,
            max_time_secs: 30,
        }
    }
}

/// Errors that can occur loading or invoking a WASM importer.
#[derive(Debug, thiserror::Error)]
pub enum WasmImporterError {
    /// Failed to read the `.wasm` file from disk.
    #[error("failed to read WASM file {path}: {source}")]
    Io {
        /// Path the host tried to read.
        path: PathBuf,
        /// Underlying I/O error.
        source: std::io::Error,
    },
    /// The WASM module is malformed or uses unsupported features.
    #[error("failed to compile WASM module {path}: {source}")]
    Compile {
        /// Path of the module that failed to compile.
        path: PathBuf,
        /// Underlying wasmtime compile error.
        source: anyhow::Error,
    },
    /// The WASM module has imports — they're forbidden in the importer
    /// sandbox. Importers must be self-contained.
    #[error(
        "WASM importer has forbidden import {module}::{name} — importers must be self-contained"
    )]
    ForbiddenImport {
        /// Import module namespace (e.g. `env`, `wasi_snapshot_preview1`).
        module: String,
        /// Import item name within the module.
        name: String,
    },
    /// A required export is missing.
    #[error("WASM importer missing required export `{0}`")]
    MissingExport(&'static str),
    /// Runtime error during a wasmtime call (trap, fuel exhausted,
    /// memory limit, etc.).
    #[error("WASM importer runtime error: {0}")]
    Runtime(#[source] anyhow::Error),
    /// `MessagePack` decode error on the WASM-returned bytes.
    #[error("WASM importer returned malformed MessagePack: {0}")]
    Decode(#[source] rmp_serde::decode::Error),
    /// `MessagePack` encode error on the input being sent to the WASM
    /// importer. Practically only happens if `ImporterConfig` carries
    /// non-serializable state, which shouldn't.
    #[error("failed to encode input for WASM importer: {0}")]
    Encode(#[source] rmp_serde::encode::Error),
    /// The WASM importer returned an `out_len` larger than the host's
    /// allocation cap ([`MAX_OUTPUT_BYTES`]). Either the module is
    /// buggy/malicious or `MAX_OUTPUT_BYTES` needs raising for a
    /// genuinely huge import.
    #[error("WASM importer returned output of {len} bytes, exceeds cap of {max} bytes")]
    OutputTooLarge {
        /// Length the module reported.
        len: usize,
        /// Host's enforced cap (`MAX_OUTPUT_BYTES`).
        max: usize,
    },
}

/// Per-store memory limiter. Wired into [`Store::limiter`] so wasmtime
/// rejects `memory.grow` past `max_memory`. Without this, the
/// [`WasmRuntimeConfig::max_memory`] field would be silently ignored —
/// the sandbox would have unbounded heap, which defeats the
/// "self-contained importer" guarantee.
struct MemoryLimiter {
    max_memory: usize,
}

impl ResourceLimiter for MemoryLimiter {
    fn memory_growing(
        &mut self,
        _current: usize,
        desired: usize,
        _maximum: Option<usize>,
    ) -> wasmtime::Result<bool> {
        Ok(desired <= self.max_memory)
    }

    fn table_growing(
        &mut self,
        _current: usize,
        desired: usize,
        _maximum: Option<usize>,
    ) -> wasmtime::Result<bool> {
        // wasmtime accounts memory and tables separately — without
        // this cap, `table.grow` would bypass the memory limiter.
        // [`MAX_TABLE_ELEMENTS`] is conservative; bump it if a
        // legitimate importer ever needs more.
        Ok(desired <= MAX_TABLE_ELEMENTS)
    }
}

/// Store user-data — just the [`MemoryLimiter`] today. Kept in a named
/// struct so `Store::limiter`'s closure can return a stable reference
/// and future additions (e.g. a host-side metrics counter) can land
/// without changing the `Store<T>` type.
struct StoreState {
    limiter: MemoryLimiter,
}

// Note: no manual `impl From<WasmImporterError> for anyhow::Error` — `anyhow`
// has a blanket impl for any `std::error::Error + Send + Sync + 'static`,
// which thiserror's derive already satisfies. Adding our own would conflict.

/// Wrap a `wasmtime::Error` in `WasmImporterError::Runtime`. Function form
/// (not closure) so call sites stay terse: `.map_err(runtime_err)`.
#[inline]
fn runtime_err(e: wasmtime::Error) -> WasmImporterError {
    WasmImporterError::Runtime(anyhow::Error::from(e))
}

/// A WASM-loaded importer. Implements [`Importer`] by dispatching to
/// the loaded module's `extract` / `extract_enriched` entry points.
///
/// Cheap to clone — the underlying [`Engine`] and [`Module`] are
/// shared via `Arc`. A fresh wasmtime [`Store`] is created per call,
/// so concurrent extract calls don't share state.
#[derive(Clone)]
pub struct WasmImporter {
    /// Filesystem path the module was loaded from (for diagnostics).
    path: PathBuf,
    /// Module's declared name (from the cached `metadata` call).
    name: String,
    /// Module's declared description (from the cached `metadata` call).
    description: String,
    /// Compiled module.
    module: Arc<Module>,
    /// Shared wasmtime engine.
    engine: Arc<Engine>,
    /// Per-call runtime limits.
    config: WasmRuntimeConfig,
}

impl WasmImporter {
    /// Load a WASM importer from a `.wasm` file with default runtime
    /// limits.
    pub fn load(path: impl Into<PathBuf>) -> Result<Self, WasmImporterError> {
        Self::load_with_config(path, WasmRuntimeConfig::default())
    }

    /// Load a WASM importer with custom runtime limits.
    pub fn load_with_config(
        path: impl Into<PathBuf>,
        config: WasmRuntimeConfig,
    ) -> Result<Self, WasmImporterError> {
        let path = path.into();
        let bytes = std::fs::read(&path).map_err(|source| WasmImporterError::Io {
            path: path.clone(),
            source,
        })?;
        Self::load_from_bytes(path, &bytes, config)
    }

    /// Load from in-memory WASM bytes — useful for tests and embedders
    /// that ship the module inside their binary.
    pub fn load_from_bytes(
        path: impl Into<PathBuf>,
        bytes: &[u8],
        config: WasmRuntimeConfig,
    ) -> Result<Self, WasmImporterError> {
        let path = path.into();

        let mut engine_config = Config::new();
        engine_config.consume_fuel(true);
        let engine =
            Arc::new(
                Engine::new(&engine_config).map_err(|e| WasmImporterError::Compile {
                    path: path.clone(),
                    source: anyhow::Error::from(e),
                })?,
            );

        let module = Module::new(&engine, bytes).map_err(|e| WasmImporterError::Compile {
            path: path.clone(),
            source: anyhow::Error::from(e),
        })?;

        Self::validate_module(&module)?;

        let module = Arc::new(module);

        // Call `metadata` once and cache the result. Importers don't
        // change name/description across calls; this avoids paying the
        // wasmtime instantiation cost on every `name()` / `description()`.
        let metadata = call_metadata(&engine, &module, config)?;

        Ok(Self {
            path,
            name: metadata.name,
            description: metadata.description,
            module,
            engine,
            config,
        })
    }

    /// The path the module was loaded from.
    #[must_use]
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Reject imports (sandbox requirement) and check required exports.
    fn validate_module(module: &Module) -> Result<(), WasmImporterError> {
        if let Some(import) = module.imports().next() {
            return Err(WasmImporterError::ForbiddenImport {
                module: import.module().to_string(),
                name: import.name().to_string(),
            });
        }

        let exports: Vec<_> = module.exports().map(|e| e.name().to_string()).collect();
        for required in &[
            "memory",
            "alloc",
            "metadata",
            "identify",
            "extract",
            "extract_enriched",
        ] {
            if !exports.iter().any(|n| n == required) {
                return Err(WasmImporterError::MissingExport(required));
            }
        }
        Ok(())
    }

    /// Wraps a wasmtime call that takes msgpack input and returns
    /// msgpack output. The WASM module's entry-point convention:
    /// `fn (ptr: u32, len: u32) -> u64` where the return packs
    /// `(out_ptr << 32) | out_len`.
    fn call_msgpack<I: Serialize, O: DeserializeOwned>(
        &self,
        entry: &'static str,
        input: &I,
    ) -> Result<O, WasmImporterError> {
        call_msgpack_with(&self.engine, &self.module, self.config, entry, input)
    }
}

/// Create + configure a [`Store`] with both the memory limiter (so
/// `WasmRuntimeConfig::max_memory` is actually enforced) and the fuel
/// budget (so `max_time_secs` actually bounds execution).
///
/// `max_time_secs` is clamped to at least 1 so `max_time_secs = 0`
/// doesn't immediately trap the WASM call on no-fuel.
fn make_store(
    engine: &Engine,
    config: WasmRuntimeConfig,
) -> Result<Store<StoreState>, WasmImporterError> {
    let state = StoreState {
        limiter: MemoryLimiter {
            max_memory: config.max_memory,
        },
    };
    let mut store = Store::new(engine, state);
    store.limiter(|s| &mut s.limiter);
    // 1M instructions per second is the same rough budget used by the
    // directive-plugin runtime.
    let fuel = config.max_time_secs.max(1) * 1_000_000;
    store.set_fuel(fuel).map_err(runtime_err)?;
    Ok(store)
}

/// Read a packed `(out_ptr, out_len)` u64 from a WASM entry-point
/// return, validate `out_len` against [`MAX_OUTPUT_BYTES`], and copy
/// the bytes out of WASM memory.
///
/// Centralized so the cap is enforced uniformly across `metadata`,
/// `identify`, `extract`, and `extract_enriched`.
fn read_packed_output(
    store: &Store<StoreState>,
    memory: &wasmtime::Memory,
    packed: u64,
) -> Result<Vec<u8>, WasmImporterError> {
    let out_ptr = (packed >> 32) as u32;
    let out_len = (packed & 0xFFFF_FFFF) as u32 as usize;
    if out_len > MAX_OUTPUT_BYTES {
        return Err(WasmImporterError::OutputTooLarge {
            len: out_len,
            max: MAX_OUTPUT_BYTES,
        });
    }
    let mut out_bytes = vec![0u8; out_len];
    memory
        .read(store, out_ptr as usize, &mut out_bytes)
        .map_err(|e| WasmImporterError::Runtime(e.into()))?;
    Ok(out_bytes)
}

/// Free-form wasmtime call helper. Extracted from `WasmImporter`'s
/// methods so the load-time `metadata` call can use it before `self`
/// is fully constructed.
fn call_msgpack_with<I: Serialize, O: DeserializeOwned>(
    engine: &Engine,
    module: &Module,
    config: WasmRuntimeConfig,
    entry: &'static str,
    input: &I,
) -> Result<O, WasmImporterError> {
    let input_bytes = rmp_serde::to_vec(input).map_err(WasmImporterError::Encode)?;

    let mut store = make_store(engine, config)?;

    // No imports at all — full sandbox.
    let linker = Linker::new(engine);
    let instance = linker
        .instantiate(&mut store, module)
        .map_err(runtime_err)?;

    let memory = instance
        .get_memory(&mut store, "memory")
        .ok_or(WasmImporterError::MissingExport("memory"))?;

    let alloc = instance
        .get_typed_func::<u32, u32>(&mut store, "alloc")
        .map_err(|_| WasmImporterError::MissingExport("alloc"))?;

    let input_ptr = alloc
        .call(&mut store, input_bytes.len() as u32)
        .map_err(runtime_err)?;
    memory
        .write(&mut store, input_ptr as usize, &input_bytes)
        .map_err(|e| WasmImporterError::Runtime(e.into()))?;

    let func = instance
        .get_typed_func::<(u32, u32), u64>(&mut store, entry)
        .map_err(|_| WasmImporterError::MissingExport(entry))?;

    let packed = func
        .call(&mut store, (input_ptr, input_bytes.len() as u32))
        .map_err(runtime_err)?;

    let out_bytes = read_packed_output(&store, &memory, packed)?;
    rmp_serde::from_slice(&out_bytes).map_err(WasmImporterError::Decode)
}

/// Special-case helper for the no-input `metadata` entry point. The
/// WASM convention is `fn metadata() -> u64` returning the packed
/// `(ptr, len)` of msgpack-encoded [`MetadataOutput`].
fn call_metadata(
    engine: &Engine,
    module: &Module,
    config: WasmRuntimeConfig,
) -> Result<MetadataOutput, WasmImporterError> {
    let mut store = make_store(engine, config)?;

    let linker = Linker::new(engine);
    let instance = linker
        .instantiate(&mut store, module)
        .map_err(runtime_err)?;

    let memory = instance
        .get_memory(&mut store, "memory")
        .ok_or(WasmImporterError::MissingExport("memory"))?;

    let metadata = instance
        .get_typed_func::<(), u64>(&mut store, "metadata")
        .map_err(|_| WasmImporterError::MissingExport("metadata"))?;

    let packed = metadata.call(&mut store, ()).map_err(runtime_err)?;
    let out_bytes = read_packed_output(&store, &memory, packed)?;
    rmp_serde::from_slice(&out_bytes).map_err(WasmImporterError::Decode)
}

/// Flatten the host's [`ImporterConfig`] into the wire-format
/// [`ImporterInput`] expected by the WASM module. CSV-specific config
/// fields are serialized into the free-form `options` map.
fn build_wasm_input(path: &Path, content: Vec<u8>, config: &ImporterConfig) -> ImporterInput {
    let mut options = std::collections::HashMap::new();
    let ImporterType::Csv(csv) = &config.importer_type;
    project_csv_config_into_options(csv, &mut options);
    ImporterInput {
        path: path.to_string_lossy().into_owned(),
        content,
        account: config.account.clone(),
        currency: config.currency.clone(),
        options,
    }
}

/// Project CSV-specific config into the wire-format `options` map.
/// String-encoded per the ABI's String→String contract.
fn project_csv_config_into_options(
    csv: &CsvConfig,
    options: &mut std::collections::HashMap<String, String>,
) {
    options.insert("date_format".to_string(), csv.date_format.clone());
    options.insert("delimiter".to_string(), csv.delimiter.to_string());
    options.insert("has_header".to_string(), csv.has_header.to_string());
    options.insert("skip_rows".to_string(), csv.skip_rows.to_string());
    options.insert("invert_sign".to_string(), csv.invert_sign.to_string());
    options.insert(
        "skip_zero_amounts".to_string(),
        csv.skip_zero_amounts.to_string(),
    );
    if let Some(de) = &csv.default_expense {
        options.insert("default_expense".to_string(), de.clone());
    }
    if let Some(di) = &csv.default_income {
        options.insert("default_income".to_string(), di.clone());
    }
}

/// Format a [`PluginError`] into a single human-readable line that
/// preserves the severity ("error" vs "warning") and avoids orphan
/// colons when location fields are absent.
///
/// Examples:
/// - severity=Error, file="foo.csv", line=42 → `"error foo.csv:42: bad row"`
/// - severity=Warning, file="foo.csv", line=None → `"warning foo.csv: weird value"`
/// - severity=Warning, file=None, line=Some(7) → `"warning line 7: weird value"`
/// - severity=Error, file=None, line=None → `"error: parser bug"`
fn format_plugin_error(e: &PluginError) -> String {
    let severity = match e.severity {
        PluginErrorSeverity::Error => "error",
        PluginErrorSeverity::Warning => "warning",
    };
    let location = match (&e.source_file, e.line_number) {
        (Some(f), Some(n)) => format!(" {f}:{n}"),
        (Some(f), None) => format!(" {f}"),
        (None, Some(n)) => format!(" line {n}"),
        (None, None) => String::new(),
    };
    format!("{severity}{location}: {}", e.message)
}

/// Materialize an [`ImporterOutput`] wire-format value back to the
/// host-side [`ImportResult`]. Reuses
/// `rustledger_plugin::convert::wrapper_to_directive` semantics —
/// duplicated here so this crate doesn't need to depend on the full
/// `rustledger-plugin` graph just for the converter.
fn output_to_import_result(out: ImporterOutput) -> anyhow::Result<ImportResult> {
    let mut directives = Vec::with_capacity(out.directives.len());
    for w in out.directives {
        // Reuse the canonical conversion path. NOTE: this is the same
        // converter the directive plugins use, so any improvements
        // there land here too.
        let d = rustledger_plugin::convert::wrapper_to_directive(&w)
            .map_err(|e| anyhow::anyhow!("WASM importer returned invalid directive: {e:?}"))?;
        directives.push(d);
    }
    let mut result = ImportResult::new(directives);
    for w in out.warnings {
        result = result.with_warning(w);
    }
    // Errors and warnings flow through the same `warnings` channel,
    // but the formatted string preserves the severity prefix so a
    // fatal-but-recoverable importer error is still distinguishable
    // from informational chatter. The structured error path
    // (`LedgerError::location`) is reserved for the loader layer.
    for e in &out.errors {
        result = result.with_warning(format_plugin_error(e));
    }
    Ok(result)
}

impl Importer for WasmImporter {
    fn name(&self) -> &str {
        &self.name
    }

    fn description(&self) -> &str {
        &self.description
    }

    fn identify(&self, path: &Path) -> bool {
        let input = IdentifyInput {
            path: path.to_string_lossy().into_owned(),
        };
        // identify() failures (trap, decode error) conservatively return
        // false — the registry treats this as "this importer doesn't
        // handle the file" and falls back to the next candidate.
        match self.call_msgpack::<_, IdentifyOutput>("identify", &input) {
            Ok(out) => out.matches,
            Err(_) => false,
        }
    }

    fn extract(&self, path: &Path, config: &ImporterConfig) -> anyhow::Result<ImportResult> {
        let content = std::fs::read(path)
            .map_err(|e| anyhow::anyhow!("failed to read {}: {e}", path.display()))?;
        let input = build_wasm_input(path, content, config);
        let output: ImporterOutput = self.call_msgpack("extract", &input)?;
        output_to_import_result(output)
    }

    fn extract_enriched(
        &self,
        path: &Path,
        config: &ImporterConfig,
    ) -> anyhow::Result<EnrichedImportResult> {
        let content = std::fs::read(path)
            .map_err(|e| anyhow::anyhow!("failed to read {}: {e}", path.display()))?;
        let input = build_wasm_input(path, content, config);
        let output: EnrichedImporterOutput = self.call_msgpack("extract_enriched", &input)?;
        bridge_enriched_output(output)
    }
}

/// Bridge a wire-format [`EnrichedImporterOutput`] into the host's
/// [`EnrichedImportResult`]. Extracted as a free function so the lossy
/// paths (unknown method strings, malformed fingerprint hex) can be
/// unit-tested without standing up wasmtime.
///
/// # Warning ordering
///
/// Warnings are emitted in this order, which is part of the contract
/// for any downstream consumer that filters or surfaces them:
///
/// 1. **Bridge warnings** (per-entry lossy paths: unknown method,
///    malformed fingerprint hex) — host-side issues with the wire
///    data, surface first so the importer author sees them prominently.
/// 2. **Output warnings** (importer's own informational warnings),
///    forwarded verbatim from `output.warnings`.
/// 3. **Output errors** (importer's structured errors), formatted via
///    [`format_plugin_error`] which preserves severity prefix.
fn bridge_enriched_output(output: EnrichedImporterOutput) -> anyhow::Result<EnrichedImportResult> {
    let mut entries = Vec::with_capacity(output.entries.len());
    let mut bridge_warnings: Vec<String> = Vec::new();
    for (wrapper, enr) in output.entries {
        let dir = rustledger_plugin::convert::wrapper_to_directive(&wrapper)
            .map_err(|e| anyhow::anyhow!("WASM importer returned invalid directive: {e:?}"))?;
        let method = parse_method(&enr.method).unwrap_or_else(|unknown| {
            bridge_warnings.push(format!(
                "warning: WASM importer used unknown categorization method `{unknown}`, falling back to Default"
            ));
            rustledger_ops::enrichment::CategorizationMethod::Default
        });
        let alternatives = enr
            .alternatives
            .into_iter()
            .map(|a| {
                let alt_method = parse_method(&a.method).unwrap_or_else(|unknown| {
                    bridge_warnings.push(format!(
                        "warning: WASM importer used unknown categorization method `{unknown}` in alternative, falling back to Default"
                    ));
                    rustledger_ops::enrichment::CategorizationMethod::Default
                });
                rustledger_ops::enrichment::Alternative {
                    account: a.account,
                    confidence: a.confidence,
                    method: alt_method,
                }
            })
            .collect();
        let fingerprint = match enr.fingerprint {
            Some(hex) => match Fingerprint::from_hex(&hex) {
                Ok(fp) => Some(fp),
                Err(e) => {
                    bridge_warnings.push(format!(
                        "warning: WASM importer returned malformed fingerprint hex `{hex}`: {e}"
                    ));
                    None
                }
            },
            None => None,
        };
        let enrichment = rustledger_ops::enrichment::Enrichment {
            directive_index: enr.directive_index,
            confidence: enr.confidence,
            method,
            alternatives,
            fingerprint,
        };
        entries.push((dir, enrichment));
    }
    let mut enriched = EnrichedImportResult::new(entries);
    for w in bridge_warnings {
        enriched = enriched.with_warning(w);
    }
    for w in output.warnings {
        enriched = enriched.with_warning(w);
    }
    for e in &output.errors {
        enriched = enriched.with_warning(format_plugin_error(e));
    }
    Ok(enriched)
}

/// Convert the wire-format method string (as emitted by
/// `CategorizationMethod::as_meta_value`) back into the host enum.
///
/// Returns `Err(unknown)` for strings the host doesn't recognize — the
/// caller is expected to surface a warning and fall back to
/// [`CategorizationMethod::Default`]. We don't silently absorb unknown
/// strings here: a typo like `"merchant_dict"` vs `"merchant-dict"`
/// (the exact Copilot-flagged bug from #1130) would otherwise degrade
/// data without any signal to the user.
fn parse_method(s: &str) -> Result<rustledger_ops::enrichment::CategorizationMethod, &str> {
    use rustledger_ops::enrichment::CategorizationMethod;
    match s {
        "rule" => Ok(CategorizationMethod::Rule),
        "merchant-dict" => Ok(CategorizationMethod::MerchantDict),
        "ml" => Ok(CategorizationMethod::Ml),
        "llm" => Ok(CategorizationMethod::Llm),
        "manual" => Ok(CategorizationMethod::Manual),
        "default" => Ok(CategorizationMethod::Default),
        unknown => Err(unknown),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wasm_runtime_config_default_is_sensible() {
        let c = WasmRuntimeConfig::default();
        assert_eq!(c.max_memory, 256 * 1024 * 1024);
        assert_eq!(c.max_time_secs, 30);
    }

    #[test]
    fn validate_module_rejects_module_with_imports() {
        // A WAT module with a single import — should be rejected.
        let wat = r#"
            (module
                (import "env" "ext" (func $ext))
                (memory (export "memory") 1)
                (func (export "alloc") (param i32) (result i32) i32.const 0)
                (func (export "metadata") (result i64) i64.const 0)
                (func (export "identify") (param i32 i32) (result i64) i64.const 0)
                (func (export "extract") (param i32 i32) (result i64) i64.const 0)
                (func (export "extract_enriched") (param i32 i32) (result i64) i64.const 0)
            )
        "#;
        let bytes = wat::parse_str(wat).expect("WAT parses");
        let mut engine_config = Config::new();
        engine_config.consume_fuel(true);
        let engine = Engine::new(&engine_config).unwrap();
        let module = Module::new(&engine, &bytes).unwrap();
        let err = WasmImporter::validate_module(&module).unwrap_err();
        assert!(matches!(err, WasmImporterError::ForbiddenImport { .. }));
    }

    #[test]
    fn validate_module_rejects_missing_export() {
        // Has memory + alloc + metadata but missing identify/extract/extract_enriched.
        let wat = r#"
            (module
                (memory (export "memory") 1)
                (func (export "alloc") (param i32) (result i32) i32.const 0)
                (func (export "metadata") (result i64) i64.const 0)
            )
        "#;
        let bytes = wat::parse_str(wat).expect("WAT parses");
        let mut engine_config = Config::new();
        engine_config.consume_fuel(true);
        let engine = Engine::new(&engine_config).unwrap();
        let module = Module::new(&engine, &bytes).unwrap();
        let err = WasmImporter::validate_module(&module).unwrap_err();
        assert!(matches!(err, WasmImporterError::MissingExport(_)));
    }

    #[test]
    fn parse_method_round_trips_known_values() {
        use rustledger_ops::enrichment::CategorizationMethod;
        assert!(matches!(
            parse_method("rule"),
            Ok(CategorizationMethod::Rule)
        ));
        assert!(matches!(
            parse_method("merchant-dict"),
            Ok(CategorizationMethod::MerchantDict)
        ));
        assert!(matches!(parse_method("ml"), Ok(CategorizationMethod::Ml)));
        assert!(matches!(parse_method("llm"), Ok(CategorizationMethod::Llm)));
        assert!(matches!(
            parse_method("manual"),
            Ok(CategorizationMethod::Manual)
        ));
        assert!(matches!(
            parse_method("default"),
            Ok(CategorizationMethod::Default)
        ));
    }

    #[test]
    fn parse_method_round_trips_via_as_meta_value() {
        // Pin the contract: every `CategorizationMethod` round-trips
        // through its `as_meta_value()` string. If a host variant is
        // added without updating `parse_method`, this test fails.
        use rustledger_ops::enrichment::CategorizationMethod;
        for m in [
            CategorizationMethod::Rule,
            CategorizationMethod::MerchantDict,
            CategorizationMethod::Ml,
            CategorizationMethod::Llm,
            CategorizationMethod::Manual,
            CategorizationMethod::Default,
        ] {
            let s = m.as_meta_value();
            let parsed = parse_method(s)
                .unwrap_or_else(|u| panic!("as_meta_value `{u}` not handled by parse_method"));
            assert_eq!(parsed, m, "round-trip failed for {m:?}");
        }
    }

    #[test]
    fn parse_method_unknown_surfaces_the_unknown_string() {
        // Previously: silently fell back to Default. Now: returns
        // Err(unknown) so the caller can warn — protects against
        // typos like `merchant_dict` (underscore) vs `merchant-dict`
        // (hyphen, the actual wire encoding from
        // `CategorizationMethod::as_meta_value`).
        assert_eq!(parse_method("future-method"), Err("future-method"));
        assert_eq!(parse_method("merchant_dict"), Err("merchant_dict"));
        assert_eq!(parse_method(""), Err(""));
    }

    #[test]
    fn format_plugin_error_with_full_location() {
        let e = PluginError::error("bad row").at("foo.csv", 42);
        assert_eq!(format_plugin_error(&e), "error foo.csv:42: bad row");
    }

    #[test]
    fn format_plugin_error_warning_severity() {
        let e = PluginError::warning("weird value").at("foo.csv", 42);
        assert_eq!(format_plugin_error(&e), "warning foo.csv:42: weird value");
    }

    #[test]
    fn format_plugin_error_no_location_no_orphan_colon() {
        let e = PluginError::error("parser bug");
        // Previously: ": parser bug" (orphan colon). Now: "error: parser bug".
        assert_eq!(format_plugin_error(&e), "error: parser bug");
    }

    #[test]
    fn format_plugin_error_file_only() {
        let e = PluginError::warning("weird value");
        let e = PluginError {
            source_file: Some("foo.csv".to_string()),
            ..e
        };
        assert_eq!(format_plugin_error(&e), "warning foo.csv: weird value");
    }

    #[test]
    fn format_plugin_error_line_only_uses_human_phrasing() {
        // Previously: ":42: weird" (orphan colon). Now: "warning line 42: weird".
        let e = PluginError::warning("weird");
        let e = PluginError {
            line_number: Some(42),
            ..e
        };
        assert_eq!(format_plugin_error(&e), "warning line 42: weird");
    }

    /// Build a WAT module that pre-loads `MessagePack` outputs for every
    /// entry point in low memory and returns hardcoded packed
    /// `(ptr, len)` u64s. `alloc` is a bump allocator starting at
    /// offset 1024, so host-allocated input never overlaps the
    /// pre-loaded data.
    ///
    /// Wire-format bytes are rmp-serde's default positional encoding
    /// (struct → fixarray-N, fields in declaration order).
    fn roundtrip_wat() -> &'static str {
        r#"
        (module
            (memory (export "memory") 1)

            ;; MetadataOutput { name: "tst", description: "tst" }
            ;; 0x92 fixarray-2, 0xa3 fixstr-3 "tst", 0xa3 fixstr-3 "tst"
            (data (i32.const 0) "\92\a3tst\a3tst")

            ;; IdentifyOutput { matches: true }
            ;; 0x91 fixarray-1, 0xc3 true
            (data (i32.const 16) "\91\c3")

            ;; ImporterOutput { directives: [], warnings: [], errors: [] }
            ;; 0x93 fixarray-3, then three 0x90 fixarray-0
            (data (i32.const 24) "\93\90\90\90")

            ;; EnrichedImporterOutput { entries: [], warnings: [], errors: [] }
            (data (i32.const 32) "\93\90\90\90")

            ;; bump allocator: hand out at $bump, advance by $size.
            ;; NOTE: real importers MUST bounds-check $bump+$size
            ;; against current memory and call `memory.grow` (subject
            ;; to MemoryLimiter approval). This test fixture skips
            ;; that — inputs in the test are small and we declare 1
            ;; full page (64 KiB), so the bump never crosses the
            ;; boundary.
            (global $bump (mut i32) (i32.const 1024))
            (func (export "alloc") (param $size i32) (result i32)
                (local $ret i32)
                global.get $bump
                local.set $ret
                global.get $bump
                local.get $size
                i32.add
                global.set $bump
                local.get $ret)

            ;; metadata: ptr=0, len=9 → (0<<32) | 9 = 9
            (func (export "metadata") (result i64)
                i64.const 9)

            ;; identify: ptr=16, len=2 → (16<<32) | 2
            (func (export "identify") (param i32 i32) (result i64)
                i64.const 0x10_0000_0002)

            ;; extract: ptr=24, len=4 → (24<<32) | 4
            (func (export "extract") (param i32 i32) (result i64)
                i64.const 0x18_0000_0004)

            ;; extract_enriched: ptr=32, len=4 → (32<<32) | 4
            (func (export "extract_enriched") (param i32 i32) (result i64)
                i64.const 0x20_0000_0004)
        )
        "#
    }

    fn minimal_config() -> ImporterConfig {
        ImporterConfig {
            account: "Assets:Bank:Checking".to_string(),
            currency: Some("USD".to_string()),
            importer_type: ImporterType::Csv(CsvConfig::default()),
        }
    }

    #[test]
    fn end_to_end_wat_module_round_trips_all_entry_points() {
        let bytes = wat::parse_str(roundtrip_wat()).expect("WAT parses");
        let importer = WasmImporter::load_from_bytes(
            PathBuf::from("test.wasm"),
            &bytes,
            WasmRuntimeConfig::default(),
        )
        .expect("module loads + metadata round-trips");

        // metadata was decoded once at load and cached for these
        // accessors — proves the MetadataOutput msgpack flowed end to
        // end through the host.
        assert_eq!(importer.name(), "tst");
        assert_eq!(importer.description(), "tst");

        // identify round-trip — input ignored, module hardcodes true.
        assert!(importer.identify(Path::new("anything.csv")));

        // extract + extract_enriched need a real file for std::fs::read.
        let tmp = tempfile::NamedTempFile::new().expect("tempfile");
        let config = minimal_config();

        let result = importer
            .extract(tmp.path(), &config)
            .expect("extract round-trip");
        assert!(result.directives.is_empty());
        assert!(result.warnings.is_empty());

        let enriched = importer
            .extract_enriched(tmp.path(), &config)
            .expect("extract_enriched round-trip");
        assert!(enriched.entries.is_empty());
        assert!(enriched.warnings.is_empty());
    }

    #[test]
    fn oversized_output_is_rejected_before_allocation() {
        // Module's metadata() returns out_len = u32::MAX. Without the
        // MAX_OUTPUT_BYTES check, the host would attempt a ~4 GiB Vec
        // allocation. The check should catch it during load.
        let wat = r#"
            (module
                (memory (export "memory") 1)
                (func (export "alloc") (param i32) (result i32) i32.const 0)
                ;; metadata: ptr=0, len=u32::MAX
                (func (export "metadata") (result i64)
                    i64.const 0x0000_0000_ffff_ffff)
                (func (export "identify") (param i32 i32) (result i64) i64.const 0)
                (func (export "extract") (param i32 i32) (result i64) i64.const 0)
                (func (export "extract_enriched") (param i32 i32) (result i64) i64.const 0)
            )
        "#;
        let bytes = wat::parse_str(wat).expect("WAT parses");
        // Can't use `.expect_err(...)` here — `WasmImporter` doesn't
        // implement `Debug` (the wasmtime `Module`/`Engine` it holds
        // aren't trivially debuggable), so we destructure manually.
        let Err(err) = WasmImporter::load_from_bytes(
            PathBuf::from("oversized.wasm"),
            &bytes,
            WasmRuntimeConfig::default(),
        ) else {
            panic!("oversized metadata output should have been rejected at load");
        };
        assert!(
            matches!(
                err,
                WasmImporterError::OutputTooLarge { len, max }
                    if len == u32::MAX as usize && max == MAX_OUTPUT_BYTES
            ),
            "expected OutputTooLarge, got {err:?}"
        );
    }

    #[test]
    fn memory_limiter_rejects_grow_above_max() {
        // Pin the ResourceLimiter behavior directly. The full
        // wasm.grow → trap path is wasmtime-internal and hard to
        // observe without a custom module, so this test guards the
        // bit we own: that memory_growing returns Ok(false) past the
        // cap.
        let mut limiter = MemoryLimiter { max_memory: 1024 };
        assert!(
            limiter
                .memory_growing(0, 512, None)
                .expect("under cap is Ok")
        ); // under cap
        assert!(limiter.memory_growing(0, 1024, None).expect("at cap is Ok")); // exactly at cap
        assert!(
            !limiter
                .memory_growing(0, 1025, None)
                .expect("over cap is Ok(false)")
        ); // over cap
    }

    #[test]
    fn zero_max_time_secs_does_not_starve_fuel() {
        // Regression: previously fuel = 0 * 1_000_000 = 0, causing
        // immediate trap on first instruction. Now clamped via
        // .max(1) so a 0 config still gets enough fuel to complete a
        // trivial call.
        let config = WasmRuntimeConfig {
            max_memory: 256 * 1024 * 1024,
            max_time_secs: 0,
        };
        let bytes = wat::parse_str(roundtrip_wat()).expect("WAT parses");
        // Loading calls metadata(), which is a single i64.const +
        // return — well under 1M instructions.
        let importer = WasmImporter::load_from_bytes(PathBuf::from("test.wasm"), &bytes, config)
            .expect("zero max_time_secs is clamped, not starved");
        assert_eq!(importer.name(), "tst");
    }

    #[test]
    fn table_limiter_rejects_grow_above_max() {
        let mut limiter = MemoryLimiter {
            max_memory: usize::MAX,
        };
        assert!(
            limiter
                .table_growing(0, MAX_TABLE_ELEMENTS, None)
                .expect("at cap is Ok")
        );
        assert!(
            !limiter
                .table_growing(0, MAX_TABLE_ELEMENTS + 1, None)
                .expect("over cap is Ok(false)")
        );
    }

    #[test]
    fn initial_memory_above_cap_is_rejected_via_limiter_wiring() {
        // Pins the `store.limiter(|s| &mut s.limiter)` wiring against
        // refactor regression. wasmtime calls `memory_growing` for
        // both initial allocation and grow — a module declaring 5000
        // pages (320 MiB) initial memory with a 64 MiB cap should
        // fail to instantiate. If the limiter wiring breaks, this
        // test catches it (the direct trait-method test above does
        // not).
        let wat = r#"
            (module
                (memory (export "memory") 5000)
                (func (export "alloc") (param i32) (result i32) i32.const 0)
                (func (export "metadata") (result i64) i64.const 0)
                (func (export "identify") (param i32 i32) (result i64) i64.const 0)
                (func (export "extract") (param i32 i32) (result i64) i64.const 0)
                (func (export "extract_enriched") (param i32 i32) (result i64) i64.const 0)
            )
        "#;
        let bytes = wat::parse_str(wat).expect("WAT parses");
        let config = WasmRuntimeConfig {
            max_memory: 64 * 1024 * 1024,
            max_time_secs: 30,
        };
        let Err(err) = WasmImporter::load_from_bytes(PathBuf::from("bigmem.wasm"), &bytes, config)
        else {
            panic!("module declaring 320 MiB initial memory should be rejected with 64 MiB cap");
        };
        // wasmtime turns Ok(false) at instantiation into an instantiate
        // error, which the host maps to Runtime.
        assert!(
            matches!(err, WasmImporterError::Runtime(_)),
            "expected Runtime (instantiate failed via limiter), got {err:?}"
        );
    }

    // ===== bridge_enriched_output direct tests =====
    //
    // These exercise the lossy paths (unknown method, malformed
    // fingerprint hex, valid fingerprint round-trip) without standing
    // up wasmtime — the bridge logic is the testable piece, the
    // wasmtime round-trip is covered by the end-to-end WAT test.

    use rustledger_plugin_types::{
        AlternativeWrapper, DirectiveData, DirectiveWrapper, EnrichmentWrapper, OpenData,
    };

    fn open_wrapper(account: &str) -> DirectiveWrapper {
        DirectiveWrapper {
            directive_type: String::new(),
            date: "2024-01-01".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Open(OpenData {
                account: account.to_string(),
                currencies: vec![],
                booking: None,
                metadata: vec![],
            }),
        }
    }

    fn enrichment_wrapper(method: &str, fingerprint: Option<String>) -> EnrichmentWrapper {
        EnrichmentWrapper {
            directive_index: 0,
            confidence: 1.0,
            method: method.to_string(),
            alternatives: vec![],
            fingerprint,
        }
    }

    #[test]
    fn bridge_round_trips_valid_fingerprint_hex() {
        let fp = Fingerprint::compute("2024-01-01", Some("100"), "coffee");
        let hex = fp.to_hex();
        let out = EnrichedImporterOutput {
            entries: vec![(
                open_wrapper("Assets:Bank"),
                enrichment_wrapper("rule", Some(hex)),
            )],
            warnings: vec![],
            errors: vec![],
        };
        let bridged = bridge_enriched_output(out).expect("bridge succeeds");
        assert_eq!(bridged.entries.len(), 1);
        assert_eq!(
            bridged.entries[0].1.fingerprint,
            Some(fp),
            "fingerprint should round-trip"
        );
        assert!(bridged.warnings.is_empty(), "no warnings expected");
    }

    #[test]
    fn bridge_warns_on_malformed_fingerprint_hex_and_drops_to_none() {
        let out = EnrichedImporterOutput {
            entries: vec![(
                open_wrapper("Assets:Bank"),
                enrichment_wrapper("rule", Some("not-a-valid-hex".to_string())),
            )],
            warnings: vec![],
            errors: vec![],
        };
        let bridged = bridge_enriched_output(out).expect("bridge succeeds");
        assert_eq!(bridged.entries.len(), 1);
        assert_eq!(bridged.entries[0].1.fingerprint, None);
        // Warning text names the bad hex so the importer author can
        // find the bug quickly.
        assert_eq!(bridged.warnings.len(), 1);
        assert!(
            bridged.warnings[0].contains("not-a-valid-hex"),
            "warning should name the bad hex: {}",
            bridged.warnings[0]
        );
    }

    #[test]
    fn bridge_warns_on_unknown_method_and_falls_back_to_default() {
        use rustledger_ops::enrichment::CategorizationMethod;
        let out = EnrichedImporterOutput {
            entries: vec![(
                open_wrapper("Assets:Bank"),
                enrichment_wrapper("merchant_dict", None), // underscore typo, exact #1130 bug shape
            )],
            warnings: vec![],
            errors: vec![],
        };
        let bridged = bridge_enriched_output(out).expect("bridge succeeds");
        assert_eq!(bridged.entries[0].1.method, CategorizationMethod::Default);
        assert_eq!(bridged.warnings.len(), 1);
        assert!(
            bridged.warnings[0].contains("merchant_dict"),
            "warning should name the unknown method: {}",
            bridged.warnings[0]
        );
    }

    #[test]
    fn bridge_warns_on_unknown_method_in_alternative() {
        use rustledger_ops::enrichment::CategorizationMethod;
        let mut enr = enrichment_wrapper("rule", None);
        enr.alternatives = vec![AlternativeWrapper {
            account: "Expenses:Other".to_string(),
            confidence: 0.3,
            method: "future-method".to_string(),
        }];
        let out = EnrichedImporterOutput {
            entries: vec![(open_wrapper("Assets:Bank"), enr)],
            warnings: vec![],
            errors: vec![],
        };
        let bridged = bridge_enriched_output(out).expect("bridge succeeds");
        let alt = &bridged.entries[0].1.alternatives[0];
        assert_eq!(alt.method, CategorizationMethod::Default);
        assert_eq!(bridged.warnings.len(), 1);
        assert!(bridged.warnings[0].contains("future-method"));
        assert!(
            bridged.warnings[0].contains("alternative"),
            "warning should distinguish the alternative slot: {}",
            bridged.warnings[0]
        );
    }

    #[test]
    fn bridge_warning_ordering_is_bridge_then_output_warnings_then_errors() {
        // Pins the warning-emission order documented on
        // `bridge_enriched_output`. Order matters for downstream
        // consumers that filter or surface them.
        let out = EnrichedImporterOutput {
            entries: vec![(
                open_wrapper("Assets:Bank"),
                enrichment_wrapper("nonsense", None),
            )],
            warnings: vec!["informational warning".to_string()],
            errors: vec![PluginError::error("structured error").at("foo.csv", 7)],
        };
        let bridged = bridge_enriched_output(out).expect("bridge succeeds");
        assert_eq!(bridged.warnings.len(), 3);
        assert!(
            bridged.warnings[0].contains("nonsense"),
            "first: bridge warning, got {}",
            bridged.warnings[0]
        );
        assert_eq!(
            bridged.warnings[1], "informational warning",
            "second: output.warnings forwarded verbatim"
        );
        assert_eq!(
            bridged.warnings[2], "error foo.csv:7: structured error",
            "third: output.errors via format_plugin_error"
        );
    }

    #[test]
    fn output_to_import_result_uses_severity_aware_formatter() {
        // Integration test: proves format_plugin_error is actually
        // wired into the production path, not just unit-tested in
        // isolation. A refactor that switches back to raw format!()
        // would regress this.
        let out = ImporterOutput {
            directives: vec![],
            warnings: vec!["plain warning".to_string()],
            errors: vec![
                PluginError::error("bad row").at("foo.csv", 42),
                PluginError::warning("weird value"),
            ],
        };
        let result = output_to_import_result(out).expect("succeeds");
        assert_eq!(
            result.warnings,
            vec![
                "plain warning".to_string(),
                "error foo.csv:42: bad row".to_string(),
                "warning: weird value".to_string(),
            ]
        );
    }
}
