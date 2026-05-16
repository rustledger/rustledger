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

use rustledger_plugin_types::{
    EnrichedImporterOutput, IdentifyInput, IdentifyOutput, ImporterInput, ImporterOutput,
    MetadataOutput,
};
use serde::{Serialize, de::DeserializeOwned};
use wasmtime::{Config, Engine, Linker, Module, Store};

use crate::config::{CsvConfig, ImporterType};
use crate::{EnrichedImportResult, ImportResult, Importer, ImporterConfig};

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

    let mut store = Store::new(engine, ());
    // 1M instructions per second is the same rough budget used by the
    // directive-plugin runtime.
    let fuel = config.max_time_secs * 1_000_000;
    store.set_fuel(fuel).map_err(runtime_err)?;

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

    let out_ptr = (packed >> 32) as u32;
    let out_len = (packed & 0xFFFF_FFFF) as u32;

    let mut out_bytes = vec![0u8; out_len as usize];
    memory
        .read(&store, out_ptr as usize, &mut out_bytes)
        .map_err(|e| WasmImporterError::Runtime(e.into()))?;

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
    let mut store = Store::new(engine, ());
    let fuel = config.max_time_secs * 1_000_000;
    store.set_fuel(fuel).map_err(runtime_err)?;

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

    let out_ptr = (packed >> 32) as u32;
    let out_len = (packed & 0xFFFF_FFFF) as u32;

    let mut out_bytes = vec![0u8; out_len as usize];
    memory
        .read(&store, out_ptr as usize, &mut out_bytes)
        .map_err(|e| WasmImporterError::Runtime(e.into()))?;

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
    // Errors are non-fatal at this layer — surface them as warnings so
    // the existing extract pipeline doesn't need a new error channel.
    // The structured error path goes through LedgerError in the loader.
    for e in out.errors {
        result = result.with_warning(format!(
            "{}{}: {}",
            e.source_file.unwrap_or_default(),
            e.line_number.map(|n| format!(":{n}")).unwrap_or_default(),
            e.message
        ));
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

        // Bridge from wire-format EnrichedImporterOutput to the
        // host-side EnrichedImportResult. The enrichment-wrapper →
        // host-Enrichment conversion is intentionally lossy on
        // `method` (string → enum): unknown methods fall back to
        // `Default` rather than failing the whole import.
        let mut entries = Vec::with_capacity(output.entries.len());
        for (wrapper, enr) in output.entries {
            let dir = rustledger_plugin::convert::wrapper_to_directive(&wrapper)
                .map_err(|e| anyhow::anyhow!("WASM importer returned invalid directive: {e:?}"))?;
            let enrichment = rustledger_ops::enrichment::Enrichment {
                directive_index: enr.directive_index,
                confidence: enr.confidence,
                method: parse_method(&enr.method),
                alternatives: enr
                    .alternatives
                    .into_iter()
                    .map(|a| rustledger_ops::enrichment::Alternative {
                        account: a.account,
                        confidence: a.confidence,
                        method: parse_method(&a.method),
                    })
                    .collect(),
                fingerprint: None, // Fingerprint round-trip via hex string is wave 2.3+
            };
            entries.push((dir, enrichment));
        }
        let mut enriched = EnrichedImportResult::new(entries);
        for w in output.warnings {
            enriched = enriched.with_warning(w);
        }
        for e in output.errors {
            enriched = enriched.with_warning(format!(
                "{}{}: {}",
                e.source_file.unwrap_or_default(),
                e.line_number.map(|n| format!(":{n}")).unwrap_or_default(),
                e.message
            ));
        }
        Ok(enriched)
    }
}

/// Convert the wire-format method string (as emitted by
/// `CategorizationMethod::as_meta_value`) back into the host enum.
/// Unknown strings fall back to `Default` so a future addition to the
/// host enum doesn't break older WASM importers.
fn parse_method(s: &str) -> rustledger_ops::enrichment::CategorizationMethod {
    use rustledger_ops::enrichment::CategorizationMethod;
    match s {
        "rule" => CategorizationMethod::Rule,
        "merchant-dict" => CategorizationMethod::MerchantDict,
        "ml" => CategorizationMethod::Ml,
        "llm" => CategorizationMethod::Llm,
        "manual" => CategorizationMethod::Manual,
        _ => CategorizationMethod::Default,
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
    fn parse_method_unknown_falls_back_to_default() {
        use rustledger_ops::enrichment::CategorizationMethod;
        assert!(matches!(parse_method("rule"), CategorizationMethod::Rule));
        assert!(matches!(
            parse_method("merchant-dict"),
            CategorizationMethod::MerchantDict
        ));
        // Forward-compat: a WASM importer emitting a method this host
        // doesn't know about gets Default rather than a failed import.
        assert!(matches!(
            parse_method("future-method"),
            CategorizationMethod::Default
        ));
    }
}
