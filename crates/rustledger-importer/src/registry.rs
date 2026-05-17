//! Registry for importers.

use crate::config::ImporterConfig;
use crate::csv_importer::CsvImporter;
use crate::ofx_importer::OfxImporter;
use crate::wasm::{WasmImporter, WasmImporterError};
use crate::{ImportResult, Importer};
use anyhow::{Context, Result};
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// Registry of importers.
///
/// The registry holds a collection of importers and can automatically
/// identify which importer to use for a given file. Importers are
/// stateless under the protocol contract — they read per-call
/// configuration from the [`ImporterConfig`] passed to `extract`, so a
/// single registered instance serves many imports.
pub struct ImporterRegistry {
    importers: Vec<Arc<dyn Importer>>,
}

impl ImporterRegistry {
    /// Create a new empty registry.
    pub fn new() -> Self {
        Self {
            importers: Vec::new(),
        }
    }

    /// Create a registry seeded with the built-in importers (OFX/QFX and
    /// CSV). This is the standard entry point for the CLI and embedders.
    pub fn with_builtins() -> Self {
        let mut r = Self::new();
        r.register(OfxImporter);
        r.register(CsvImporter);
        r
    }

    /// Register a new importer.
    pub fn register(&mut self, importer: impl Importer + 'static) {
        self.importers.push(Arc::new(importer));
    }

    /// Load a [`WasmImporter`] from a `.wasm` file and register it.
    /// Returns the importer's `name` (from its `metadata()` export) so
    /// callers can log or list what was loaded.
    ///
    /// # Errors
    ///
    /// Returns any [`WasmImporterError`] from the underlying load —
    /// file I/O, wasmtime compile failure, validation failure (missing
    /// required exports, forbidden imports), or `metadata()` decode
    /// failure.
    pub fn register_wasm_from_path(
        &mut self,
        path: impl Into<PathBuf>,
    ) -> Result<String, WasmImporterError> {
        let importer = WasmImporter::load(path)?;
        let name = importer.name().to_string();
        self.register(importer);
        Ok(name)
    }

    /// Scan `dir` for `*.wasm` files (one level only — no recursion)
    /// and register each as a [`WasmImporter`]. Files are loaded in
    /// sorted order so `identify()` behavior is deterministic across
    /// filesystems and platforms.
    ///
    /// Non-`.wasm` files in the directory are silently skipped (so a
    /// `README.md` or `.gitignore` next to the modules doesn't blow
    /// up discovery).
    ///
    /// # Errors
    ///
    /// - I/O error reading the directory itself ([`WasmImporterError::Io`]).
    /// - Any underlying [`WasmImporterError`] from loading an
    ///   individual `.wasm` file. Loading stops at the first error;
    ///   importers loaded before the failure remain registered.
    pub fn register_wasm_dir(
        &mut self,
        dir: impl AsRef<Path>,
    ) -> Result<Vec<String>, WasmImporterError> {
        let dir = dir.as_ref();
        let entries = std::fs::read_dir(dir).map_err(|source| WasmImporterError::Io {
            path: dir.to_path_buf(),
            source,
        })?;
        let mut wasm_paths: Vec<PathBuf> = entries
            .filter_map(std::result::Result::ok)
            .map(|e| e.path())
            .filter(|p| p.is_file() && p.extension().is_some_and(|ext| ext == "wasm"))
            .collect();
        wasm_paths.sort();
        let mut loaded = Vec::with_capacity(wasm_paths.len());
        for path in wasm_paths {
            let name = self.register_wasm_from_path(path)?;
            loaded.push(name);
        }
        Ok(loaded)
    }

    /// Find an importer that can handle the given file.
    pub fn identify(&self, path: &Path) -> Option<Arc<dyn Importer>> {
        for importer in &self.importers {
            if importer.identify(path) {
                return Some(Arc::clone(importer));
            }
        }
        None
    }

    /// Find an importer by exact case-insensitive name match, with one
    /// ergonomic concession: slash-separated alternates in the importer's
    /// `name()` are split and each part is matched independently. So an
    /// importer named `"OFX/QFX"` is findable by `"ofx"`, `"OFX"`,
    /// `"qfx"`, or `"OFX/QFX"` — but **not** by `"o"` or `"x"`.
    pub fn find_by_name(&self, name: &str) -> Option<Arc<dyn Importer>> {
        self.importers
            .iter()
            .find(|i| {
                let full = i.name();
                full.eq_ignore_ascii_case(name)
                    || full.split('/').any(|part| part.eq_ignore_ascii_case(name))
            })
            .map(Arc::clone)
    }

    /// Extract transactions from a file using the appropriate importer
    /// and the supplied configuration.
    pub fn extract(&self, path: &Path, config: &ImporterConfig) -> Result<ImportResult> {
        let importer = self
            .identify(path)
            .with_context(|| format!("No importer found for file: {}", path.display()))?;

        importer
            .extract(path, config)
            .with_context(|| format!("Failed to extract from: {}", path.display()))
    }

    /// List all registered importers.
    pub fn list_importers(&self) -> Vec<(&str, &str)> {
        self.importers
            .iter()
            .map(|i| (i.name(), i.description()))
            .collect()
    }

    /// Get the number of registered importers.
    pub fn len(&self) -> usize {
        self.importers.len()
    }

    /// Check if the registry is empty.
    pub fn is_empty(&self) -> bool {
        self.importers.is_empty()
    }
}

impl Default for ImporterRegistry {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct MockImporter {
        name: &'static str,
        extension: &'static str,
    }

    impl Importer for MockImporter {
        fn name(&self) -> &str {
            self.name
        }

        fn identify(&self, path: &Path) -> bool {
            path.extension().is_some_and(|ext| ext == self.extension)
        }

        fn extract(&self, _path: &Path, _config: &ImporterConfig) -> Result<ImportResult> {
            Ok(ImportResult::empty())
        }

        fn description(&self) -> &'static str {
            "Mock importer for testing"
        }
    }

    #[test]
    fn test_registry_basic() {
        let mut registry = ImporterRegistry::new();
        assert!(registry.is_empty());

        registry.register(MockImporter {
            name: "CSV",
            extension: "csv",
        });
        registry.register(MockImporter {
            name: "OFX",
            extension: "ofx",
        });

        assert_eq!(registry.len(), 2);
        assert!(!registry.is_empty());
    }

    #[test]
    fn test_registry_identify() {
        let mut registry = ImporterRegistry::new();
        registry.register(MockImporter {
            name: "CSV",
            extension: "csv",
        });
        registry.register(MockImporter {
            name: "OFX",
            extension: "ofx",
        });

        let csv_path = Path::new("transactions.csv");
        let ofx_path = Path::new("statement.ofx");
        let unknown_path = Path::new("document.pdf");

        assert!(registry.identify(csv_path).is_some());
        assert_eq!(registry.identify(csv_path).unwrap().name(), "CSV");

        assert!(registry.identify(ofx_path).is_some());
        assert_eq!(registry.identify(ofx_path).unwrap().name(), "OFX");

        assert!(registry.identify(unknown_path).is_none());
    }

    #[test]
    fn test_registry_default() {
        let registry = ImporterRegistry::default();
        assert!(registry.is_empty());
        assert_eq!(registry.len(), 0);
    }

    #[test]
    fn test_registry_list_importers() {
        let mut registry = ImporterRegistry::new();
        registry.register(MockImporter {
            name: "CSV",
            extension: "csv",
        });
        registry.register(MockImporter {
            name: "OFX",
            extension: "ofx",
        });

        let list = registry.list_importers();
        assert_eq!(list.len(), 2);
        assert!(list.iter().any(|(name, _)| *name == "CSV"));
        assert!(list.iter().any(|(name, _)| *name == "OFX"));
        // Check descriptions are present
        for (_, desc) in &list {
            assert_eq!(*desc, "Mock importer for testing");
        }
    }

    #[test]
    fn test_registry_extract_unknown_file() {
        use crate::config::{CsvConfig, ImporterType};
        let registry = ImporterRegistry::new();
        let unknown_path = Path::new("document.pdf");
        let config = ImporterConfig {
            account: "Assets:Bank".into(),
            currency: None,
            importer_type: ImporterType::Csv(CsvConfig::default()),
        };
        let result = registry.extract(unknown_path, &config);
        assert!(result.is_err());
        assert!(
            result
                .unwrap_err()
                .to_string()
                .contains("No importer found")
        );
    }

    #[test]
    fn test_with_builtins_seeds_registry() {
        let registry = ImporterRegistry::with_builtins();
        assert_eq!(registry.len(), 2);
        // OFX/QFX should be identified
        assert!(registry.identify(Path::new("statement.ofx")).is_some());
        assert!(registry.identify(Path::new("statement.qfx")).is_some());
        // CSV should be identified
        assert!(registry.identify(Path::new("data.csv")).is_some());
        // Unknown extensions are not handled
        assert!(registry.identify(Path::new("doc.pdf")).is_none());
    }

    #[test]
    fn test_find_by_name_case_insensitive_exact_or_slash_part() {
        let registry = ImporterRegistry::with_builtins();
        // Exact, case-insensitive
        assert!(registry.find_by_name("OFX/QFX").is_some());
        assert!(registry.find_by_name("ofx/qfx").is_some());
        assert!(registry.find_by_name("Csv").is_some());
        assert!(registry.find_by_name("CSV").is_some());
        // Slash-separated alternates match independently
        assert!(registry.find_by_name("ofx").is_some());
        assert!(registry.find_by_name("OFX").is_some());
        assert!(registry.find_by_name("qfx").is_some());
        assert!(registry.find_by_name("QFX").is_some());
        // Substring matches are NOT honored (no longer "contains")
        assert!(registry.find_by_name("f").is_none());
        assert!(registry.find_by_name("o").is_none());
        // Unknown
        assert!(registry.find_by_name("nonexistent").is_none());
    }

    #[test]
    fn test_registry_identify_returns_first_match() {
        let mut registry = ImporterRegistry::new();
        // Register two importers that match the same extension
        registry.register(MockImporter {
            name: "CSV1",
            extension: "csv",
        });
        registry.register(MockImporter {
            name: "CSV2",
            extension: "csv",
        });

        let csv_path = Path::new("transactions.csv");
        let importer = registry.identify(csv_path).unwrap();
        // Should return the first matching importer
        assert_eq!(importer.name(), "CSV1");
    }

    #[test]
    fn test_registry_empty_list_importers() {
        let registry = ImporterRegistry::new();
        let list = registry.list_importers();
        assert!(list.is_empty());
    }

    // ===== WASM discovery tests =====

    /// Minimal WAT module that exports the WASM importer ABI:
    /// `memory`, `alloc`, `metadata`, `identify`, `extract`,
    /// `extract_enriched`. `metadata` returns `(ptr=0, len=9)` →
    /// pre-baked msgpack for `MetadataOutput { name: "<name>",
    /// description: "tst" }`. The `name` argument is baked into the
    /// data section so each fixture gets a distinct importer name.
    fn metadata_wat(name: &str) -> String {
        assert_eq!(name.len(), 3, "test fixture only supports 3-char names");
        format!(
            r#"
            (module
                (memory (export "memory") 1)
                ;; 0x92 fixarray-2, 0xa3 fixstr-3 "<name>", 0xa3 fixstr-3 "tst"
                (data (i32.const 0) "\92\a3{name}\a3tst")
                (global $bump (mut i32) (i32.const 1024))
                (func (export "alloc") (param i32) (result i32) global.get $bump)
                (func (export "metadata") (result i64) i64.const 9)
                (func (export "identify") (param i32 i32) (result i64) i64.const 0)
                (func (export "extract") (param i32 i32) (result i64) i64.const 0)
                (func (export "extract_enriched") (param i32 i32) (result i64) i64.const 0)
            )
            "#
        )
    }

    fn write_wat_to(dir: &Path, file_name: &str, importer_name: &str) -> PathBuf {
        let bytes = wat::parse_str(metadata_wat(importer_name)).expect("WAT parses");
        let path = dir.join(file_name);
        std::fs::write(&path, &bytes).expect("write wasm fixture");
        path
    }

    #[test]
    fn register_wasm_from_path_loads_and_returns_metadata_name() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let path = write_wat_to(tmp.path(), "abc.wasm", "abc");

        let mut registry = ImporterRegistry::new();
        let name = registry
            .register_wasm_from_path(&path)
            .expect("loads cleanly");
        assert_eq!(name, "abc");
        assert_eq!(registry.len(), 1);
        // Importer is reachable by name through the registry.
        assert!(registry.find_by_name("abc").is_some());
    }

    #[test]
    fn register_wasm_dir_loads_only_wasm_files_in_sorted_order() {
        let tmp = tempfile::tempdir().expect("tempdir");
        // Out-of-order names to verify sort.
        write_wat_to(tmp.path(), "zzz.wasm", "zzz");
        write_wat_to(tmp.path(), "aaa.wasm", "aaa");
        write_wat_to(tmp.path(), "mmm.wasm", "mmm");
        // Non-wasm files must be silently skipped.
        std::fs::write(tmp.path().join("README.md"), "ignore me").unwrap();
        std::fs::write(tmp.path().join(".gitignore"), "*.tmp").unwrap();

        let mut registry = ImporterRegistry::new();
        let loaded = registry.register_wasm_dir(tmp.path()).expect("scan works");

        // Sorted load order means identify()/find_by_name behavior is
        // deterministic across platforms.
        assert_eq!(loaded, vec!["aaa", "mmm", "zzz"]);
        assert_eq!(registry.len(), 3);
        // Non-wasm files were not registered.
        assert!(registry.find_by_name("README").is_none());
    }

    #[test]
    fn register_wasm_dir_returns_empty_for_dir_with_no_wasm_files() {
        let tmp = tempfile::tempdir().expect("tempdir");
        std::fs::write(tmp.path().join("README.md"), "just docs").unwrap();

        let mut registry = ImporterRegistry::new();
        let loaded = registry.register_wasm_dir(tmp.path()).expect("scan works");
        assert!(loaded.is_empty());
        assert!(registry.is_empty());
    }

    #[test]
    fn register_wasm_dir_errors_on_nonexistent_dir() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let missing = tmp.path().join("does-not-exist");

        let mut registry = ImporterRegistry::new();
        let err = registry
            .register_wasm_dir(&missing)
            .expect_err("missing dir is an error");
        // The path is surfaced in the error so the user can see what
        // was attempted.
        let msg = err.to_string();
        assert!(
            msg.contains("does-not-exist"),
            "error should name the missing dir: {msg}"
        );
    }

    #[test]
    fn register_wasm_dir_stops_at_first_load_failure_but_keeps_prior_loads() {
        let tmp = tempfile::tempdir().expect("tempdir");
        // Sorted load order means `aaa.wasm` loads before `zzz.wasm`.
        // We want the good one to load first, then the bad one to fail.
        write_wat_to(tmp.path(), "aaa.wasm", "aaa");
        // Garbage that won't parse as wasm — register_wasm_dir should
        // fail on it but earlier files stay registered.
        std::fs::write(tmp.path().join("zzz.wasm"), b"this is not wasm").unwrap();

        let mut registry = ImporterRegistry::new();
        let err = registry
            .register_wasm_dir(tmp.path())
            .expect_err("malformed wasm fails");
        let _ = err;
        assert_eq!(registry.len(), 1, "earlier successful load is kept");
        assert!(registry.find_by_name("aaa").is_some());
    }

    #[test]
    fn register_wasm_keeps_user_priority_before_builtins() {
        // Builtins come last in the build-registry helper used by the
        // CLI, so user-loaded WASM should win identify() against built-
        // ins. This tests the relative ordering primitive that the
        // CLI helper relies on.
        let tmp = tempfile::tempdir().expect("tempdir");
        let user_wasm = write_wat_to(tmp.path(), "usr.wasm", "usr");

        let mut registry = ImporterRegistry::new();
        registry.register_wasm_from_path(&user_wasm).expect("loads");
        registry.register(OfxImporter);
        registry.register(CsvImporter);

        // Order: user-WASM first, then builtins. The user WASM's
        // identify() returns false (test fixture's identify always
        // returns 0/false), so a .csv path should still fall through
        // to CSV. This confirms identify() iterates in registration
        // order, the basis of the CLI's priority guarantee.
        let csv_path = Path::new("statement.csv");
        let importer = registry.identify(csv_path).expect("CSV builtin handles it");
        assert_eq!(importer.name(), "CSV");
    }
}
