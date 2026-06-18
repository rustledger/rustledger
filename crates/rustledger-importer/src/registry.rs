//! Registry for importers.

use crate::config::ImporterConfig;
use crate::csv_importer::CsvImporter;
use crate::ofx_importer::OfxImporter;
#[cfg(feature = "wasm-importer")]
use crate::wasm::{WasmImporter, WasmImporterError};
use crate::{ImportResult, Importer};
use anyhow::{Context, Result};
use std::path::Path;
#[cfg(feature = "wasm-importer")]
use std::path::PathBuf;
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
    #[cfg(feature = "wasm-importer")]
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
    /// and register each as a [`WasmImporter`].
    ///
    /// Files are loaded in sorted order so `identify()` behavior is
    /// deterministic across filesystems and platforms. Extension
    /// matching is case-insensitive — both `foo.wasm` and `BAR.WASM`
    /// are picked up.
    ///
    /// Loading is **skip-and-collect**: every loadable module is
    /// registered; failures are accumulated in
    /// [`WasmDirScanReport::failures`] so the caller can decide
    /// whether to log them, abort, or ignore. A single broken module
    /// in a dir with 19 good ones doesn't prevent the 19 from
    /// loading.
    ///
    /// Non-`.wasm` files (a `README.md` or `.gitignore`) and
    /// subdirectories are silently skipped. Per-entry I/O errors
    /// (rare — permission denied on a single inode, broken symlinks)
    /// are surfaced in [`WasmDirScanReport::failures`] tagged with the
    /// dir path (the entry's name is unavailable when read fails).
    ///
    /// # Duplicate names
    ///
    /// If two `.wasm` modules export the same `metadata.name`, both
    /// are registered. [`Self::find_by_name`] returns the first match
    /// — which, given the sorted load order, is the file with the
    /// lexicographically-earlier filename.
    ///
    /// # Errors
    ///
    /// The outer `Result` reports an I/O error reading `dir` itself
    /// (e.g. dir doesn't exist) — without that, the scan can't even
    /// start. Per-file failures land inside
    /// [`WasmDirScanReport::failures`].
    #[cfg(feature = "wasm-importer")]
    pub fn register_wasm_dir(
        &mut self,
        dir: impl AsRef<Path>,
    ) -> Result<WasmDirScanReport, WasmImporterError> {
        let dir = dir.as_ref();
        // Listing/filtering/sorting is shared with
        // `PluginManager::register_wasm_dir` — see
        // `rustledger_plugin::wasm_dir_scan` for the common helper.
        // Caller-side: dir-level error wrapping + per-file load fn +
        // per-entry error wrapping (importer uses the typed `DirEntry`
        // variant, plugin uses `anyhow::Error::new`).
        let scan = rustledger_plugin::wasm_dir_scan::collect_wasm_paths(dir).map_err(|source| {
            WasmImporterError::Io {
                path: dir.to_path_buf(),
                source,
            }
        })?;
        let mut report = WasmDirScanReport::default();
        // Per-entry I/O errors → the typed `DirEntry` variant so a
        // user debugging a missing importer can distinguish them from
        // file-read errors. The path on the report entry is the dir
        // itself because the per-entry error doesn't expose the
        // offending inode's name.
        for (entry_path, source) in scan.entry_failures {
            report.failures.push((
                entry_path,
                WasmImporterError::DirEntry {
                    dir: dir.to_path_buf(),
                    source,
                },
            ));
        }
        for path in scan.sorted_paths {
            match self.register_wasm_from_path(&path) {
                Ok(name) => report.loaded.push(name),
                Err(e) => report.failures.push((path, e)),
            }
        }
        Ok(report)
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

/// Outcome of [`ImporterRegistry::register_wasm_dir`].
///
/// Splits the successfully-loaded importer names from the per-file
/// failures so callers can log/report both. A single broken module
/// in a dir with 19 good ones leaves the 19 registered; the broken
/// one's path + error land in [`Self::failures`].
#[cfg(feature = "wasm-importer")]
#[derive(Debug, Default)]
pub struct WasmDirScanReport {
    /// `metadata.name` of each successfully-loaded module, in load
    /// order (lexicographic by file path).
    pub loaded: Vec<String>,
    /// Per-file load failures. Each entry is the `.wasm` path plus
    /// the underlying error.
    pub failures: Vec<(PathBuf, WasmImporterError)>,
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

    #[cfg(feature = "wasm-importer")]
    use crate::test_fixtures::metadata_wat;

    #[cfg(feature = "wasm-importer")]
    fn write_wat_to(dir: &Path, file_name: &str, importer_name: &str) -> PathBuf {
        let bytes = wat::parse_str(metadata_wat(importer_name)).expect("WAT parses");
        let path = dir.join(file_name);
        std::fs::write(&path, &bytes).expect("write wasm fixture");
        path
    }

    #[test]
    #[cfg(feature = "wasm-importer")]
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
    #[cfg(feature = "wasm-importer")]
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
        let report = registry.register_wasm_dir(tmp.path()).expect("scan works");

        // Sorted load order means identify()/find_by_name behavior is
        // deterministic across platforms.
        assert_eq!(report.loaded, vec!["aaa", "mmm", "zzz"]);
        assert!(report.failures.is_empty());
        assert_eq!(registry.len(), 3);
        // Non-wasm files were not registered.
        assert!(registry.find_by_name("README").is_none());
    }

    #[test]
    #[cfg(feature = "wasm-importer")]
    fn register_wasm_dir_returns_empty_for_dir_with_no_wasm_files() {
        let tmp = tempfile::tempdir().expect("tempdir");
        std::fs::write(tmp.path().join("README.md"), "just docs").unwrap();

        let mut registry = ImporterRegistry::new();
        let report = registry.register_wasm_dir(tmp.path()).expect("scan works");
        assert!(report.loaded.is_empty());
        assert!(report.failures.is_empty());
        assert!(registry.is_empty());
    }

    #[test]
    #[cfg(feature = "wasm-importer")]
    fn register_wasm_dir_matches_uppercase_extension_too() {
        let tmp = tempfile::tempdir().expect("tempdir");
        // Mixed case extensions: all should be picked up.
        let bytes = wat::parse_str(metadata_wat("low")).expect("WAT parses");
        std::fs::write(tmp.path().join("low.wasm"), &bytes).unwrap();
        let bytes = wat::parse_str(metadata_wat("upp")).expect("WAT parses");
        std::fs::write(tmp.path().join("UPP.WASM"), &bytes).unwrap();
        let bytes = wat::parse_str(metadata_wat("mix")).expect("WAT parses");
        std::fs::write(tmp.path().join("MiX.WasM"), &bytes).unwrap();

        let mut registry = ImporterRegistry::new();
        let report = registry.register_wasm_dir(tmp.path()).expect("scan works");
        assert_eq!(report.loaded.len(), 3, "all three case variants load");
    }

    #[test]
    #[cfg(feature = "wasm-importer")]
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
    #[cfg(feature = "wasm-importer")]
    fn register_wasm_dir_skip_and_collect_keeps_loading_past_failures() {
        // Skip-and-collect semantics: one broken module doesn't
        // prevent the others from loading. The good modules end up
        // in `report.loaded`; the bad one ends up in `report.failures`
        // with its path. This is critical for a discovery dir with
        // dozens of community-shipped importers — a single broken
        // one shouldn't take down the rest.
        let tmp = tempfile::tempdir().expect("tempdir");
        write_wat_to(tmp.path(), "aaa.wasm", "aaa");
        // Bracket the bad file between two good ones so we exercise
        // continuation in both directions.
        std::fs::write(tmp.path().join("mmm.wasm"), b"this is not wasm").unwrap();
        write_wat_to(tmp.path(), "zzz.wasm", "zzz");

        let mut registry = ImporterRegistry::new();
        let report = registry
            .register_wasm_dir(tmp.path())
            .expect("scan itself works; per-file failure is in `failures`");
        // Both good ones loaded despite the bad one in the middle.
        assert_eq!(report.loaded, vec!["aaa", "zzz"]);
        assert_eq!(registry.len(), 2);
        // The bad one is surfaced with its path so the user can fix it.
        assert_eq!(report.failures.len(), 1);
        assert!(
            report.failures[0].0.ends_with("mmm.wasm"),
            "failure entry should name the bad file: {:?}",
            report.failures[0].0
        );
    }

    #[test]
    #[cfg(feature = "wasm-importer")]
    fn register_wasm_wins_identify_collision_when_registered_before_builtins() {
        // The actual precedence guarantee the CLI helper relies on:
        // when a WASM importer's `identify()` returns true for the
        // SAME file a builtin would also accept, the one registered
        // first wins. Uses `identifying_wat` (identify always true)
        // so the collision is real — without it, the test would only
        // exercise fallthrough order, not the collision path.
        use crate::test_fixtures::identifying_wat;
        let tmp = tempfile::tempdir().expect("tempdir");
        let bytes = wat::parse_str(identifying_wat("usr")).expect("WAT parses");
        let user_wasm = tmp.path().join("usr.wasm");
        std::fs::write(&user_wasm, &bytes).expect("write fixture");

        let mut registry = ImporterRegistry::new();
        registry.register_wasm_from_path(&user_wasm).expect("loads");
        registry.register(OfxImporter);
        registry.register(CsvImporter);

        // .csv path that the CSV builtin would also accept. The user
        // WASM is registered first AND returns true for identify, so
        // it must win the dispatch. This test would FAIL if
        // registration order were reversed — which `metadata_wat`'s
        // always-false identify can't catch.
        let csv_path = Path::new("statement.csv");
        let importer = registry.identify(csv_path).expect("WASM handles it");
        assert_eq!(
            importer.name(),
            "usr",
            "user WASM should win over CSV builtin on identify collision"
        );

        // Sanity: swap registration order, builtin wins instead.
        let bytes2 = wat::parse_str(identifying_wat("usr")).expect("WAT parses");
        let user_wasm2 = tmp.path().join("usr2.wasm");
        std::fs::write(&user_wasm2, &bytes2).expect("write fixture");
        let mut reversed = ImporterRegistry::new();
        reversed.register(CsvImporter);
        reversed
            .register_wasm_from_path(&user_wasm2)
            .expect("loads");
        let importer = reversed.identify(csv_path).expect("CSV handles it");
        assert_eq!(
            importer.name(),
            "CSV",
            "CSV builtin should win when registered first — confirms order matters"
        );
    }
}
