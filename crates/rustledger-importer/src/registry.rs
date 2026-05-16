//! Registry for importers.

use crate::config::ImporterConfig;
use crate::csv_importer::CsvImporter;
use crate::ofx_importer::OfxImporter;
use crate::{ImportResult, Importer};
use anyhow::{Context, Result};
use std::path::Path;
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
}
