//! Registry for importers.

use crate::{ImportResult, Importer};
use anyhow::{Context, Result};
use std::path::Path;
use std::sync::Arc;

/// Registry of importers.
///
/// The registry holds a collection of importers and can automatically
/// identify which importer to use for a given file.
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

    /// Extract transactions from a file using the appropriate importer.
    pub fn extract(&self, path: &Path) -> Result<ImportResult> {
        let importer = self
            .identify(path)
            .with_context(|| format!("No importer found for file: {}", path.display()))?;

        importer
            .extract(path)
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

        fn extract(&self, _path: &Path) -> Result<ImportResult> {
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
}
