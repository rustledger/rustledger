//! Manifest tracking for synthetic beancount files.
//!
//! Tracks generated files with metadata for reproducibility and CI reporting.

use serde::{Deserialize, Serialize};
use std::path::Path;

/// Manifest tracking all generated synthetic files.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SyntheticManifest {
    /// ISO 8601 timestamp when the manifest was generated
    pub generated_at: String,

    /// Random seed used for generation (for reproducibility)
    pub seed: u64,

    /// Version of the generator that created these files
    pub generator_version: String,

    /// List of generated files
    pub files: Vec<ManifestEntry>,
}

impl SyntheticManifest {
    /// Create a new empty manifest.
    pub fn new(seed: u64) -> Self {
        Self {
            generated_at: jiff::Zoned::now().to_string(),
            seed,
            generator_version: env!("CARGO_PKG_VERSION").to_string(),
            files: Vec::new(),
        }
    }

    /// Add an entry to the manifest.
    pub fn add_entry(&mut self, entry: ManifestEntry) {
        self.files.push(entry);
    }

    /// Get the total number of files.
    pub const fn file_count(&self) -> usize {
        self.files.len()
    }

    /// Get files by category.
    pub fn files_by_category(&self, category: &str) -> Vec<&ManifestEntry> {
        self.files
            .iter()
            .filter(|e| e.category == category)
            .collect()
    }

    /// Get all unique categories.
    pub fn categories(&self) -> Vec<String> {
        let mut cats: Vec<_> = self.files.iter().map(|e| e.category.clone()).collect();
        cats.sort();
        cats.dedup();
        cats
    }

    /// Serialize to JSON.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Deserialize from JSON.
    pub fn from_json(json: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(json)
    }

    /// Save manifest to a file.
    pub fn save(&self, path: &Path) -> std::io::Result<()> {
        let json = self
            .to_json()
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
        std::fs::write(path, json)
    }

    /// Load manifest from a file.
    pub fn load(path: &Path) -> std::io::Result<Self> {
        let json = std::fs::read_to_string(path)?;
        Self::from_json(&json).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
    }

    /// Generate a summary report.
    pub fn summary(&self) -> String {
        let mut report = String::new();
        report.push_str("Synthetic Manifest Summary\n");
        report.push_str("==========================\n\n");
        report.push_str(&format!("Generated: {}\n", self.generated_at));
        report.push_str(&format!("Seed: {}\n", self.seed));
        report.push_str(&format!("Generator: v{}\n", self.generator_version));
        report.push_str(&format!("Total files: {}\n\n", self.files.len()));

        report.push_str("Files by category:\n");
        for category in self.categories() {
            let count = self.files_by_category(&category).len();
            report.push_str(&format!("  {category}: {count}\n"));
        }

        let total_directives: usize = self.files.iter().map(|e| e.directive_count).sum();
        report.push_str(&format!("\nTotal directives: {total_directives}\n"));

        report
    }
}

/// Entry for a single generated file.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ManifestEntry {
    /// Filename (relative path from manifest location)
    pub filename: String,

    /// Category of the file (e.g., "proptest", "bean-example", "edge-case")
    pub category: String,

    /// Number of directives in the file
    pub directive_count: usize,

    /// SHA-256 hash of file contents (hex-encoded)
    pub sha256: String,

    /// File size in bytes
    #[serde(skip_serializing_if = "Option::is_none")]
    pub size_bytes: Option<u64>,

    /// Optional description of the file's purpose
    #[serde(skip_serializing_if = "Option::is_none")]
    pub description: Option<String>,

    /// Whether the file passed bean-check validation
    #[serde(skip_serializing_if = "Option::is_none")]
    pub bean_check_valid: Option<bool>,
}

impl ManifestEntry {
    /// Create a new manifest entry.
    pub fn new(filename: impl Into<String>, category: impl Into<String>) -> Self {
        Self {
            filename: filename.into(),
            category: category.into(),
            directive_count: 0,
            sha256: String::new(),
            size_bytes: None,
            description: None,
            bean_check_valid: None,
        }
    }

    /// Set the directive count.
    pub const fn with_directive_count(mut self, count: usize) -> Self {
        self.directive_count = count;
        self
    }

    /// Set the SHA-256 hash.
    pub fn with_sha256(mut self, hash: impl Into<String>) -> Self {
        self.sha256 = hash.into();
        self
    }

    /// Set the file size.
    pub const fn with_size(mut self, size: u64) -> Self {
        self.size_bytes = Some(size);
        self
    }

    /// Set the description.
    pub fn with_description(mut self, desc: impl Into<String>) -> Self {
        self.description = Some(desc.into());
        self
    }

    /// Set bean-check validation status.
    pub const fn with_validation(mut self, valid: bool) -> Self {
        self.bean_check_valid = Some(valid);
        self
    }
}

/// Calculate SHA-256 hash of content (requires sha2 crate in calling code).
/// Returns hex-encoded string.
pub fn sha256_hex(content: &[u8]) -> String {
    use std::fmt::Write;

    // Simple SHA-256 implementation using std only is complex,
    // so this function expects the caller to provide the hash.
    // This is a placeholder that returns a dummy value.
    // In actual use, use sha2::Sha256::digest(content).
    let mut result = String::with_capacity(64);
    for byte in content.iter().take(32) {
        write!(&mut result, "{byte:02x}").unwrap();
    }
    // Pad with zeros if content is shorter
    while result.len() < 64 {
        result.push('0');
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_manifest_new() {
        let manifest = SyntheticManifest::new(12345);
        assert_eq!(manifest.seed, 12345);
        assert!(manifest.files.is_empty());
    }

    #[test]
    fn test_manifest_add_entry() {
        let mut manifest = SyntheticManifest::new(42);
        manifest.add_entry(
            ManifestEntry::new("test.beancount", "proptest")
                .with_directive_count(10)
                .with_sha256("abc123"),
        );
        assert_eq!(manifest.file_count(), 1);
        assert_eq!(manifest.files[0].directive_count, 10);
    }

    #[test]
    fn test_manifest_categories() {
        let mut manifest = SyntheticManifest::new(42);
        manifest.add_entry(ManifestEntry::new("a.beancount", "proptest"));
        manifest.add_entry(ManifestEntry::new("b.beancount", "edge-case"));
        manifest.add_entry(ManifestEntry::new("c.beancount", "proptest"));

        let cats = manifest.categories();
        assert_eq!(cats.len(), 2);
        assert!(cats.contains(&"proptest".to_string()));
        assert!(cats.contains(&"edge-case".to_string()));
    }

    #[test]
    fn test_manifest_json_roundtrip() {
        let mut manifest = SyntheticManifest::new(12345);
        manifest.add_entry(
            ManifestEntry::new("test.beancount", "proptest")
                .with_directive_count(50)
                .with_sha256("deadbeef")
                .with_description("Test file"),
        );

        let json = manifest.to_json().unwrap();
        let loaded = SyntheticManifest::from_json(&json).unwrap();

        assert_eq!(loaded.seed, 12345);
        assert_eq!(loaded.files.len(), 1);
        assert_eq!(loaded.files[0].directive_count, 50);
    }

    #[test]
    fn test_manifest_summary() {
        let mut manifest = SyntheticManifest::new(42);
        manifest.add_entry(ManifestEntry::new("a.beancount", "proptest").with_directive_count(10));
        manifest.add_entry(ManifestEntry::new("b.beancount", "edge-case").with_directive_count(20));

        let summary = manifest.summary();
        assert!(summary.contains("Seed: 42"));
        assert!(summary.contains("Total files: 2"));
        assert!(summary.contains("Total directives: 30"));
    }
}
