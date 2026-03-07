//! Auto-discover documents from directories.

use crate::types::{
    DirectiveData, DirectiveWrapper, DocumentData, PluginError, PluginInput, PluginOutput,
    sort_directives,
};

use super::super::NativePlugin;

/// Maximum recursion depth for directory scanning to prevent denial-of-service from deeply nested structures.
const MAX_SCAN_DEPTH: usize = 32;

/// Plugin that auto-discovers document files from configured directories.
///
/// Scans directories specified in `option "documents"` for files matching
/// the pattern: `{Account}/YYYY-MM-DD.description.*`
///
/// For example: `documents/Assets/Bank/Checking/2024-01-15.statement.pdf`
/// generates: `2024-01-15 document Assets:Bank:Checking "documents/Assets/Bank/Checking/2024-01-15.statement.pdf"`
///
/// # Security
///
/// - Symlinks are skipped to prevent infinite recursion from symlink cycles
/// - Maximum recursion depth is enforced to prevent denial-of-service from deeply nested directories
pub struct DocumentDiscoveryPlugin {
    /// Directories to scan for documents (resolved to absolute paths).
    pub directories: Vec<String>,
    /// Base directory for resolving relative paths in existing document directives.
    pub base_dir: std::path::PathBuf,
}

impl DocumentDiscoveryPlugin {
    /// Create a new plugin with the given directories and base directory.
    ///
    /// The `base_dir` is used to resolve relative paths in existing document directives
    /// for duplicate detection.
    pub const fn new(directories: Vec<String>, base_dir: std::path::PathBuf) -> Self {
        Self {
            directories,
            base_dir,
        }
    }
}

impl NativePlugin for DocumentDiscoveryPlugin {
    fn name(&self) -> &'static str {
        "document_discovery"
    }

    fn description(&self) -> &'static str {
        "Auto-discover documents from directories"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use std::path::Path;

        let mut new_directives = Vec::new();
        let mut errors = Vec::new();

        // Collect existing document paths to avoid duplicates.
        // Normalize paths by resolving relative paths against base_dir, then canonicalizing.
        let mut existing_docs: std::collections::HashSet<String> = std::collections::HashSet::new();
        for wrapper in &input.directives {
            if let DirectiveData::Document(doc) = &wrapper.data {
                let doc_path = Path::new(&doc.path);
                // Resolve relative paths against base_dir
                let resolved = if doc_path.is_absolute() {
                    doc_path.to_path_buf()
                } else {
                    self.base_dir.join(doc_path)
                };
                // Canonicalize for consistent path comparison
                let normalized = resolved
                    .canonicalize()
                    .map_or_else(|_| doc.path.clone(), |p| p.to_string_lossy().to_string());
                existing_docs.insert(normalized);
            }
        }

        // Scan each directory
        for dir in &self.directories {
            let dir_path = Path::new(dir);
            if !dir_path.exists() {
                continue;
            }

            if let Err(e) = scan_documents(
                dir_path,
                dir,
                &existing_docs,
                &mut new_directives,
                &mut errors,
                0, // Initial depth
            ) {
                errors.push(PluginError::error(format!(
                    "Error scanning documents in {dir}: {e}"
                )));
            }
        }

        // Add discovered documents to directives
        let mut all_directives = input.directives;
        all_directives.extend(new_directives);

        // Sort using beancount's standard ordering
        sort_directives(&mut all_directives);

        PluginOutput {
            directives: all_directives,
            errors,
        }
    }
}

/// Recursively scan a directory for document files.
///
/// # Security
/// - Uses `symlink_metadata` to detect and skip symlinks, preventing infinite loops
/// - Enforces maximum recursion depth to prevent denial-of-service from deeply nested directories
#[allow(clippy::only_used_in_recursion)]
fn scan_documents(
    path: &std::path::Path,
    base_dir: &str,
    existing: &std::collections::HashSet<String>,
    directives: &mut Vec<DirectiveWrapper>,
    errors: &mut Vec<PluginError>,
    depth: usize,
) -> std::io::Result<()> {
    use std::fs;

    // Enforce maximum recursion depth
    if depth > MAX_SCAN_DEPTH {
        errors.push(PluginError::warning(format!(
            "Maximum directory depth ({MAX_SCAN_DEPTH}) exceeded at {}",
            path.display()
        )));
        return Ok(());
    }

    for entry in fs::read_dir(path)? {
        let entry = entry?;
        let entry_path = entry.path();

        // Use symlink_metadata to check file type WITHOUT following symlinks.
        // This prevents infinite recursion from symlink cycles.
        let metadata = match fs::symlink_metadata(&entry_path) {
            Ok(m) => m,
            Err(_) => continue, // Skip entries we can't stat
        };

        // Skip symlinks entirely to prevent security issues
        if metadata.file_type().is_symlink() {
            continue;
        }

        if metadata.is_dir() {
            scan_documents(
                &entry_path,
                base_dir,
                existing,
                directives,
                errors,
                depth + 1,
            )?;
        } else if metadata.is_file() {
            // Try to parse filename as YYYY-MM-DD.description.ext
            if let Some(file_name) = entry_path.file_name().and_then(|n| n.to_str())
                && file_name.len() >= 10
                && file_name.chars().nth(4) == Some('-')
                && file_name.chars().nth(7) == Some('-')
            {
                let date_str = &file_name[0..10];
                // Validate date format
                if date_str.chars().take(4).all(|c| c.is_ascii_digit())
                    && date_str.chars().skip(5).take(2).all(|c| c.is_ascii_digit())
                    && date_str.chars().skip(8).take(2).all(|c| c.is_ascii_digit())
                {
                    // Extract account from path relative to base_dir
                    if let Ok(rel_path) = entry_path.strip_prefix(base_dir)
                        && let Some(parent) = rel_path.parent()
                    {
                        let account = parent
                            .components()
                            .map(|c| c.as_os_str().to_string_lossy().to_string())
                            .collect::<Vec<_>>()
                            .join(":");

                        if !account.is_empty() {
                            let full_path = entry_path.to_string_lossy().to_string();

                            // Canonicalize for consistent comparison with existing docs
                            let canonical = entry_path.canonicalize().map_or_else(
                                |_| full_path.clone(),
                                |p| p.to_string_lossy().to_string(),
                            );

                            // Skip if already exists (compare canonical paths)
                            if existing.contains(&canonical) {
                                continue;
                            }

                            directives.push(DirectiveWrapper {
                                directive_type: "document".to_string(),
                                date: date_str.to_string(),
                                filename: None, // Plugin-generated
                                lineno: None,
                                data: DirectiveData::Document(DocumentData {
                                    account,
                                    path: full_path,
                                    metadata: vec![],
                                }),
                            });
                        }
                    }
                }
            }
        }
    }

    Ok(())
}
