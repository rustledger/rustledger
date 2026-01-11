//! Beancount file loader with include resolution.
//!
//! This crate handles loading beancount files, resolving includes,
//! and collecting options. It builds on the parser to provide a
//! complete loading pipeline.
//!
//! # Features
//!
//! - Recursive include resolution with cycle detection
//! - Options collection and parsing
//! - Plugin directive collection
//! - Source map for error reporting
//! - Push/pop tag and metadata handling
//! - Automatic GPG decryption for encrypted files (`.gpg`, `.asc`)
//!
//! # Example
//!
//! ```ignore
//! use rustledger_loader::Loader;
//! use std::path::Path;
//!
//! let result = Loader::new().load(Path::new("ledger.beancount"))?;
//! for directive in result.directives {
//!     println!("{:?}", directive);
//! }
//! ```

#![forbid(unsafe_code)]
#![warn(missing_docs)]

mod options;
mod source_map;

pub use options::Options;
pub use source_map::{SourceFile, SourceMap};

use rustledger_core::Directive;
use rustledger_parser::{ParseError, Span, Spanned};
use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use thiserror::Error;

/// Errors that can occur during loading.
#[derive(Debug, Error)]
pub enum LoadError {
    /// IO error reading a file.
    #[error("failed to read file {path}: {source}")]
    Io {
        /// The path that failed to read.
        path: PathBuf,
        /// The underlying IO error.
        #[source]
        source: std::io::Error,
    },

    /// Include cycle detected.
    #[error("include cycle detected: {}", .cycle.join(" -> "))]
    IncludeCycle {
        /// The cycle of file paths.
        cycle: Vec<String>,
    },

    /// Parse errors occurred.
    #[error("parse errors in {path}")]
    ParseErrors {
        /// The file with parse errors.
        path: PathBuf,
        /// The parse errors.
        errors: Vec<ParseError>,
    },

    /// Path traversal attempt detected.
    #[error("path traversal not allowed: {include_path} escapes base directory {base_dir}")]
    PathTraversal {
        /// The include path that attempted traversal.
        include_path: String,
        /// The base directory.
        base_dir: PathBuf,
    },

    /// GPG decryption failed.
    #[error("failed to decrypt {path}: {message}")]
    Decryption {
        /// The encrypted file path.
        path: PathBuf,
        /// Error message from GPG.
        message: String,
    },
}

/// Result of loading a beancount file.
#[derive(Debug)]
pub struct LoadResult {
    /// All directives from all files, in order.
    pub directives: Vec<Spanned<Directive>>,
    /// Parsed options.
    pub options: Options,
    /// Plugins to load.
    pub plugins: Vec<Plugin>,
    /// Source map for error reporting.
    pub source_map: SourceMap,
    /// All errors encountered during loading.
    pub errors: Vec<LoadError>,
}

/// A plugin directive.
#[derive(Debug, Clone)]
pub struct Plugin {
    /// Plugin module name.
    pub name: String,
    /// Optional configuration string.
    pub config: Option<String>,
    /// Source location.
    pub span: Span,
    /// File this plugin was declared in.
    pub file_id: usize,
}

/// Check if a file is GPG-encrypted based on extension or content.
///
/// Returns `true` for:
/// - Files with `.gpg` extension
/// - Files with `.asc` extension containing a PGP message header
fn is_encrypted_file(path: &Path) -> bool {
    match path.extension().and_then(|e| e.to_str()) {
        Some("gpg") => true,
        Some("asc") => {
            // Check for PGP header in first 1024 bytes
            if let Ok(content) = fs::read_to_string(path) {
                let check_len = 1024.min(content.len());
                content[..check_len].contains("-----BEGIN PGP MESSAGE-----")
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Decrypt a GPG-encrypted file using the system `gpg` command.
///
/// This uses `gpg --batch --decrypt` which will use the user's
/// GPG keyring and gpg-agent for passphrase handling.
fn decrypt_gpg_file(path: &Path) -> Result<String, LoadError> {
    let output = Command::new("gpg")
        .args(["--batch", "--decrypt"])
        .arg(path)
        .output()
        .map_err(|e| LoadError::Decryption {
            path: path.to_path_buf(),
            message: format!("failed to run gpg: {e}"),
        })?;

    if !output.status.success() {
        return Err(LoadError::Decryption {
            path: path.to_path_buf(),
            message: String::from_utf8_lossy(&output.stderr).trim().to_string(),
        });
    }

    String::from_utf8(output.stdout).map_err(|e| LoadError::Decryption {
        path: path.to_path_buf(),
        message: format!("decrypted content is not valid UTF-8: {e}"),
    })
}

/// Beancount file loader.
#[derive(Debug, Default)]
pub struct Loader {
    /// Files that have been loaded (for cycle detection).
    loaded_files: HashSet<PathBuf>,
    /// Stack for cycle detection during loading.
    include_stack: Vec<PathBuf>,
    /// Root directory for path traversal protection.
    /// If set, includes must resolve to paths within this directory.
    root_dir: Option<PathBuf>,
    /// Whether to enforce path traversal protection.
    enforce_path_security: bool,
}

impl Loader {
    /// Create a new loader.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Enable path traversal protection.
    ///
    /// When enabled, include directives cannot escape the root directory
    /// of the main beancount file. This prevents malicious ledger files
    /// from accessing sensitive files outside the ledger directory.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let result = Loader::new()
    ///     .with_path_security(true)
    ///     .load(Path::new("ledger.beancount"))?;
    /// ```
    #[must_use]
    pub const fn with_path_security(mut self, enabled: bool) -> Self {
        self.enforce_path_security = enabled;
        self
    }

    /// Set a custom root directory for path security.
    ///
    /// By default, the root directory is the parent directory of the main file.
    /// This method allows overriding that to a custom directory.
    #[must_use]
    pub fn with_root_dir(mut self, root: PathBuf) -> Self {
        self.root_dir = Some(root);
        self.enforce_path_security = true;
        self
    }

    /// Load a beancount file and all its includes.
    ///
    /// Parses the file, processes options and plugin directives, and recursively
    /// loads any included files.
    ///
    /// # Errors
    ///
    /// Returns [`LoadError`] in the following cases:
    ///
    /// - [`LoadError::Io`] - Failed to read the file or an included file
    /// - [`LoadError::IncludeCycle`] - Circular include detected
    ///
    /// Note: Parse errors and path traversal errors are collected in
    /// [`LoadResult::errors`] rather than returned directly, allowing
    /// partial results to be returned.
    pub fn load(&mut self, path: &Path) -> Result<LoadResult, LoadError> {
        let mut directives = Vec::new();
        let mut options = Options::default();
        let mut plugins = Vec::new();
        let mut source_map = SourceMap::new();
        let mut errors = Vec::new();

        // Get canonical path
        let canonical = path.canonicalize().map_err(|e| LoadError::Io {
            path: path.to_path_buf(),
            source: e,
        })?;

        // Set root directory for path security if enabled but not explicitly set
        if self.enforce_path_security && self.root_dir.is_none() {
            self.root_dir = canonical.parent().map(Path::to_path_buf);
        }

        self.load_recursive(
            &canonical,
            &mut directives,
            &mut options,
            &mut plugins,
            &mut source_map,
            &mut errors,
        )?;

        Ok(LoadResult {
            directives,
            options,
            plugins,
            source_map,
            errors,
        })
    }

    fn load_recursive(
        &mut self,
        path: &Path,
        directives: &mut Vec<Spanned<Directive>>,
        options: &mut Options,
        plugins: &mut Vec<Plugin>,
        source_map: &mut SourceMap,
        errors: &mut Vec<LoadError>,
    ) -> Result<(), LoadError> {
        // Check for cycles
        let path_buf = path.to_path_buf();
        if self.include_stack.contains(&path_buf) {
            let mut cycle: Vec<String> = self
                .include_stack
                .iter()
                .map(|p| p.display().to_string())
                .collect();
            cycle.push(path.display().to_string());
            return Err(LoadError::IncludeCycle { cycle });
        }

        // Check if already loaded
        if self.loaded_files.contains(path) {
            return Ok(());
        }

        // Read file (decrypting if necessary)
        let source = if is_encrypted_file(path) {
            decrypt_gpg_file(path)?
        } else {
            fs::read_to_string(path).map_err(|e| LoadError::Io {
                path: path.to_path_buf(),
                source: e,
            })?
        };

        // Add to source map
        let file_id = source_map.add_file(path.to_path_buf(), source.clone());

        // Mark as loading
        self.include_stack.push(path.to_path_buf());
        self.loaded_files.insert(path.to_path_buf());

        // Parse
        let result = rustledger_parser::parse(&source);

        // Collect parse errors
        if !result.errors.is_empty() {
            errors.push(LoadError::ParseErrors {
                path: path.to_path_buf(),
                errors: result.errors,
            });
        }

        // Process options
        for (key, value, _span) in result.options {
            options.set(&key, &value);
        }

        // Process plugins
        for (name, config, span) in result.plugins {
            plugins.push(Plugin {
                name,
                config,
                span,
                file_id,
            });
        }

        // Process includes
        let base_dir = path.parent().unwrap_or(Path::new("."));
        for (include_path, _span) in &result.includes {
            let full_path = base_dir.join(include_path);
            let canonical = match full_path.canonicalize() {
                Ok(p) => p,
                Err(e) => {
                    errors.push(LoadError::Io {
                        path: full_path,
                        source: e,
                    });
                    continue;
                }
            };

            // Path traversal protection: ensure include stays within root directory
            if self.enforce_path_security {
                if let Some(ref root) = self.root_dir {
                    if !canonical.starts_with(root) {
                        errors.push(LoadError::PathTraversal {
                            include_path: include_path.clone(),
                            base_dir: root.clone(),
                        });
                        continue;
                    }
                }
            }

            if let Err(e) =
                self.load_recursive(&canonical, directives, options, plugins, source_map, errors)
            {
                errors.push(e);
            }
        }

        // Add directives from this file
        directives.extend(result.directives);

        // Pop from stack
        self.include_stack.pop();

        Ok(())
    }
}

/// Load a beancount file.
///
/// This is a convenience function that creates a loader and loads a single file.
pub fn load(path: &Path) -> Result<LoadResult, LoadError> {
    Loader::new().load(path)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    #[test]
    fn test_is_encrypted_file_gpg_extension() {
        let path = Path::new("test.beancount.gpg");
        assert!(is_encrypted_file(path));
    }

    #[test]
    fn test_is_encrypted_file_plain_beancount() {
        let path = Path::new("test.beancount");
        assert!(!is_encrypted_file(path));
    }

    #[test]
    fn test_is_encrypted_file_asc_with_pgp_header() {
        let mut file = NamedTempFile::with_suffix(".asc").unwrap();
        writeln!(file, "-----BEGIN PGP MESSAGE-----").unwrap();
        writeln!(file, "some encrypted content").unwrap();
        writeln!(file, "-----END PGP MESSAGE-----").unwrap();
        file.flush().unwrap();

        assert!(is_encrypted_file(file.path()));
    }

    #[test]
    fn test_is_encrypted_file_asc_without_pgp_header() {
        let mut file = NamedTempFile::with_suffix(".asc").unwrap();
        writeln!(file, "This is just a plain text file").unwrap();
        writeln!(file, "with .asc extension but no PGP content").unwrap();
        file.flush().unwrap();

        assert!(!is_encrypted_file(file.path()));
    }

    #[test]
    fn test_decrypt_gpg_file_missing_gpg() {
        // Create a fake .gpg file
        let mut file = NamedTempFile::with_suffix(".gpg").unwrap();
        writeln!(file, "fake encrypted content").unwrap();
        file.flush().unwrap();

        // This will fail because the content isn't actually GPG-encrypted
        // (or gpg isn't installed, or there's no matching key)
        let result = decrypt_gpg_file(file.path());
        assert!(result.is_err());

        if let Err(LoadError::Decryption { path, message }) = result {
            assert_eq!(path, file.path().to_path_buf());
            assert!(!message.is_empty());
        } else {
            panic!("Expected Decryption error");
        }
    }
}
