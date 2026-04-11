//! Virtual filesystem abstraction for platform-agnostic file loading.
//!
//! This module provides a trait for abstracting file system operations,
//! enabling the loader to work with both real filesystems and in-memory
//! file maps (useful for WASM environments).
//!
//! # Performance
//!
//! Uses SIMD-accelerated UTF-8 validation (simdutf8) for 2-4x faster
//! file loading on large files.

use crate::LoadError;
use simdutf8::ascii;
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// Abstract file system interface for file loading.
///
/// This trait allows the loader to work with different file system backends:
/// - [`DiskFileSystem`]: Reads from the actual filesystem (default)
/// - [`VirtualFileSystem`]: Reads from an in-memory file map (for WASM)
pub trait FileSystem: Send + Sync + std::fmt::Debug {
    /// Read file content at the given path.
    ///
    /// # Errors
    ///
    /// Returns [`LoadError::Io`] if the file cannot be read.
    fn read(&self, path: &Path) -> Result<Arc<str>, LoadError>;

    /// Check if a file exists at the given path.
    fn exists(&self, path: &Path) -> bool;

    /// Check if a path is a GPG-encrypted file.
    ///
    /// For virtual filesystems, this always returns false since
    /// encrypted files should be decrypted before being added.
    fn is_encrypted(&self, path: &Path) -> bool;

    /// Normalize a path for this filesystem.
    ///
    /// For disk filesystems, this makes paths absolute.
    /// For virtual filesystems, this just cleans up the path.
    fn normalize(&self, path: &Path) -> PathBuf;

    /// Expand a glob pattern and return matching paths.
    ///
    /// # Errors
    ///
    /// Returns an error string if the pattern is invalid.
    fn glob(&self, pattern: &str) -> Result<Vec<PathBuf>, String> {
        let _ = pattern;
        Err("glob is not supported by this filesystem".to_string())
    }
}

/// Default filesystem that reads from disk.
///
/// This is the standard implementation used by the CLI and other
/// filesystem-based tools.
#[derive(Debug, Default, Clone)]
pub struct DiskFileSystem;

impl FileSystem for DiskFileSystem {
    fn read(&self, path: &Path) -> Result<Arc<str>, LoadError> {
        let bytes = fs::read(path).map_err(|e| LoadError::Io {
            path: path.to_path_buf(),
            source: e,
        })?;

        // Use SIMD-accelerated UTF-8 validation for faster loading
        // simdutf8 is 2-4x faster than std::str::from_utf8 on large files
        let content = if ascii::validate_utf8(&bytes) {
            // Fast path: pure ASCII, safe to convert directly
            unsafe { String::from_utf8_unchecked(bytes) }
        } else {
            // SIMD UTF-8 validation for non-ASCII content
            match simdutf8::utf8::validate_utf8(&bytes) {
                true => unsafe { String::from_utf8_unchecked(bytes) },
                false => String::from_utf8_lossy(&bytes).into_owned(),
            }
        };

        Ok(content.into())
    }

    fn exists(&self, path: &Path) -> bool {
        path.exists()
    }

    fn is_encrypted(&self, path: &Path) -> bool {
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

    fn normalize(&self, path: &Path) -> PathBuf {
        // Try canonicalize first (works on most platforms, resolves symlinks)
        if let Ok(canonical) = path.canonicalize() {
            return canonical;
        }

        // Fallback: make absolute without resolving symlinks (WASI-compatible)
        if path.is_absolute() {
            path.to_path_buf()
        } else if let Ok(cwd) = std::env::current_dir() {
            // Join with current directory and clean up the path
            let mut result = cwd;
            for component in path.components() {
                match component {
                    std::path::Component::ParentDir => {
                        result.pop();
                    }
                    std::path::Component::Normal(s) => {
                        result.push(s);
                    }
                    std::path::Component::CurDir => {}
                    std::path::Component::RootDir => {
                        result = PathBuf::from("/");
                    }
                    std::path::Component::Prefix(p) => {
                        result = PathBuf::from(p.as_os_str());
                    }
                }
            }
            result
        } else {
            // Last resort: just return the path as-is
            path.to_path_buf()
        }
    }

    fn glob(&self, pattern: &str) -> Result<Vec<PathBuf>, String> {
        let entries = glob::glob(pattern).map_err(|e| e.to_string())?;
        // Skip entries that error (e.g., permission denied) rather than
        // failing the entire glob. The loader will catch missing/unreadable
        // files later when it tries to read them.
        let mut matched: Vec<PathBuf> = entries.filter_map(Result::ok).collect();
        matched.sort();
        Ok(matched)
    }
}

/// In-memory virtual filesystem for WASM and testing.
///
/// This implementation stores files in a `HashMap`, allowing the loader
/// to resolve includes without actual filesystem access. This is essential
/// for WASM environments where filesystem access is not available.
///
/// # Example
///
/// ```
/// use rustledger_loader::VirtualFileSystem;
/// use std::path::PathBuf;
///
/// let mut vfs = VirtualFileSystem::new();
/// vfs.add_file("main.beancount", "include \"accounts.beancount\"");
/// vfs.add_file("accounts.beancount", "2024-01-01 open Assets:Bank USD");
/// ```
#[derive(Debug, Default, Clone)]
pub struct VirtualFileSystem {
    files: HashMap<PathBuf, Arc<str>>,
}

impl VirtualFileSystem {
    /// Create a new empty virtual filesystem.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a file to the virtual filesystem.
    ///
    /// The path is normalized to handle different path separators
    /// and relative paths consistently.
    pub fn add_file(&mut self, path: impl AsRef<Path>, content: impl Into<String>) {
        let normalized = normalize_vfs_path(path.as_ref());
        self.files.insert(normalized, content.into().into());
    }

    /// Add multiple files from a map.
    ///
    /// This is a convenience method for adding many files at once.
    pub fn add_files(
        &mut self,
        files: impl IntoIterator<Item = (impl AsRef<Path>, impl Into<String>)>,
    ) {
        for (path, content) in files {
            self.add_file(path, content);
        }
    }

    /// Create a virtual filesystem from a map of files.
    #[must_use]
    pub fn from_files(
        files: impl IntoIterator<Item = (impl AsRef<Path>, impl Into<String>)>,
    ) -> Self {
        let mut vfs = Self::new();
        vfs.add_files(files);
        vfs
    }

    /// Get the number of files in the virtual filesystem.
    #[must_use]
    pub fn len(&self) -> usize {
        self.files.len()
    }

    /// Check if the virtual filesystem is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.files.is_empty()
    }
}

impl FileSystem for VirtualFileSystem {
    fn read(&self, path: &Path) -> Result<Arc<str>, LoadError> {
        let normalized = normalize_vfs_path(path);

        self.files
            .get(&normalized)
            .cloned()
            .ok_or_else(|| LoadError::Io {
                path: path.to_path_buf(),
                source: std::io::Error::new(
                    std::io::ErrorKind::NotFound,
                    format!("file not found in virtual filesystem: {}", path.display()),
                ),
            })
    }

    fn exists(&self, path: &Path) -> bool {
        let normalized = normalize_vfs_path(path);
        self.files.contains_key(&normalized)
    }

    fn is_encrypted(&self, _path: &Path) -> bool {
        // Virtual filesystem doesn't support encrypted files
        // Users should decrypt before adding to VFS
        false
    }

    fn normalize(&self, path: &Path) -> PathBuf {
        // For virtual filesystem, just clean up the path without making it absolute
        normalize_vfs_path(path)
    }

    fn glob(&self, pattern: &str) -> Result<Vec<PathBuf>, String> {
        // Normalize the pattern the same way stored keys are normalized,
        // so that backslashes or leading "./" in the pattern still match.
        let normalized = pattern.replace('\\', "/");
        let normalized = normalized.strip_prefix("./").unwrap_or(&normalized);
        let glob_pattern = glob::Pattern::new(normalized).map_err(|e| e.to_string())?;
        let mut matched: Vec<PathBuf> = self
            .files
            .keys()
            .filter(|path| glob_pattern.matches_path(path))
            .cloned()
            .collect();
        matched.sort();
        Ok(matched)
    }
}

/// Normalize a path for virtual filesystem storage and lookup.
///
/// This handles:
/// - Converting backslashes to forward slashes
/// - Removing leading `./`
/// - Simplifying `..` components where possible
fn normalize_vfs_path(path: &Path) -> PathBuf {
    let path_str = path.to_string_lossy();

    // Convert backslashes to forward slashes
    let normalized = path_str.replace('\\', "/");

    // Remove leading ./
    let normalized = normalized.strip_prefix("./").unwrap_or(&normalized);

    // Build normalized path
    let mut components = Vec::new();
    for part in normalized.split('/') {
        match part {
            "" | "." => {}
            ".." => {
                // Only pop if we have non-root components
                if !components.is_empty() && components.last() != Some(&"..") {
                    components.pop();
                } else {
                    components.push("..");
                }
            }
            _ => components.push(part),
        }
    }

    if components.is_empty() {
        PathBuf::from(".")
    } else {
        PathBuf::from(components.join("/"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_normalize_vfs_path() {
        assert_eq!(
            normalize_vfs_path(Path::new("foo/bar")),
            PathBuf::from("foo/bar")
        );
        assert_eq!(
            normalize_vfs_path(Path::new("./foo/bar")),
            PathBuf::from("foo/bar")
        );
        assert_eq!(
            normalize_vfs_path(Path::new("foo/../bar")),
            PathBuf::from("bar")
        );
        assert_eq!(
            normalize_vfs_path(Path::new("foo/./bar")),
            PathBuf::from("foo/bar")
        );
        assert_eq!(
            normalize_vfs_path(Path::new("foo\\bar")),
            PathBuf::from("foo/bar")
        );
    }

    #[test]
    fn test_virtual_filesystem_basic() {
        let mut vfs = VirtualFileSystem::new();
        vfs.add_file("test.beancount", "2024-01-01 open Assets:Bank USD");

        assert!(vfs.exists(Path::new("test.beancount")));
        assert!(!vfs.exists(Path::new("nonexistent.beancount")));

        let content = vfs.read(Path::new("test.beancount")).unwrap();
        assert_eq!(&*content, "2024-01-01 open Assets:Bank USD");
    }

    #[test]
    fn test_virtual_filesystem_path_normalization() {
        let mut vfs = VirtualFileSystem::new();
        vfs.add_file("foo/bar.beancount", "content");

        // Should find with normalized path
        assert!(vfs.exists(Path::new("foo/bar.beancount")));
        assert!(vfs.exists(Path::new("./foo/bar.beancount")));

        // Content should be accessible
        let content = vfs.read(Path::new("./foo/bar.beancount")).unwrap();
        assert_eq!(&*content, "content");
    }

    #[test]
    fn test_virtual_filesystem_not_encrypted() {
        let vfs = VirtualFileSystem::new();

        // Virtual filesystem never reports files as encrypted
        assert!(!vfs.is_encrypted(Path::new("test.gpg")));
        assert!(!vfs.is_encrypted(Path::new("test.asc")));
    }

    #[test]
    fn test_virtual_filesystem_from_files() {
        let vfs = VirtualFileSystem::from_files([
            ("a.beancount", "content a"),
            ("b.beancount", "content b"),
        ]);

        assert_eq!(vfs.len(), 2);
        assert!(vfs.exists(Path::new("a.beancount")));
        assert!(vfs.exists(Path::new("b.beancount")));
    }
}
