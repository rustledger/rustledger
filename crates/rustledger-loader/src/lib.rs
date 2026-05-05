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

#[cfg(feature = "cache")]
pub mod cache;
mod options;
#[cfg(any(feature = "booking", feature = "plugins", feature = "validation"))]
mod process;
mod source_map;
mod vfs;

#[cfg(feature = "cache")]
pub use cache::{
    CACHE_FILENAME_ENV, CacheEntry, CachedOptions, CachedPlugin, DISABLE_CACHE_ENV,
    cache_disabled_by_env, cache_path, default_cache_path, invalidate_cache, load_cache_entry,
    reintern_directives, reintern_plain_directives, save_cache_entry,
};
pub use options::Options;
pub use source_map::{SourceFile, SourceMap};
pub use vfs::{DiskFileSystem, FileSystem, VirtualFileSystem};

// Re-export processing API when features are enabled
#[cfg(feature = "plugins")]
pub use process::run_plugins;
#[cfg(any(feature = "booking", feature = "plugins", feature = "validation"))]
pub use process::{
    ErrorLocation, ErrorSeverity, Ledger, LedgerError, LoadOptions, ProcessError, load, load_raw,
    process,
};

use rustledger_core::{Directive, DisplayContext};
use rustledger_parser::{ParseError, Span, Spanned};
use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::process::Command;
use thiserror::Error;

/// Try to canonicalize a path, falling back to making it absolute if canonicalize
/// is not supported (e.g., on WASI).
///
/// This function:
/// 1. First tries `fs::canonicalize()` which resolves symlinks and returns absolute path
/// 2. If that fails (e.g., WASI doesn't support it), tries to make an absolute path manually
/// 3. As a last resort, returns the original path
fn normalize_path(path: &Path) -> PathBuf {
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
    ///
    /// The Display string intentionally begins with `Duplicate filename
    /// parsed:` to match Python beancount's wording for the same
    /// condition. The pta-standards `include-cycle-detection`
    /// conformance test asserts on the substring `"Duplicate filename"`,
    /// so this wording is load-bearing (#765). The full cycle path is
    /// preserved in a trailing parenthetical for debuggability.
    #[error(
        "Duplicate filename parsed: \"{}\" (include cycle: {})",
        .cycle.last().map_or("", String::as_str),
        .cycle.join(" -> ")
    )]
    IncludeCycle {
        /// The cycle of file paths. The last element is the
        /// re-encountered filename (equal to one of the earlier
        /// entries), and it's the one quoted in the `"Duplicate
        /// filename parsed:"` prefix.
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

    /// Glob pattern did not match any files.
    #[error("include pattern \"{pattern}\" does not match any files")]
    GlobNoMatch {
        /// The glob pattern that matched nothing.
        pattern: String,
    },

    /// Glob pattern expansion failed.
    #[error("failed to expand include pattern \"{pattern}\": {message}")]
    GlobError {
        /// The glob pattern that failed.
        pattern: String,
        /// The error message.
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
    /// Display context for formatting numbers (tracks precision per currency).
    pub display_context: DisplayContext,
}

/// A plugin directive.
#[derive(Debug, Clone)]
pub struct Plugin {
    /// Plugin module name (with any `python:` prefix stripped).
    pub name: String,
    /// Optional configuration string.
    pub config: Option<String>,
    /// Source location.
    pub span: Span,
    /// File this plugin was declared in.
    pub file_id: usize,
    /// Whether the `python:` prefix was used to force Python execution.
    pub force_python: bool,
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
#[derive(Debug)]
pub struct Loader {
    /// Files that have been loaded (for cycle detection).
    loaded_files: HashSet<PathBuf>,
    /// Stack for cycle detection during loading (maintains order for error messages).
    include_stack: Vec<PathBuf>,
    /// Set for O(1) cycle detection (mirrors `include_stack`).
    include_stack_set: HashSet<PathBuf>,
    /// Root directory for path traversal protection.
    /// If set, includes must resolve to paths within this directory.
    root_dir: Option<PathBuf>,
    /// Whether to enforce path traversal protection.
    enforce_path_security: bool,
    /// Filesystem abstraction for reading files.
    fs: Box<dyn FileSystem>,
}

impl Default for Loader {
    fn default() -> Self {
        Self {
            loaded_files: HashSet::new(),
            include_stack: Vec::new(),
            include_stack_set: HashSet::new(),
            root_dir: None,
            enforce_path_security: false,
            fs: Box::new(DiskFileSystem),
        }
    }
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

    /// Set a custom filesystem for file loading.
    ///
    /// This allows using a virtual filesystem (e.g., for WASM) instead of
    /// the default disk filesystem.
    ///
    /// # Example
    ///
    /// ```
    /// use rustledger_loader::{Loader, VirtualFileSystem};
    ///
    /// let mut vfs = VirtualFileSystem::new();
    /// vfs.add_file("main.beancount", "2024-01-01 open Assets:Bank USD");
    ///
    /// let loader = Loader::new().with_filesystem(Box::new(vfs));
    /// ```
    #[must_use]
    pub fn with_filesystem(mut self, fs: Box<dyn FileSystem>) -> Self {
        self.fs = fs;
        self
    }

    /// Load a beancount file and all its includes.
    ///
    /// Uses parallel file parsing when multiple files are discovered via
    /// include directives. The root file is parsed first to resolve the
    /// include tree, then all included files are read and parsed in
    /// parallel using rayon.
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

        // Get normalized path (uses filesystem-specific normalization)
        let canonical = self.fs.normalize(path);

        // Set root directory for path security if enabled but not explicitly set
        if self.enforce_path_security && self.root_dir.is_none() {
            self.root_dir = canonical.parent().map(Path::to_path_buf);
        }

        // Phase 1: Parse the root file to discover includes.
        // The root file is typically small (just includes + options).
        self.load_recursive(
            &canonical,
            None,
            &mut directives,
            &mut options,
            &mut plugins,
            &mut source_map,
            &mut errors,
        )?;

        // Build display context from directives and options
        let display_context = build_display_context(&directives, &options);

        Ok(LoadResult {
            directives,
            options,
            plugins,
            source_map,
            errors,
            display_context,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn load_recursive(
        &mut self,
        path: &Path,
        pre_parsed: Option<(std::sync::Arc<str>, rustledger_parser::ParseResult)>,
        directives: &mut Vec<Spanned<Directive>>,
        options: &mut Options,
        plugins: &mut Vec<Plugin>,
        source_map: &mut SourceMap,
        errors: &mut Vec<LoadError>,
    ) -> Result<(), LoadError> {
        // Allocate path once for reuse
        let path_buf = path.to_path_buf();

        // Check for cycles using O(1) HashSet lookup
        if self.include_stack_set.contains(&path_buf) {
            // `collect::<Vec<_>>()` on a chain of two `ExactSizeIterator`s
            // preallocates the exact capacity via `size_hint`, so an
            // explicit `Vec::with_capacity(...)` + `extend` + `push` is
            // equivalent and noisier. This is the cycle-error cold path
            // anyway — readability wins over micro-optimization.
            let cycle: Vec<String> = self
                .include_stack
                .iter()
                .map(|p| p.display().to_string())
                .chain(std::iter::once(path.display().to_string()))
                .collect();
            return Err(LoadError::IncludeCycle { cycle });
        }

        // Check if already loaded
        if self.loaded_files.contains(&path_buf) {
            return Ok(());
        }

        // Use pre-parsed data if available (from parallel loading path),
        // otherwise read and parse the file.
        let (source, result) = if let Some(pre) = pre_parsed {
            pre
        } else {
            let src: std::sync::Arc<str> = if self.fs.is_encrypted(path) {
                decrypt_gpg_file(path)?.into()
            } else {
                self.fs.read(path)?
            };
            let parsed = rustledger_parser::parse(&src);
            (src, parsed)
        };

        // Add to source map (Arc::clone is cheap - just increments refcount)
        let file_id = source_map.add_file(path_buf.clone(), std::sync::Arc::clone(&source));

        // Mark as loading (update both stack and set)
        self.include_stack_set.insert(path_buf.clone());
        self.include_stack.push(path_buf.clone());
        self.loaded_files.insert(path_buf);

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
            // Check for "python:" prefix to force Python execution
            let (actual_name, force_python) = if let Some(stripped) = name.strip_prefix("python:") {
                (stripped.to_string(), true)
            } else {
                (name, false)
            };
            plugins.push(Plugin {
                name: actual_name,
                config,
                span,
                file_id,
                force_python,
            });
        }

        // Process includes (with glob pattern support)
        let base_dir = path.parent().unwrap_or(Path::new("."));
        for (include_path, _span) in &result.includes {
            // Check if the include path contains glob metacharacters
            // (check on include_path, not full_path, to avoid false positives from directory names)
            let has_glob = include_path.contains('*')
                || include_path.contains('?')
                || include_path.contains('[');

            let full_path = base_dir.join(include_path);

            // Path traversal protection: check BEFORE glob expansion to avoid
            // enumerating files outside the allowed root directory
            if self.enforce_path_security
                && let Some(ref root) = self.root_dir
            {
                // For glob patterns, extract and check the non-glob prefix
                let path_to_check = if has_glob {
                    // Find where the first glob metacharacter is
                    let glob_start = include_path
                        .find(['*', '?', '['])
                        .unwrap_or(include_path.len());
                    // Get the directory prefix before the glob
                    let prefix = &include_path[..glob_start];
                    let prefix_path = if let Some(last_sep) = prefix.rfind('/') {
                        base_dir.join(&include_path[..=last_sep])
                    } else {
                        base_dir.to_path_buf()
                    };
                    normalize_path(&prefix_path)
                } else {
                    normalize_path(&full_path)
                };

                if !path_to_check.starts_with(root) {
                    errors.push(LoadError::PathTraversal {
                        include_path: include_path.clone(),
                        base_dir: root.clone(),
                    });
                    continue;
                }
            }

            let full_path_str = full_path.to_string_lossy();

            // Expand glob patterns or use literal path
            let paths_to_load: Vec<PathBuf> = if has_glob {
                match self.fs.glob(&full_path_str) {
                    Ok(matched) => matched,
                    Err(e) => {
                        errors.push(LoadError::GlobError {
                            pattern: include_path.clone(),
                            message: e,
                        });
                        continue;
                    }
                }
            } else {
                vec![full_path.clone()]
            };

            // Check if glob matched nothing
            if has_glob && paths_to_load.is_empty() {
                errors.push(LoadError::GlobNoMatch {
                    pattern: include_path.clone(),
                });
                continue;
            }

            // Normalize and security-check all matched paths first.
            let mut valid_paths = Vec::with_capacity(paths_to_load.len());
            for matched_path in paths_to_load {
                let canonical = self.fs.normalize(&matched_path);

                // Security check: glob could match files outside root via symlinks
                if self.enforce_path_security
                    && let Some(ref root) = self.root_dir
                    && !canonical.starts_with(root)
                {
                    errors.push(LoadError::PathTraversal {
                        include_path: matched_path.to_string_lossy().into_owned(),
                        base_dir: root.clone(),
                    });
                    continue;
                }

                valid_paths.push(canonical);
            }

            // Parallel optimization: when loading multiple sibling includes
            // from disk, read and parse them in parallel. The expensive work
            // (I/O + tokenize + parse) runs on rayon's thread pool while the
            // main thread coordinates the include tree walk.
            //
            // Each file is read and parsed independently. Results are then
            // merged sequentially to preserve include order and process any
            // nested includes via recursive calls.
            if valid_paths.len() > 1 && self.fs.supports_parallel_read() {
                use rayon::prelude::*;

                // Read + parse non-encrypted files in parallel, preserving
                // original include order. Each entry becomes either
                // Some((source, parsed)) for successful reads, or None for
                // encrypted/failed files (which fall back to sequential).
                //
                // We keep the original index to merge results in order,
                // ensuring option/directive precedence matches the declared
                // include sequence.
                let fs = &*self.fs;
                let pre_parsed: Vec<Option<(std::sync::Arc<str>, rustledger_parser::ParseResult)>> =
                    valid_paths
                        .par_iter()
                        .map(|p| {
                            // Skip encrypted files — they need sequential GPG decryption
                            if fs.is_encrypted(p) {
                                return None;
                            }
                            // Read through the FileSystem trait so all I/O goes
                            // through one code path (UTF-8 handling, error types, etc.)
                            let source = fs.read(p).ok()?;
                            let parsed = rustledger_parser::parse(&source);
                            Some((source, parsed))
                        })
                        .collect();

                // Merge in original include order. Files that were
                // pre-parsed pass their data to load_recursive; files
                // that weren't (encrypted or I/O error) are loaded
                // sequentially as a fallback.
                for (canonical, pre) in valid_paths.iter().zip(pre_parsed) {
                    if let Err(e) = self.load_recursive(
                        canonical, pre, directives, options, plugins, source_map, errors,
                    ) {
                        errors.push(e);
                    }
                }
            } else {
                // Sequential fallback: single file or VFS.
                for canonical in valid_paths {
                    if let Err(e) = self.load_recursive(
                        &canonical, None, directives, options, plugins, source_map, errors,
                    ) {
                        errors.push(e);
                    }
                }
            }
        }

        // Add directives from this file, setting the file_id
        directives.extend(
            result
                .directives
                .into_iter()
                .map(|d| d.with_file_id(file_id)),
        );

        // Pop from stack and set
        if let Some(popped) = self.include_stack.pop() {
            self.include_stack_set.remove(&popped);
        }

        Ok(())
    }
}

/// Build a display context from loaded directives and options.
///
/// This scans all directives for amounts and tracks the maximum precision seen
/// for each currency. Fixed precisions from `option "display_precision"` override
/// the inferred values.
fn build_display_context(directives: &[Spanned<Directive>], options: &Options) -> DisplayContext {
    let mut ctx = DisplayContext::new();

    // Set render_commas from options
    ctx.set_render_commas(options.render_commas);

    // Scan directives for amounts to infer precision
    for spanned in directives {
        match &spanned.value {
            Directive::Transaction(txn) => {
                for posting in &txn.postings {
                    // Units (IncompleteAmount)
                    if let Some(ref units) = posting.units
                        && let (Some(number), Some(currency)) = (units.number(), units.currency())
                    {
                        ctx.update(number, currency);
                    }
                    // Cost (CostSpec)
                    if let Some(ref cost) = posting.cost
                        && let (Some(number), Some(currency)) =
                            (cost.number_per.or(cost.number_total), &cost.currency)
                    {
                        ctx.update(number, currency.as_str());
                    }
                    // Price annotations: included so the per-currency dist
                    // sees them, matching Python beancount's DisplayContext
                    // population. With the default `Precision::MostCommon`
                    // policy (introduced for bean-query parity), high-
                    // precision computed exchange rates are naturally
                    // ignored by the mode — they're a small minority next
                    // to mainstream postings. Pre-fix (under MAX policy)
                    // they were excluded to avoid inflating display
                    // precision; that exclusion is no longer needed.
                    if let Some(ref price) = posting.price
                        && let Some(amount) = price.amount()
                    {
                        ctx.update(amount.number, amount.currency.as_str());
                    }
                }
            }
            Directive::Balance(bal) => {
                ctx.update(bal.amount.number, bal.amount.currency.as_str());
                if let Some(tol) = bal.tolerance {
                    ctx.update(tol, bal.amount.currency.as_str());
                }
            }
            Directive::Price(p) => {
                // Same rationale as posting price annotations above —
                // included now that MostCommon is the default. The single
                // 28dp computed-rate price won't shift the mode for a
                // currency with hundreds of mainstream postings.
                ctx.update(p.amount.number, p.amount.currency.as_str());
            }
            Directive::Pad(_)
            | Directive::Open(_)
            | Directive::Close(_)
            | Directive::Commodity(_)
            | Directive::Event(_)
            | Directive::Query(_)
            | Directive::Note(_)
            | Directive::Document(_)
            | Directive::Custom(_) => {}
        }
    }

    // Apply fixed precisions from options (these override inferred values)
    for (currency, precision) in &options.display_precision {
        ctx.set_fixed_precision(currency, *precision);
    }

    ctx
}

/// Load a beancount file without processing.
///
/// This is a convenience function that creates a loader and loads a single file.
/// For fully processed results (booking, plugins, validation), use the
/// [`load`] function with [`LoadOptions`] instead.
#[cfg(not(any(feature = "booking", feature = "plugins", feature = "validation")))]
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
        let fs = DiskFileSystem;
        let path = Path::new("test.beancount.gpg");
        assert!(fs.is_encrypted(path));
    }

    #[test]
    fn test_is_encrypted_file_plain_beancount() {
        let fs = DiskFileSystem;
        let path = Path::new("test.beancount");
        assert!(!fs.is_encrypted(path));
    }

    #[test]
    fn test_is_encrypted_file_asc_with_pgp_header() {
        let fs = DiskFileSystem;
        let mut file = NamedTempFile::with_suffix(".asc").unwrap();
        writeln!(file, "-----BEGIN PGP MESSAGE-----").unwrap();
        writeln!(file, "some encrypted content").unwrap();
        writeln!(file, "-----END PGP MESSAGE-----").unwrap();
        file.flush().unwrap();

        assert!(fs.is_encrypted(file.path()));
    }

    #[test]
    fn test_is_encrypted_file_asc_without_pgp_header() {
        let fs = DiskFileSystem;
        let mut file = NamedTempFile::with_suffix(".asc").unwrap();
        writeln!(file, "This is just a plain text file").unwrap();
        writeln!(file, "with .asc extension but no PGP content").unwrap();
        file.flush().unwrap();

        assert!(!fs.is_encrypted(file.path()));
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

    #[test]
    fn test_plugin_force_python_prefix() {
        let mut file = NamedTempFile::with_suffix(".beancount").unwrap();
        writeln!(file, r#"plugin "python:my_plugin""#).unwrap();
        writeln!(file, r#"plugin "regular_plugin""#).unwrap();
        file.flush().unwrap();

        let result = Loader::new().load(file.path()).unwrap();

        assert_eq!(result.plugins.len(), 2);

        // First plugin should have force_python = true and name without prefix
        assert_eq!(result.plugins[0].name, "my_plugin");
        assert!(result.plugins[0].force_python);

        // Second plugin should have force_python = false
        assert_eq!(result.plugins[1].name, "regular_plugin");
        assert!(!result.plugins[1].force_python);
    }

    #[test]
    fn test_plugin_force_python_with_config() {
        let mut file = NamedTempFile::with_suffix(".beancount").unwrap();
        writeln!(file, r#"plugin "python:my_plugin" "config_value""#).unwrap();
        file.flush().unwrap();

        let result = Loader::new().load(file.path()).unwrap();

        assert_eq!(result.plugins.len(), 1);
        assert_eq!(result.plugins[0].name, "my_plugin");
        assert!(result.plugins[0].force_python);
        assert_eq!(result.plugins[0].config, Some("config_value".to_string()));
    }

    #[test]
    fn test_virtual_filesystem_include_resolution() {
        // Create a virtual filesystem with multiple files
        let mut vfs = VirtualFileSystem::new();
        vfs.add_file(
            "main.beancount",
            r#"
include "accounts.beancount"

2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD
"#,
        );
        vfs.add_file(
            "accounts.beancount",
            r"
2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD
",
        );

        // Load with virtual filesystem
        let result = Loader::new()
            .with_filesystem(Box::new(vfs))
            .load(Path::new("main.beancount"))
            .unwrap();

        // Should have 3 directives: 2 opens + 1 transaction
        assert_eq!(result.directives.len(), 3);
        assert!(result.errors.is_empty());

        // Verify directive types
        let directive_types: Vec<_> = result
            .directives
            .iter()
            .map(|d| match &d.value {
                rustledger_core::Directive::Open(_) => "open",
                rustledger_core::Directive::Transaction(_) => "txn",
                _ => "other",
            })
            .collect();
        assert_eq!(directive_types, vec!["open", "open", "txn"]);
    }

    #[test]
    fn test_virtual_filesystem_nested_includes() {
        // Test deeply nested includes
        let mut vfs = VirtualFileSystem::new();
        vfs.add_file("main.beancount", r#"include "level1.beancount""#);
        vfs.add_file(
            "level1.beancount",
            r#"
include "level2.beancount"
2024-01-01 open Assets:Level1 USD
"#,
        );
        vfs.add_file("level2.beancount", "2024-01-01 open Assets:Level2 USD");

        let result = Loader::new()
            .with_filesystem(Box::new(vfs))
            .load(Path::new("main.beancount"))
            .unwrap();

        // Should have 2 open directives from nested includes
        assert_eq!(result.directives.len(), 2);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn test_virtual_filesystem_missing_include() {
        let mut vfs = VirtualFileSystem::new();
        vfs.add_file("main.beancount", r#"include "nonexistent.beancount""#);

        let result = Loader::new()
            .with_filesystem(Box::new(vfs))
            .load(Path::new("main.beancount"))
            .unwrap();

        // Should have an error for missing file
        assert!(!result.errors.is_empty());
        let error_msg = result.errors[0].to_string();
        assert!(error_msg.contains("not found") || error_msg.contains("Io"));
    }

    #[test]
    fn test_virtual_filesystem_glob_include() {
        let mut vfs = VirtualFileSystem::new();
        vfs.add_file(
            "main.beancount",
            r#"
include "transactions/*.beancount"

2024-01-01 open Assets:Bank USD
"#,
        );
        vfs.add_file(
            "transactions/2024.beancount",
            r#"
2024-01-01 open Expenses:Food USD

2024-06-15 * "Groceries"
  Expenses:Food  50.00 USD
  Assets:Bank   -50.00 USD
"#,
        );
        vfs.add_file(
            "transactions/2025.beancount",
            r#"
2025-01-01 open Expenses:Rent USD

2025-02-01 * "Rent"
  Expenses:Rent  1000.00 USD
  Assets:Bank   -1000.00 USD
"#,
        );
        // This file should NOT be matched by the glob
        vfs.add_file(
            "other/ignored.beancount",
            "2024-01-01 open Expenses:Other USD",
        );

        let result = Loader::new()
            .with_filesystem(Box::new(vfs))
            .load(Path::new("main.beancount"))
            .unwrap();

        // Should have: 1 open from main + 2 opens from transactions + 2 txns
        let opens = result
            .directives
            .iter()
            .filter(|d| matches!(d.value, rustledger_core::Directive::Open(_)))
            .count();
        assert_eq!(
            opens, 3,
            "expected 3 open directives (1 main + 2 transactions)"
        );

        let txns = result
            .directives
            .iter()
            .filter(|d| matches!(d.value, rustledger_core::Directive::Transaction(_)))
            .count();
        assert_eq!(txns, 2, "expected 2 transactions from glob-matched files");

        assert!(
            result.errors.is_empty(),
            "expected no errors, got: {:?}",
            result.errors
        );
    }

    #[test]
    fn test_virtual_filesystem_glob_dot_slash_prefix() {
        let mut vfs = VirtualFileSystem::new();
        vfs.add_file(
            "main.beancount",
            r#"
include "./transactions/*.beancount"

2024-01-01 open Assets:Bank USD
"#,
        );
        vfs.add_file(
            "transactions/2024.beancount",
            r#"
2024-01-01 open Expenses:Food USD

2024-06-15 * "Groceries"
  Expenses:Food  50.00 USD
  Assets:Bank   -50.00 USD
"#,
        );
        vfs.add_file(
            "transactions/2025.beancount",
            r#"
2025-01-01 open Expenses:Rent USD

2025-02-01 * "Rent"
  Expenses:Rent  1000.00 USD
  Assets:Bank   -1000.00 USD
"#,
        );

        let result = Loader::new()
            .with_filesystem(Box::new(vfs))
            .load(Path::new("main.beancount"))
            .unwrap();

        // Should have: 1 open from main + 2 opens from transactions + 2 txns
        let opens = result
            .directives
            .iter()
            .filter(|d| matches!(d.value, rustledger_core::Directive::Open(_)))
            .count();
        assert_eq!(
            opens, 3,
            "expected 3 open directives (1 main + 2 transactions), ./ prefix should be normalized"
        );

        let txns = result
            .directives
            .iter()
            .filter(|d| matches!(d.value, rustledger_core::Directive::Transaction(_)))
            .count();
        assert_eq!(
            txns, 2,
            "expected 2 transactions from glob-matched files despite ./ prefix"
        );

        assert!(
            result.errors.is_empty(),
            "expected no errors, got: {:?}",
            result.errors
        );
    }

    #[test]
    fn test_virtual_filesystem_glob_no_match() {
        let mut vfs = VirtualFileSystem::new();
        vfs.add_file("main.beancount", r#"include "nonexistent/*.beancount""#);

        let result = Loader::new()
            .with_filesystem(Box::new(vfs))
            .load(Path::new("main.beancount"))
            .unwrap();

        // Should have a GlobNoMatch error
        let has_glob_error = result
            .errors
            .iter()
            .any(|e| matches!(e, LoadError::GlobNoMatch { .. }));
        assert!(
            has_glob_error,
            "expected GlobNoMatch error, got: {:?}",
            result.errors
        );
    }
}
