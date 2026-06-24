//! Plugin dispatch: classify a plugin reference into a runtime, then run it.
//!
//! This is the single entry point the loader uses to invoke a `plugin "..."`
//! reference. It is deliberately split into two phases:
//!
//! - [`resolve_plugin`] — pure classification: native vs WASM vs Python,
//!   path-security, feature-gating, and the #1432 bare-module-name rejection.
//!   Returns a runnable [`ResolvedPlugin`] or a typed [`PluginResolveError`].
//! - [`ResolvedPlugin::run`] — execute the chosen runtime, returning the plugin's
//!   [`PluginOutput`] (ops + diagnostics) or a typed [`PluginRunError`].
//!
//! Errors are typed (not host `LedgerError`s) so the loader keeps ownership of
//! its error-code convention: it maps these kinds to `E8001/E8002/E8004/E8005`
//! and records diagnostics through one uniform path. The split lets the loader
//! build wrappers and apply ops once per plugin instead of once per runtime.

use std::path::Path;

use crate::native::{NativePlugin, NativePluginRegistry};
use crate::{DirectiveWrapper, PluginInput, PluginOptions, PluginOutput};

/// Which pass's native plugins to resolve.
///
/// Native plugins are partitioned into synth (pre-booking) and regular
/// (post-booking) registries; a `RegularPlugin` is never returned from the synth
/// lookup and vice versa.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PluginPass {
    /// Pre-booking synth plugins (`find_synth`).
    Synth,
    /// Post-booking regular plugins (`find_regular`).
    Regular,
}

/// A plugin reference resolved to a concrete runtime, ready to [`run`].
///
/// [`run`]: ResolvedPlugin::run
pub enum ResolvedPlugin<'a> {
    /// A native plugin from the typed registry (already matched to the pass).
    Native(&'a dyn NativePlugin),
    /// A WASM plugin file — path resolved and path-security-checked.
    #[cfg(feature = "wasm-runtime")]
    Wasm(std::path::PathBuf),
    /// A Python file-based plugin — path resolved and checked. Bare module-name
    /// references are rejected during resolution (#1432), so this is a file.
    #[cfg(feature = "python-plugins")]
    Python {
        /// The raw reference as written in `plugin "..."`.
        raw: String,
        /// The resolved absolute path.
        resolved: std::path::PathBuf,
    },
}

/// Why a plugin reference could not be resolved to a runnable runtime. The host
/// maps each kind to its own error code and message.
#[derive(Debug)]
pub enum PluginResolveError {
    /// The resolved path escapes the ledger base directory (path-security).
    PathOutsideBase {
        /// The offending reference.
        name: String,
    },
    /// A `.wasm` reference, but the WASM runtime is not compiled in.
    WasmFeatureDisabled {
        /// The reference.
        name: String,
    },
    /// A Python reference, but the Python runtime is not compiled in.
    PythonFeatureDisabled {
        /// The reference.
        name: String,
    },
    /// A bare Python module name (`plugin "pkg.mod"`), unsupported by design.
    /// `suggested_file` is the module's source path if system Python found it.
    PythonModuleName {
        /// The reference.
        name: String,
        /// Resolved source path, if discoverable.
        suggested_file: Option<String>,
    },
    /// An unknown reference (not native, WASM, or Python-shaped).
    NotFound {
        /// The reference.
        name: String,
        /// Resolved source path if system Python could find it as a module.
        suggested_file: Option<String>,
    },
}

/// Why a resolved plugin failed at runtime (load or execution).
#[derive(Debug)]
pub enum PluginRunError {
    /// A WASM plugin failed to load or execute. `message` is the inner reason.
    WasmFailed {
        /// The plugin file path.
        path: std::path::PathBuf,
        /// The underlying failure detail.
        message: String,
    },
    /// A Python plugin failed (runtime unavailable or execution error).
    PythonFailed {
        /// The full failure message.
        message: String,
    },
}

/// Classify a plugin invocation into a runnable [`ResolvedPlugin`].
///
/// Native plugins resolve through the typed registry keyed on `pass`; everything
/// else is classified by extension/shape. The Python file-vs-module test is the
/// single-sourced [`crate::python::is_python_plugin_file_ref`] criterion.
///
/// # Errors
///
/// Returns a [`PluginResolveError`] when the reference can't run: a path-security
/// violation, a bare module name (#1432), an unknown name, or a runtime whose
/// feature is disabled.
#[cfg_attr(
    not(any(feature = "wasm-runtime", feature = "python-plugins")),
    allow(unused_variables)
)]
pub fn resolve_plugin<'a>(
    name: &str,
    force_python: bool,
    pass: PluginPass,
    registry: &'a NativePluginRegistry,
    base_dir: &Path,
    path_security: bool,
) -> Result<ResolvedPlugin<'a>, PluginResolveError> {
    // Native plugins resolve through the typed registry keyed on the pass.
    // Prefixed names resolve via the short last segment inside the registry.
    let native: Option<&dyn NativePlugin> = if force_python {
        None
    } else {
        match pass {
            PluginPass::Synth => registry.find_synth(name).map(|p| p as &dyn NativePlugin),
            PluginPass::Regular => registry.find_regular(name).map(|p| p as &dyn NativePlugin),
        }
    };
    if let Some(plugin) = native {
        return Ok(ResolvedPlugin::Native(plugin));
    }

    // Not native — classify by extension / shape.
    let ext = Path::new(name)
        .extension()
        .and_then(|e| e.to_str())
        .unwrap_or("")
        .to_lowercase();

    if ext == "wasm" {
        #[cfg(feature = "wasm-runtime")]
        {
            return Ok(ResolvedPlugin::Wasm(resolve_path(
                name,
                base_dir,
                path_security,
            )?));
        }
        #[cfg(not(feature = "wasm-runtime"))]
        return Err(PluginResolveError::WasmFeatureDisabled {
            name: name.to_string(),
        });
    }

    if force_python || ext == "py" || name.contains(std::path::MAIN_SEPARATOR) || name.contains('.')
    {
        // Python module or file-based plugin (or `python:`-prefixed force_python).
        #[cfg(feature = "python-plugins")]
        {
            let resolved = resolve_path(name, base_dir, path_security)?;
            // A bare module name (`plugin "pkg.mod"`) is unsupported by design —
            // reject it up front with an actionable message rather than spinning
            // up the runtime just to fail and relabel the error (#1432).
            if is_python_module_name(&resolved, name) {
                return Err(PluginResolveError::PythonModuleName {
                    name: name.to_string(),
                    suggested_file: crate::python::suggest_module_path(name),
                });
            }
            return Ok(ResolvedPlugin::Python {
                raw: name.to_string(),
                resolved,
            });
        }
        #[cfg(not(feature = "python-plugins"))]
        return Err(PluginResolveError::PythonFeatureDisabled {
            name: name.to_string(),
        });
    }

    // Completely unknown plugin name. If system Python can resolve it as a
    // module, surface the file path; otherwise it is genuinely not found.
    #[cfg(feature = "python-plugins")]
    {
        Err(PluginResolveError::NotFound {
            name: name.to_string(),
            suggested_file: crate::python::suggest_module_path(name),
        })
    }
    #[cfg(not(feature = "python-plugins"))]
    Err(PluginResolveError::NotFound {
        name: name.to_string(),
        suggested_file: None,
    })
}

impl ResolvedPlugin<'_> {
    /// Execute the resolved plugin against `wrappers`, returning the plugin's
    /// [`PluginOutput`] (ops + diagnostics).
    ///
    /// # Errors
    ///
    /// Returns a [`PluginRunError`] only for a runtime-level failure (a WASM
    /// load/execution error or a Python execution error). Per-directive plugin
    /// diagnostics travel in `PluginOutput::errors`, not as an `Err`.
    #[cfg_attr(not(feature = "python-plugins"), allow(unused_variables))]
    pub fn run(
        &self,
        wrappers: Vec<DirectiveWrapper>,
        options: &PluginOptions,
        config: &Option<String>,
        base_dir: &Path,
    ) -> Result<PluginOutput, PluginRunError> {
        match self {
            ResolvedPlugin::Native(plugin) => Ok(plugin.process(PluginInput {
                directives: wrappers,
                options: options.clone(),
                config: config.clone(),
            })),
            #[cfg(feature = "wasm-runtime")]
            ResolvedPlugin::Wasm(path) => {
                let mut mgr = crate::PluginManager::new();
                let idx = mgr.load(path).map_err(|e| PluginRunError::WasmFailed {
                    path: path.clone(),
                    message: format!("failed to load: {e}"),
                })?;
                mgr.execute(
                    idx,
                    &PluginInput {
                        directives: wrappers,
                        options: options.clone(),
                        config: config.clone(),
                    },
                )
                .map_err(|e| PluginRunError::WasmFailed {
                    path: path.clone(),
                    message: format!("execution failed: {e}"),
                })
            }
            #[cfg(feature = "python-plugins")]
            ResolvedPlugin::Python { raw, resolved } => {
                let runtime = crate::python::PythonRuntime::new().map_err(|e| {
                    PluginRunError::PythonFailed {
                        message: format!("Python runtime unavailable: {e}"),
                    }
                })?;
                let input = PluginInput {
                    directives: wrappers,
                    options: options.clone(),
                    config: config.clone(),
                };
                // File-vs-module classifier matches the up-front #1432 rejection.
                if is_python_plugin_file(resolved, raw) {
                    runtime
                        .execute_module(raw, &input, Some(base_dir))
                        .map_err(|e| PluginRunError::PythonFailed {
                            message: format!("Python plugin execution failed: {e}"),
                        })
                } else {
                    runtime
                        .execute_module(raw, &input, Some(base_dir))
                        .map_err(|e| PluginRunError::PythonFailed {
                            message: format!("Python plugin '{raw}' execution failed: {e}"),
                        })
                }
            }
        }
    }
}

/// Resolve a plugin reference to a path under the ledger directory (absolute
/// when `base_dir` is — a relative `name` is joined onto `base_dir` as-is),
/// enforcing path-security fail-closed (see [`path_within_base`]).
#[cfg(any(feature = "wasm-runtime", feature = "python-plugins"))]
fn resolve_path(
    name: &str,
    base_dir: &Path,
    path_security: bool,
) -> Result<std::path::PathBuf, PluginResolveError> {
    let p = Path::new(name);
    let resolved = if p.is_absolute() {
        p.to_path_buf()
    } else {
        base_dir.join(name)
    };
    if path_security && !path_within_base(&resolved, base_dir) {
        return Err(PluginResolveError::PathOutsideBase {
            name: name.to_string(),
        });
    }
    Ok(resolved)
}

/// Whether `raw` is a bare Python *module name* (no `.py`, no separator, no such
/// file) rather than a file reference. Module names are unsupported (#1432).
#[cfg(feature = "python-plugins")]
fn is_python_module_name(resolved: &Path, raw: &str) -> bool {
    !is_python_plugin_file(resolved, raw)
}

/// Classify a Python reference as a FILE path: a file when it resolves to an
/// existing path, or its name is file-like by the shared
/// [`crate::python::is_python_plugin_file_ref`] criterion (`.py` or a separator).
#[cfg(feature = "python-plugins")]
fn is_python_plugin_file(resolved: &Path, raw: &str) -> bool {
    resolved.exists() || crate::python::is_python_plugin_file_ref(raw)
}

/// Lexically resolve `.` / `..` in `p` WITHOUT touching the filesystem, so a
/// `..` escape is caught even when the target does not exist on disk.
#[cfg(any(feature = "wasm-runtime", feature = "python-plugins"))]
fn lexically_normalize(p: &Path) -> std::path::PathBuf {
    use std::path::Component;
    let mut out = std::path::PathBuf::new();
    for comp in p.components() {
        match comp {
            Component::ParentDir => {
                if !out.pop() {
                    // `..` above the root is clamped (mirrors canonicalize).
                }
            }
            Component::CurDir => {}
            other => out.push(other.as_os_str()),
        }
    }
    out
}

/// True if `resolved` is inside `base_dir`.
///
/// Canonicalizes when the path exists (symlink-safe). ONLY a not-yet-existing
/// path (`NotFound`) falls back to the lexical `..` check; every other case —
/// the base failing to canonicalize, or a permission/I/O error on the plugin
/// path — is unverifiable and fails CLOSED (returns `false`) rather than
/// guessing via the symlink-blind lexical comparison.
#[cfg(any(feature = "wasm-runtime", feature = "python-plugins"))]
fn path_within_base(resolved: &Path, base_dir: &Path) -> bool {
    match resolved.canonicalize() {
        Ok(canon_plugin) => match base_dir.canonicalize() {
            Ok(canon_base) => canon_plugin.starts_with(&canon_base),
            // Plugin canonicalized but base didn't — cannot compare in one
            // namespace, so fail closed.
            Err(_) => false,
        },
        // Only a not-yet-existing path falls back to the lexical `..` check; a
        // permission/I/O error is unverifiable, so reject rather than guess.
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            lexically_normalize(resolved).starts_with(lexically_normalize(base_dir))
        }
        Err(_) => false,
    }
}

#[cfg(all(test, any(feature = "wasm-runtime", feature = "python-plugins")))]
mod path_security_tests {
    use super::{lexically_normalize, path_within_base};
    use std::path::Path;

    #[test]
    fn lexically_normalize_resolves_dotdot_for_nonexistent_paths() {
        assert_eq!(
            lexically_normalize(Path::new("/ledger/../../etc/passwd")),
            Path::new("/etc/passwd"),
        );
        assert_eq!(lexically_normalize(Path::new("/../../x")), Path::new("/x"));
        assert_eq!(
            lexically_normalize(Path::new("/ledger/./plugins/p.py")),
            Path::new("/ledger/plugins/p.py"),
        );
    }

    #[test]
    fn path_within_base_rejects_traversal_even_when_path_absent() {
        assert!(!path_within_base(
            Path::new("/ledger/../../etc/evil.wasm"),
            Path::new("/ledger"),
        ));
        assert!(path_within_base(
            Path::new("/ledger/plugins/ok.wasm"),
            Path::new("/ledger"),
        ));
        assert!(!path_within_base(
            Path::new("/other/p.wasm"),
            Path::new("/ledger"),
        ));
    }
}

#[cfg(all(test, feature = "python-plugins"))]
mod module_name_tests {
    use super::is_python_module_name;
    use std::path::Path;

    #[test]
    fn bare_module_name_is_a_module() {
        // No `.py`, no separator, and the resolved path does not exist.
        let missing = Path::new("/nonexistent/beancount.plugins.foo");
        assert!(is_python_module_name(missing, "beancount.plugins.foo"));
    }

    #[test]
    fn py_file_is_not_a_module() {
        let missing = Path::new("/nonexistent/myplugin.py");
        assert!(!is_python_module_name(missing, "myplugin.py"));
        // Case-insensitive extension (mirrors the runtime).
        assert!(!is_python_module_name(
            Path::new("/nonexistent/MyPlugin.PY"),
            "MyPlugin.PY"
        ));
    }

    #[test]
    fn path_separated_ref_is_not_a_module() {
        // Both `/` and the platform separator count as path markers, so a
        // forward-slash ref is a file even on Windows.
        assert!(!is_python_module_name(
            Path::new("/nonexistent/plugins/foo"),
            "plugins/foo"
        ));
    }

    #[test]
    fn existing_file_is_not_a_module() {
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("pkg.mod");
        std::fs::write(&file, "").unwrap();
        // A real file named like a module is still a file reference.
        assert!(!is_python_module_name(&file, "pkg.mod"));
    }
}
