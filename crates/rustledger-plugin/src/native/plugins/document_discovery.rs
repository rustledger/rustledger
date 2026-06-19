//! Auto-discover documents from directories.

use serde::Deserialize;

use crate::types::{
    DirectiveData, DirectiveWrapper, DocumentData, PluginError, PluginInput, PluginOp, PluginOutput,
};

use super::super::{NativePlugin, SynthPlugin};

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
/// # Configuration
///
/// The plugin reads its per-load context (resolved document directories
/// and the ledger's base directory for relative-path normalization) from
/// [`PluginInput::config`] as a JSON object:
///
/// ```json
/// {"base_dir": "/path/to/ledger", "directories": ["/abs/path/docs"]}
/// ```
///
/// The loader constructs this config when populating the synth pass; if
/// `config` is `None` or `directories` is empty, the plugin returns a
/// no-op (every input directive is kept, nothing synthesized). If `config`
/// is present but malformed JSON, every input directive is still kept and
/// a `PluginError::error` is added to the output errors — the plugin
/// never silently drops directives on bad config. This lets the plugin
/// sit in the registry as a static instance and be dispatched through
/// the normal synth-pass machinery.
///
/// # Security
///
/// - Symlinks are skipped to prevent infinite recursion from symlink cycles
/// - Maximum recursion depth is enforced to prevent denial-of-service from deeply nested directories
pub struct DocumentDiscoveryPlugin;

/// Name passed to file-declared / extra-plugin lookups and used by the
/// loader when emitting the synth-pass config entry. Kept as a constant
/// so the registry, the loader, and the rustdoc stay in sync.
pub const DOCUMENT_DISCOVERY_NAME: &str = "document_discovery";

/// JSON config schema parsed from [`PluginInput::config`].
#[derive(Debug, Deserialize)]
struct DocumentDiscoveryConfig {
    base_dir: std::path::PathBuf,
    directories: Vec<String>,
}

/// Build the [`PluginInput::config`] JSON string for this plugin.
///
/// Centralized here so callers (the loader) don't need to know the
/// schema — the plugin owns its own config shape.
#[must_use]
pub fn document_discovery_config(base_dir: &std::path::Path, directories: &[String]) -> String {
    serde_json::json!({
        "base_dir": base_dir,
        "directories": directories,
    })
    .to_string()
}

impl NativePlugin for DocumentDiscoveryPlugin {
    fn name(&self) -> &'static str {
        DOCUMENT_DISCOVERY_NAME
    }

    fn description(&self) -> &'static str {
        "Auto-discover documents from directories"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use std::path::Path;

        // No config → no-op pass-through. Lets the plugin sit in the
        // registry unconditionally without doing work when the ledger
        // hasn't declared `option "documents"`.
        let Some(config_json) = input.config.as_deref() else {
            return PluginOutput {
                ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
                errors: Vec::new(),
            };
        };

        let config: DocumentDiscoveryConfig = match serde_json::from_str(config_json) {
            Ok(c) => c,
            Err(e) => {
                return PluginOutput {
                    ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
                    errors: vec![PluginError::error(format!(
                        "document_discovery: invalid config JSON: {e}"
                    ))],
                };
            }
        };

        if config.directories.is_empty() {
            return PluginOutput {
                ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
                errors: Vec::new(),
            };
        }

        let mut new_directives = Vec::new();
        let mut errors = Vec::new();

        // Collect existing document paths to avoid duplicates.
        // Normalize paths by resolving relative paths against base_dir, then canonicalizing.
        let mut existing_docs: std::collections::HashSet<String> = std::collections::HashSet::new();
        for wrapper in &input.directives {
            if let DirectiveData::Document(doc) = &wrapper.data {
                let doc_path = Path::new(&doc.path);
                let resolved = if doc_path.is_absolute() {
                    doc_path.to_path_buf()
                } else {
                    config.base_dir.join(doc_path)
                };
                let normalized = resolved
                    .canonicalize()
                    .map_or_else(|_| doc.path.clone(), |p| p.to_string_lossy().to_string());
                existing_docs.insert(normalized);
            }
        }

        // Accounts opened in the ledger. This is exactly the set the validator
        // treats as known (`validate_document` checks `state.accounts`, which
        // is populated only by `open`), so a document we skip here is precisely
        // one that would otherwise hard-fail `E1001 AccountNotOpen`.
        //
        // Like beancount, we don't synthesize documents for unknown accounts
        // (so `check` passes, matching `bean-check`). Unlike beancount — which
        // drops them silently — we surface a *warning* per unknown account, to
        // catch the common footgun of a stale `documents/` path after an
        // account rename (a deliberate, more-helpful deviation; #1434). Warnings
        // don't affect the exit code, so compatibility is preserved.
        //
        // Note the asymmetry (intentional — do not "fix" it): an *explicit*
        // `document` directive to an unopened account still hard-errors via the
        // validator, matching beancount's `validate_active_accounts`. Only
        // auto-discovery is lenient, because beancount's discovery never emits
        // the directive in the first place.
        let opened: std::collections::HashSet<String> = input
            .directives
            .iter()
            .filter_map(|w| match &w.data {
                DirectiveData::Open(o) => Some(o.account.clone()),
                _ => None,
            })
            .collect();

        // Files found under directories that map to an unopened account,
        // grouped by account (BTreeMap → deterministic, one warning per
        // account instead of one per file).
        let mut unknown: std::collections::BTreeMap<String, Vec<String>> =
            std::collections::BTreeMap::new();

        // Scan each directory
        for dir in &config.directories {
            let dir_path = Path::new(dir);
            if !dir_path.exists() {
                continue;
            }

            if let Err(e) = scan_documents(
                dir_path,
                dir,
                &existing_docs,
                &opened,
                &mut new_directives,
                &mut unknown,
                &mut errors,
                0, // Initial depth
            ) {
                errors.push(PluginError::error(format!(
                    "Error scanning documents in {dir}: {e}"
                )));
            }
        }

        // One aggregated warning per unknown account.
        for (account, paths) in &unknown {
            errors.push(PluginError::warning(unknown_account_warning(
                account, paths, &opened,
            )));
        }

        // Keep all input directives, then insert discovered documents.
        let mut ops: Vec<PluginOp> = (0..input.directives.len()).map(PluginOp::Keep).collect();
        for w in new_directives {
            ops.push(PluginOp::Insert(w));
        }

        // Final ordering is the loader's responsibility — it re-sorts
        // directives after the plugin pass.
        PluginOutput { ops, errors }
    }
}

/// Synthesizes `Document` directives that downstream consumers expect
/// alongside user-written ones — runs in the synth pass so the early
/// validator sees them.
impl SynthPlugin for DocumentDiscoveryPlugin {}

/// Max "did you mean" suggestions to list in a warning.
const MAX_SUGGESTIONS: usize = 3;

/// Opened accounts that plausibly match `account` — sharing both the root
/// (first segment) and the leaf (last segment). This finds the sibling-rename
/// case (`Expenses:Electricity` → `Expenses:Home:Electricity`) without the
/// false positives of a leaf-only match (e.g. `Income:Refunds:Electricity`).
fn suggested_accounts(account: &str, opened: &std::collections::HashSet<String>) -> Vec<String> {
    let root = account.split(':').next();
    let leaf = account.rsplit(':').next();
    let mut hits: Vec<String> = opened
        .iter()
        .filter(|a| a.split(':').next() == root && a.rsplit(':').next() == leaf)
        .filter(|a| a.as_str() != account)
        .cloned()
        .collect();
    hits.sort_unstable();
    hits.truncate(MAX_SUGGESTIONS);
    hits
}

/// Build the (aggregated) warning for documents discovered under a directory
/// that maps to an account that is not open. Names the account, how many files
/// were skipped (with an example), and suggests likely-intended opened
/// accounts (the account-rename case).
fn unknown_account_warning(
    account: &str,
    paths: &[String],
    opened: &std::collections::HashSet<String>,
) -> String {
    let example = paths.first().map_or("", String::as_str);
    let more = paths.len().saturating_sub(1);
    let files = if more == 0 {
        example.to_string()
    } else {
        format!("{example} (+{more} more)")
    };
    let suggestions = suggested_accounts(account, opened);
    let hint = if suggestions.is_empty() {
        String::new()
    } else {
        format!("; did you mean: {}?", suggestions.join(", "))
    };
    format!(
        "{n} document(s) reference unknown account '{account}' and were skipped \
         (no such account is open): {files}{hint}",
        n = paths.len()
    )
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
    opened: &std::collections::HashSet<String>,
    directives: &mut Vec<DirectiveWrapper>,
    unknown: &mut std::collections::BTreeMap<String, Vec<String>>,
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
                opened,
                directives,
                unknown,
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

                            // Only synthesize documents for opened accounts
                            // (see the note in `process`). A file under an
                            // unopened account — e.g. a stale path after an
                            // account rename — is collected for an aggregated
                            // warning and skipped, never synthesized into a
                            // hard `E1001`. (#1434)
                            if !opened.contains(&account) {
                                unknown.entry(account).or_default().push(full_path);
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
                                    tags: vec![],
                                    links: vec![],
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
