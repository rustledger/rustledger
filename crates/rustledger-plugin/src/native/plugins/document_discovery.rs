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
/// {"base_dir": "/path/to/ledger", "main_file": "/path/to/ledger/main.beancount",
///  "directories": ["/abs/path/docs"]}
/// ```
///
/// `main_file` is the location each found document is given, at line 0, as
/// beancount gives it (#2713); without it a document has no location.
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
    #[serde(default)]
    main_file: Option<String>,
    directories: Vec<String>,
}

/// Build the [`PluginInput::config`] JSON string for this plugin.
///
/// Centralized here so callers (the loader) don't need to know the
/// schema — the plugin owns its own config shape.
///
/// This is the original two-argument form: the documents it finds carry
/// no location. Callers that know the ledger's main file use
/// [`document_discovery_config_with_main_file`] so each document is placed
/// at the location beancount gives it (#2713).
#[must_use]
pub fn document_discovery_config(base_dir: &std::path::Path, directories: &[String]) -> String {
    document_discovery_config_with_main_file(base_dir, None, directories)
}

/// [`document_discovery_config`] with the ledger's main file.
///
/// `main_file` is the location (at line 0) of each document the plugin
/// finds, as beancount's `find_documents` gives it (#2713); `None` leaves
/// the documents without a location.
#[must_use]
pub fn document_discovery_config_with_main_file(
    base_dir: &std::path::Path,
    main_file: Option<&std::path::Path>,
    directories: &[String],
) -> String {
    serde_json::json!({
        "base_dir": base_dir,
        "main_file": main_file.map(|f| f.to_string_lossy()),
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

        // Collect existing document paths to avoid duplicates. A relative
        // path resolves against its own directive's file, as the validator
        // and beancount resolve it (#2650); the ledger's base dir is only the
        // fallback for a directive with no file. Then canonicalized.
        let mut existing_docs: std::collections::HashSet<String> = std::collections::HashSet::new();
        for wrapper in &input.directives {
            if let DirectiveData::Document(doc) = &wrapper.data {
                let doc_path = Path::new(&doc.path);
                let resolved = if doc_path.is_absolute() {
                    doc_path.to_path_buf()
                } else {
                    wrapper
                        .filename
                        .as_deref()
                        .and_then(|f| Path::new(f).parent())
                        .unwrap_or(&config.base_dir)
                        .join(doc_path)
                };
                let normalized = resolved
                    .canonicalize()
                    .map_or_else(|_| doc.path.clone(), |p| p.to_string_lossy().to_string());
                existing_docs.insert(normalized);
            }
        }

        // Accounts the ledger names anywhere, the set beancount restricts
        // discovery to (`getters.get_accounts`): `open`, `close`, `balance`,
        // `note`, `document`, both accounts of a `pad`, and every posting.
        // NOT only the opened ones (#2649): a document for an account that
        // only a posting names is discovered, so a later `auto_accounts`
        // opens the account at the document's date when that is earlier,
        // and without `auto_accounts` the document is reported as an
        // unknown account (E1001) next to the posting, as in `bean-check`.
        //
        // A file under an account nothing names is skipped, as beancount
        // skips it. Unlike beancount — which drops them silently — we surface
        // a *warning* per such account, to catch the common footgun of a
        // stale `documents/` path after an account rename (a deliberate,
        // more-helpful deviation; #1434). Warnings don't affect the exit
        // code, so compatibility is preserved.
        let known = referenced_accounts(&input.directives);

        // Files found under directories that map to an account nothing names,
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

            // Seed the ancestor chain with this root so a link pointing at
            // the root itself is caught. Fresh per root: a cycle is a property
            // of one walk, not of the whole scan.
            let mut ancestors =
                vec![std::fs::canonicalize(dir_path).unwrap_or_else(|_| dir_path.to_path_buf())];

            if let Err(e) = scan_documents(
                dir_path,
                dir,
                &existing_docs,
                &known,
                &mut new_directives,
                &mut unknown,
                &mut errors,
                &mut ancestors,
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
                account, paths, &known,
            )));
        }

        // Keep all input directives, then insert discovered documents, each
        // at the main file's line 0, as beancount's `find_documents` places
        // them (`new_metadata(input_filename, 0)`), so an error on one names
        // the ledger instead of no location (#2713).
        let mut ops: Vec<PluginOp> = (0..input.directives.len()).map(PluginOp::Keep).collect();
        for mut w in new_directives {
            if let Some(main_file) = &config.main_file {
                w.filename = Some(main_file.clone());
                w.lineno = Some(0);
            }
            ops.push(PluginOp::Insert(w));
        }

        // Final ordering is the loader's responsibility — it re-sorts
        // directives after the plugin pass.
        PluginOutput { ops, errors }
    }
}

/// Every account a directive names, as beancount's `getters.get_accounts`
/// collects them; see the note in `process`.
fn referenced_accounts(directives: &[DirectiveWrapper]) -> std::collections::HashSet<String> {
    let mut accounts = std::collections::HashSet::new();
    for wrapper in directives {
        match &wrapper.data {
            DirectiveData::Open(d) => {
                accounts.insert(d.account.clone());
            }
            DirectiveData::Close(d) => {
                accounts.insert(d.account.clone());
            }
            DirectiveData::Balance(d) => {
                accounts.insert(d.account.clone());
            }
            DirectiveData::Note(d) => {
                accounts.insert(d.account.clone());
            }
            DirectiveData::Document(d) => {
                accounts.insert(d.account.clone());
            }
            DirectiveData::Pad(d) => {
                accounts.insert(d.account.clone());
                accounts.insert(d.source_account.clone());
            }
            DirectiveData::Transaction(t) => {
                accounts.extend(t.postings.iter().map(|p| p.account.clone()));
            }
            _ => {}
        }
    }
    accounts
}

/// Synthesizes `Document` directives that downstream consumers expect
/// alongside user-written ones — runs in the synth pass so the early
/// validator sees them.
impl SynthPlugin for DocumentDiscoveryPlugin {}

/// Max "did you mean" suggestions to list in a warning.
const MAX_SUGGESTIONS: usize = 3;

/// Known accounts that plausibly match `account` — sharing both the root
/// (first segment) and the leaf (last segment). This finds the sibling-rename
/// case (`Expenses:Electricity` → `Expenses:Home:Electricity`) without the
/// false positives of a leaf-only match (e.g. `Income:Refunds:Electricity`).
fn suggested_accounts(account: &str, known: &std::collections::HashSet<String>) -> Vec<String> {
    let root = account.split(':').next();
    let leaf = account.rsplit(':').next();
    let mut hits: Vec<String> = known
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
/// that maps to an account no directive names. Names the account, how many
/// files were skipped (with an example), and suggests likely-intended known
/// accounts (the account-rename case).
fn unknown_account_warning(
    account: &str,
    paths: &[String],
    known: &std::collections::HashSet<String>,
) -> String {
    let example = paths.first().map_or("", String::as_str);
    let more = paths.len().saturating_sub(1);
    let files = if more == 0 {
        example.to_string()
    } else {
        format!("{example} (+{more} more)")
    };
    let suggestions = suggested_accounts(account, known);
    let hint = if suggestions.is_empty() {
        String::new()
    } else {
        format!("; did you mean: {}?", suggestions.join(", "))
    };
    format!(
        "{n} document(s) reference unknown account '{account}' and were skipped \
         (no directive names that account): {files}{hint}",
        n = paths.len()
    )
}

/// Recursively scan a directory for document files.
///
/// Symlinked subdirectories ARE followed, because beancount follows them:
/// `beancount/ops/documents.py` walks with `account.walk(directory)`, whose
/// `followlinks` parameter defaults to `True`. Skipping them made an entire
/// document tree silently invisible — no error, no warning, indistinguishable
/// from an empty folder (#1997). A documents tree assembled from links is the
/// normal shape whenever the ledger repo and the document library cannot share
/// a root, e.g. invoices in a synced folder linked into the `documents` tree.
///
/// This is not Windows-specific. It was reported for Windows directory
/// junctions, because Rust's `FileType::is_symlink` is true for name-surrogate
/// reparse points while Python's `os.path.islink` is false for them — so a
/// junction was the case where the two implementations visibly disagreed even
/// under `followlinks=False`. But `followlinks` is `True`, so the divergence
/// covers ordinary POSIX symlinks too, and it reproduces on Linux.
///
/// # Security
/// - Breaks symlink cycles by tracking the canonicalized *ancestor chain* of
///   the current walk. Following links without a guard would hang;
///   beancount's `os.walk(followlinks=True)` has none, so this is deliberately
///   stricter than the thing it matches.
///
///   Deliberately an ancestor chain and NOT a global visited-set. A visited-set
///   also terminates, but it silently drops legitimate re-reachability: two
///   account directories may link to the same physical folder, and beancount
///   walks both, emitting one document per account. A global set would walk
///   whichever came first and drop the other — trading this bug for a new
///   divergence. A directory is only a cycle when it is its own ancestor.
/// - Enforces maximum recursion depth to prevent denial-of-service from deeply nested directories
// One argument more than the lint allows. The alternative is a context struct
// that exists only to satisfy the count; `load_recursive` in the loader
// carries the same allow for the same reason.
#[allow(clippy::too_many_arguments)]
fn scan_documents(
    path: &std::path::Path,
    base_dir: &str,
    existing: &std::collections::HashSet<String>,
    known: &std::collections::HashSet<String>,
    directives: &mut Vec<DirectiveWrapper>,
    unknown: &mut std::collections::BTreeMap<String, Vec<String>>,
    errors: &mut Vec<PluginError>,
    ancestors: &mut Vec<std::path::PathBuf>,
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

    let mut entries: Vec<(std::path::PathBuf, fs::Metadata)> = Vec::new();
    for entry in fs::read_dir(path)? {
        let entry_path = entry?.path();

        // `metadata`, not `symlink_metadata`: this FOLLOWS the link, so a
        // linked subtree is classified by what it points at rather than being
        // seen as an opaque "symlink" and dropped. A broken link fails to stat
        // and is skipped here, which is also what a walk that cannot enter it
        // would do.
        let Ok(metadata) = fs::metadata(&entry_path) else {
            continue; // Skip entries we can't stat (incl. dangling links)
        };
        entries.push((entry_path, metadata));
    }
    // Files first, then subdirectories, each sorted by name: the order
    // beancount's `account.walk` (an `os.walk` that sorts `dirs` and `files`)
    // visits them. `read_dir` yields entries in whatever order the filesystem
    // keeps them, so the documents found, and the paths an unknown-account
    // warning lists, came out in a different order on another machine or
    // after the directory was rewritten (#2625).
    entries.sort_by(|(a, a_meta), (b, b_meta)| {
        a_meta
            .is_dir()
            .cmp(&b_meta.is_dir())
            .then_with(|| a.file_name().cmp(&b.file_name()))
    });

    for (entry_path, metadata) in entries {
        if metadata.is_dir() {
            // Cycle guard: canonicalize so a link collapses to its target,
            // then refuse to descend into a directory that is already on the
            // path we took to get here. `a/b -> a` is caught; `x -> t` and
            // `y -> t` are both still walked.
            let key = fs::canonicalize(&entry_path).unwrap_or_else(|_| entry_path.clone());
            if ancestors.contains(&key) {
                errors.push(PluginError::warning(format!(
                    "Skipped {} while scanning documents: it links back into a \
                     directory already being scanned ({})",
                    entry_path.display(),
                    key.display()
                )));
                continue;
            }
            ancestors.push(key);
            let result = scan_documents(
                &entry_path,
                base_dir,
                existing,
                known,
                directives,
                unknown,
                errors,
                ancestors,
                depth + 1,
            );
            ancestors.pop();
            result?;
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

                            // Only synthesize documents for accounts the
                            // ledger names (see the note in `process`). A
                            // file under any other account — e.g. a stale
                            // path after an account rename — is collected for
                            // an aggregated warning and skipped. (#1434)
                            if !known.contains(&account) {
                                unknown.entry(account).or_default().push(full_path);
                                continue;
                            }

                            directives.push(DirectiveWrapper {
                                directive_type: "document".to_string(),
                                date: date_str.to_string(),
                                // Located by `process` (#2713).
                                filename: None,
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
