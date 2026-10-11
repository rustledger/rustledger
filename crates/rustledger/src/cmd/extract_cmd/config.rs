//! Importers TOML configuration for extract command.

use anyhow::{Context, Result, anyhow};
use serde::Deserialize;
use std::path::Path;

// The `[[importers]]` entry schema and its `ImporterConfig` mapping live in
// the canonical `rustledger_importer::toml_entry` module (shared with the
// WASI component's `importer` interface); this module keeps only file
// discovery and the CLI-side `ImportersFile` wrapper.
use rustledger_importer::payees::PayeeRules;
pub(super) use rustledger_importer::toml_entry::{
    ImporterEntry, apply_column, build_config_from_entry,
};
use rustledger_importer::toml_entry::{PayeeTable, SHARED_PAYEES};
use std::path::PathBuf;

/// Top-level importers configuration file.
#[derive(Debug, Deserialize)]
pub(super) struct ImportersFile {
    /// Director(ies) to scan for WASM importer modules at startup.
    /// Accepts either a single string for the common case
    /// (`wasm_importer_dir = "~/imp"`) or a list
    /// (`wasm_importer_dir = ["a", "b"]`). The CLI
    /// `--wasm-importer-dir` flag(s) override this setting entirely
    /// when present.
    #[serde(default)]
    pub(super) wasm_importer_dir: WasmDirSetting,
    #[serde(default)]
    pub(super) importers: Vec<ImporterEntry>,
    /// Payee rewrites shared by every entry (#2550): pattern → canonical
    /// payee, in file order. An entry's own `[importers.payees]` is tried
    /// first. Applies on every import that finds this file, whichever
    /// importer reads the statement.
    #[serde(default)]
    pub(super) payees: PayeeTable,
}

impl ImportersFile {
    /// The payee rewrite rules for a statement imported through the entry
    /// named `entry_name` (none for an import that used no entry): that
    /// entry's `[importers.payees]`, then the shared `[payees]` table.
    pub(super) fn payee_rules(&self, entry_name: Option<&str>) -> Result<PayeeRules> {
        if let Some(entry) =
            entry_name.and_then(|name| self.importers.iter().find(|e| e.name == name))
        {
            return entry.payee_rules(Some(&self.payees));
        }
        let mut rules = PayeeRules::new();
        self.payees.extend_rules(&mut rules, SHARED_PAYEES)?;
        Ok(rules)
    }

    /// Check every payee table compiles, so a bad pattern is reported by
    /// whatever reads the file (`--list-importers` included), naming the
    /// table it is in, rather than only by an import that reaches it.
    fn validate_payees(&self) -> Result<()> {
        self.payee_rules(None)?;
        for entry in &self.importers {
            entry.payee_rules(None)?;
        }
        Ok(())
    }
}

/// TOML-side representation of `wasm_importer_dir` — accepts a
/// bare string or a list of strings so the common single-dir case
/// stays ergonomic while multi-dir is also expressible.
#[derive(Debug, Default, Deserialize)]
#[serde(untagged)]
pub(super) enum WasmDirSetting {
    #[default]
    None,
    Single(PathBuf),
    Many(Vec<PathBuf>),
}

impl WasmDirSetting {
    /// Normalize into a flat `Vec<PathBuf>` for the registry-build
    /// pipeline. Empty for [`Self::None`].
    pub(super) fn into_vec(self) -> Vec<PathBuf> {
        match self {
            Self::None => Vec::new(),
            Self::Single(p) => vec![p],
            Self::Many(v) => v,
        }
    }
}

/// Expand a leading `~` in a path to the user's home directory.
/// Without this, `wasm_importer_dir = "~/imp"` in `importers.toml`
/// would be read as a literal `~/imp` path that doesn't exist — a
/// real footgun for a config setting where shell expansion isn't
/// available.
///
/// Only handles `~` and `~/...` (no `~user/...`); falls through to
/// the original path if the home directory can't be determined.
pub(super) fn expand_tilde(path: &Path) -> PathBuf {
    let s = path.to_string_lossy();
    if s == "~" {
        return dirs::home_dir().unwrap_or_else(|| path.to_path_buf());
    }
    if let Some(rest) = s.strip_prefix("~/")
        && let Some(home) = dirs::home_dir()
    {
        return home.join(rest);
    }
    path.to_path_buf()
}

/// Find the importers.toml file, searching in standard locations.
/// Where an `importers.toml` came from.
///
/// Matters because a config can do two very different things: DECLARE
/// importers, and EXECUTE a `preprocess` command. Declaring is safe from
/// anywhere. Executing is not — a config discovered in the current directory
/// belongs to whoever put a file there, not necessarily to the user.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ConfigSource {
    /// Named by `--config`: the user pointed at this file.
    Explicit,
    /// `~/.config/rledger/importers.toml`: the user's own.
    UserConfigDir,
    /// `./importers.toml`, found by looking around. Convenient, but its
    /// contents are a property of the directory, not of the user.
    CurrentDirectory,
}

/// [`find_importers_config`] plus where the file came from.
pub(super) fn find_importers_config_with_source(
    explicit_path: Option<&Path>,
) -> Result<Option<(std::path::PathBuf, ConfigSource)>> {
    if let Some(path) = explicit_path {
        if path.exists() {
            return Ok(Some((path.to_path_buf(), ConfigSource::Explicit)));
        }
        return Err(anyhow!("Importers config not found: {}", path.display()));
    }

    if let Ok(cwd) = std::env::current_dir() {
        let local = cwd.join("importers.toml");
        if local.exists() {
            return Ok(Some((local, ConfigSource::CurrentDirectory)));
        }
    }

    if let Some(user_path) = crate::config::user_config_file("importers.toml")
        && user_path.exists()
    {
        return Ok(Some((user_path, ConfigSource::UserConfigDir)));
    }

    Ok(None)
}

pub(super) fn find_importers_config(
    explicit_path: Option<&Path>,
) -> Result<Option<std::path::PathBuf>> {
    Ok(find_importers_config_with_source(explicit_path)?.map(|(path, _)| path))
}

/// Load and parse an importers.toml file.
pub(super) fn load_importers_config(path: &Path) -> Result<ImportersFile> {
    let content = std::fs::read_to_string(path)
        .with_context(|| format!("Failed to read importers config: {}", path.display()))?;
    let config: ImportersFile = toml::from_str(&content)
        .with_context(|| format!("Failed to parse importers config: {}", path.display()))?;
    config
        .validate_payees()
        .with_context(|| format!("Invalid importers config: {}", path.display()))?;
    Ok(config)
}

/// Check if an importer matches the given filename using its glob pattern.
pub(super) fn importer_matches_filename(entry: &ImporterEntry, filename: &str) -> bool {
    if let Some(pattern) = &entry.filename_pattern {
        glob::Pattern::new(pattern).is_ok_and(|p| p.matches(filename))
    } else {
        false
    }
}

/// Find importers that match the given filename.
pub(super) fn find_matching_importers<'a>(
    config: &'a ImportersFile,
    filename: &str,
) -> Vec<&'a ImporterEntry> {
    config
        .importers
        .iter()
        .filter(|imp| importer_matches_filename(imp, filename))
        .collect()
}
