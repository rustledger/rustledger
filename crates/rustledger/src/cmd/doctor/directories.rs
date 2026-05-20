use anyhow::{Context, Result};
use rustledger_core::{Account, Directive};
use rustledger_loader::Loader;
use std::collections::BTreeSet;
use std::fs;
use std::io::Write;
use std::path::PathBuf;

pub(super) fn cmd_directories<W: Write>(
    file: &PathBuf,
    dirs: &[PathBuf],
    writer: &mut W,
) -> Result<()> {
    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    // Collect all account names
    let mut accounts: BTreeSet<Account> = BTreeSet::new();
    for spanned in &load_result.directives {
        match &spanned.value {
            Directive::Open(open) => {
                accounts.insert(open.account.clone());
            }
            Directive::Transaction(txn) => {
                for posting in &txn.postings {
                    accounts.insert(posting.account.clone());
                }
            }
            _ => {}
        }
    }

    writeln!(
        writer,
        "Validating directories against {} accounts",
        accounts.len()
    )?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    let mut errors = 0;

    for dir in dirs {
        if !dir.exists() {
            writeln!(writer, "ERROR: Directory does not exist: {}", dir.display())?;
            errors += 1;
            continue;
        }

        writeln!(writer, "Checking {}...", dir.display())?;

        // Walk the directory and check subdirectory names
        for entry in walkdir(dir)? {
            let entry = entry?;
            if entry.file_type().is_dir() {
                let file_name = entry.file_name();
                let name = file_name.to_string_lossy();
                // Check if it looks like an account component (capitalized)
                if name.chars().next().is_some_and(char::is_uppercase) {
                    // Build account path from directory path
                    let rel_path = entry.path().strip_prefix(dir).unwrap_or(entry.path());
                    let account_path: String = rel_path
                        .components()
                        .filter_map(|c| c.as_os_str().to_str())
                        .collect::<Vec<_>>()
                        .join(":");

                    // Check if any account starts with this path
                    let has_match = accounts
                        .iter()
                        .any(|a| a.starts_with(&account_path) || a == &account_path);
                    if !has_match && !account_path.is_empty() {
                        writeln!(
                            writer,
                            "  WARNING: No matching account for directory: {account_path}"
                        )?;
                    }
                }
            }
        }
    }

    writeln!(writer)?;
    if errors == 0 {
        writeln!(writer, "Directory validation complete.")?;
    } else {
        writeln!(writer, "Found {errors} errors.")?;
    }

    Ok(())
}

/// Simple directory walker
fn walkdir(dir: &PathBuf) -> Result<Vec<Result<DirEntry, std::io::Error>>> {
    let mut entries = Vec::new();
    walk_dir_recursive(dir, &mut entries)?;
    Ok(entries)
}

struct DirEntry {
    path: PathBuf,
    file_type: std::fs::FileType,
}

impl DirEntry {
    const fn path(&self) -> &PathBuf {
        &self.path
    }

    fn file_name(&self) -> std::ffi::OsString {
        self.path.file_name().unwrap_or_default().to_os_string()
    }

    const fn file_type(&self) -> &std::fs::FileType {
        &self.file_type
    }
}

fn walk_dir_recursive(
    dir: &PathBuf,
    entries: &mut Vec<Result<DirEntry, std::io::Error>>,
) -> Result<()> {
    if dir.is_dir() {
        for entry in fs::read_dir(dir)? {
            match entry {
                Ok(e) => {
                    let path = e.path();
                    if let Ok(ft) = e.file_type() {
                        entries.push(Ok(DirEntry {
                            path: path.clone(),
                            file_type: ft,
                        }));
                        if ft.is_dir() {
                            let _ = walk_dir_recursive(&path, entries);
                        }
                    }
                }
                Err(e) => entries.push(Err(e)),
            }
        }
    }
    Ok(())
}
