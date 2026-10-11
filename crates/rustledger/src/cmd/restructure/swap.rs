//! Writing a verified plan: new files alongside the originals, a backup, and
//! one commit point.
//!
//! Every new file is written to a temporary name next to its target first.
//! Then the originals that will change are copied into a backup directory.
//! Then the new files are renamed into place, the file that COMMITS the change
//! last: for `split` that is the root, which is the only file that names the
//! new period files, so until it is swapped the old root is still the whole
//! ledger and the new files are inert. For `merge` it is the merged root, which
//! stops naming the included files the moment it lands; only then are those
//! removed. At no point is the ledger on disk half old and half new.
//!
//! After the swap the ledger is loaded again from disk and compared with the
//! original once more. If that fails, the backup is restored.

use anyhow::{Context, Result, bail};
use std::fs;
use std::io::Write as _;
use std::path::{Path, PathBuf};

/// What to write.
#[derive(Debug)]
pub(super) struct Plan {
    /// Files to write, with their new content. The commit file may replace an
    /// existing file; every other write must create a new one.
    pub(super) writes: Vec<(PathBuf, String)>,
    /// The write that makes the new layout live. Renamed into place last.
    pub(super) commit: PathBuf,
    /// Files to delete once the commit is in place (backed up first).
    pub(super) removes: Vec<PathBuf>,
    /// Directory the backup goes under (`<dir>/.rledger-backup/...`).
    pub(super) backup_base: PathBuf,
    /// Original contents of every file this plan replaces or removes, as read
    /// when the plan was made. The swap refuses to proceed if any has changed
    /// on disk since.
    pub(super) originals: Vec<(PathBuf, Vec<u8>)>,
    /// `split` or `merge`, used in the backup directory's name.
    pub(super) operation: &'static str,
    /// Whose permissions new files get (the file being restructured).
    pub(super) template: PathBuf,
}

/// Where the backup went.
#[derive(Debug)]
pub(super) struct Applied {
    /// `None` when the plan replaced and removed nothing.
    pub(super) backup_dir: Option<PathBuf>,
}

/// Refuse a plan whose preconditions no longer hold, before touching anything.
pub(super) fn preflight(plan: &Plan) -> Result<()> {
    for (path, _) in &plan.writes {
        if path != &plan.commit && path.exists() {
            bail!(
                "{} already exists; refusing to overwrite it (move it away or choose another --dir)",
                path.display()
            );
        }
    }
    for (path, original) in &plan.originals {
        let now = fs::read(path).with_context(|| format!("failed to read {}", path.display()))?;
        if &now != original {
            bail!(
                "{} changed on disk while the plan was being checked; nothing was written",
                path.display()
            );
        }
    }
    Ok(())
}

/// Apply `plan`. `verify` reloads the ledger from disk after the swap and
/// fails if it no longer matches; on failure the backup is restored.
pub(super) fn apply(plan: &Plan, verify: impl FnOnce() -> Result<()>) -> Result<Applied> {
    preflight(plan)?;
    let backup_dir = if plan.originals.is_empty() {
        None
    } else {
        Some(make_backup(plan)?)
    };
    let backup_note = backup_dir.as_ref().map_or_else(String::new, |d| {
        format!("; a backup copy is in {}", d.display())
    });

    let mut created_dirs: Vec<PathBuf> = Vec::new();
    let mut temps: Vec<(PathBuf, PathBuf)> = Vec::new();
    let staged = stage(plan, &mut created_dirs, &mut temps);
    if let Err(e) = staged {
        cleanup(&temps, &[], &created_dirs);
        return Err(e.context(format!("nothing was changed{backup_note}")));
    }

    // Rename: new files first, the commit file last.
    let mut placed: Vec<PathBuf> = Vec::new();
    let mut order: Vec<&(PathBuf, PathBuf)> =
        temps.iter().filter(|(_, t)| t != &plan.commit).collect();
    order.extend(temps.iter().filter(|(_, t)| t == &plan.commit));
    for (tmp, target) in order {
        if let Err(e) = fs::rename(tmp, target) {
            let committed = placed.contains(&plan.commit);
            if !committed {
                cleanup(&temps, &placed, &created_dirs);
                return Err(anyhow::Error::new(e).context(format!(
                    "failed to move {} into place; nothing was changed",
                    target.display()
                )));
            }
            // Unreachable in practice: the commit is renamed last.
            return Err(anyhow::Error::new(e)
                .context(format!("failed to move {} into place", target.display())));
        }
        placed.push(target.clone());
    }

    let mut leftovers = Vec::new();
    for path in &plan.removes {
        if let Err(e) = fs::remove_file(path) {
            leftovers.push(format!("{}: {e}", path.display()));
        }
    }

    if let Err(e) = verify() {
        let restored = restore(plan, backup_dir.as_deref(), &placed, &created_dirs);
        let how = match restored {
            Ok(()) => "the original files were restored".to_string(),
            Err(r) => format!("restoring failed too ({r:#}){backup_note}"),
        };
        return Err(e.context(format!(
            "the ledger written to disk did not load the same as before; {how}"
        )));
    }

    if !leftovers.is_empty() {
        eprintln!(
            "warning: could not remove {} file(s) that are no longer included:\n  {}",
            leftovers.len(),
            leftovers.join("\n  ")
        );
    }
    Ok(Applied { backup_dir })
}

fn stage(
    plan: &Plan,
    created_dirs: &mut Vec<PathBuf>,
    temps: &mut Vec<(PathBuf, PathBuf)>,
) -> Result<()> {
    for (target, content) in &plan.writes {
        let parent = target
            .parent()
            .with_context(|| format!("{} has no parent directory", target.display()))?;
        create_dirs(parent, created_dirs)?;
        let name = target
            .file_name()
            .with_context(|| format!("{} has no file name", target.display()))?
            .to_string_lossy();
        let tmp = parent.join(format!(".{name}.rledger-tmp-{}", std::process::id()));
        let mut f = fs::File::create(&tmp)
            .with_context(|| format!("failed to create {}", tmp.display()))?;
        temps.push((tmp.clone(), target.clone()));
        f.write_all(content.as_bytes())
            .with_context(|| format!("failed to write {}", tmp.display()))?;
        // Keep the permissions of the file being replaced, and give new files
        // those of the file being restructured: a ledger kept at 0600 must not reappear as
        // world-readable period files.
        let template = if target.exists() {
            target
        } else {
            &plan.template
        };
        if let Ok(meta) = fs::metadata(template) {
            fs::set_permissions(&tmp, meta.permissions())
                .with_context(|| format!("failed to set permissions on {}", tmp.display()))?;
        }
        f.sync_all()
            .with_context(|| format!("failed to flush {}", tmp.display()))?;
    }
    Ok(())
}

fn create_dirs(dir: &Path, created: &mut Vec<PathBuf>) -> Result<()> {
    let mut missing = Vec::new();
    let mut cur = Some(dir);
    while let Some(d) = cur {
        if d.as_os_str().is_empty() || d.exists() {
            break;
        }
        missing.push(d.to_path_buf());
        cur = d.parent();
    }
    for d in missing.into_iter().rev() {
        fs::create_dir(&d).with_context(|| format!("failed to create {}", d.display()))?;
        created.push(d);
    }
    Ok(())
}

/// Remove temporaries, files already placed (new ones only — the commit file
/// is never placed before everything else succeeded), and directories created.
fn cleanup(temps: &[(PathBuf, PathBuf)], placed: &[PathBuf], created_dirs: &[PathBuf]) {
    for (tmp, _) in temps {
        let _ = fs::remove_file(tmp);
    }
    for p in placed {
        let _ = fs::remove_file(p);
    }
    for d in created_dirs.iter().rev() {
        let _ = fs::remove_dir(d);
    }
}

fn restore(
    plan: &Plan,
    backup_dir: Option<&Path>,
    placed: &[PathBuf],
    created: &[PathBuf],
) -> Result<()> {
    let base = &plan.backup_base;
    for (path, _) in &plan.originals {
        let Some(backup_dir) = backup_dir else {
            break;
        };
        let saved = backup_dir.join(backup_rel(base, path));
        let tmp = path.with_extension("rledger-restore");
        fs::copy(&saved, &tmp).with_context(|| format!("failed to restore {}", path.display()))?;
        fs::rename(&tmp, path).with_context(|| format!("failed to restore {}", path.display()))?;
    }
    let originals: Vec<&PathBuf> = plan.originals.iter().map(|(p, _)| p).collect();
    for p in placed {
        if !originals.contains(&p) {
            let _ = fs::remove_file(p);
        }
    }
    for d in created.iter().rev() {
        let _ = fs::remove_dir(d);
    }
    Ok(())
}

/// Copy every file the plan replaces or removes into a fresh backup
/// directory, with a manifest saying where each came from and which files the
/// plan creates.
fn make_backup(plan: &Plan) -> Result<PathBuf> {
    let stamp = jiff::Timestamp::now()
        .strftime("%Y%m%dT%H%M%SZ")
        .to_string();
    let root = plan.backup_base.join(".rledger-backup");
    let mut dir = root.join(format!("{stamp}-{}", plan.operation));
    let mut n = 1;
    while dir.exists() {
        dir = root.join(format!("{stamp}-{}-{n}", plan.operation));
        n += 1;
    }
    fs::create_dir_all(&dir).with_context(|| format!("failed to create {}", dir.display()))?;
    let mut manifest = format!(
        "# rledger {} backup, {stamp}\n# To undo: copy each file below back to its original path,\n# and delete the files listed as created.\n",
        plan.operation
    );
    for (path, original) in &plan.originals {
        let rel = backup_rel(&plan.backup_base, path);
        let dest = dir.join(&rel);
        if let Some(parent) = dest.parent() {
            fs::create_dir_all(parent)
                .with_context(|| format!("failed to create {}", parent.display()))?;
        }
        let mut f = fs::File::create(&dest)
            .with_context(|| format!("failed to back up {}", path.display()))?;
        f.write_all(original)
            .with_context(|| format!("failed to back up {}", path.display()))?;
        // The copy is as private as the original: a ledger kept at 0600 must
        // not sit world-readable in the backup (and `restore` copies these
        // permissions back).
        if let Ok(meta) = fs::metadata(path) {
            fs::set_permissions(&dest, meta.permissions())
                .with_context(|| format!("failed to back up {}", path.display()))?;
        }
        f.sync_all()
            .with_context(|| format!("failed to back up {}", path.display()))?;
        manifest.push_str(&format!("saved\t{}\t{}\n", path.display(), rel.display()));
    }
    for (path, _) in &plan.writes {
        if !plan.originals.iter().any(|(p, _)| p == path) {
            manifest.push_str(&format!("created\t{}\n", path.display()));
        }
    }
    fs::write(dir.join("manifest.txt"), manifest)
        .with_context(|| format!("failed to write the backup manifest in {}", dir.display()))?;
    Ok(dir)
}

/// Where `path` is kept inside a backup: its path relative to `base`, or,
/// for a file outside `base`, its absolute path under `_outside/`, with
/// `.bak` appended. The suffix matters: the backup sits inside the ledger's
/// directory, and a root that includes a glob such as `*/*.beancount` must not
/// pick the backup copies up as part of the ledger.
fn backup_rel(base: &Path, path: &Path) -> PathBuf {
    let mut out = if let Ok(rel) = path.strip_prefix(base) {
        rel.to_path_buf()
    } else {
        let mut out = PathBuf::from("_outside");
        for c in path.components() {
            if let std::path::Component::Normal(s) = c {
                out.push(s);
            }
        }
        out
    };
    let mut name = out.file_name().unwrap_or_default().to_os_string();
    name.push(".bak");
    out.set_file_name(name);
    out
}
