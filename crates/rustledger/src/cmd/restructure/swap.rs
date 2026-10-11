//! Writing a verified plan: new files alongside the originals, a backup, and
//! one commit point.
//!
//! The originals that will change are copied into a backup directory first.
//! Then every new file is written to a temporary name next to its target.
//! Then the new files are renamed into place, the file that COMMITS the change
//! last: for `split` that is the root, which is the only file that names the
//! new period files, so until it is swapped the old root is still the whole
//! ledger and the new files are inert. For `merge` it is the merged root, which
//! stops naming the included files the moment it lands; only then are those
//! removed. At no point is the ledger on disk half old and half new.
//!
//! After the swap the ledger is loaded again from disk and compared with the
//! original once more. If that fails, the backup is restored. A failure
//! before the commit point changes nothing on disk except the backup, which
//! stays behind (the error says where).
//!
//! The ledger is also loaded once right after the backup is written, before
//! anything else is touched: the backup sits in FILE's directory, and an
//! include pattern that matches it (`years/*` when FILE is in `years/`) would
//! make the backup itself part of the ledger. That is refused, and the fresh
//! backup removed, while the originals are still untouched.
//!
//! Every original is compared with the bytes the plan was made from twice:
//! before the backup is written, and again after the new files are staged,
//! immediately before the first rename, so an edit made while the backup and
//! the temporaries were being written and flushed is not overwritten.

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
    /// Unix permission bits the commit file may have at most (`merge`: the
    /// bits every merged file allows).
    pub(super) mode_mask: Option<u32>,
}

/// When `apply` asks for the ledger to be verified.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Phase {
    /// The backup exists and nothing else has been touched.
    BackedUp,
    /// The new layout is in place.
    Swapped,
}

/// Whether anything (a file, a directory, or a symlink, dangling or not)
/// occupies `path`. `Path::exists` follows symlinks, so a dangling one reads
/// as free and `rename` would silently replace it.
pub(super) fn occupied(path: &Path) -> bool {
    fs::symlink_metadata(path).is_ok()
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
        if path != &plan.commit && occupied(path) {
            bail!(
                "{} already exists; refusing to overwrite it (move it away or choose another --dir)",
                path.display()
            );
        }
    }
    unchanged(plan)
}

/// Refuse if any original no longer has the bytes the plan was made from.
fn unchanged(plan: &Plan) -> Result<()> {
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

/// Apply `plan`. `verify` reloads the ledger from disk and fails if it no
/// longer matches the original: once with the backup written and nothing else
/// touched ([`Phase::BackedUp`]; a failure removes the backup and changes
/// nothing), and once after the swap ([`Phase::Swapped`]; a failure restores
/// the backup).
pub(super) fn apply(plan: &Plan, mut verify: impl FnMut(Phase) -> Result<()>) -> Result<Applied> {
    preflight(plan)?;
    let backup_dir = if plan.originals.is_empty() {
        None
    } else {
        Some(make_backup(plan).context("nothing was changed")?)
    };
    let backup_note = backup_dir.as_ref().map_or_else(String::new, |d| {
        format!("; a backup copy is in {}", d.display())
    });
    if let Some(dir) = &backup_dir
        && let Err(e) = verify(Phase::BackedUp)
    {
        let removed = if remove_backup(dir) {
            "was removed".to_string()
        } else {
            format!("could not be removed; delete {} by hand", dir.display())
        };
        return Err(e.context(format!(
            "nothing was changed: with the backup in {} the ledger no longer loads as \
             before (an include pattern that matches the backup is the usual cause), \
             so the backup {removed}",
            dir.display()
        )));
    }

    let mut created_dirs: Vec<PathBuf> = Vec::new();
    let mut temps: Vec<(PathBuf, PathBuf)> = Vec::new();
    let staged = stage(plan, &mut created_dirs, &mut temps).and_then(|()| {
        // Last look before the first rename: an original edited while the
        // backup and temporaries were written must not be overwritten.
        fault(&Fault::BeforeRename)?;
        unchanged(plan)
    });
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

    if let Err(e) = verify(Phase::Swapped) {
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
        let tmp = parent.join(format!(".{name}.rledger-tmp-{}", unique_suffix()));
        let mut f = create_private(&tmp)?;
        temps.push((tmp.clone(), target.clone()));
        fault(&Fault::Write(&tmp))?;
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
            let mask = if target == &plan.commit {
                plan.mode_mask
            } else {
                None
            };
            copy_access(&tmp, &meta, mask)?;
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
        let name = path.file_name().unwrap_or_default().to_string_lossy();
        let tmp = path.with_file_name(format!(".{name}.rledger-restore-{}", unique_suffix()));
        let bytes =
            fs::read(&saved).with_context(|| format!("failed to restore {}", path.display()))?;
        let mut f = create_private(&tmp)?;
        f.write_all(&bytes)
            .and_then(|()| f.sync_all())
            .with_context(|| format!("failed to restore {}", path.display()))?;
        // The backup copy carries the original's group and mode; so must the
        // restored file (a plain copy would take the process's group).
        let meta = fs::metadata(&saved)
            .with_context(|| format!("failed to restore {}", path.display()))?;
        copy_access(&tmp, &meta, None)?;
        fault(&Fault::Restore(path))?;
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
    create_private_dirs(&root)?;
    // Claim a directory no other run is using. Creating it is the claim: a
    // check-then-create would let two runs started in the same second share
    // one directory, and the second's manifest would replace the first's.
    let mut n = 0;
    let dir = loop {
        let dir = root.join(if n == 0 {
            format!("{stamp}-{}", plan.operation)
        } else {
            format!("{stamp}-{}-{n}", plan.operation)
        });
        n += 1;
        fault(&Fault::ClaimBackup(&dir))?;
        match create_private_dir(&dir) {
            Ok(()) => break dir,
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(e) => {
                return Err(
                    anyhow::Error::new(e).context(format!("failed to create {}", dir.display()))
                );
            }
        }
    };
    // From here the directory is this run's alone; a failure removes it so a
    // half-written backup without a manifest is not left behind.
    match fill_backup(plan, &dir, &stamp) {
        Ok(()) => Ok(dir),
        Err(e) => {
            remove_backup(&dir);
            Err(e)
        }
    }
}

fn fill_backup(plan: &Plan, dir: &Path, stamp: &str) -> Result<()> {
    let mut manifest = format!(
        "# rledger {} backup, {stamp}\n# To undo: copy each file below back to its original path,\n# and delete the files listed as created.\n",
        plan.operation
    );
    for (path, original) in &plan.originals {
        let rel = backup_rel(&plan.backup_base, path);
        let dest = dir.join(&rel);
        if let Some(parent) = dest.parent() {
            create_private_dirs(parent)?;
        }
        let mut f = create_private(&dest)?;
        fault(&Fault::Backup(&dest))?;
        f.write_all(original)
            .with_context(|| format!("failed to back up {}", path.display()))?;
        // The copy is as private as the original: a ledger kept at 0600 must
        // not sit world-readable in the backup (and `restore` copies these
        // permissions back).
        if let Ok(meta) = fs::metadata(path) {
            copy_access(&dest, &meta, None)?;
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
    Ok(())
}

/// Remove a backup directory this run created, and `.rledger-backup` too if
/// that leaves it empty. Returns whether the backup directory is gone.
fn remove_backup(dir: &Path) -> bool {
    let gone = fs::remove_dir_all(dir).is_ok();
    if let Some(parent) = dir.parent() {
        let _ = fs::remove_dir(parent);
    }
    gone
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

/// Create a file only its owner can read; its final permissions are set once
/// written. A file created with the default umask would expose a private
/// ledger for as long as it takes to write it.
fn create_private(path: &Path) -> Result<fs::File> {
    let mut opts = fs::OpenOptions::new();
    opts.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        opts.mode(0o600);
    }
    opts.open(path)
        .with_context(|| format!("failed to create {}", path.display()))
}

/// `create_dir_all`, owner-only for the directories it creates.
fn create_private_dirs(dir: &Path) -> Result<()> {
    let mut builder = fs::DirBuilder::new();
    builder.recursive(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;
        builder.mode(0o700);
    }
    builder
        .create(dir)
        .with_context(|| format!("failed to create {}", dir.display()))
}

/// Create one directory, owner-only; fails if it exists.
fn create_private_dir(dir: &Path) -> std::io::Result<()> {
    let mut builder = fs::DirBuilder::new();
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;
        builder.mode(0o700);
    }
    builder.create(dir)
}

/// Points where tests inject a failure (an I/O error, or a panic standing in
/// for the process being killed) or a concurrent change.
#[derive(Debug)]
#[cfg_attr(not(test), allow(dead_code))] // read only by the tests' hooks
pub(super) enum Fault<'a> {
    /// About to create this backup directory.
    ClaimBackup(&'a Path),
    /// About to write this backup copy.
    Backup(&'a Path),
    /// About to write the content of this temporary.
    Write(&'a Path),
    /// Everything staged; about to rename the first file into place.
    BeforeRename,
    /// About to rename this restored original into place.
    Restore(&'a Path),
}

#[cfg(test)]
type FaultHook = Box<dyn FnMut(&Fault<'_>) -> Result<()>>;

#[cfg(test)]
thread_local! {
    static FAULT: std::cell::RefCell<Option<FaultHook>> = std::cell::RefCell::new(None);
}

/// Install `hook` for the swaps run on this thread until the guard drops.
#[cfg(test)]
pub(super) fn inject(hook: impl FnMut(&Fault<'_>) -> Result<()> + 'static) -> impl Drop {
    struct Guard;
    impl Drop for Guard {
        fn drop(&mut self) {
            FAULT.with(|f| f.borrow_mut().take());
        }
    }
    FAULT.with(|f| *f.borrow_mut() = Some(Box::new(hook)));
    Guard
}

#[cfg(test)]
fn fault(point: &Fault<'_>) -> Result<()> {
    FAULT.with(|f| match f.borrow_mut().as_mut() {
        Some(hook) => hook(point),
        None => Ok(()),
    })
}

#[cfg(not(test))]
#[allow(clippy::unnecessary_wraps)]
#[inline]
const fn fault(_: &Fault<'_>) -> Result<()> {
    Ok(())
}

/// A suffix no other run (and no earlier crashed run with a reused pid) is
/// using: the pid, the time, and a per-process counter.
fn unique_suffix() -> String {
    static COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos());
    let n = COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    format!("{}-{nanos}-{n}", std::process::id())
}

/// Give `path` the group and permission bits of `template`, narrowed by
/// `mask`. A new file belongs to the process's group, which may be shared
/// more widely than the original's: the group is copied where the user may
/// set it, and where not, group access is dropped rather than handed to a
/// different group.
fn copy_access(path: &Path, template: &fs::Metadata, mask: Option<u32>) -> Result<()> {
    let mut perms = template.permissions();
    #[cfg(unix)]
    {
        use std::os::unix::fs::{MetadataExt, PermissionsExt};
        let mut mode = perms.mode() & mask.unwrap_or(0o7777);
        let regrouped = std::os::unix::fs::chown(path, None, Some(template.gid())).is_ok()
            || fs::metadata(path).is_ok_and(|m| m.gid() == template.gid());
        if !regrouped {
            mode &= !0o070;
        }
        perms.set_mode(mode);
    }
    #[cfg(not(unix))]
    let _ = mask;
    fs::set_permissions(path, perms)
        .with_context(|| format!("failed to set permissions on {}", path.display()))
}
