//! `rledger split` and `rledger merge`: move directives between files without
//! changing what the ledger means (#2264).
//!
//! Both commands follow the same shape. Plan the new files in memory. Load the
//! ledger as it is and as it would be (through an in-memory overlay, so
//! nothing is written yet) and compare the two with the equivalence check in
//! the `equivalence` module. Refuse unless they match. Otherwise write the new files
//! alongside the originals, back the originals up, and swap the new layout in
//! with a single commit point (the `swap` module); then load once more from disk and
//! restore the backup if that load disagrees.
//!
//! # Why splitting by date cannot change booking
//!
//! The loader orders directives by `(date, priority, file, offset)`, where
//! `file` is the file's position in a depth-first walk of the include tree
//! that visits a file before the files it includes (`canonical_sort_key` in
//! `rustledger-loader`). Booking walks the stable `(date, priority)` sort of
//! that order. So the only way moving text between files can change booking
//! is by changing the relative order of two directives with the same date and
//! priority, and that order is decided by `(file, offset)`.
//!
//! `split` sends every directive with a given date to ONE period file and
//! keeps their relative order within it. It writes the period `include` lines
//! into the split file BEFORE any `include` the file already had. In the walk
//! the period files therefore come right after the split file and before
//! everything the split file used to include, which is exactly where the split
//! file's own directives used to sort. For any date, the directives that
//! moved still sort after every file that came before the split file, before
//! every file that came after it, and in their original order among
//! themselves. Nothing that ties can change places.
//!
//! `merge` is the same argument run backwards. It writes each file's own
//! directives, then the flattened content of each file it includes, in
//! include order: the walk's order, concatenated. Offsets in the merged file
//! then rank directives exactly as `(file, offset)` did.
//!
//! An account split has no such argument (two same-date transactions in one
//! account land in different files, and their order then depends on the
//! include order of those files), which is why it is not offered.
//!
//! `pushtag` and `pushmeta` are per file in beancount and here: each file
//! starts with empty stacks, and an unpopped push is an error. A split that
//! cuts through a `pushtag` span re-opens the span at the top of each later
//! file and closes it at the end of each file it is open in; see
//! [`split`] for the rule.
//!
//! The proof is about ordering; the equivalence check is what makes the
//! command safe regardless, since it compares the loaded result rather than
//! trusting the argument.

mod equivalence;
pub mod merge;
mod overlay;
mod segment;
pub mod split;
mod swap;

use anyhow::{Context, Result, bail};
use std::io::Write;
use std::path::{Component, Path, PathBuf};

/// Read a file the restructurer will rewrite. Invalid UTF-8 is refused: the
/// loader reads such a file lossily, so writing back what it read would
/// replace the offending bytes, which is a change the user did not ask for.
fn read_source(path: &Path) -> Result<(String, Vec<u8>)> {
    if rustledger_loader::FileSystem::is_encrypted(&rustledger_loader::DiskFileSystem, path) {
        bail!(
            "{} is encrypted; refusing to restructure it (the result would be written in plain text)",
            path.display()
        );
    }
    let bytes =
        std::fs::read(path).with_context(|| format!("failed to read {}", path.display()))?;
    let text = String::from_utf8(bytes.clone()).map_err(|_| {
        anyhow::anyhow!(
            "{} is not valid UTF-8; refusing to rewrite it",
            path.display()
        )
    })?;
    Ok((text, bytes))
}

/// The newline a generated line should use, matching the file.
fn newline_of(source: &str) -> &'static str {
    if source.contains("\r\n") {
        "\r\n"
    } else {
        "\n"
    }
}

/// Append `text` to `out`, making sure the two are separated by a line break
/// and that `out` ends with one.
fn push_block(out: &mut String, text: &str, nl: &str) {
    if !out.is_empty() && !out.ends_with('\n') {
        out.push_str(nl);
    }
    out.push_str(text);
    if !out.is_empty() && !out.ends_with('\n') {
        out.push_str(nl);
    }
}

/// `to` relative to the directory `from`, with `/` separators, for an
/// `include` line. Both must be normalized absolute paths.
fn relative_include(from_dir: &Path, to: &Path) -> String {
    let from: Vec<Component<'_>> = from_dir.components().collect();
    let target: Vec<Component<'_>> = to.components().collect();
    let common = from.iter().zip(&target).take_while(|(a, b)| a == b).count();
    if common == 0 {
        return to.to_string_lossy().replace('\\', "/");
    }
    let mut parts: Vec<String> = Vec::new();
    for _ in common..from.len() {
        parts.push("..".to_string());
    }
    for c in &target[common..] {
        parts.push(c.as_os_str().to_string_lossy().into_owned());
    }
    parts.join("/")
}

/// Quote a path for an `include` line, refusing what the string syntax cannot
/// carry unambiguously.
fn include_line(path: &str) -> Result<String> {
    if path.contains(['"', '\\', '\n', '\r']) {
        bail!(
            "cannot write an include for {path:?}: the path contains a quote, backslash or newline"
        );
    }
    if rustledger_loader::is_glob_pattern(path) {
        bail!(
            "cannot write an include for {path:?}: the loader would read `*`, `?` or `[` as a glob; choose another --dir"
        );
    }
    Ok(format!("include \"{path}\""))
}

/// Path for display: relative to the current directory when under it.
fn show(path: &Path) -> String {
    std::env::current_dir()
        .ok()
        .and_then(|cwd| {
            let cwd = cwd.canonicalize().unwrap_or(cwd);
            path.strip_prefix(&cwd).ok().map(Path::to_path_buf)
        })
        .unwrap_or_else(|| path.to_path_buf())
        .display()
        .to_string()
}

/// Resolve the file argument to the canonical path of an existing file.
fn existing_file(path: &Path) -> Result<PathBuf> {
    if !path.is_file() {
        bail!("file not found: {}", path.display());
    }
    path.canonicalize()
        .with_context(|| format!("failed to resolve {}", path.display()))
}

/// The ledger loaded as it is, and the files it consists of.
struct Before {
    fingerprint: equivalence::Fingerprint,
    files: Vec<PathBuf>,
}

fn load_before(root: &Path) -> Result<Before> {
    let (fingerprint, files) = equivalence::load(root, overlay::OverlayFs::disk())?;
    Ok(Before { fingerprint, files })
}

/// How `unstable` starts its reason, so the refusal names the input, not the
/// result, as the problem.
const UNSTABLE: &str = "The ledger does not load the same way twice,";

/// Load `root` a second time and compare with `before`. A ledger that loads
/// differently from one run to the next (a plugin that emits entries in hash
/// order, say) cannot be certified by comparing two loads, so it is refused
/// when caught. Catching it is probabilistic: two varying loads can agree by
/// chance, and the reload after writing (which restores the backup on a
/// difference) is the backstop. The real fix for such a ledger is in the
/// plugin.
fn unstable(root: &Path, before: &Before) -> Result<Option<String>> {
    let (again, _) = equivalence::load(root, overlay::OverlayFs::disk())?;
    Ok(
        equivalence::first_difference(&before.fingerprint, &again).map(|d| {
            format!(
                "{UNSTABLE} even unchanged, so no \
                 restructuring of it can be verified (a plugin producing entries in a \
                 varying order is the usual cause): {d}"
            )
        }),
    )
}

/// Compare the planned ledger with `before`. `Ok(None)` when they match,
/// `Ok(Some(reason))` when they do not.
fn check_planned(
    root: &Path,
    before: &Before,
    writes: &[(PathBuf, String)],
    removes: &[PathBuf],
) -> Result<Option<String>> {
    let mut fs = overlay::OverlayFs::disk();
    for (path, content) in writes {
        fs.add(path, content);
    }
    for path in removes {
        fs.remove(path);
    }
    let (after, _) = equivalence::load(root, fs)?;
    Ok(equivalence::first_difference(&before.fingerprint, &after))
}

/// Report the check's verdict. Returns whether it passed.
fn report_check(
    out: &mut dyn Write,
    err: &mut dyn Write,
    operation: &str,
    before: &Before,
    difference: Option<&str>,
) -> Result<bool> {
    if let Some(reason) = difference {
        writeln!(
            err,
            "error: refusing to {operation}: {}\n  {reason}\n  Nothing was written.",
            if reason.starts_with(UNSTABLE) {
                "the ledger as it is cannot be verified."
            } else {
                "the result would not load as the same ledger."
            }
        )?;
        return Ok(false);
    }
    writeln!(
        out,
        "Equivalence check passed: {} directives, {} errors and warnings, options and plugins unchanged.",
        before.fingerprint.directive_count(),
        before.fingerprint.error_count()
    )?;
    Ok(true)
}

/// Write `plan` and verify it on disk against `before`.
fn write_plan(out: &mut dyn Write, root: &Path, before: &Before, plan: &swap::Plan) -> Result<()> {
    let applied = swap::apply(plan, |_phase| {
        let (again, _) = equivalence::load(root, overlay::OverlayFs::disk())?;
        match equivalence::first_difference(&before.fingerprint, &again) {
            None => Ok(()),
            Some(reason) => bail!("{reason}"),
        }
    })?;
    if let Some(dir) = &applied.backup_dir {
        writeln!(out, "Backup of the original files: {}", show(dir))?;
    }
    writeln!(out, "Done; the ledger was reloaded from disk and matches.")?;
    Ok(())
}

/// Tests shared by both commands.
#[cfg(test)]
mod tests;
