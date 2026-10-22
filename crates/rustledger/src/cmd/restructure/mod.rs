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

/// Return a [`Refusal`] with a stable code from the current function.
///
/// The message is exactly what `rledger` prints after `error: `; the code is
/// for a caller that reports refusals some other way (`ag-rledger`, #2633).
macro_rules! refuse {
    ($code:expr, $($arg:tt)+) => {
        return Err(anyhow::Error::new($crate::cmd::restructure::Refusal::new(
            $code,
            format!($($arg)+),
        )))
    };
}

mod equivalence;
pub mod merge;
mod overlay;
mod segment;
pub mod split;
mod swap;

use anyhow::{Context, Result, bail};
use std::fmt;
use std::io::Write;
use std::path::{Component, Path, PathBuf};

/// The stable codes of what `split` and `merge` refuse to do, and of the
/// warning they can leave behind. `rledger` prints the message; `ag-rledger`
/// reports the code with it (#2633).
pub mod code {
    /// No FILE was given and the config names none.
    pub const MISSING_FILE: &str = "MISSING_FILE";
    /// FILE, or `--ledger`, does not exist.
    pub const FILE_NOT_FOUND: &str = "FILE_NOT_FOUND";
    /// FILE is a symlink to a file in another directory (#2614, #2635).
    pub const SYMLINK_ELSEWHERE: &str = "SYMLINK_ELSEWHERE";
    /// A file to rewrite is encrypted; the result would be plain text.
    pub const ENCRYPTED_FILE: &str = "ENCRYPTED_FILE";
    /// A file to rewrite is not valid UTF-8.
    pub const NOT_UTF8: &str = "NOT_UTF8";
    /// A file to rewrite has parse errors (or a malformed push/pop).
    pub const PARSE_ERRORS: &str = "PARSE_ERRORS";
    /// `split`: FILE has no dated directives.
    pub const NOTHING_TO_SPLIT: &str = "NOTHING_TO_SPLIT";
    /// `merge`: FILE includes nothing.
    pub const NOTHING_TO_MERGE: &str = "NOTHING_TO_MERGE";
    /// `split --dir` names a file.
    pub const NOT_A_DIRECTORY: &str = "NOT_A_DIRECTORY";
    /// A file the plan creates already exists (a dangling symlink included).
    pub const TARGET_EXISTS: &str = "TARGET_EXISTS";
    /// `split`: a period file would be FILE itself.
    pub const TARGET_IS_SOURCE: &str = "TARGET_IS_SOURCE";
    /// `--ledger` names a ledger FILE is not part of.
    pub const NOT_IN_LEDGER: &str = "NOT_IN_LEDGER";
    /// `split`: an `include` for a period file cannot be written (quote,
    /// backslash, newline, or a glob character in the path).
    pub const UNWRITABLE_INCLUDE: &str = "UNWRITABLE_INCLUDE";
    /// `merge`: an `include` names no file, or a glob that matches none.
    pub const INCLUDE_NOT_FOUND: &str = "INCLUDE_NOT_FOUND";
    /// `merge`: an `include` glob is malformed.
    pub const BAD_INCLUDE_PATTERN: &str = "BAD_INCLUDE_PATTERN";
    /// The ledger failed to load, before or as planned.
    pub const LOAD_FAILED: &str = "LOAD_FAILED";
    /// The planned layout would not load as the same ledger.
    pub const EQUIVALENCE_FAILED: &str = "EQUIVALENCE_FAILED";
    /// The ledger as it is loads differently from one run to the next, so
    /// no restructuring of it can be verified.
    pub const LEDGER_UNSTABLE: &str = "LEDGER_UNSTABLE";
    /// A file changed on disk while the plan was being checked.
    pub const CHANGED_ON_DISK: &str = "CHANGED_ON_DISK";
    /// The backup would itself be read as part of the ledger (an include
    /// pattern matches it); it was removed and nothing changed.
    pub const BACKUP_INCLUDED: &str = "BACKUP_INCLUDED";
    /// The files were written, did not reload as the same ledger, and the
    /// originals were restored from the backup.
    pub const WRITE_ROLLED_BACK: &str = "WRITE_ROLLED_BACK";
    /// As [`WRITE_ROLLED_BACK`], but restoring failed too: the backup named
    /// in the message holds the originals.
    pub const RESTORE_FAILED: &str = "RESTORE_FAILED";
    /// Warning: the merge was written, but some inlined files that are no
    /// longer included could not be removed.
    pub const FILES_NOT_REMOVED: &str = "FILES_NOT_REMOVED";
}

/// Something `split` or `merge` refuses, with a stable [`code`].
///
/// It displays as the message alone, so `rledger` prints exactly what it
/// printed before the codes existed.
#[derive(Debug)]
pub struct Refusal {
    code: &'static str,
    message: String,
}

impl Refusal {
    /// A refusal with `code` (one of [`code`]) and `message`.
    #[must_use]
    pub const fn new(code: &'static str, message: String) -> Self {
        Self { code, message }
    }

    /// The refusal's code, one of [`code`].
    #[must_use]
    pub const fn code(&self) -> &'static str {
        self.code
    }
}

impl fmt::Display for Refusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for Refusal {}

/// The code of the outermost [`Refusal`] in `error`'s chain, or `None` for
/// an error that is not one (an I/O failure, an internal error).
#[must_use]
pub fn refusal_code(error: &anyhow::Error) -> Option<&'static str> {
    error.downcast_ref::<Refusal>().map(Refusal::code)
}

/// What a `split` or `merge` run planned, checked and wrote.
///
/// Filled in as the run goes, so a run that fails still says how far it got,
/// what the equivalence check found, and what it wrote. `rledger` prints the
/// same facts as text.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Outcome {
    /// The plan, once it is made.
    pub plan: Option<Planned>,
    /// The equivalence check's verdict, once it has run.
    pub check: Option<Check>,
    /// Whether this was a dry run (nothing is written).
    pub dry_run: bool,
    /// What was written, once the new layout is in place and verified.
    pub written: Option<Written>,
    /// Where the originals were backed up, from the moment the backup
    /// exists: also on a failed write (the backup is kept, and holds the
    /// originals if restoring failed), and `None` again if it was removed.
    pub backup_dir: Option<PathBuf>,
}

impl Outcome {
    /// Exit status as `rledger` reports it: 1 when the check refused.
    #[must_use]
    pub const fn exit_status(&self) -> u8 {
        match self.check {
            Some(Check::Refused { .. }) => 1,
            _ => 0,
        }
    }
}

/// The plan: the file restructured and what happens to each file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Planned {
    /// `split` or `merge`.
    pub operation: &'static str,
    /// The file being restructured (canonical).
    pub file: PathBuf,
    /// `split`: the period (`year` or `month`).
    pub by: Option<&'static str>,
    /// Each file the plan touches, in the order it lists them.
    pub steps: Vec<Step>,
}

/// One file in a plan.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Step {
    /// A new file: a period file (`split`, with its dated directive count)
    /// or `merge --output`'s file.
    Create {
        /// The file created.
        path: PathBuf,
        /// `split`: how many dated directives the period file holds.
        dated_directives: Option<usize>,
    },
    /// FILE, rewritten in place.
    Rewrite {
        /// The file rewritten.
        path: PathBuf,
        /// `split`: how many option/plugin/include lines it keeps, and how
        /// many period includes it gains.
        split: Option<(usize, usize)>,
    },
    /// `merge`: a file inlined into the merged file.
    Inline {
        /// The file inlined.
        path: PathBuf,
        /// Whether it is removed once the merged file is in place.
        remove: bool,
        /// Whether it is kept because it may belong to another ledger: it is
        /// outside FILE's directory, reached through a symlink, or included
        /// by a file that is itself kept.
        shared: bool,
    },
}

/// The equivalence check's verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Check {
    /// The planned ledger loads as the same ledger.
    Passed {
        /// Directives in the ledger.
        directives: usize,
        /// Errors and warnings, the same before and after.
        errors: usize,
    },
    /// The plan was refused, and nothing was written.
    Refused {
        /// The first difference found.
        reason: String,
        /// Whether the ledger as it is loads differently twice
        /// ([`code::LEDGER_UNSTABLE`]) rather than the plan changing it
        /// ([`code::EQUIVALENCE_FAILED`]).
        unstable: bool,
    },
}

impl Check {
    /// [`code::LEDGER_UNSTABLE`] or [`code::EQUIVALENCE_FAILED`] for a
    /// refusal, `None` when the check passed.
    #[must_use]
    pub const fn refusal_code(&self) -> Option<&'static str> {
        match self {
            Self::Passed { .. } => None,
            Self::Refused { unstable: true, .. } => Some(code::LEDGER_UNSTABLE),
            Self::Refused { .. } => Some(code::EQUIVALENCE_FAILED),
        }
    }
}

/// What a run that was not a dry run wrote.
///
/// Also for a write that failed after the swap: the lists then say how far
/// the write got, and the refusal's code says whether the rollback restored
/// these files ([`code::WRITE_ROLLED_BACK`]) or some may still be in place
/// ([`code::RESTORE_FAILED`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Written {
    /// Every file written: new files and the rewritten FILE.
    pub written: Vec<PathBuf>,
    /// The inlined files removed (`merge`).
    pub removed: Vec<PathBuf>,
    /// Inlined files that should have been removed and could not be, each
    /// with why ([`code::FILES_NOT_REMOVED`]).
    pub not_removed: Vec<String>,
}

/// Read a file the restructurer will rewrite. Invalid UTF-8 is refused: the
/// loader reads such a file lossily, so writing back what it read would
/// replace the offending bytes, which is a change the user did not ask for.
fn read_source(path: &Path) -> Result<(String, Vec<u8>)> {
    if rustledger_loader::FileSystem::is_encrypted(&rustledger_loader::DiskFileSystem, path) {
        refuse!(
            code::ENCRYPTED_FILE,
            "{} is encrypted; refusing to restructure it (the result would be written in plain text)",
            path.display()
        );
    }
    let bytes =
        std::fs::read(path).with_context(|| format!("failed to read {}", path.display()))?;
    let Ok(text) = String::from_utf8(bytes.clone()) else {
        refuse!(
            code::NOT_UTF8,
            "{} is not valid UTF-8; refusing to rewrite it",
            path.display()
        );
    };
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
        refuse!(
            code::UNWRITABLE_INCLUDE,
            "cannot write an include for {path:?}: the path contains a quote, backslash or newline"
        );
    }
    if rustledger_loader::is_glob_pattern(path) {
        refuse!(
            code::UNWRITABLE_INCLUDE,
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

/// Refuse FILE when it is a symlink to a file in another directory.
///
/// rledger, beancount and fava all read such a file's includes next to the
/// LINK (#2635), but `split` and `merge` work on the canonical file: `split`
/// would write the period files next to the target, where nothing opening
/// the link looks for them, and `merge` would inline the target's
/// neighbors, not the files the link's ledger includes. The equivalence
/// check cannot see either, because it loads the canonical file too. A link
/// beside its target reads the same files either way, so it is allowed.
fn refuse_link_elsewhere(given: &Path, file: &Path, operation: &str) -> Result<()> {
    if !std::fs::symlink_metadata(given).is_ok_and(|m| m.file_type().is_symlink()) {
        return Ok(());
    }
    let link_dir = overlay::normalize(given.parent().unwrap_or_else(|| Path::new(".")));
    if file.parent() == Some(link_dir.as_path()) {
        return Ok(());
    }
    refuse!(
        code::SYMLINK_ELSEWHERE,
        "{} is a symlink to a file in another directory; refusing to {operation} it: \
         its includes are read next to the link, but {operation} would work on {} and \
         the files next to it. Run it on that file instead if nothing opens the \
         ledger through the link",
        given.display(),
        file.display()
    );
}

/// Resolve the file argument to the canonical path of an existing file.
fn existing_file(path: &Path) -> Result<PathBuf> {
    if !path.is_file() {
        refuse!(code::FILE_NOT_FOUND, "file not found: {}", path.display());
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

/// Report the check's verdict, and record it in `outcome`. Returns whether
/// it passed.
fn report_check(
    out: &mut dyn Write,
    err: &mut dyn Write,
    operation: &str,
    before: &Before,
    difference: Option<&str>,
    outcome: &mut Outcome,
) -> Result<bool> {
    if let Some(reason) = difference {
        let unstable = reason.starts_with(UNSTABLE);
        outcome.check = Some(Check::Refused {
            reason: reason.to_string(),
            unstable,
        });
        writeln!(
            err,
            "error: refusing to {operation}: {}\n  {reason}\n  Nothing was written.",
            if unstable {
                "the ledger as it is cannot be verified."
            } else {
                "the result would not load as the same ledger."
            }
        )?;
        return Ok(false);
    }
    let directives = before.fingerprint.directive_count();
    let errors = before.fingerprint.error_count();
    outcome.check = Some(Check::Passed { directives, errors });
    writeln!(
        out,
        "Equivalence check passed: {directives} directives, {errors} errors and warnings, options and plugins unchanged.",
    )?;
    Ok(true)
}

/// Print the plan, and record it in `outcome`.
fn report_plan(out: &mut dyn Write, planned: Planned, outcome: &mut Outcome) -> Result<()> {
    match planned.by {
        Some(by) => writeln!(
            out,
            "Plan: {} {} by {by}",
            planned.operation,
            show(&planned.file)
        )?,
        None => writeln!(
            out,
            "Plan: {} {} and the files it includes",
            planned.operation,
            show(&planned.file)
        )?,
    }
    for step in &planned.steps {
        match step {
            Step::Create {
                path,
                dated_directives: Some(count),
            } => writeln!(out, "  create   {}  ({count} dated directives)", show(path))?,
            Step::Create {
                path,
                dated_directives: None,
            } => writeln!(out, "  create  {}", show(path))?,
            Step::Rewrite {
                path,
                split: Some((kept, added)),
            } => writeln!(
                out,
                "  rewrite  {}  (keeps {kept} option/plugin/include lines; adds {added} includes)",
                show(path)
            )?,
            Step::Rewrite { path, split: None } => writeln!(out, "  rewrite  {}", show(path))?,
            Step::Inline {
                path,
                remove,
                shared,
            } => {
                let verb = if *remove {
                    "inline and remove"
                } else if *shared {
                    "inline (kept: outside FILE's directory or reached through a symlink)"
                } else {
                    "inline"
                };
                writeln!(out, "  {verb}  {}", show(path))?;
            }
        }
    }
    outcome.plan = Some(planned);
    Ok(())
}

/// Write `plan` and verify it on disk against `before`, recording what was
/// written in `outcome`.
fn write_plan(
    out: &mut dyn Write,
    root: &Path,
    before: &Before,
    plan: &swap::Plan,
    outcome: &mut Outcome,
) -> Result<()> {
    let mut touched = swap::Touched::default();
    let applied = swap::apply_recording(plan, &mut touched, |_phase| {
        let (again, _) = equivalence::load(root, overlay::OverlayFs::disk())?;
        match equivalence::first_difference(&before.fingerprint, &again) {
            None => Ok(()),
            Some(reason) => bail!("{reason}"),
        }
    });
    outcome.backup_dir.clone_from(&touched.backup_dir);
    let applied = match applied {
        Ok(applied) => applied,
        Err(e) => {
            // How far the write got, even when it failed: the refusal's
            // code and message say whether the rollback restored these
            // files or left some in place (#2721).
            outcome.written = Some(Written {
                written: std::mem::take(&mut touched.written),
                removed: std::mem::take(&mut touched.removed),
                not_removed: std::mem::take(&mut touched.not_removed)
                    .into_iter()
                    .map(|(p, why)| format!("{}: {why}", p.display()))
                    .collect(),
            });
            return Err(e);
        }
    };
    outcome.written = Some(Written {
        written: plan.writes.iter().map(|(p, _)| p.clone()).collect(),
        removed: plan
            .removes
            .iter()
            .filter(|p| !applied.not_removed.iter().any(|(n, _)| n == *p))
            .cloned()
            .collect(),
        not_removed: applied
            .not_removed
            .iter()
            .map(|(p, why)| format!("{}: {why}", p.display()))
            .collect(),
    });
    if let Some(dir) = &applied.backup_dir {
        writeln!(out, "Backup of the original files: {}", show(dir))?;
    }
    writeln!(out, "Done; the ledger was reloaded from disk and matches.")?;
    Ok(())
}

/// Tests shared by both commands.
#[cfg(test)]
mod tests;
