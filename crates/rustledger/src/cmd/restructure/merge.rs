//! `rledger merge` — inline a file's includes back into it.
//!
//! The merged file is the file's own text with its `include` lines taken out
//! (the comments above them stay), followed by the flattened content of each
//! included file in include order, recursively: a file's own text, then what
//! it includes. That is the order the loader visits files in, so the merged
//! file ranks same-date directives exactly as the original layout did (see
//! [`super`]). A file included twice is inlined once, as the loader loads it
//! once.
//!
//! Each file's `pushtag`/`pushmeta` stack is balanced (an unbalanced one is a
//! parse error, which is refused), so concatenating whole files never lets one
//! file's pushed tags leak into the next.
//!
//! By default the merged file replaces FILE and the inlined files are removed
//! (they are backed up first). With `--output`, the merged ledger is written
//! to a new file and nothing else is touched.

use super::segment::{ItemKind, segment};
use super::{Before, swap};
use anyhow::{Context, Result, bail};
use clap::Parser;
use std::collections::HashSet;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

/// Merge a beancount file and everything it includes into one file.
///
/// The ledger is loaded before and after (plugins, booking, validation) and
/// nothing is written unless the two agree.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// The beancount file whose includes to inline (uses config default if
    /// not specified)
    #[arg(value_name = "FILE")]
    pub file: Option<PathBuf>,

    /// Write the merged ledger to this new file instead of replacing FILE;
    /// FILE and the files it includes are left untouched
    #[arg(short = 'o', long, value_name = "OUTPUT", conflicts_with = "ledger")]
    pub output: Option<PathBuf>,

    /// Keep the inlined files on disk instead of removing them
    #[arg(long)]
    pub keep_included: bool,

    /// Ledger root that FILE belongs to, when FILE is itself included by
    /// another file. The equivalence check loads this root. Default: FILE
    #[arg(long, value_name = "ROOT")]
    pub ledger: Option<PathBuf>,

    /// Show the plan and run the equivalence check, but write nothing
    #[arg(short = 'n', long)]
    pub dry_run: bool,
}

/// Run `merge`, printing the plan to stdout and diagnostics to stderr.
pub fn run(args: &Args) -> Result<ExitCode> {
    run_with_writer(args, &mut io::stdout().lock(), &mut io::stderr())
}

/// Run `merge` with explicit output streams. Exit codes as for `split`.
pub fn run_with_writer(args: &Args, out: &mut dyn Write, err: &mut dyn Write) -> Result<ExitCode> {
    let Some(file) = &args.file else {
        bail!("FILE is required (or set default.file in config)");
    };
    let file = super::existing_file(file)?;
    let (source, original) = super::read_source(&file)?;

    let file_dir = file.parent().map(Path::to_path_buf).unwrap_or_default();
    let mut flat = Flattener {
        visited: HashSet::from([file.clone()]),
        order: Vec::new(),
        originals: Vec::new(),
        removable: Vec::new(),
        root_dir: file_dir.clone(),
    };
    let merged = flat.flatten(&file, &source, true)?;
    if flat.order.is_empty() {
        bail!(
            "{} includes nothing; there is nothing to merge",
            file.display()
        );
    }

    let (target, root, removes, originals) = if let Some(o) = &args.output {
        let target = super::overlay::normalize(o);
        (target.clone(), target, Vec::new(), Vec::new())
    } else {
        let root = match &args.ledger {
            Some(r) => super::existing_file(r)?,
            None => file.clone(),
        };
        let removes: Vec<PathBuf> = if args.keep_included {
            Vec::new()
        } else {
            flat.removable.clone()
        };
        let mut originals = vec![(file.clone(), original)];
        originals.extend(
            flat.originals
                .iter()
                .filter(|(p, _)| removes.contains(p))
                .cloned(),
        );
        (file.clone(), root, removes, originals)
    };

    let swap_plan = swap::Plan {
        writes: vec![(target.clone(), merged)],
        commit: target.clone(),
        removes,
        backup_base: file_dir,
        originals,
        operation: "merge",
        template: file.clone(),
        mode_mask: strictest_mode(std::iter::once(&file).chain(&flat.order)),
    };
    if args.output.is_some() && target.exists() {
        bail!(
            "{} already exists; refusing to overwrite it",
            target.display()
        );
    }
    swap::preflight(&swap_plan)?;

    // With --output the original ledger is the reference and the new file is
    // the candidate; otherwise both loads go through the same root.
    let reference = if args.output.is_some() { &file } else { &root };
    let before: Before = super::load_before(reference)?;
    if args.ledger.is_some() && !before.files.contains(&file) {
        bail!(
            "{} is not part of the ledger rooted at {}",
            file.display(),
            root.display()
        );
    }

    writeln!(
        out,
        "Plan: merge {} and the files it includes",
        super::show(&file)
    )?;
    for path in &flat.order {
        let verb = if args.output.is_some() || args.keep_included {
            "inline"
        } else if flat.removable.contains(path) {
            "inline and remove"
        } else {
            "inline (kept: outside FILE's directory or reached through a symlink)"
        };
        writeln!(out, "  {verb}  {}", super::show(path))?;
    }
    let verb = if args.output.is_some() {
        "create"
    } else {
        "rewrite"
    };
    writeln!(out, "  {verb}  {}", super::show(&target))?;

    let mut difference =
        super::check_planned(&root, &before, &swap_plan.writes, &swap_plan.removes)?;
    if args.output.is_some() && difference.is_none() {
        // The new file must not change the ledger it was made from either: a
        // glob in FILE's tree that matches the output path would pick the
        // merged copy up and count every directive twice.
        difference = super::check_planned(&file, &before, &swap_plan.writes, &[])?.map(|d| {
            format!(
                "{} would change once the output file exists: {d}",
                file.display()
            )
        });
    }
    if !super::report_check(out, err, "merge", &before, difference.as_deref())? {
        return Ok(ExitCode::from(1));
    }
    if args.dry_run {
        writeln!(out, "Dry run: nothing was written.")?;
        return Ok(ExitCode::SUCCESS);
    }
    super::write_plan(out, &root, &before, &swap_plan)?;
    Ok(ExitCode::SUCCESS)
}

struct Flattener {
    /// Files already inlined (or the file being merged), canonical.
    visited: HashSet<PathBuf>,
    /// Included files in the order they were inlined.
    order: Vec<PathBuf>,
    /// Their contents as read.
    originals: Vec<(PathBuf, Vec<u8>)>,
    /// The inlined files that may be removed afterwards.
    removable: Vec<PathBuf>,
    /// FILE's directory, canonical.
    root_dir: PathBuf,
}

impl Flattener {
    /// `path`'s own text without its include lines, then each included file
    /// flattened, in include order.
    fn flatten(&mut self, path: &Path, source: &str, owned: bool) -> Result<String> {
        let seg = segment(source, path)?;
        let nl = super::newline_of(source);
        // Only the file being merged into keeps a byte-order mark; one from
        // an included file would land in the middle of the merged file.
        let mut out = if self.order.is_empty() || !seg.leading.starts_with('\u{FEFF}') {
            seg.leading.clone()
        } else {
            seg.leading['\u{FEFF}'.len_utf8()..].to_string()
        };
        let mut includes: Vec<String> = Vec::new();
        for item in &seg.items {
            if let ItemKind::Include(p) = &item.kind {
                // Keep the comments written above the include and on its
                // line; drop the include itself.
                super::push_block(&mut out, &item.text[..item.lead_len], nl);
                if !item.line_comment.is_empty() {
                    super::push_block(&mut out, &item.line_comment, nl);
                }
                includes.push(p.clone());
            } else {
                super::push_block(&mut out, &item.text, nl);
            }
        }
        if !seg.trailing.is_empty() {
            super::push_block(&mut out, &seg.trailing, nl);
        }

        let base = path.parent().unwrap_or_else(|| Path::new("."));
        for inc in includes {
            for (named, target) in resolve_include(base, &inc)? {
                if !self.visited.insert(target.clone()) {
                    continue;
                }
                // Only a plain file inside FILE's directory, reached without
                // a symlink, is ours to remove. A symlinked or out-of-tree
                // include may be shared with another ledger; deleting it (or
                // the file a symlink points at) would break that ledger.
                //
                // And only when its includer is ours too: a kept file still
                // includes its children, so removing them would leave it with
                // a dangling include.
                let removable =
                    owned && target.starts_with(&self.root_dir) && lexical(&named) == target;
                if removable {
                    self.removable.push(target.clone());
                }
                let (text, bytes) = super::read_source(&target)?;
                self.order.push(target.clone());
                self.originals.push((target.clone(), bytes));
                let inner = self.flatten(&target, &text, removable)?;
                if !out.is_empty() && !out.ends_with("\n\n") {
                    out.push_str(nl);
                }
                super::push_block(&mut out, &inner, nl);
            }
        }
        Ok(out)
    }
}

/// `path` made absolute and cleaned lexically, symlinks NOT followed.
fn lexical(path: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for c in path.components() {
        match c {
            std::path::Component::ParentDir => {
                out.pop();
            }
            std::path::Component::CurDir => {}
            other => out.push(other.as_os_str()),
        }
    }
    out
}

/// The files an `include` names, as the loader resolves them: relative to the
/// including file's directory, glob patterns expanded and sorted. Each comes
/// as the path the include names and the file it resolves to.
fn resolve_include(base: &Path, include: &str) -> Result<Vec<(PathBuf, PathBuf)>> {
    let full = base.join(include);
    let paths = if rustledger_loader::is_glob_pattern(include) {
        let matched = rustledger_loader::FileSystem::glob(
            &rustledger_loader::DiskFileSystem,
            &full.to_string_lossy(),
        )
        .map_err(|e| anyhow::anyhow!("bad include pattern {include:?}: {e}"))?;
        if matched.is_empty() {
            bail!("include pattern {include:?} matches no files");
        }
        matched
    } else {
        vec![full]
    };
    paths
        .into_iter()
        .map(|p| {
            let c = p
                .canonicalize()
                .with_context(|| format!("included file not found: {}", p.display()))?;
            Ok((p, c))
        })
        .collect()
}

/// The permission bits every one of `files` allows: the merged file holds the
/// content of all of them, so it must be no more readable than the most
/// private one.
#[cfg(unix)]
fn strictest_mode<'a>(files: impl Iterator<Item = &'a PathBuf>) -> Option<u32> {
    use std::os::unix::fs::PermissionsExt;
    files
        .filter_map(|f| std::fs::metadata(f).ok())
        .map(|m| m.permissions().mode() & 0o7777)
        .reduce(|a, b| a & b)
}

#[cfg(not(unix))]
fn strictest_mode<'a>(_files: impl Iterator<Item = &'a PathBuf>) -> Option<u32> {
    None
}
