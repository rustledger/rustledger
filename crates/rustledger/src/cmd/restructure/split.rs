//! `rledger split` — one file per period, plus a root of `include` lines.
//!
//! # What goes where
//!
//! - Every dated directive goes to the file for its period, with the comments
//!   and blank lines written above it, copied verbatim.
//! - `option`, `plugin` and `include` stay in the split file, which becomes the
//!   root. The new period `include` lines go in front of the first `include`
//!   the file already had (or at the end, if it had none); the module docs of
//!   [`super`] explain why that position is the one that cannot reorder
//!   anything.
//! - The file's header (text above the first directive, up to the last blank
//!   line) and anything after its last directive stay in the root.
//!
//! # `pushtag` / `pushmeta` across a boundary
//!
//! The parser keeps a stack per file, and every file starts empty. A span
//! such as
//!
//! ```text
//! pushtag #trip
//! 2023-12-30 * "Hotel"   ...
//! 2024-01-02 * "Flight"  ...
//! poptag #trip
//! ```
//!
//! split by year must still tag both transactions, so the stack each moved
//! directive saw in the original is rebuilt in its new file: before writing a
//! directive, the file's stack is brought in line with the original's at that
//! point, popping what should not be open and re-pushing (a copy of the
//! original `pushtag` line) what should; at the end of every file, whatever is
//! still open is popped. The original `pushtag`/`poptag` lines themselves,
//! with their comments, are written once: a push into the file of the next
//! dated directive after it, a pop into the file of the dated directive
//! before it.

use super::segment::{ItemKind, Segmented, StackKey, segment};
use super::{Before, swap};
use anyhow::{Result, bail};
use clap::{Parser, ValueEnum};
use rustledger_core::NaiveDate;
use std::collections::BTreeMap;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

/// How to group directives into files.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum Period {
    /// One file per calendar year (`2024.beancount`).
    Year,
    /// One file per calendar month (`2024-03.beancount`).
    Month,
}

impl Period {
    fn key(self, date: NaiveDate) -> String {
        match self {
            Self::Year => format!("{:04}", date.year()),
            Self::Month => format!("{:04}-{:02}", date.year(), date.month()),
        }
    }

    const fn name(self) -> &'static str {
        match self {
            Self::Year => "year",
            Self::Month => "month",
        }
    }
}

/// Split a beancount file into one file per period, plus a root file of
/// `include` lines.
///
/// The ledger is loaded before and after (plugins, booking, validation) and
/// nothing is written unless the two agree.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// The beancount file to split (uses config default if not specified).
    /// It becomes the root: its options, plugins and includes stay in it.
    #[arg(value_name = "FILE")]
    pub file: Option<PathBuf>,

    /// Period each new file covers
    #[arg(long, value_enum, value_name = "PERIOD")]
    pub by: Period,

    /// Directory for the period files (default: a directory named after FILE,
    /// next to it: `ledger.beancount` -> `ledger/`)
    #[arg(long, value_name = "DIR")]
    pub dir: Option<PathBuf>,

    /// Ledger root that FILE belongs to, when FILE is itself included by
    /// another file. The equivalence check loads this root. Default: FILE
    #[arg(long, value_name = "ROOT")]
    pub ledger: Option<PathBuf>,

    /// Show the plan and run the equivalence check, but write nothing
    #[arg(short = 'n', long)]
    pub dry_run: bool,
}

/// Run `split`, printing the plan to stdout and diagnostics to stderr.
pub fn run(args: &Args) -> Result<ExitCode> {
    run_with_writer(args, &mut io::stdout().lock(), &mut io::stderr())
}

/// Run `split` with explicit output streams.
///
/// Exit codes: 0 when the split was written (or, with `--dry-run`, would be);
/// 1 when the equivalence check refused it; errors (unreadable file, parse
/// errors, a target that already exists) are returned as `Err`.
pub fn run_with_writer(args: &Args, out: &mut dyn Write, err: &mut dyn Write) -> Result<ExitCode> {
    let Some(file) = &args.file else {
        bail!("FILE is required (or set default.file in config)");
    };
    let given = file;
    let file = super::existing_file(file)?;
    if std::fs::symlink_metadata(given).is_ok_and(|m| m.file_type().is_symlink()) {
        // rledger resolves a file's includes next to the file a symlink
        // points to; beancount and fava resolve them next to the link. Unless
        // the two are in one directory, no include line is read the same way
        // by both.
        let link_dir = super::overlay::normalize(given.parent().unwrap_or_else(|| Path::new(".")));
        if file.parent() != Some(link_dir.as_path()) {
            bail!(
                "{} is a symlink to a file in another directory; refusing to split it: \
                 beancount and fava would look for the new period files next to the link, \
                 rledger next to {}. Split that file instead if nothing opens the ledger \
                 through the link",
                given.display(),
                file.display()
            );
        }
    }
    let root = match &args.ledger {
        Some(r) => super::existing_file(r)?,
        None => file.clone(),
    };
    let (source, original) = super::read_source(&file)?;
    let seg = segment(&source, &file)?;
    if seg.dated_count() == 0 {
        bail!("{} has no dated directives to split", file.display());
    }

    let file_dir = file.parent().map(Path::to_path_buf).unwrap_or_default();
    let dir = match &args.dir {
        Some(d) => super::overlay::normalize(d),
        None => file_dir.join(file.file_stem().unwrap_or_default()),
    };
    if dir.is_file() {
        bail!("{} is a file, not a directory", dir.display());
    }
    let ext = file.extension().map_or_else(
        || "beancount".to_string(),
        |e| e.to_string_lossy().into_owned(),
    );

    let layout = plan(&seg, args.by, &source)?;
    let mut writes: Vec<(PathBuf, String)> = Vec::new();
    let mut include_lines: Vec<String> = Vec::new();
    for (key, (content, _)) in &layout.periods {
        let path = dir.join(format!("{key}.{ext}"));
        include_lines.push(super::include_line(&super::relative_include(
            &file_dir, &path,
        ))?);
        writes.push((path, content.clone()));
    }
    if let Some((clash, _)) = writes.iter().find(|(p, _)| *p == file) {
        bail!(
            "the period file {} would overwrite the file being split; choose another --dir",
            clash.display()
        );
    }
    let root_text = layout.root_text(&include_lines, super::newline_of(&source));
    writes.push((file.clone(), root_text));

    let swap_plan = swap::Plan {
        writes,
        commit: file.clone(),
        removes: Vec::new(),
        backup_base: file_dir,
        originals: vec![(file.clone(), original)],
        operation: "split",
        template: file.clone(),
        mode_mask: None,
    };
    // Targets that already exist are refused before the (slow) check runs.
    swap::preflight(&swap_plan)?;

    let before: Before = super::load_before(&root)?;
    if root != file && !before.files.contains(&file) {
        bail!(
            "{} is not part of the ledger rooted at {}",
            file.display(),
            root.display()
        );
    }

    writeln!(
        out,
        "Plan: split {} by {}",
        super::show(&file),
        args.by.name()
    )?;
    for ((path, _), (_, count)) in swap_plan.writes.iter().zip(layout.periods.values()) {
        writeln!(
            out,
            "  create   {}  ({count} dated directives)",
            super::show(path)
        )?;
    }
    writeln!(
        out,
        "  rewrite  {}  (keeps {} option/plugin/include lines; adds {} includes)",
        super::show(&file),
        layout.root_items,
        layout.periods.len()
    )?;

    let difference = match super::unstable(&root, &before)? {
        Some(reason) => Some(reason),
        None => super::check_planned(&root, &before, &swap_plan.writes, &[])?,
    };
    if !super::report_check(out, err, "split", &before, difference.as_deref())? {
        return Ok(ExitCode::from(1));
    }
    if args.dry_run {
        writeln!(out, "Dry run: nothing was written.")?;
        return Ok(ExitCode::SUCCESS);
    }
    super::write_plan(out, &root, &before, &swap_plan)?;
    Ok(ExitCode::SUCCESS)
}

/// Where each item of the source goes.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Home {
    Root,
    Period(String),
}

/// The planned layout: period file contents and the root's pieces.
pub(super) struct Layout<'a> {
    /// Period key -> (file content, number of dated directives).
    pub(super) periods: BTreeMap<String, (String, usize)>,
    seg: &'a Segmented,
    homes: Vec<Home>,
    root_items: usize,
}

impl Layout<'_> {
    /// The new root: header, every root-homed item in order with the period
    /// includes in front of the first existing `include`, and the trailer.
    pub(super) fn root_text(&self, include_lines: &[String], nl: &str) -> String {
        let mut block = String::new();
        for line in include_lines {
            block.push_str(line);
            block.push_str(nl);
        }
        let mut out = self.seg.leading.clone();
        let mut inserted = false;
        let insert = |out: &mut String| {
            if !out.is_empty() && !out.ends_with('\n') {
                out.push_str(nl);
            }
            if !out.is_empty() && !out.ends_with("\n\n") && !out.ends_with("\n\r\n") {
                out.push_str(nl);
            }
            out.push_str(&block);
        };
        for (item, home) in self.seg.items.iter().zip(&self.homes) {
            if *home != Home::Root {
                continue;
            }
            if matches!(item.kind, ItemKind::Include(_)) && !inserted {
                insert(&mut out);
                inserted = true;
            }
            super::push_block(&mut out, &item.text, nl);
        }
        if !inserted {
            insert(&mut out);
        }
        if !self.seg.trailing.is_empty() {
            super::push_block(&mut out, &self.seg.trailing, nl);
        }
        out
    }
}

/// Assign every item a home and render the period files.
pub(super) fn plan<'a>(seg: &'a Segmented, by: Period, source: &str) -> Result<Layout<'a>> {
    let nl = super::newline_of(source);
    let items = &seg.items;
    let dated_home = |i: usize| match items[i].kind {
        ItemKind::Dated(d) => Some(by.key(d)),
        _ => None,
    };
    // Nearest dated item after / before each index.
    let mut next: Vec<Option<String>> = vec![None; items.len() + 1];
    for i in (0..items.len()).rev() {
        next[i] = dated_home(i).or_else(|| next[i + 1].clone());
    }
    let mut prev: Vec<Option<String>> = Vec::with_capacity(items.len());
    let mut last: Option<String> = None;
    for i in 0..items.len() {
        prev.push(last.clone());
        if let Some(h) = dated_home(i) {
            last = Some(h);
        }
    }
    let homes: Vec<Home> = items
        .iter()
        .enumerate()
        .map(|(i, item)| match &item.kind {
            ItemKind::Dated(d) => Home::Period(by.key(*d)),
            ItemKind::Global | ItemKind::Include(_) => Home::Root,
            // A push introduces what follows it; a pop closes what precedes it.
            ItemKind::Push(_) => next[i + 1]
                .clone()
                .or_else(|| prev[i].clone())
                .map_or(Home::Root, Home::Period),
            ItemKind::Pop(_) => prev[i]
                .clone()
                .or_else(|| next[i + 1].clone())
                .map_or(Home::Root, Home::Period),
        })
        .collect();
    if homes
        .iter()
        .zip(items)
        .any(|(h, i)| *h == Home::Root && matches!(i.kind, ItemKind::Push(_) | ItemKind::Pop(_)))
    {
        bail!("internal error: a pushtag/pushmeta was planned into the root");
    }

    let mut periods: BTreeMap<String, (String, usize)> = BTreeMap::new();
    for h in &homes {
        if let Home::Period(k) = h {
            periods.entry(k.clone()).or_default();
        }
    }
    for (key, (content, count)) in &mut periods {
        let (text, n) = render_period(seg, &homes, key, nl);
        *content = text;
        *count = n;
    }
    let root_items = homes.iter().filter(|h| **h == Home::Root).count();
    Ok(Layout {
        periods,
        seg,
        homes,
        root_items,
    })
}

/// One stack entry: the index of the push item that opened it, and its key.
type Entry = (usize, StackKey);

/// Render the file for period `key`. Returns its text and how many dated
/// directives it holds.
fn render_period(seg: &Segmented, homes: &[Home], key: &str, nl: &str) -> (String, usize) {
    let mine = |h: &Home| matches!(h, Home::Period(k) if k == key);
    let mut out = String::new();
    let mut count = 0;
    // The stack the original file had at this point, and the one this file
    // has so far.
    let mut actual: Vec<Entry> = Vec::new();
    let mut emitted: Vec<Entry> = Vec::new();

    let sync = |out: &mut String, emitted: &mut Vec<Entry>, actual: &[Entry]| {
        let common = emitted
            .iter()
            .zip(actual)
            .take_while(|(a, b)| a.0 == b.0)
            .count();
        while emitted.len() > common {
            if let Some((_, k)) = emitted.pop() {
                super::push_block(out, &k.pop_line(), nl);
            }
        }
        for entry in &actual[common..] {
            super::push_block(out, &seg.items[entry.0].content, nl);
            emitted.push(entry.clone());
        }
    };
    let pop = |stack: &mut Vec<Entry>, k: &StackKey| {
        if let Some(pos) = stack.iter().rposition(|(_, e)| e == k) {
            stack.remove(pos);
        }
    };

    for (i, (item, home)) in seg.items.iter().zip(homes).enumerate() {
        match &item.kind {
            ItemKind::Dated(_) if mine(home) => {
                sync(&mut out, &mut emitted, &actual);
                super::push_block(&mut out, &item.text, nl);
                count += 1;
            }
            ItemKind::Push(k) => {
                if mine(home) {
                    sync(&mut out, &mut emitted, &actual);
                    super::push_block(&mut out, &item.text, nl);
                    emitted.push((i, k.clone()));
                }
                actual.push((i, k.clone()));
            }
            ItemKind::Pop(k) => {
                if mine(home) {
                    sync(&mut out, &mut emitted, &actual);
                    super::push_block(&mut out, &item.text, nl);
                    pop(&mut emitted, k);
                }
                pop(&mut actual, k);
            }
            _ => {}
        }
    }
    while let Some((_, k)) = emitted.pop() {
        super::push_block(&mut out, &k.pop_line(), nl);
    }
    (trim_leading_blank_lines(&out).to_string(), count)
}

/// Drop blank lines at the very top of a generated file: the first directive
/// in it was usually separated from its predecessor by one.
fn trim_leading_blank_lines(s: &str) -> &str {
    let mut rest = s;
    loop {
        let line_end = rest.find('\n').map_or(rest.len(), |i| i + 1);
        let line = &rest[..line_end];
        if line_end > 0 && line.trim().is_empty() && line.ends_with('\n') {
            rest = &rest[line_end..];
        } else {
            return rest;
        }
    }
}
