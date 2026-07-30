//! `rledger format` — opinionated whole-file formatter.
//!
//! Routes every input file through the canonical CST-backed formatter
//! ([`rustledger_parser::format::format_source`]). One canonical form per AST
//! shape, no knobs: see the canonical-form spec in the formatter's
//! rustdoc and in the PR-4 decision comment on #1262.

use crate::cmd::completions::ShellType;
use anyhow::{Context, Result};
use clap::Parser;
use rustledger_parser::format::{
    GroupingStyle, cr_outside_strings_present, try_format_source_grouped,
};
use std::collections::HashMap;
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

/// Format beancount files in the canonical opinionated form.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// The beancount file(s) to format (uses config default if not specified)
    #[arg(value_name = "FILE")]
    pub files: Vec<PathBuf>,

    /// Generate shell completions and exit
    #[arg(long, value_name = "SHELL", hide = true)]
    pub generate_completions: Option<ShellType>,

    /// Output file (only valid with single input file, default: stdout)
    #[arg(short = 'o', long, value_name = "OUTPUT")]
    pub output: Option<PathBuf>,

    /// Format file(s) in place
    #[arg(short = 'i', long)]
    pub in_place: bool,

    /// Check if file is formatted (exit 1 if not)
    #[arg(long)]
    pub check: bool,

    /// Show diff when using --check
    #[arg(long, requires = "check")]
    pub diff: bool,

    /// Ledger root to read display declarations from (`option
    /// "render_commas"`, per-commodity `render_commas:`).
    ///
    /// `format` is otherwise a per-file text transform: it never loads a
    /// ledger, so it cannot see declarations that live in the root while the
    /// postings live in an `include`d file. Naming the root explicitly is
    /// deterministic regardless of which files are listed or in what order —
    /// which matters because pre-commit hooks pass whichever files changed.
    ///
    /// This locates the declarations; it does not choose a style. Without it,
    /// output is byte-identical to a ledger that declares nothing.
    #[arg(long, value_name = "ROOT", conflicts_with = "no_ledger")]
    pub ledger: Option<PathBuf>,

    /// Do not look for a ledger root; format as a standalone text transform.
    ///
    /// Without this, `format` finds the nearest root journal at or above each
    /// file and honors its declarations, matching what the editor does on
    /// save. Pass this where output must depend only on the file's own bytes —
    /// a hook that must behave identically whatever surrounds a checkout.
    #[arg(long)]
    pub no_ledger: bool,

    /// Show verbose output
    #[arg(short, long)]
    pub verbose: bool,
}

/// Run the format command with the given arguments, writing formatted
/// output to stdout.
///
/// Thin wrapper over [`run_with_writer`] for the synchronous `rledger`
/// binary; `ag-rledger` calls `run_with_writer` with a buffer.
pub fn run(args: &Args) -> Result<ExitCode> {
    let mut stdout = io::stdout().lock();
    run_with_writer(args, &mut stdout)
}

/// Run the format command, writing any stdout-bound formatted output to
/// `out`.
///
/// Only the default "print formatted file to stdout" path is redirected
/// to `out`; `--in-place` and `--output <file>` still write to disk, and
/// `--check`/`--diff`/verbose notes still go to stderr, exactly as in the
/// original `run()`.
pub fn run_with_writer<W: Write>(args: &Args, out: &mut W) -> Result<ExitCode> {
    if args.files.is_empty() {
        anyhow::bail!("FILE is required (or set default.file in config)");
    }

    if args.output.is_some() && args.files.len() > 1 {
        anyhow::bail!(
            "--output can only be used with a single input file. Use --in-place for multiple files."
        );
    }

    if args.output.is_some() && args.in_place {
        anyhow::bail!("--output and --in-place cannot be used together");
    }

    // Which ledger's declarations govern each file. Resolved before any
    // loading so the roots can be de-duplicated: formatting twenty files of
    // one ledger loads it once.
    let roots: Vec<Option<PathBuf>> = args
        .files
        .iter()
        .map(|file| resolve_root(file, args))
        .collect();

    let explicit = args.ledger.is_some();
    let mut ledgers: HashMap<PathBuf, Option<Ledger>> = HashMap::new();
    for root in roots.iter().flatten() {
        if !ledgers.contains_key(root) {
            let ledger = load_ledger_declarations(root, explicit, args.verbose)?;
            ledgers.insert(root.clone(), ledger);
        }
    }

    let mut any_needs_formatting = false;

    for (file, root) in args.files.iter().zip(&roots) {
        let ledger = root
            .as_ref()
            .and_then(|r| ledgers.get(r))
            .and_then(Option::as_ref);
        let style = ledger
            .filter(|l| l.governs(file))
            .map_or_else(GroupingStyle::default, |l| {
                GroupingStyle::from_context(&l.display_context)
            });
        let result = format_file(file, args, style, out)?;
        if result == ExitCode::from(1) {
            any_needs_formatting = true;
        }
    }

    if args.check && any_needs_formatting {
        Ok(ExitCode::from(1))
    } else {
        Ok(ExitCode::SUCCESS)
    }
}

/// A ledger root's display declarations, plus which files it actually spans.
struct Ledger {
    display_context: rustledger_core::DisplayContext,
    /// Canonicalized paths of the root and everything it includes.
    files: std::collections::HashSet<PathBuf>,
    /// Whether the user named this root explicitly.
    explicit: bool,
}

impl Ledger {
    /// Whether this ledger's declarations govern `file`.
    ///
    /// An explicitly named root always governs: the user pointed at it, and
    /// obeying that is not our call to second-guess even for a file the ledger
    /// does not include.
    ///
    /// A DISCOVERED root has to earn it. Discovery is a guess made from
    /// directory layout, so it is confirmed against the files the ledger really
    /// spans. Without that check, a stray `.beancount` sitting beside someone's
    /// journal — a scratch file, a vendor export, a fixture — would be
    /// reformatted to a ledger that has never heard of it.
    fn governs(&self, file: &Path) -> bool {
        if self.explicit {
            return true;
        }
        canonical(file).is_some_and(|c| self.files.contains(&c))
    }
}

/// Canonicalize for comparison, matching how the ledger's own files were
/// recorded. Falls back to the path as given when the file cannot be resolved.
fn canonical(path: &Path) -> Option<PathBuf> {
    path.canonicalize()
        .ok()
        .or_else(|| Some(path.to_path_buf()))
}

/// Which ledger root, if any, should supply `file`'s display declarations.
///
/// `--ledger` wins outright; `--no-ledger` disables the search. Otherwise the
/// nearest root journal at or above the file, which is the same rule the
/// language server uses — so a file formats the same on save as it does in a
/// pre-commit hook.
fn resolve_root(file: &Path, args: &Args) -> Option<PathBuf> {
    if args.no_ledger {
        return None;
    }
    if let Some(explicit) = &args.ledger {
        return Some(explicit.clone());
    }
    let dir = file.parent().filter(|p| !p.as_os_str().is_empty());
    let start = match dir {
        Some(d) => d.to_path_buf(),
        None => std::env::current_dir().ok()?,
    };
    rustledger_loader::discover_journal_upward(&start)
}

/// Load `root` purely to obtain its resolved display declarations.
///
/// Takes the RAW load and stops there — no booking, no plugins. `process`
/// forwards `display_context` from the raw result untouched, so the extra work
/// cannot change the answer, and skipping it means a ledger that fails to book
/// still formats. That is the point: `format` must keep working on a ledger
/// that does not yet `check` clean, which is often exactly when you reach for
/// it. A missing `include`, an unbalanced transaction or a failed assertion all
/// still yield a usable display context.
///
/// Goes through the shared cached loader for the same reason every other
/// command does — a pre-commit hook invoking `format` should not re-parse the
/// whole ledger on each run.
///
/// A root that cannot be READ fails only when the user NAMED it: they pointed
/// at a file to take declarations from, so silently substituting defaults would
/// format their ledger the wrong way and say nothing. A DISCOVERED root that
/// will not load is not an error — nobody asked for it — so it degrades to no
/// declarations, exactly as if none had been found.
fn load_ledger_declarations(root: &Path, explicit: bool, verbose: bool) -> Result<Option<Ledger>> {
    match crate::cmd::loadcache::load_result_cached(root, false, verbose) {
        Ok((raw, _from_cache)) => {
            let files = raw
                .source_map
                .files()
                .iter()
                .filter_map(|f| canonical(&f.path))
                .collect();
            Ok(Some(Ledger {
                display_context: raw.display_context,
                files,
                explicit,
            }))
        }
        Err(e) if explicit => {
            Err(e.context(format!("failed to read ledger root {}", root.display())))
        }
        Err(e) => {
            if verbose {
                eprintln!(
                    "note: ignoring discovered ledger {} ({e}); formatting without declarations",
                    root.display()
                );
            }
            Ok(None)
        }
    }
}

fn format_file<W: Write>(
    file: &PathBuf,
    args: &Args,
    style: GroupingStyle<'_>,
    out: &mut W,
) -> Result<ExitCode> {
    if !file.exists() {
        anyhow::bail!("file not found: {}", file.display());
    }

    // Read tolerantly to match the loader/cache (rustledger-loader `vfs.rs`,
    // `cache.rs`), which decode with `from_utf8_lossy`. Otherwise a ledger that
    // `rledger check` accepts — e.g. one with stray invalid-UTF-8 bytes, which
    // beancount also accepts — would fail to `format` with a hard read error.
    let bytes = fs::read(file).with_context(|| format!("failed to read {}", file.display()))?;
    // Track whether the input was valid UTF-8. If not, `from_utf8_lossy`
    // replaced bytes with U+FFFD, so writing the formatted output would rewrite
    // the file even if the formatted text equals the lossy-decoded original —
    // `--check` must report that as "needs formatting" (see below).
    let had_invalid_utf8 = std::str::from_utf8(&bytes).is_err();
    let original_content = String::from_utf8_lossy(&bytes).into_owned();

    let formatted = match try_format_source_grouped(&original_content, style) {
        Ok(out) => out,
        Err(errors) => {
            for err in &errors {
                eprintln!("error: {err}");
            }
            anyhow::bail!("file has parse errors, cannot format");
        }
    };

    if args.check {
        // Byte-exact comparison: --check must report the same diff
        // --in-place would actually write. A trim-based comparison
        // masks trailing-blank-line / leading-blank-line differences
        // that the canonical form rewrites — exactly the kind of
        // change the new formatter introduces (one trailing newline,
        // exactly one blank between directives).
        // Invalid UTF-8 always counts as "needs formatting": `--in-place`
        // would rewrite the offending bytes to U+FFFD, so reporting "already
        // formatted" here would let CI miss a real rewrite.
        if formatted == original_content && !had_invalid_utf8 {
            if args.verbose {
                eprintln!("File is already formatted: {}", file.display());
            }
            Ok(ExitCode::SUCCESS)
        } else {
            if args.verbose {
                eprintln!("File needs formatting: {}", file.display());
            }
            if args.diff {
                emit_diff(file, &original_content, &formatted);
            }
            Ok(ExitCode::from(1))
        }
    } else if args.in_place {
        fs::write(file, &formatted)
            .with_context(|| format!("failed to write {}", file.display()))?;
        if args.verbose {
            eprintln!("Formatted: {}", file.display());
        }
        Ok(ExitCode::SUCCESS)
    } else if let Some(ref output_path) = args.output {
        fs::write(output_path, &formatted)
            .with_context(|| format!("failed to write {}", output_path.display()))?;
        if args.verbose {
            eprintln!("Formatted {} -> {}", file.display(), output_path.display());
        }
        Ok(ExitCode::SUCCESS)
    } else {
        out.write_all(formatted.as_bytes())
            .context("failed to write to stdout")?;
        Ok(ExitCode::SUCCESS)
    }
}

/// Render a `--diff` block for a non-canonical file.
///
/// Handles four cases beyond the obvious per-line replacement:
///
/// - **Whitespace-only normalization.** The canonical form strips
///   the leading BOM, folds CR-bearing line endings to LF outside
///   strings, and emits exactly one trailing LF. If the file's
///   delta is fully explained by one or more of those passes, we
///   surface the cause explicitly instead of producing a per-line
///   diff that just shows BOMs and `\r`s.
/// - **Line-by-line replacements.** Otherwise emit `@@ line N @@`
///   per-line diff hunks.
fn emit_diff(file: &PathBuf, original: &str, formatted: &str) {
    eprintln!("--- {}", file.display());
    eprintln!("+++ {} (formatted)", file.display());

    // Compute the canonical-noise-stripped view of the original:
    // drop the BOM, normalize CR-bearing line endings to LF outside
    // strings, then trim_end_matches('\n'). The formatted side
    // gets the same trim. If the bodies match, the file's delta is
    // entirely explainable by canonical normalization; surface the
    // specific cause so the user knows what to expect from
    // `--in-place`.
    let original_no_bom = original.strip_prefix('\u{FEFF}').unwrap_or(original);
    let had_bom = original_no_bom.len() < original.len();
    let folded_cr = cr_outside_strings_present(original_no_bom);
    let lf_only: std::borrow::Cow<'_, str> = if folded_cr {
        rustledger_parser::format::crlf_to_lf_outside_strings(original_no_bom)
    } else {
        std::borrow::Cow::Borrowed(original_no_bom)
    };

    let orig_body = lf_only.trim_end_matches('\n');
    let fmt_body = formatted.trim_end_matches('\n');
    if orig_body == fmt_body {
        let mut causes: Vec<&'static str> = Vec::new();
        if had_bom {
            causes.push("leading BOM (dropped)");
        }
        // `folded_cr` comes from the explicit
        // `cr_outside_strings_present` predicate: a file whose
        // only `\r` is inside a string literal returns false (the
        // formatter doesn't fold those), so we don't surface a
        // misleading "CR folded" cause for an in-string `\r`.
        if folded_cr {
            causes.push("CR-bearing line endings (folded to LF)");
        }
        let orig_trailing = lf_only.len() - orig_body.len();
        let fmt_trailing = formatted.len() - fmt_body.len();
        match orig_trailing.cmp(&fmt_trailing) {
            std::cmp::Ordering::Less => causes.push("missing final newline (added)"),
            std::cmp::Ordering::Greater => causes.push("extra trailing newlines (collapsed)"),
            std::cmp::Ordering::Equal => {}
        }
        if causes.is_empty() {
            // Bodies equal AND no whitespace-noise cause — this
            // can only happen on byte-identical input, which the
            // caller already gates against. Defensive message in
            // case a future caller invokes emit_diff regardless.
            eprintln!(
                "  (no per-line content change; the difference is in \
                 leading/trailing whitespace that `.lines()` strips)"
            );
        } else {
            eprintln!(
                "  (no per-line content change; canonical normalization: {} — \
                 run `rledger format -i` to rewrite)",
                causes.join(", "),
            );
        }
        return;
    }

    let orig_lines: Vec<&str> = original.lines().collect();
    let fmt_lines: Vec<&str> = formatted.lines().collect();
    for (i, (orig, fmt)) in orig_lines.iter().zip(fmt_lines.iter()).enumerate() {
        if orig != fmt {
            eprintln!("@@ line {} @@", i + 1);
            eprintln!("-{orig}");
            eprintln!("+{fmt}");
        }
    }
    if orig_lines.len() != fmt_lines.len() {
        let min_len = orig_lines.len().min(fmt_lines.len());
        for (i, line) in orig_lines.iter().skip(min_len).enumerate() {
            eprintln!("@@ line {} (removed) @@", min_len + i + 1);
            eprintln!("-{line}");
        }
        for (i, line) in fmt_lines.iter().skip(min_len).enumerate() {
            eprintln!("@@ line {} (added) @@", min_len + i + 1);
            eprintln!("+{line}");
        }
    }
}
