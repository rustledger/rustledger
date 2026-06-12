//! `rledger lint transfers` — detect and (optionally) link inter-account
//! transfer pairs across one or more beancount files.
//!
//! Default behavior is read-only: emit a report of detected pairs plus the
//! exact `^link:` lines that `--apply` would write. With `--apply`, the
//! tool edits the source files in place, appending a deterministic
//! `^xfer-YYYYMMDD-<hash>` link to both sides of each match. Re-running
//! `--apply` is a no-op because the detector skips pairs that already
//! share a link.

use anyhow::{Context, Result, anyhow};
use clap::{Parser, ValueEnum};
use rust_decimal::Decimal;
use rustledger_loader::Loader;
use rustledger_ops::transfer::{TransferConfig, TransferMatch, find_transfers_in_ledger};
use rustledger_plugin::convert::directive_to_wrapper_with_location;
use rustledger_plugin::types::DirectiveWrapper;
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::PathBuf;
use std::process::ExitCode;
use std::str::FromStr;

/// Output format for the report.
#[derive(Debug, Clone, Copy, Default, ValueEnum)]
pub enum OutputFormat {
    /// Human-readable text (default).
    #[default]
    Text,
    /// JSON: a single object with a `matches` array and an `applied` flag.
    Json,
}

/// Detect inter-account transfer pairs across imported beancount files.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// Beancount files to scan. At least one is required.
    #[arg(value_name = "FILE", required = true)]
    pub files: Vec<PathBuf>,

    /// Minimum confidence (0.0 - 1.0) for a match to be reported.
    ///
    /// Default 0.8 filters out the bare 0.7 floor (amount + date window only,
    /// no keyword and not same-date), which tends to be noisy. Pass 0.7 to
    /// see every match.
    #[arg(long, default_value_t = 0.8)]
    pub min_confidence: f64,

    /// Maximum number of days between matched transactions.
    #[arg(long, default_value_t = 3)]
    pub date_window: i64,

    /// Amount tolerance for matching (in the transaction currency).
    #[arg(long, default_value = "0.01")]
    pub amount_tolerance: String,

    /// Write `^xfer-YYYYMMDD-<hash>` links to source files instead of just
    /// previewing them.
    #[arg(long)]
    pub apply: bool,

    /// Output format.
    #[arg(long, short = 'f', value_enum, default_value_t = OutputFormat::Text)]
    pub format: OutputFormat,
}

/// Run the lint.
///
/// Exit code: `0` if no matches above the threshold, `0` if matches were
/// found and reported (this is a lint, not a check — finding matches is not
/// a failure). Returns a non-zero `ExitCode` only on hard errors (file not
/// found, parse failure, etc., propagated via `anyhow::Error`).
///
/// # Errors
/// - Fails if any input file does not exist or cannot be parsed.
/// - Fails if `--apply` is set and a file edit can't be written.
///
/// Thin wrapper over [`run_with_writer`] for the synchronous `rledger`
/// binary (writes its report to stdout); `ag-rledger` calls
/// `run_with_writer` with a buffer.
pub fn run(args: &Args) -> Result<ExitCode> {
    let mut stdout = std::io::stdout().lock();
    run_with_writer(args, &mut stdout)
}

/// Run the transfers lint, writing the text/JSON report to `out`.
///
/// Behavior matches the original `run()`; `--apply` still mutates source
/// files. Only the report sink is redirected to the injected writer.
pub fn run_with_writer<W: std::io::Write>(args: &Args, out: &mut W) -> Result<ExitCode> {
    let tolerance = Decimal::from_str(&args.amount_tolerance)
        .with_context(|| format!("invalid --amount-tolerance: {}", args.amount_tolerance))?;
    let config = TransferConfig {
        date_window_days: args.date_window,
        amount_tolerance: tolerance,
    };

    // Load every input file separately so we can attach the file's path to
    // each directive's `filename`/`lineno` before merging into one flat list.
    let mut wrappers: Vec<DirectiveWrapper> = Vec::new();
    for path in &args.files {
        let resolved = canonicalize_for_report(path)?;
        let mut loader = Loader::new();
        let result = loader
            .load(path)
            .with_context(|| format!("failed to load {}", path.display()))?;

        for spanned in &result.directives {
            let (filename, lineno) =
                if let Some(file) = result.source_map.get(spanned.file_id as usize) {
                    let (line, _col) = file.line_col(spanned.span.start);
                    (
                        Some(file.path.to_string_lossy().into_owned()),
                        u32::try_from(line).ok(),
                    )
                } else {
                    (Some(resolved.clone()), None)
                };
            wrappers.push(directive_to_wrapper_with_location(
                &spanned.value,
                filename,
                lineno,
            ));
        }
    }

    // Run detection. Phase 0's `find_transfers_in_ledger` groups by the
    // first posting's account and skips pairs that already share a link.
    let all_matches = find_transfers_in_ledger(&wrappers, &config);
    let matches: Vec<TransferMatch> = all_matches
        .into_iter()
        .filter(|m| m.confidence >= args.min_confidence)
        .collect();

    if args.apply {
        apply_links(&matches)?;
    }

    match args.format {
        OutputFormat::Text => print_text_report(&matches, args.apply, out)?,
        OutputFormat::Json => print_json_report(&matches, args.apply, out)?,
    }

    Ok(ExitCode::SUCCESS)
}

/// Canonicalize a path for stable display in the report. Falls back to the
/// raw path if canonicalization fails (e.g. file doesn't exist yet during
/// argument validation).
fn canonicalize_for_report(path: &std::path::Path) -> Result<String> {
    if let Ok(canon) = path.canonicalize() {
        Ok(canon.to_string_lossy().into_owned())
    } else {
        Ok(path.to_string_lossy().into_owned())
    }
}

// ─── Link-name generation ────────────────────────────────────────────────

/// Build a deterministic, idempotent link name for a match.
///
/// Form: `xfer-YYYYMMDD-<hash>` where `<hash>` is a 6-hex-char prefix of
/// `sha256(from_filename ++ from_lineno ++ to_filename ++ to_lineno ++
/// amount ++ currency)`. Same conceptual pair → same name across runs, so
/// re-applying is a no-op (the Phase 0 idempotency filter will then skip
/// it on the next detection).
fn link_name_for(m: &TransferMatch) -> String {
    let date_compact = m.date.replace('-', "");
    let mut h = Sha256::new();
    h.update(m.from_filename.as_deref().unwrap_or("").as_bytes());
    h.update(b"\0");
    h.update(m.from_lineno.unwrap_or(0).to_le_bytes());
    h.update(b"\0");
    h.update(m.to_filename.as_deref().unwrap_or("").as_bytes());
    h.update(b"\0");
    h.update(m.to_lineno.unwrap_or(0).to_le_bytes());
    h.update(b"\0");
    h.update(m.amount.to_string().as_bytes());
    h.update(b"\0");
    h.update(m.currency.as_bytes());
    let digest = h.finalize();
    let mut suffix = String::with_capacity(6);
    for b in digest.iter().take(3) {
        write!(suffix, "{b:02x}").expect("writing to String never fails");
    }
    format!("xfer-{date_compact}-{suffix}")
}

// ─── File mutation (`--apply`) ───────────────────────────────────────────

/// Apply detected links to source files in place. Each match adds the same
/// `^xfer-…` link to both the from-side and to-side transaction header
/// lines. Multiple edits per file are batched into a single read/write
/// cycle.
fn apply_links(matches: &[TransferMatch]) -> Result<()> {
    // Group edits by filename: `filename -> {lineno -> link_name}`.
    // BTreeMap on the outer key for stable iteration order in tests.
    let mut edits: BTreeMap<String, BTreeMap<u32, String>> = BTreeMap::new();
    for m in matches {
        let name = link_name_for(m);
        for (file, line) in [
            (m.from_filename.as_deref(), m.from_lineno),
            (m.to_filename.as_deref(), m.to_lineno),
        ] {
            let (Some(file), Some(line)) = (file, line) else {
                continue;
            };
            edits
                .entry(file.to_string())
                .or_default()
                .insert(line, name.clone());
        }
    }

    for (file, line_edits) in edits {
        apply_file_edits(&file, &line_edits)?;
    }
    Ok(())
}

fn apply_file_edits(path: &str, edits: &BTreeMap<u32, String>) -> Result<()> {
    let original = std::fs::read_to_string(path)
        .with_context(|| format!("failed to read {path} for --apply"))?;

    // Split into lines preserving trailing newline state — we keep the
    // original line terminators when writing back.
    let mut lines: Vec<String> = original.split_inclusive('\n').map(String::from).collect();

    for (&lineno, link_name) in edits {
        let idx = lineno
            .checked_sub(1)
            .ok_or_else(|| anyhow!("invalid 0 lineno in {path}"))? as usize;
        let Some(line) = lines.get_mut(idx) else {
            return Err(anyhow!(
                "line {lineno} out of range in {path} ({} total)",
                lines.len()
            ));
        };
        *line = insert_link_into_header(line, link_name);
    }

    let new = lines.concat();
    if new != original {
        std::fs::write(path, new).with_context(|| format!("failed to write {path}"))?;
    }
    Ok(())
}

/// Append ` ^link_name` to a transaction header line, preserving the
/// original trailing newline. If the line already contains `^link_name`,
/// the line is returned unchanged (defensive; the Phase 0 detector should
/// already filter these out).
fn insert_link_into_header(line: &str, link_name: &str) -> String {
    let needle = format!("^{link_name}");
    let (body, term) = split_terminator(line);
    if body.split_whitespace().any(|tok| tok == needle) {
        return line.to_string();
    }
    let trimmed = body.trim_end_matches([' ', '\t']);
    format!("{trimmed} {needle}{term}")
}

/// Split a line into its body and its trailing newline (`\n`, `\r\n`, or
/// none).
fn split_terminator(line: &str) -> (&str, &str) {
    if let Some(body) = line.strip_suffix("\r\n") {
        (body, "\r\n")
    } else if let Some(body) = line.strip_suffix('\n') {
        (body, "\n")
    } else {
        (line, "")
    }
}

// ─── Reporting ───────────────────────────────────────────────────────────

#[derive(Serialize)]
struct JsonMatch<'a> {
    confidence: f64,
    date: &'a str,
    amount: String,
    currency: &'a str,
    from: JsonSide<'a>,
    to: JsonSide<'a>,
    link_name: String,
}

#[derive(Serialize)]
struct JsonSide<'a> {
    account: Option<&'a str>,
    filename: Option<&'a str>,
    lineno: Option<u32>,
}

#[derive(Serialize)]
struct JsonReport<'a> {
    matches: Vec<JsonMatch<'a>>,
    applied: bool,
}

fn print_json_report<W: std::io::Write>(
    matches: &[TransferMatch],
    applied: bool,
    out: &mut W,
) -> Result<()> {
    let report = JsonReport {
        matches: matches
            .iter()
            .map(|m| JsonMatch {
                confidence: round_to(m.confidence, 3),
                date: &m.date,
                amount: m.amount.to_string(),
                currency: &m.currency,
                from: JsonSide {
                    account: m.from_account.as_deref(),
                    filename: m.from_filename.as_deref(),
                    lineno: m.from_lineno,
                },
                to: JsonSide {
                    account: m.to_account.as_deref(),
                    filename: m.to_filename.as_deref(),
                    lineno: m.to_lineno,
                },
                link_name: link_name_for(m),
            })
            .collect(),
        applied,
    };
    serde_json::to_writer_pretty(&mut *out, &report).context("write JSON report")?;
    writeln!(out).ok();
    Ok(())
}

fn print_text_report<W: std::io::Write>(
    matches: &[TransferMatch],
    applied: bool,
    out: &mut W,
) -> Result<()> {
    if matches.is_empty() {
        writeln!(out, "No transfer pairs detected.").ok();
        return Ok(());
    }

    writeln!(
        out,
        "{} likely transfer{} detected:\n",
        matches.len(),
        if matches.len() == 1 { "" } else { "s" }
    )
    .ok();

    for m in matches {
        let link = link_name_for(m);
        let from_acct = m.from_account.as_deref().unwrap_or("?");
        let to_acct = m.to_account.as_deref().unwrap_or("?");
        writeln!(
            out,
            "  {} {} {} → {}    confidence {:.2}",
            m.amount, m.currency, from_acct, to_acct, m.confidence
        )
        .ok();
        writeln!(
            out,
            "    from: {}:{}  {}",
            m.from_filename.as_deref().unwrap_or("?"),
            m.from_lineno.map_or_else(|| "?".into(), |n| n.to_string()),
            m.date,
        )
        .ok();
        writeln!(
            out,
            "    to:   {}:{}",
            m.to_filename.as_deref().unwrap_or("?"),
            m.to_lineno.map_or_else(|| "?".into(), |n| n.to_string()),
        )
        .ok();
        writeln!(
            out,
            "    {} ^{link}",
            if applied { "applied:" } else { "would add:" }
        )
        .ok();
        writeln!(out).ok();
    }

    if !applied {
        writeln!(out, "Run with --apply to write these links.").ok();
    }
    Ok(())
}

fn round_to(x: f64, places: u32) -> f64 {
    let mult = 10f64.powi(places as i32);
    (x * mult).round() / mult
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_plugin::types::{AmountData, DirectiveData, PostingData, TransactionData};

    fn match_with(
        date: &str,
        from_file: &str,
        from_line: u32,
        to_file: &str,
        to_line: u32,
    ) -> TransferMatch {
        TransferMatch {
            from_group: 0,
            from_index: 0,
            from_account: Some("Assets:Checking".into()),
            from_filename: Some(from_file.into()),
            from_lineno: Some(from_line),
            to_group: 1,
            to_index: 0,
            to_account: Some("Assets:Savings".into()),
            to_filename: Some(to_file.into()),
            to_lineno: Some(to_line),
            amount: Decimal::new(50000, 2),
            currency: "USD".into(),
            confidence: 0.95,
            date: date.into(),
        }
    }

    #[test]
    fn link_name_is_deterministic() {
        let m = match_with("2024-01-15", "a.bean", 10, "b.bean", 20);
        let n1 = link_name_for(&m);
        let n2 = link_name_for(&m);
        assert_eq!(n1, n2, "same match must produce same link name");
        assert!(n1.starts_with("xfer-20240115-"));
        assert_eq!(n1.len(), "xfer-YYYYMMDD-XXXXXX".len());
    }

    #[test]
    fn link_name_differs_for_different_pairs() {
        let m1 = match_with("2024-01-15", "a.bean", 10, "b.bean", 20);
        let m2 = match_with("2024-01-15", "a.bean", 11, "b.bean", 20);
        assert_ne!(link_name_for(&m1), link_name_for(&m2));
    }

    #[test]
    fn insert_link_appends_to_header_preserving_newline() {
        let line = "2024-01-15 * \"Transfer\"\n";
        let out = insert_link_into_header(line, "xfer-20240115-abcdef");
        assert_eq!(out, "2024-01-15 * \"Transfer\" ^xfer-20240115-abcdef\n");
    }

    #[test]
    fn insert_link_handles_crlf() {
        let line = "2024-01-15 * \"Transfer\"\r\n";
        let out = insert_link_into_header(line, "xfer-20240115-abcdef");
        assert_eq!(out, "2024-01-15 * \"Transfer\" ^xfer-20240115-abcdef\r\n");
    }

    #[test]
    fn insert_link_strips_trailing_whitespace_before_appending() {
        let line = "2024-01-15 * \"Transfer\"   \n";
        let out = insert_link_into_header(line, "xfer-20240115-abcdef");
        assert_eq!(out, "2024-01-15 * \"Transfer\" ^xfer-20240115-abcdef\n");
    }

    #[test]
    fn insert_link_is_idempotent_when_already_present() {
        let line = "2024-01-15 * \"Transfer\" ^xfer-20240115-abcdef\n";
        let out = insert_link_into_header(line, "xfer-20240115-abcdef");
        assert_eq!(out, line, "already-present link must not be duplicated");
    }

    #[test]
    fn insert_link_adds_alongside_existing_unrelated_link() {
        let line = "2024-01-15 * \"Transfer\" ^batch-import-A\n";
        let out = insert_link_into_header(line, "xfer-20240115-abcdef");
        assert_eq!(
            out,
            "2024-01-15 * \"Transfer\" ^batch-import-A ^xfer-20240115-abcdef\n"
        );
    }

    #[test]
    fn insert_link_handles_no_terminator() {
        let line = "2024-01-15 * \"Transfer\"";
        let out = insert_link_into_header(line, "xfer-20240115-abcdef");
        assert_eq!(out, "2024-01-15 * \"Transfer\" ^xfer-20240115-abcdef");
    }

    /// Integration test: write two beancount files representing a transfer
    /// pair, run the lint end-to-end with `--apply`, and verify the files
    /// now contain matching `^xfer-…` links and that re-running is a no-op.
    #[test]
    fn end_to_end_apply_writes_and_is_idempotent() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let checking = dir.path().join("checking.bean");
        let savings = dir.path().join("savings.bean");
        std::fs::write(
            &checking,
            "2024-01-01 open Assets:Checking USD\n\
             \n\
             2024-01-15 * \"Transfer to savings\"\n  \
             Assets:Checking  -500.00 USD\n  \
             Assets:Savings    500.00 USD\n",
        )?;
        std::fs::write(
            &savings,
            "2024-01-01 open Assets:Savings USD\n\
             \n\
             2024-01-15 * \"Transfer from checking\"\n  \
             Assets:Savings    500.00 USD\n  \
             Assets:Checking  -500.00 USD\n",
        )?;

        let args = Args {
            files: vec![checking.clone(), savings.clone()],
            min_confidence: 0.8,
            date_window: 3,
            amount_tolerance: "0.01".to_string(),
            apply: true,
            format: OutputFormat::Json,
        };

        // First run: should apply links.
        let _ = run(&args)?;
        let after_checking = std::fs::read_to_string(&checking)?;
        let after_savings = std::fs::read_to_string(&savings)?;
        assert!(
            after_checking.contains("^xfer-20240115-"),
            "checking file should have a link: {after_checking}"
        );
        assert!(
            after_savings.contains("^xfer-20240115-"),
            "savings file should have a link: {after_savings}"
        );

        // Second run: idempotent — files unchanged.
        let _ = run(&args)?;
        let final_checking = std::fs::read_to_string(&checking)?;
        let final_savings = std::fs::read_to_string(&savings)?;
        assert_eq!(
            after_checking, final_checking,
            "second --apply run must not modify the checking file"
        );
        assert_eq!(
            after_savings, final_savings,
            "second --apply run must not modify the savings file"
        );

        Ok(())
    }

    /// Verify --min-confidence actually filters.
    #[test]
    fn min_confidence_filters_low_confidence_matches() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let a = dir.path().join("a.bean");
        let b = dir.path().join("b.bean");
        // No keyword, dates 2 days apart → confidence 0.7 (base only).
        std::fs::write(
            &a,
            "2024-01-01 open Assets:A USD\n\
             2024-01-15 * \"Something\"\n  \
             Assets:A  -100.00 USD\n  \
             Assets:Other  100.00 USD\n",
        )?;
        std::fs::write(
            &b,
            "2024-01-01 open Assets:B USD\n\
             2024-01-17 * \"Something else\"\n  \
             Assets:B   100.00 USD\n  \
             Assets:Other  -100.00 USD\n",
        )?;

        // At default 0.8, no match should be reported.
        let args = Args {
            files: vec![a.clone(), b],
            min_confidence: 0.8,
            date_window: 3,
            amount_tolerance: "0.01".to_string(),
            apply: false,
            format: OutputFormat::Json,
        };
        // run() returns ExitCode::SUCCESS regardless; we instead verify that
        // re-running with --apply doesn't add any links (because filtered).
        let apply_args = Args {
            apply: true,
            ..clone_args(&args)
        };
        let _ = run(&apply_args)?;
        let after_a = std::fs::read_to_string(&a)?;
        assert!(
            !after_a.contains("^xfer-"),
            "0.7-confidence match must be filtered by default min_confidence 0.8; got {after_a}"
        );

        // At 0.7, the same match should now be applied.
        let permissive = Args {
            min_confidence: 0.7,
            apply: true,
            ..clone_args(&args)
        };
        let _ = run(&permissive)?;
        let after_a2 = std::fs::read_to_string(&a)?;
        assert!(
            after_a2.contains("^xfer-"),
            "with min_confidence 0.7 the 0.7-confidence match should be applied; got {after_a2}"
        );
        Ok(())
    }

    fn clone_args(a: &Args) -> Args {
        Args {
            files: a.files.clone(),
            min_confidence: a.min_confidence,
            date_window: a.date_window,
            amount_tolerance: a.amount_tolerance.clone(),
            apply: a.apply,
            format: a.format,
        }
    }

    #[test]
    fn no_match_within_same_account() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let f = dir.path().join("single.bean");
        // Two transactions on the same account — algorithm shouldn't pair them.
        std::fs::write(
            &f,
            "2024-01-01 open Assets:Single USD\n\
             2024-01-15 * \"Out\"\n  \
             Assets:Single  -500.00 USD\n  \
             Equity:Misc  500.00 USD\n\
             2024-01-15 * \"In\"\n  \
             Assets:Single   500.00 USD\n  \
             Equity:Misc  -500.00 USD\n",
        )?;
        let args = Args {
            files: vec![f.clone()],
            min_confidence: 0.7, // permissive so we'd see the match if it existed
            date_window: 3,
            amount_tolerance: "0.01".to_string(),
            apply: true,
            format: OutputFormat::Json,
        };
        let _ = run(&args)?;
        let after = std::fs::read_to_string(&f)?;
        assert!(
            !after.contains("^xfer-"),
            "same-account transactions must not be paired"
        );
        Ok(())
    }

    // Silence unused import warning when not building this module.
    #[allow(dead_code)]
    fn _unused_imports() {
        let _: DirectiveData;
        let _: TransactionData;
        let _: PostingData;
        let _: AmountData;
    }
}
