//! How a lint loads its inputs: the one place every `rledger lint`
//! subcommand gets its ledger from, so that no lint re-derives which load
//! and processing errors it may answer over.
//!
//! A lint reads its input at one of three levels:
//!
//! - [`load_booked`]: the ledger as `rledger check` sees it, booked, with
//!   plugins and validation run. A file with load errors is refused, and so
//!   is a ledger whose booking or plugins failed
//!   ([`LedgerError::is_booking_failure`], [`LedgerError::is_plugin_failure`]):
//!   either drops or alters transactions, so an answer over it could be
//!   wrong, and a clean "nothing found" would be the most misleading answer
//!   of all. The other processing errors are left in [`Ledger::errors`] for
//!   the lint to treat as it can (`linked-transit` makes a link `ambiguous`
//!   or passes the error on as a warning; `closed-nonempty` reads its
//!   advisory out of them). Used by `linked-transit` and `closed-nonempty`.
//! - [`load_clean`]: the parsed source, refused if it has load errors. Used
//!   by `transfers --apply`, which rewrites the source files and must not
//!   do so from a parse it cannot trust.
//! - [`load_source`]: the parsed source, load errors and all, for a lint
//!   that can still answer over what parsed. Such a lint must say that the
//!   input had load errors ([`warn_load_errors`]), so that it never prints a
//!   clean "no findings" over a file it only partly read. Used by
//!   `control-chars` (a control character is often what broke the parse, and
//!   the parser recovers enough to find it) and read-only `transfers`.
//!
//! [`load_clean`] and [`load_booked`] refuse every load error, including
//! those the loader counts as harmless to the ledger's contents
//! ([`LoadError::leaves_ledger_complete`]: a duplicate include, an include
//! cycle, an include glob that matches nothing), as `bean-check` reports
//! each of them as an error.
//!
//! The refusals are `Err`s: `rledger lint` reports them as `error: ...` and
//! exits with [`super::ERROR_EXIT_CODE`], 2 for every lint.
//!
//! A lint over the booked ledger that reports per transaction places each
//! remaining error on the transaction it sits on with an [`ErrorIndex`], and
//! identifies each transaction by its [`TransactionSite`]: where it is, and
//! whether a plugin inserted it somewhere that does not tell it apart from
//! another.

use anyhow::{Context, Result};
use rustledger_core::{Directive, Spanned};
use rustledger_loader::{
    ErrorSeverity, Ledger, LedgerError, LoadError, LoadOptions, LoadResult, Loader, SourceMap,
};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::{Path, PathBuf};

use crate::cmd::messages::Messages;

/// The code of the warning [`warn_load_errors`] emits, as carried in
/// `ag-rledger`'s `warnings`.
pub const LOAD_ERRORS: &str = "LOAD_ERRORS";

/// How many load errors a refusal or warning lists before it says how many
/// more there are.
const LISTED_LOAD_ERRORS: usize = 10;

/// The processing `rledger check` runs: plugins (within the configured
/// budget) and validation.
fn check_options() -> LoadOptions {
    LoadOptions {
        run_plugins: true,
        validate: true,
        plugin_max_time_secs: crate::plugin_budget::max_time_secs(),
        plugin_max_memory_mb: crate::plugin_budget::max_memory_mb(),
        ..Default::default()
    }
}

/// `file:line: CODE: message`.
pub fn describe_error(err: &LedgerError) -> String {
    let at = err
        .location
        .as_ref()
        .map(|l| format!("{}:{}: ", l.file.display(), l.line))
        .unwrap_or_default();
    format!("{at}{}: {}", err.code, err.message)
}

/// [`describe_error`] for each error, joined for one message.
pub fn describe_errors<'a>(errors: impl Iterator<Item = &'a LedgerError>) -> String {
    errors.map(describe_error).collect::<Vec<_>>().join("; ")
}

/// Each load error, joined for one message, at most
/// [`LISTED_LOAD_ERRORS`] of them and then how many more there are.
///
/// A file's parse errors are listed one by one, each as
/// `file:line: Pnnnn: message`, rather than as the loader's one-line
/// `parse errors in <file>`, so the message says where to look. The other
/// load errors already name their file.
fn describe_load_errors(result: &LoadResult) -> String {
    let mut listed = Vec::new();
    for error in &result.errors {
        match error {
            LoadError::ParseErrors { path, errors } => {
                let source = find_source(&result.source_map, path);
                for parse_error in errors {
                    let at = source.map_or_else(
                        || path.display().to_string(),
                        |file| {
                            let (line, _) = file.line_col(parse_error.span.start);
                            format!("{}:{line}", path.display())
                        },
                    );
                    listed.push(format!(
                        "{at}: P{:04}: {}",
                        parse_error.kind_code(),
                        parse_error.message()
                    ));
                }
            }
            other => listed.push(other.to_string()),
        }
    }
    let omitted = listed.len().saturating_sub(LISTED_LOAD_ERRORS);
    listed.truncate(LISTED_LOAD_ERRORS);
    let mut described = listed.join("; ");
    if omitted > 0 {
        described.push_str(&format!("; and {omitted} more"));
    }
    described
}

/// The loaded file at `path`, for a parse error's line.
fn find_source<'a>(
    source_map: &'a SourceMap,
    path: &Path,
) -> Option<&'a rustledger_loader::SourceFile> {
    source_map.files().iter().find(|f| f.path == path)
}

/// Load `path`, load errors and all.
///
/// A lint that answers over the result must call [`warn_load_errors`].
///
/// # Errors
/// Fails if `path` cannot be loaded at all (it does not exist, or cannot be
/// read).
pub fn load_source(path: &Path) -> Result<LoadResult> {
    Loader::new()
        .load(path)
        .with_context(|| format!("failed to load {}", path.display()))
}

/// Load `path`, refusing it if it has load errors (a parse error, a missing
/// include, ...).
///
/// # Errors
/// As [`load_source`], and when the file has load errors.
pub fn load_clean(path: &Path) -> Result<LoadResult> {
    let result = load_source(path)?;
    anyhow::ensure!(
        result.errors.is_empty(),
        "{}: cannot inspect source with load errors: {}",
        path.display(),
        describe_load_errors(&result)
    );
    Ok(result)
}

/// Load `path` and process it as `rledger check` does.
///
/// Booking, plugins and validation run. Load errors, a booking failure, or a
/// plugin failure refuse the input; every other processing error is left in
/// [`Ledger::errors`].
///
/// # Errors
/// As [`load_clean`], when processing fails outright, and when it reports a
/// booking or plugin failure.
pub fn load_booked(path: &Path) -> Result<Ledger> {
    let result = load_clean(path)?;
    let ledger = rustledger_loader::process(result, &check_options())
        .with_context(|| format!("failed to process {}", path.display()))?;
    let mut refusals = ledger
        .errors
        .iter()
        .filter(|e| e.is_booking_failure() || e.is_plugin_failure())
        .peekable();
    anyhow::ensure!(
        refusals.peek().is_none(),
        "{}: cannot inspect a ledger whose processing failed: {}",
        path.display(),
        describe_errors(refusals)
    );
    Ok(ledger)
}

/// Warn, when `result` has load errors, that the lint's answer over `path`
/// may be incomplete. A lint that reads its input with [`load_source`]
/// calls this for every input.
pub fn warn_load_errors(messages: &mut Messages<'_>, path: &Path, result: &LoadResult) {
    if result.errors.is_empty() {
        return;
    }
    messages.warn(
        LOAD_ERRORS,
        format!(
            "{}: has load errors, so findings may be incomplete: {}",
            path.display(),
            describe_load_errors(result)
        ),
    );
}

/// Errors by the file and line they are located at: the caller's indices.
type ErrorsByLine = HashMap<PathBuf, BTreeMap<usize, Vec<usize>>>;

/// The first and last line `span` covers in `source`. A directive's span
/// runs from its date to the start of the next directive, so for a
/// transaction it covers the header, the postings, and any blank or comment
/// lines before the next directive (none of which an error is located at).
fn span_lines(
    source: &rustledger_loader::SourceFile,
    span: rustledger_core::Span,
) -> (usize, usize) {
    let (first, _) = source.line_col(span.start);
    let (last, _) = source.line_col(span.end.saturating_sub(1).max(span.start));
    (first, last)
}

/// The errors located on lines `first..=last` of `file`: for a transaction,
/// the lines [`span_lines`] gives, so a plugin error located at one of its
/// postings is the transaction's too.
fn errors_within<'a>(
    by_line: &'a ErrorsByLine,
    file: &Path,
    first: usize,
    last: usize,
) -> impl Iterator<Item = usize> + 'a {
    by_line
        .get(file)
        .into_iter()
        .flat_map(move |lines| lines.range(first..=last))
        .flat_map(|(_, indices)| indices.iter().copied())
}

/// The processing errors of one ledger, by the transaction each is on.
///
/// These are the errors a [`load_booked`] lint did not refuse: a validator's
/// is placed by its span, a plugin's by its file and line (anywhere in the
/// transaction's lines, since a plugin can locate an error at one of its
/// postings).
///
/// The caller numbers the errors (`index`), so its own list of what it
/// reports can span several inputs. Build one per ledger.
#[derive(Default)]
pub struct ErrorIndex {
    by_span: HashMap<(u16, usize), Vec<usize>>,
    by_line: ErrorsByLine,
}

impl ErrorIndex {
    /// Record `error` as the caller's `index`. Only an error of severity
    /// `Error` is located on a transaction; a warning never is.
    pub fn insert(&mut self, index: usize, error: &LedgerError) {
        if error.severity != ErrorSeverity::Error {
            return;
        }
        if let (Some(file_id), Some((start, _))) = (error.file_id, error.source_span) {
            self.by_span
                .entry((file_id, start))
                .or_default()
                .push(index);
        }
        if let Some(location) = &error.location {
            self.by_line
                .entry(location.file.clone())
                .or_default()
                .entry(location.line)
                .or_default()
                .push(index);
        }
    }

    /// The indices of the errors on `directive`, a transaction at `site`.
    #[must_use]
    pub fn on_transaction(
        &self,
        directive: &Spanned<Directive>,
        site: &TransactionSite,
    ) -> BTreeSet<usize> {
        self.by_span
            .get(&(directive.file_id, directive.span.start))
            .into_iter()
            .flatten()
            .copied()
            .chain(
                site.lines.iter().flat_map(|(file, first, last)| {
                    errors_within(&self.by_line, file, *first, *last)
                }),
            )
            .collect()
    }
}

/// Where a transaction of the booked ledger is, and whether that tells it
/// apart from every other.
pub struct TransactionSite {
    /// The transaction's identity: its file (symlinks resolved, one path for
    /// every include of it) and span start. A transaction read twice (an
    /// included file also given as an input) has one key; a plugin-inserted
    /// one with no source location has a key of its own.
    pub key: (PathBuf, usize),
    /// The file to print, as the lints print paths.
    pub file: String,
    /// The 1-based line to print (0 when a plugin gave none).
    pub line: usize,
    /// The file and the lines the transaction covers, when it has a source
    /// location: where its errors are looked up.
    lines: Option<(PathBuf, usize, usize)>,
    /// Why the transaction cannot be told apart from another, when it
    /// cannot: a plugin inserted it with no source location, or at a
    /// location another transaction already has (`forecast`'s copies keep
    /// the template's, `effective_date`'s keep the parent's).
    pub unidentified: Option<&'static str>,
}

/// Numbers the transactions with no source location across a whole run.
///
/// Keep one for the run, so that such transactions are numbered apart
/// across inputs, and take each ledger's sites from
/// [`Self::for_ledger`]: the per-ledger counts live in the view it returns,
/// so a site can never be read against another ledger's counts.
#[derive(Default)]
pub struct TransactionSites {
    /// Transactions with no source location so far.
    unlocated: usize,
}

impl TransactionSites {
    /// The sites of `ledger`'s transactions.
    pub fn for_ledger<'a>(&'a mut self, ledger: &'a Ledger) -> LedgerSites<'a> {
        let mut per_location: HashMap<(u16, usize), usize> = HashMap::new();
        for directive in &ledger.directives {
            if matches!(directive.value, Directive::Transaction(_)) {
                *per_location
                    .entry((directive.file_id, directive.span.start))
                    .or_default() += 1;
            }
        }
        LedgerSites {
            ledger,
            per_location,
            unlocated: &mut self.unlocated,
        }
    }
}

/// One ledger's [`TransactionSite`]s, from [`TransactionSites::for_ledger`].
pub struct LedgerSites<'a> {
    ledger: &'a Ledger,
    /// How many transactions each source location of the ledger holds:
    /// more than one means a plugin inserted a transaction at its parent's
    /// location.
    per_location: HashMap<(u16, usize), usize>,
    /// The run's count of transactions with no source location.
    unlocated: &'a mut usize,
}

impl LedgerSites<'_> {
    /// The site of `directive`, a transaction of this ledger.
    pub fn site(&mut self, directive: &Spanned<Directive>) -> TransactionSite {
        let ledger = self.ledger;
        if let Some(source) = ledger.source_map.get(directive.file_id as usize) {
            let (line, _) = source.line_col(directive.span.start);
            let (_, last) = span_lines(source, directive.span);
            let shared = self
                .per_location
                .get(&(directive.file_id, directive.span.start))
                .is_some_and(|&count| count > 1);
            TransactionSite {
                key: (source.path.clone(), directive.span.start),
                file: source.path.display().to_string(),
                line,
                lines: Some((source.path.clone(), line, last)),
                unidentified: shared.then_some(
                    "several transactions share one source location \
                     (a plugin inserted one)",
                ),
            }
        } else {
            *self.unlocated += 1;
            let (file, line) = ledger
                .source_map
                .placeholder(directive.file_id)
                .map_or_else(
                    || ("<plugin>".to_string(), 0),
                    |(name, line)| (name.display().to_string(), line as usize),
                );
            TransactionSite {
                key: (PathBuf::from(format!("<unlocated {}>", *self.unlocated)), 0),
                file,
                line,
                lines: None,
                unidentified: Some(
                    "a plugin inserted this transaction, which has no source location",
                ),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cmd::report_cmd::CollectedDiagnostics;

    fn ledger(dir: &Path, body: &str) -> PathBuf {
        let path = dir.join("main.beancount");
        std::fs::write(&path, body).unwrap();
        path
    }

    /// A transaction with two elided postings (line 4 is its first posting),
    /// which booking cannot resolve, and a `close`.
    const UNBOOKABLE: &str = concat!(
        "2024-01-01 open Assets:Cash\n",
        "2024-01-01 open Expenses:Food\n",
        "2024-01-02 * \"lunch\"\n",
        "  Assets:Cash\n",
        "  Expenses:Food\n",
        "2024-12-31 close Assets:Cash\n",
    );

    /// A plugin that does not exist, and nothing else wrong.
    const MISSING_PLUGIN: &str = concat!(
        "plugin \"no.such.plugin\"\n",
        "2024-01-01 open Assets:Cash\n",
    );

    #[test]
    fn test_load_booked_refuses_a_booking_failure() {
        let dir = tempfile::tempdir().unwrap();
        let path = ledger(dir.path(), UNBOOKABLE);
        let err = load_booked(&path).unwrap_err().to_string();
        assert!(
            err.starts_with(&format!(
                "{}: cannot inspect a ledger whose processing failed: {}:4: BOOK: interpolation failed",
                path.display(),
                path.display()
            )),
            "{err}"
        );
    }

    #[test]
    fn test_load_booked_refuses_a_plugin_failure() {
        let dir = tempfile::tempdir().unwrap();
        let path = ledger(dir.path(), MISSING_PLUGIN);
        let err = load_booked(&path).unwrap_err().to_string();
        assert!(
            err.starts_with(&format!(
                "{}: cannot inspect a ledger whose processing failed: E800",
                path.display()
            )),
            "{err}"
        );
        // E8004 with the Python plugin runtime, E8005 in a build without it.
        assert!(err.contains(": Python plugin \"no.such.plugin\""), "{err}");
    }

    #[test]
    fn test_load_booked_names_every_failure() {
        let dir = tempfile::tempdir().unwrap();
        let path = ledger(dir.path(), &format!("{MISSING_PLUGIN}{UNBOOKABLE}"));
        let err = load_booked(&path).unwrap_err().to_string();
        // The two lines of MISSING_PLUGIN move the booking failure down two.
        assert!(
            err.contains(&format!("{}:6: BOOK: interpolation failed", path.display())),
            "{err}"
        );
        // E8004 with the Python plugin runtime, E8005 in a build without it.
        assert!(err.contains(": Python plugin \"no.such.plugin\""), "{err}");
    }

    #[test]
    fn test_load_booked_keeps_other_errors_for_the_lint() {
        let dir = tempfile::tempdir().unwrap();
        // An unopened account is a validation error, not a refusal.
        let path = ledger(
            dir.path(),
            concat!(
                "2024-01-01 open Assets:Cash\n",
                "2024-01-02 * \"lunch\"\n",
                "  Assets:Cash  -1 USD\n",
                "  Expenses:Food\n",
            ),
        );
        let ledger = load_booked(&path).unwrap();
        assert!(!ledger.errors.is_empty());
    }

    #[test]
    fn test_load_clean_and_load_booked_refuse_load_errors() {
        let dir = tempfile::tempdir().unwrap();
        let path = ledger(dir.path(), "include \"missing-xyz.beancount\"\n");
        let want = format!(
            "{}: cannot inspect source with load errors: ",
            path.display()
        );
        let err = load_clean(&path).unwrap_err().to_string();
        assert!(err.starts_with(&want), "{err}");
        let err = load_booked(&path).unwrap_err().to_string();
        assert!(err.starts_with(&want), "{err}");
    }

    /// A load error the loader counts as harmless is refused too, as
    /// `bean-check` reports it.
    #[test]
    fn test_load_clean_refuses_a_duplicate_include() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(dir.path().join("prices.beancount"), "").unwrap();
        let path = ledger(
            dir.path(),
            "include \"prices.beancount\"\ninclude \"prices.beancount\"\n",
        );
        let result = load_source(&path).unwrap();
        assert!(
            result.errors.iter().all(LoadError::leaves_ledger_complete),
            "{:?}",
            result.errors
        );
        let err = load_clean(&path).unwrap_err().to_string();
        assert!(err.contains("Duplicate filename parsed"), "{err}");
    }

    /// Each parse error is named with its line, not as one `parse errors in
    /// <file>`.
    #[test]
    fn test_load_clean_names_each_parse_error_with_its_line() {
        let dir = tempfile::tempdir().unwrap();
        let path = ledger(
            dir.path(),
            "2024-01-01 open Assets:Cash\nnot beancount\n2024-01-02 open Assets:Bank\nalso not\n",
        );
        let err = load_clean(&path).unwrap_err().to_string();
        let shown = path.display().to_string();
        assert!(err.contains(&format!("{shown}:2: P")), "{err}");
        assert!(err.contains(&format!("{shown}:4: P")), "{err}");
        assert!(!err.contains("parse errors in"), "{err}");
    }

    #[test]
    fn test_load_clean_caps_the_listed_load_errors() {
        let dir = tempfile::tempdir().unwrap();
        let body = "junk line\n".repeat(13);
        let path = ledger(dir.path(), &body);
        let total: usize = load_source(&path)
            .unwrap()
            .errors
            .iter()
            .map(|e| match e {
                LoadError::ParseErrors { errors, .. } => errors.len(),
                _ => 1,
            })
            .sum();
        assert!(total > LISTED_LOAD_ERRORS, "{total}");
        let err = load_clean(&path).unwrap_err().to_string();
        let shown = path.display().to_string();
        // The refusal's own `<file>: ` prefix, then each listed error.
        assert_eq!(
            err.matches(&format!("{shown}:")).count(),
            1 + LISTED_LOAD_ERRORS,
            "{err}"
        );
        assert!(
            err.ends_with(&format!("; and {} more", total - LISTED_LOAD_ERRORS)),
            "{err}"
        );
    }

    #[test]
    fn test_load_source_keeps_load_errors_and_warn_load_errors_says_so() {
        let dir = tempfile::tempdir().unwrap();
        let path = ledger(dir.path(), "include \"missing-xyz.beancount\"\n");
        let result = load_source(&path).unwrap();
        assert!(!result.errors.is_empty());

        let mut err = Vec::new();
        let mut sink = CollectedDiagnostics::default();
        warn_load_errors(
            &mut Messages::new(&mut err, Some(&mut sink)),
            &path,
            &result,
        );
        assert_eq!(sink.0.len(), 1);
        assert_eq!(sink.0[0].code.as_deref(), Some(LOAD_ERRORS));
        assert!(
            sink.0[0].message.starts_with(&format!(
                "{}: has load errors, so findings may be incomplete: ",
                path.display()
            )),
            "{:?}",
            sink.0[0]
        );

        // Without a sink, it is a `warning:` line.
        let mut err = Vec::new();
        warn_load_errors(&mut Messages::new(&mut err, None), &path, &result);
        assert!(
            String::from_utf8(err).unwrap().starts_with("warning: "),
            "expected a warning line"
        );
    }

    #[test]
    fn test_warn_load_errors_is_silent_without_errors() {
        let dir = tempfile::tempdir().unwrap();
        let path = ledger(dir.path(), "2024-01-01 open Assets:Cash\n");
        let result = load_source(&path).unwrap();
        let mut err = Vec::new();
        let mut sink = CollectedDiagnostics::default();
        warn_load_errors(
            &mut Messages::new(&mut err, Some(&mut sink)),
            &path,
            &result,
        );
        assert!(sink.0.is_empty());
        assert!(err.is_empty());
    }

    /// Every line in the range counts, header and postings alike; a line
    /// past it, or one in another file, does not.
    #[test]
    fn test_errors_within_takes_every_line_in_the_range() {
        let file = PathBuf::from("/ledger/main.bean");
        let mut by_line = ErrorsByLine::new();
        for (line, index) in [(10, 0), (12, 1), (13, 2), (20, 3)] {
            by_line
                .entry(file.clone())
                .or_default()
                .entry(line)
                .or_default()
                .push(index);
        }
        by_line
            .entry(PathBuf::from("/ledger/other.bean"))
            .or_default()
            .entry(11)
            .or_default()
            .push(4);
        // A range of lines 10 to 12, as span_lines gives for a transaction.
        let found: Vec<usize> = errors_within(&by_line, &file, 10, 12).collect();
        assert_eq!(found, [0, 1]);
        assert_eq!(
            errors_within(&by_line, Path::new("/ledger/none.bean"), 1, 99).count(),
            0
        );
    }

    /// The range of a real transaction: from its header up to the next
    /// directive, so its postings (and blank and comment lines after them)
    /// are in it, and the next transaction is not.
    #[test]
    fn test_span_lines_covers_a_parsed_transaction() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("main.bean");
        std::fs::write(
            &path,
            concat!(
                "2000-01-01 open Assets:Cash\n",
                "\n",
                "2024-01-01 * \"a\" ^xfer-a\n",
                "  Assets:Transit 5 USD\n",
                "  Assets:Cash\n",
                "\n",
                "; a comment\n",
                "2024-01-02 * \"b\"\n",
                "  Assets:Cash 1 USD\n",
                "  Assets:Transit\n",
            ),
        )
        .unwrap();
        let loaded = Loader::new().load(&path).unwrap();
        let file = &loaded.source_map.files()[0];
        let spans: Vec<(usize, usize)> = loaded
            .directives
            .iter()
            .filter(|d| matches!(d.value, Directive::Transaction(_)))
            .map(|d| span_lines(file, d.span))
            .collect();
        assert_eq!(spans.len(), 2, "{spans:?}");
        let (first, last) = spans[0];
        assert_eq!(first, 3, "{spans:?}");
        // Up to the line before the next directive: the comment.
        assert_eq!(last, 7, "{spans:?}");
        assert_eq!(spans[1].0, 8, "{spans:?}");
        // An error at the first transaction's second posting is its own,
        // not the next one's.
        let mut by_line = ErrorsByLine::new();
        by_line
            .entry(file.path.clone())
            .or_default()
            .entry(5)
            .or_default()
            .push(0);
        assert_eq!(errors_within(&by_line, &file.path, first, last).count(), 1);
        let (next_first, next_last) = spans[1];
        assert_eq!(
            errors_within(&by_line, &file.path, next_first, next_last).count(),
            0,
            "{spans:?}"
        );
    }

    /// Validator errors by span, plugin errors anywhere in the transaction's
    /// lines, warnings never; and a transaction with a location of its own
    /// is identified.
    #[test]
    fn test_error_index_places_errors_on_their_transaction() {
        let dir = tempfile::tempdir().unwrap();
        let path = ledger(
            dir.path(),
            concat!(
                "2024-01-01 open Assets:Cash\n",
                "2024-01-02 * \"unbalanced\"\n",
                "  Assets:Cash  -1 USD\n",
                "  Assets:Cash   2 USD\n",
                "2024-01-03 * \"fine\"\n",
                "  Assets:Cash  -1 USD\n",
                "  Assets:Cash   1 USD\n",
            ),
        );
        let ledger = load_booked(&path).unwrap();
        let mut index = ErrorIndex::default();
        for (i, error) in ledger.errors.iter().enumerate() {
            index.insert(i, error);
        }
        let mut run = TransactionSites::default();
        let mut sites = run.for_ledger(&ledger);
        let found: Vec<(usize, BTreeSet<usize>, Option<&str>)> = ledger
            .directives
            .iter()
            .filter(|d| matches!(d.value, Directive::Transaction(_)))
            .map(|d| {
                let site = sites.site(d);
                (site.line, index.on_transaction(d, &site), site.unidentified)
            })
            .collect();
        assert_eq!(found.len(), 2);
        assert_eq!(found[0].0, 2);
        assert!(!found[0].1.is_empty(), "{found:?} {:?}", ledger.errors);
        assert_eq!(found[0].2, None);
        assert_eq!(found[1], (5, BTreeSet::new(), None));
    }
}
