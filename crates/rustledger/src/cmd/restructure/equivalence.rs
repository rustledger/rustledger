//! The equivalence check: load the ledger before and after, compare what it
//! means, and refuse to write anything unless the two agree.
//!
//! "What it means" is everything a reader of the ledger can observe that does
//! not depend on which file a line sits in or on which line it sits:
//!
//! - the processed directive stream (plugins run, booked, validated), in its
//!   final order — booking order is the stable `(date, priority)` sort of that
//!   order, so it is covered too;
//! - the options and the plugin list;
//! - every error and warning, by severity, code, message, phase and the
//!   directive it is attached to;
//! - where each `document` directive's path resolves to, since a relative
//!   path resolves against the directory of the file that contains it;
//! - the booking method in force, realized capital gains, and failing balance
//!   assertions.
//!
//! What it deliberately ignores is file paths and byte offsets themselves:
//! moving a directive changes those by definition.

use super::overlay::OverlayFs;
use rustledger_core::Directive;
use rustledger_loader::{ErrorSeverity, Ledger, LoadOptions, Options, SourceMap};
use std::fmt::Write as _;
use std::path::{Component, Path, PathBuf};

/// Everything the check compares, extracted from one load.
#[derive(Debug, PartialEq)]
pub(super) struct Fingerprint {
    directives: Vec<Directive>,
    documents: Vec<Option<PathBuf>>,
    options: Options,
    plugins: Vec<(String, Option<String>, bool)>,
    errors: Vec<ErrorKey>,
    booking_method: String,
    capital_gains: Vec<String>,
    balance_discrepancies: Vec<String>,
}

#[derive(Debug, PartialEq)]
struct ErrorKey {
    severity: &'static str,
    code: String,
    message: String,
    phase: String,
    /// Index into the directive stream of the directive this error is
    /// attached to, when it is attached to one.
    anchor: Option<usize>,
}

/// Load `root` through `fs` the way `rledger check` does and fingerprint it.
/// Also returns the paths of the files the ledger consists of.
pub(super) fn load(root: &Path, fs: OverlayFs) -> anyhow::Result<(Fingerprint, Vec<PathBuf>)> {
    let options = LoadOptions {
        run_plugins: true,
        validate: true,
        collect_capital_gains: true,
        plugin_max_time_secs: crate::plugin_budget::max_time_secs(),
        plugin_max_memory_mb: crate::plugin_budget::max_memory_mb(),
        ..Default::default()
    };
    let ledger = rustledger_loader::load_with_fs(root, &options, Box::new(fs))
        .map_err(|e| anyhow::anyhow!("failed to load {}: {e}", root.display()))?;
    let files = ledger
        .source_map
        .files()
        .iter()
        .map(|f| f.path.clone())
        .collect();
    Ok((fingerprint(&ledger), files))
}

fn fingerprint(ledger: &Ledger) -> Fingerprint {
    let directives: Vec<Directive> = ledger.directives.iter().map(|d| d.value.clone()).collect();
    let documents = ledger
        .directives
        .iter()
        .filter_map(|d| match &d.value {
            Directive::Document(doc) => Some(resolve_document(
                &ledger.source_map,
                d.file_id,
                doc.path.as_str(),
            )),
            _ => None,
        })
        .collect();
    let plugins = ledger
        .plugins
        .iter()
        .map(|p| (p.name.clone(), p.config.clone(), p.force_python))
        .collect();
    let anchors = Anchors::new(ledger);
    let errors = ledger
        .errors
        .iter()
        .map(|e| ErrorKey {
            severity: match e.severity {
                ErrorSeverity::Error => "error",
                ErrorSeverity::Warning => "warning",
            },
            code: e.code.clone(),
            message: e.message.clone(),
            phase: e.phase.clone(),
            anchor: e
                .file_id
                .zip(e.source_span)
                .and_then(|(fid, (start, end))| anchors.find(fid, start, end)),
        })
        .collect();
    Fingerprint {
        directives,
        documents,
        options: ledger.options.clone(),
        plugins,
        errors,
        booking_method: format!("{:?}", ledger.booking_method),
        capital_gains: ledger
            .capital_gains
            .iter()
            .map(|g| format!("{g:?}"))
            .collect(),
        balance_discrepancies: ledger
            .balance_discrepancies
            .iter()
            .map(|b| format!("{b:?}"))
            .collect(),
    }
}

/// Where a `document` path points: absolute as written, otherwise against
/// the directory the file that contains the directive was opened from,
/// symlinks kept (the rule the validator falls back to, and the one beancount
/// applies at parse time, #2635).
///
/// Stricter than the validator, which consults `option "documents"` and
/// `document_base` first: a relative path that moves to a different
/// directory is reported even when one of those would have found it anyway.
/// A false refusal is recoverable; a silent change in what a document links to
/// is not.
fn resolve_document(source_map: &SourceMap, file_id: u16, path: &str) -> Option<PathBuf> {
    let p = Path::new(path);
    if p.is_absolute() {
        return Some(p.to_path_buf());
    }
    let dir = source_map.get(file_id as usize)?.dir();
    let mut out = PathBuf::new();
    for c in dir.join(p).components() {
        match c {
            Component::ParentDir => {
                out.pop();
            }
            Component::CurDir => {}
            other => out.push(other.as_os_str()),
        }
    }
    Some(out)
}

/// Maps an error's byte span to the directive that contains it.
struct Anchors {
    /// Per file id: `(start, end, index)` sorted by start.
    by_file: std::collections::HashMap<u16, Vec<(usize, usize, usize)>>,
}

impl Anchors {
    fn new(ledger: &Ledger) -> Self {
        let mut by_file: std::collections::HashMap<u16, Vec<(usize, usize, usize)>> =
            std::collections::HashMap::new();
        for (i, d) in ledger.directives.iter().enumerate() {
            by_file
                .entry(d.file_id)
                .or_default()
                .push((d.span.start, d.span.end, i));
        }
        for v in by_file.values_mut() {
            v.sort_unstable();
        }
        Self { by_file }
    }

    /// The innermost directive whose span contains `start..end`.
    fn find(&self, file_id: u16, start: usize, end: usize) -> Option<usize> {
        let v = self.by_file.get(&file_id)?;
        // Candidates start at or before `start`; directive spans in one file
        // do not nest, so the last such one is the only candidate.
        let idx = v.partition_point(|&(s, _, _)| s <= start);
        let &(s, e, i) = v.get(idx.checked_sub(1)?)?;
        (s <= start && end <= e).then_some(i)
    }
}

/// Describe the first difference between two fingerprints, for the refusal
/// message. `None` when they are equal.
pub(super) fn first_difference(before: &Fingerprint, after: &Fingerprint) -> Option<String> {
    if before == after {
        return None;
    }
    let mut out = String::new();
    if before.directives != after.directives {
        let n = before.directives.len().max(after.directives.len());
        for i in 0..n {
            let (b, a) = (before.directives.get(i), after.directives.get(i));
            if b != a {
                let _ = write!(
                    out,
                    "the directive stream differs at entry {} of {}: before {}, after {}",
                    i + 1,
                    before.directives.len(),
                    describe(b),
                    describe(a),
                );
                if let (Some(b), Some(a)) = (b, a) {
                    let (db, da) = detail(&format!("{b:?}"), &format!("{a:?}"));
                    let _ = write!(out, "\n    before: ...{db}...\n    after:  ...{da}...");
                }
                return Some(out);
            }
        }
    }
    if before.documents != after.documents {
        let i = before
            .documents
            .iter()
            .zip(&after.documents)
            .position(|(b, a)| b != a)
            .unwrap_or(0);
        let show = |d: Option<&Option<PathBuf>>| {
            d.and_then(Option::as_ref)
                .map_or_else(|| "nothing".to_string(), |p| p.display().to_string())
        };
        let _ = write!(
            out,
            "a document path would resolve differently: {} before, {} after \
             (a relative `document` path resolves against the directory of the \
             file that contains it)",
            show(before.documents.get(i)),
            show(after.documents.get(i)),
        );
        return Some(out);
    }
    if before.options != after.options {
        return Some("the options differ".to_string());
    }
    if before.plugins != after.plugins {
        return Some(format!(
            "the plugin list differs: before {:?}, after {:?}",
            before.plugins, after.plugins
        ));
    }
    if before.errors != after.errors {
        let n = before.errors.len().max(after.errors.len());
        for i in 0..n {
            let (b, a) = (before.errors.get(i), after.errors.get(i));
            if b != a {
                let show = |e: Option<&ErrorKey>| {
                    e.map_or_else(
                        || "nothing".to_string(),
                        |e| format!("{}[{}]: {}", e.severity, e.code, e.message),
                    )
                };
                return Some(format!(
                    "the errors differ ({} before, {} after); first difference: \
                     before {}, after {}",
                    before.errors.len(),
                    after.errors.len(),
                    show(b),
                    show(a),
                ));
            }
        }
    }
    if before.booking_method != after.booking_method {
        return Some("the booking method differs".to_string());
    }
    if before.capital_gains != after.capital_gains {
        return Some("the realized capital gains differ".to_string());
    }
    Some("the failing balance assertions differ".to_string())
}

/// The neighborhood of the first difference between two renderings.
fn detail(b: &str, a: &str) -> (String, String) {
    let at = b
        .char_indices()
        .zip(a.chars())
        .find(|((_, x), y)| x != y)
        .map_or_else(|| b.len().min(a.len()), |((i, _), _)| i);
    let window = |s: &str| {
        let start = s.floor_char_boundary(at.saturating_sub(40));
        let end = s.ceil_char_boundary((at + 60).min(s.len()));
        s[start..end].to_string()
    };
    (window(b), window(a))
}

fn describe(d: Option<&Directive>) -> String {
    d.map_or_else(
        || "nothing".to_string(),
        |d| format!("{} {}", d.date(), d.type_name()),
    )
}

impl Fingerprint {
    /// Number of directives in the processed stream.
    pub(super) const fn directive_count(&self) -> usize {
        self.directives.len()
    }

    /// Number of errors (any severity).
    pub(super) const fn error_count(&self) -> usize {
        self.errors.len()
    }
}
