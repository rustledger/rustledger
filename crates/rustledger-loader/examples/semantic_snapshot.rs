//! rledger's side of the semantic differential
//! (`scripts/compat-semantic-parity.py`): for each input ledger, a snapshot
//! of what the full pipeline makes of it, in pta-standards' format-generic
//! `ptadiff-snapshot/1` schema (`tooling/differential/SNAPSHOT.md` there),
//! which beancount's side produces from `beancount.loader.load_file`.
//!
//! Protocol: ptadiff's JSON lines. One input per line,
//!
//! ```text
//! {"id": "<id>", "text": "<main file>", "main": "main.beancount", "files": {"<rel path>": "<text>", ...}}
//! ```
//!
//! and per input one line, `{"id": ..., "snapshot": {...}}`, or
//! `{"id": ..., "crash": "<why>"}` when the pipeline panicked (a bug: the
//! harness reports it, it is never judged a match).
//!
//! Each input is written to a fresh temporary directory and loaded from disk
//! the way `rledger check` loads a file, every step a call to the canonical
//! function and nothing re-derived (AGENTS.md, "Canonical-Function
//! Discipline"):
//!
//! - load: [`rustledger_loader::Loader::load`];
//! - errors: the parse errors ([`LoadResult::take_parse_errors`] through
//!   [`parse_errors_to_ledger_errors`]), the option diagnostics
//!   ([`option_warnings_to_errors`]) and the pipeline's errors
//!   ([`rustledger_loader::process`], with plugins and validation, as
//!   `check` builds its `LoadOptions`), keeping what `check` counts as an
//!   error: severity error, advisory-only codes left out;
//! - entries: the processed directives, with the padding transactions placed
//!   and located by [`rustledger_booking::merge_with_padding_spanned`] (the
//!   spanned form of [`rustledger_loader::Ledger::balance_view`]). A
//!   transaction booking refused ([`rustledger_loader::Ledger::booking_refused`])
//!   is listed as written and left out of the pads and the balances, as
//!   beancount leaves a refused entry out;
//! - a posting's cost: [`rustledger_core::CostSpec::resolve`];
//! - a transaction's tolerances: [`rustledger_booking::transaction_tolerances`]
//!   over the transaction as written (the pre-booking stream), as booking and
//!   the balance check infer them;
//! - balances: [`rustledger_booking::account_balances`], the realization the
//!   reports print;
//! - display precision: the ledger's [`rustledger_core::DisplayContext`].
//!
//! Numbers are written as `Decimal` prints them and nothing is sorted: the
//! harness canonicalizes both sides in one place. Paths are relative to the
//! temporary directory.
//!
//! Run with `cargo run --release -p rustledger-loader --example
//! semantic_snapshot`.
//!
//! [`LoadResult::take_parse_errors`]: rustledger_loader::LoadResult::take_parse_errors
//! [`parse_errors_to_ledger_errors`]: rustledger_loader::parse_errors_to_ledger_errors
//! [`option_warnings_to_errors`]: rustledger_loader::option_warnings_to_errors

use std::collections::{HashMap, HashSet};
use std::io::{self, BufRead, BufWriter, Write};
use std::path::{Path, PathBuf};

use rustledger_core::{
    Amount, CostSpec, Directive, IncompleteAmount, NaiveDate, Posting, Precision, Spanned,
};
use rustledger_loader::{ErrorSeverity, LedgerError, LoadOptions, SourceMap};
use serde_json::{Value, json};

fn invalid(message: String) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

/// Paths relative to the input's directory.
struct Paths {
    /// The directory as created, and canonicalized (a path the loader read
    /// may be either).
    roots: [PathBuf; 2],
}

impl Paths {
    fn rel(&self, path: &Path) -> String {
        let shown = path.display().to_string();
        if shown.starts_with('<') {
            return shown;
        }
        let real = std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
        self.roots
            .iter()
            .find_map(|root| real.strip_prefix(root).ok())
            .map_or(shown, |rel| {
                rel.components()
                    .map(|c| c.as_os_str().to_string_lossy().into_owned())
                    .collect::<Vec<_>>()
                    .join("/")
            })
    }
}

fn amount(a: &Amount) -> Value {
    json!({ "number": a.number.to_string(), "currency": a.currency.to_string() })
}

fn incomplete(a: Option<&IncompleteAmount>) -> Value {
    match a {
        None => Value::Null,
        Some(IncompleteAmount::Complete(a)) => amount(a),
        Some(IncompleteAmount::NumberOnly(n)) => {
            json!({ "number": n.to_string(), "currency": null })
        }
        Some(IncompleteAmount::CurrencyOnly(c)) => {
            json!({ "number": null, "currency": c.to_string() })
        }
    }
}

fn date(d: NaiveDate) -> String {
    d.to_string()
}

/// A booked posting's cost, resolved as the inventory holds it; a spec
/// booking left unresolved (on a refused transaction) as written.
fn cost(posting: &Posting, txn_date: NaiveDate) -> Value {
    let Some(spec) = posting.cost.as_deref() else {
        return Value::Null;
    };
    if let Some(IncompleteAmount::Complete(units)) = &posting.units
        && let Some(c) = spec.resolve(units.number, txn_date)
    {
        return json!({
            "number": c.number.to_string(),
            "currency": c.currency.to_string(),
            "date": c.date.map(date),
            "label": c.label,
        });
    }
    cost_spec(spec)
}

fn cost_spec(spec: &CostSpec) -> Value {
    use rustledger_core::CostNumber;
    let (per, total) = match spec.number {
        None => (None, None),
        Some(CostNumber::PerUnit { value }) => (Some(value), None),
        Some(CostNumber::Total { value }) => (None, Some(value)),
        Some(CostNumber::PerUnitFromTotal(b)) => (Some(b.per_unit), Some(b.total)),
        Some(CostNumber::Compound { per_unit, total }) => (Some(per_unit), Some(total)),
    };
    let (per, total) = (per.map(|n| n.to_string()), total.map(|n| n.to_string()));
    json!({
        "spec": true,
        "number_per": per,
        "number_total": total,
        "currency": spec.currency.as_ref().map(ToString::to_string),
        "date": spec.date.map(date),
        "label": spec.label,
        "merge": spec.merge,
    })
}

fn sorted_strings<T: ToString>(items: impl IntoIterator<Item = T>) -> Vec<String> {
    let mut out: Vec<String> = items.into_iter().map(|t| t.to_string()).collect();
    out.sort();
    out
}

struct Ctx<'a> {
    paths: &'a Paths,
    source_map: &'a SourceMap,
    tolerances: HashMap<(u16, usize), Value>,
}

impl Ctx<'_> {
    fn location(&self, file_id: u16, offset: usize) -> (String, usize) {
        self.source_map
            .get(file_id as usize)
            .map_or((String::new(), 0), |f| {
                (self.paths.rel(&f.path), f.line_col(offset).0)
            })
    }

    /// A document's path as the file names it: a relative one is relative
    /// to the directory of the file that holds the directive, as the loader
    /// resolves it; `.` and `..` components are folded lexically, since the
    /// document need not exist.
    fn document_path(&self, file_id: u16, path: &str) -> String {
        let path = Path::new(path);
        let joined = if path.is_absolute() {
            path.to_path_buf()
        } else {
            self.source_map
                .get(file_id as usize)
                .and_then(|f| f.path.parent().map(|dir| dir.join(path)))
                .unwrap_or_else(|| path.to_path_buf())
        };
        let mut folded = PathBuf::new();
        for c in joined.components() {
            match c {
                std::path::Component::CurDir => {}
                std::path::Component::ParentDir => {
                    folded.pop();
                }
                other => folded.push(other),
            }
        }
        self.paths.rel(&folded)
    }

    fn entry(&self, s: &Spanned<Directive>) -> Value {
        let (file, line) = self.location(s.file_id, s.span.start);
        let d = &s.value;
        let mut base = json!({ "date": date(d.date()), "file": file, "line": line });
        let obj = base.as_object_mut().expect("an object");
        let mut put = |k: &str, v: Value| {
            obj.insert(k.to_string(), v);
        };
        match d {
            Directive::Transaction(t) => {
                put("type", json!("transaction"));
                put("flag", json!(t.flag.to_string()));
                put(
                    "payee",
                    json!(t.payee.as_ref().map(|p| p.as_str().to_string())),
                );
                put("narration", json!(t.narration.as_str()));
                put("tags", json!(sorted_strings(t.tags.iter())));
                put("links", json!(sorted_strings(t.links.iter())));
                let postings: Vec<Value> = t
                    .postings
                    .iter()
                    .map(|p| {
                        let p = &p.value;
                        json!({
                            "account": p.account.to_string(),
                            "units": incomplete(p.units.as_ref()),
                            "cost": cost(p, t.date),
                            "price": p.price.as_ref().map_or(Value::Null, |pr| incomplete(pr.amount.as_ref())),
                            "flag": p.flag.map(|f| f.to_string()),
                        })
                    })
                    .collect();
                put("postings", Value::Array(postings));
                if let Some(tol) = self.tolerances.get(&(s.file_id, s.span.start))
                    && !rustledger_booking::is_synthesized_pad(t)
                {
                    put("tolerances", tol.clone());
                }
            }
            Directive::Open(o) => {
                put("type", json!("open"));
                put("account", json!(o.account.to_string()));
                put("currencies", json!(sorted_strings(o.currencies.iter())));
                put("booking", json!(o.booking));
            }
            Directive::Close(c) => {
                put("type", json!("close"));
                put("account", json!(c.account.to_string()));
            }
            Directive::Commodity(c) => {
                put("type", json!("commodity"));
                put("currency", json!(c.currency.to_string()));
            }
            Directive::Pad(p) => {
                put("type", json!("pad"));
                put("account", json!(p.account.to_string()));
                put("source_account", json!(p.source_account.to_string()));
            }
            Directive::Balance(b) => {
                put("type", json!("balance"));
                put("account", json!(b.account.to_string()));
                put("amount", amount(&b.amount));
                put("tolerance", json!(b.tolerance.map(|t| t.to_string())));
            }
            Directive::Price(p) => {
                put("type", json!("price"));
                put("currency", json!(p.currency.to_string()));
                put("amount", amount(&p.amount));
            }
            Directive::Note(n) => {
                put("type", json!("note"));
                put("account", json!(n.account.to_string()));
                put("comment", json!(n.comment));
            }
            Directive::Event(e) => {
                put("type", json!("event"));
                put("event", json!(e.event_type));
                put("description", json!(e.value));
            }
            Directive::Query(q) => {
                put("type", json!("query"));
                put("name", json!(q.name));
                put("query", json!(q.query));
            }
            Directive::Document(doc) => {
                put("type", json!("document"));
                put("account", json!(doc.account.to_string()));
                put("filename", json!(self.document_path(s.file_id, &doc.path)));
            }
            Directive::Custom(c) => {
                put("type", json!("custom"));
                put("custom", json!(c.custom_type));
                put("values", json!(c.values.len()));
            }
        }
        base
    }

    fn error(&self, e: &LedgerError) -> Value {
        let (file, line) = e
            .location
            .as_ref()
            .map_or((String::new(), 0), |l| (self.paths.rel(&l.file), l.line));
        json!({ "file": file, "line": line, "code": e.code, "msg": e.message })
    }
}

/// Whether `rledger check` counts `e` as an error.
fn counted(e: &LedgerError) -> bool {
    matches!(e.severity, ErrorSeverity::Error)
        && !rustledger_validate::is_advisory_only_code(&e.code)
}

fn snapshot(root: &Path, main: &Path) -> Result<Value, String> {
    let paths = Paths {
        roots: [
            root.to_path_buf(),
            std::fs::canonicalize(root).map_err(|e| e.to_string())?,
        ],
    };
    let mut raw = rustledger_loader::Loader::new()
        .load(main)
        .map_err(|e| format!("load: {e}"))?;
    let parse_errors: Vec<LedgerError> = raw
        .take_parse_errors()
        .iter()
        .flat_map(|failure| {
            rustledger_loader::parse_errors_to_ledger_errors(failure, &raw.source_map)
        })
        .collect();
    // As `rledger check` builds them (`cmd/check.rs`), without its CLI-only
    // knobs.
    let options = LoadOptions {
        run_plugins: true,
        validate: true,
        retain_pre_booking_directives: true,
        ..Default::default()
    };
    let ledger = rustledger_loader::process(raw, &options).map_err(|e| format!("process: {e}"))?;
    let option_errors = rustledger_loader::option_warnings_to_errors(&ledger.options.warnings);

    let tolerance_options = rustledger_booking::ToleranceOptions {
        multiplier: ledger.options.inferred_tolerance_multiplier,
        infer_from_cost: ledger.options.infer_tolerance_from_cost,
        defaults: &ledger.options.inferred_tolerance_default,
    };
    let mut ctx = Ctx {
        paths: &paths,
        source_map: &ledger.source_map,
        tolerances: HashMap::new(),
    };
    for s in &ledger.pre_booking_directives {
        if let Directive::Transaction(t) = &s.value {
            let mut tol: Vec<(String, String)> =
                rustledger_booking::transaction_tolerances(t, &tolerance_options)
                    .into_iter()
                    .map(|(c, n)| (c.to_string(), n.to_string()))
                    .collect();
            tol.sort();
            let map: serde_json::Map<String, Value> = tol
                .into_iter()
                .map(|(c, n)| (c, Value::String(n)))
                .collect();
            ctx.tolerances
                .insert((s.file_id, s.span.start), Value::Object(map));
        }
    }

    let refused: HashSet<usize> = ledger.booking_refused.iter().copied().collect();
    let kept: Vec<Spanned<Directive>> = ledger
        .directives
        .iter()
        .enumerate()
        .filter(|(n, _)| !refused.contains(n))
        .map(|(_, s)| s.clone())
        .collect();
    let merged = rustledger_booking::merge_with_padding_spanned(
        &kept,
        ledger.options.inferred_tolerance_multiplier,
    );
    let mut entries: Vec<Value> = merged.iter().map(|s| ctx.entry(s)).collect();
    entries.extend(
        ledger
            .booking_refused
            .iter()
            .filter_map(|&n| ledger.directives.get(n))
            .map(|s| ctx.entry(s)),
    );

    let plain: Vec<Directive> = merged.into_iter().map(|s| s.value).collect();
    let realized = rustledger_booking::account_balances(&plain, ledger.booking_method)
        .map_err(|e| format!("realize: {e}"))?;
    let balances: serde_json::Map<String, Value> = realized
        .into_iter()
        .map(|(account, inventory)| {
            let positions: Vec<Value> = inventory
                .positions()
                .map(|p| {
                    json!({
                        "units": amount(&p.units),
                        "cost": p.cost.as_ref().map_or(Value::Null, |c| json!({
                            "number": c.number.to_string(),
                            "currency": c.currency.to_string(),
                            "date": c.date.map(date),
                            "label": c.label,
                        })),
                    })
                })
                .collect();
            (account.to_string(), Value::Array(positions))
        })
        .collect();

    let errors: Vec<Value> = parse_errors
        .iter()
        .chain(&option_errors)
        .chain(&ledger.errors)
        .filter(|e| counted(e))
        .map(|e| ctx.error(e))
        .collect();

    let dc = &ledger.display_context;
    let display_precision: serde_json::Map<String, Value> = dc
        .currencies()
        .map(|c| {
            (
                c.to_string(),
                json!({
                    "common": dc.precision_under(c, Precision::MostCommon),
                    "max": dc.precision_under(c, Precision::Maximum),
                }),
            )
        })
        .collect();
    let o = &ledger.options;
    let tolerance_default: serde_json::Map<String, Value> = o
        .inferred_tolerance_default
        .iter()
        .map(|(c, n)| (c.clone(), Value::String(n.to_string())))
        .collect();

    Ok(json!({
        "errors": errors,
        "entries": entries,
        "balances": balances,
        "options": {
            "operating_currency": o.operating_currency,
            "booking_method": ledger.booking_method.to_string(),
            "inferred_tolerance_default": tolerance_default,
            "tolerance_multiplier": o.inferred_tolerance_multiplier.to_string(),
            "infer_tolerance_from_cost": o.infer_tolerance_from_cost,
            "display_precision": display_precision,
        },
    }))
}

/// Write `obj`'s files under a fresh directory and snapshot the main one.
fn run_one(obj: &Value) -> io::Result<Value> {
    let id = obj["id"].as_str().unwrap_or_default().to_string();
    let text = obj["text"]
        .as_str()
        .ok_or_else(|| invalid(format!("input {id:?}: no string `text`")))?;
    let main = obj["main"].as_str().unwrap_or("main.beancount");
    let dir = tempfile::tempdir()?;
    let mut files: Vec<(&str, &str)> = vec![(main, text)];
    if let Some(map) = obj["files"].as_object() {
        for (path, body) in map {
            let body = body
                .as_str()
                .ok_or_else(|| invalid(format!("input {id:?}: file {path:?} is not a string")))?;
            files.push((path, body));
        }
    }
    for (rel, body) in files {
        if Path::new(rel).is_absolute() || rel.split('/').any(|c| c == "..") {
            return Err(invalid(format!(
                "input {id:?}: path {rel:?} leaves the input"
            )));
        }
        let path = dir.path().join(rel);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(path, body)?;
    }
    let main_path = dir.path().join(main);
    let result = std::panic::catch_unwind(|| snapshot(dir.path(), &main_path));
    Ok(match result {
        Ok(Ok(snap)) => json!({ "id": id, "snapshot": snap }),
        Ok(Err(why)) => json!({ "id": id, "crash": why }),
        Err(panic) => {
            let why = panic
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| panic.downcast_ref::<&str>().map(|s| (*s).to_string()))
                .unwrap_or_default();
            json!({ "id": id, "crash": format!("panicked: {why}") })
        }
    })
}

fn main() -> io::Result<()> {
    if let Some(other) = std::env::args().nth(1) {
        return Err(invalid(format!("unknown argument {other:?}")));
    }
    let stdin = io::stdin();
    let mut out = BufWriter::new(io::stdout());
    for (n, line) in stdin.lock().lines().enumerate() {
        let line = line?;
        if line.trim().is_empty() {
            continue;
        }
        let obj: Value = serde_json::from_str(&line)
            .map_err(|e| invalid(format!("input line {}: {e}", n + 1)))?;
        writeln!(out, "{}", run_one(&obj)?)?;
    }
    out.flush()
}
