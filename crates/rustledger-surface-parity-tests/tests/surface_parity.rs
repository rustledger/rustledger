//! Every diagnostic surface reports what `rledger check` reports, on every
//! ledger of a shared corpus.
//!
//! The recurring bug class this guards against: a surface (WASM, the FFI
//! component, the LSP) re-derives part of `rledger check`'s pipeline, and the
//! copy drifts (#2937, #2946, #2952, #2971, ...). The hand-written cases of
//! `rustledger-loader/tests/surface_agreement/cases.rs` pin one shape each;
//! this test is the differential half: it runs every ledger of the corpus
//! through every surface and asserts that each reports exactly the
//! diagnostics `check` reports, normalized to `(file, line, code, message,
//! severity)` and compared whole, as sorted lists. It also compares the
//! booked directives and a query answer where a surface exposes them.
//!
//! The surfaces, each called natively as Rust:
//!
//! - `rledger check --format json`, through the library entry point the
//!   binary runs (`cmd::check::run_with_writer`): the reference;
//! - WASM: `validateSource`, `ParsedLedger` (and restored from its cache),
//!   `validateMultiFile`, `Ledger.fromFiles` (and restored from its cache),
//!   through `rustledger_wasm::surface_probe`, which runs each export's body;
//! - the FFI component: `validate`, `load`, `validate-file`, `load-file`,
//!   `query`, `query-file`, through `rustledger_ffi_component::surface_probe`,
//!   the functions the exports delegate to;
//! - the LSP: `all_diagnostics` for a ledger that includes nothing (what the
//!   server publishes for a single file), and the real server, through the
//!   protocol harness, for a ledger with includes (what it publishes for every
//!   file of the ledger).
//!
//! A legitimate difference is an entry of [`ALLOWED`], which names the
//! surfaces, the corpus files, the codes it takes out of the comparison and
//! why. Every entry must still be needed, so a fixed divergence fails here
//! until its entry goes.

#![allow(missing_docs)]

#[allow(
    dead_code,
    unused_imports,
    clippy::all,
    clippy::pedantic,
    clippy::nursery
)]
#[path = "../../rustledger-lsp/tests/lsp_protocol/harness.rs"]
mod harness;

// The ledgers of the hand-written drift guards (#2937, #2949), which every
// surface's own test runs against bean-check's findings.
include!("../../rustledger-loader/tests/surface_agreement/cases.rs");

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::{Path, PathBuf};

use clap::Parser as _;

/// One diagnostic, normalized: `(file, line, code, message, severity)`.
///
/// `file` is relative to the ledger's directory, or absolute outside it; a
/// single-source surface, which has one file and names none, reports the
/// entry file. `line` is 1-based, `0` when the diagnostic has no location.
type Diag = (String, u32, String, String, String);

// ---------------------------------------------------------------------------
// Legitimate differences
// ---------------------------------------------------------------------------

/// The single-source surfaces: one text, no file, no directory.
const SINGLE_SOURCE: &[&str] = &[
    "wasm validateSource",
    "wasm ParsedLedger",
    "wasm ParsedLedger fromCache",
    "ffi validate",
    "ffi load",
];

/// The WASM surfaces over a file map: a virtual filesystem holding the files
/// under the ledger's directory, and nothing else.
const VFS: &[&str] = &[
    "wasm validateMultiFile",
    "wasm Ledger",
    "wasm Ledger fromCache",
];

/// One diagnostic an allowed difference takes out of the comparison: the
/// corpus file (relative to the workspace root) it is reported for, its code
/// and its line (`0`: no location).
type Item = (&'static str, &'static str, u32);

/// A legitimate difference between `check` and some surfaces.
struct Allowed {
    /// The surfaces it applies to.
    surfaces: &'static [&'static [&'static str]],
    /// Diagnostics `check` reports and these surfaces do not.
    check: &'static [Item],
    /// Diagnostics these surfaces report and `check` does not.
    surface: &'static [Item],
    /// Why the surfaces cannot, or deliberately do not, report as `check`.
    reason: &'static str,
}

/// The legitimate differences in diagnostics. Keep this short: an entry is a
/// decision, not a way to make a red test green.
const ALLOWED: &[Allowed] = &[
    Allowed {
        surfaces: &[&["lsp"]],
        check: &[
            (UNKNOWN_PLUGIN, "E8004", 0),
            (WASM_PLUGIN, "PLUGIN", 0),
            (GRAMMAR_PLUGIN, "E8004", 0),
            (PYTHON_PLUGINS, "PLUGIN", 21),
            (UC_PLUGIN_IMPORT, "E8004", 0),
        ],
        surface: &[
            (UC_PLUGIN_IMPORT, "E8006", 1),
            (UNKNOWN_PLUGIN, "E8006", 3),
            (WASM_PLUGIN, "E8006", 2),
            (GRAMMAR_PLUGIN, "E8006", 2),
            (PYTHON_PLUGINS, "E8006", 12),
        ],
        reason: "The LSP never runs a WASM or Python plugin (`lsp_load_options`: \
                 `native_plugins_only`, #2486). It says so with an E8006 note at the \
                 `plugin` line, where `check` runs the plugin and reports what it says.",
    },
    Allowed {
        surfaces: &[SINGLE_SOURCE, VFS],
        check: &[(WASM_PLUGIN, "PLUGIN", 0), (PYTHON_PLUGINS, "PLUGIN", 21)],
        surface: &[(WASM_PLUGIN, "PLUGIN", 0), (PYTHON_PLUGINS, "E8002", 0)],
        reason: "No disk: a plugin named by a relative path (`passthrough.wasm`, \
                 `./error_plugin.py`) is read from the disk, next to the ledger, and a \
                 source string or a file map has no place on it.",
    },
    Allowed {
        surfaces: &[SINGLE_SOURCE, VFS],
        check: &[
            (DOC_DISCOVERY_UNKNOWN, "PLUGIN", 0),
            (UC_DOC_INVALID_DATE, "PLUGIN", 0),
            (UC_DOC_MISSING_ROOT, "E7006", 1),
            (OPTION_LIST, "E7006", 1),
            (OPTION_LIST, "E7006", 2),
            (OPTION_LIST, "E7006", 3),
        ],
        surface: &[],
        reason: "No disk: `option \"documents\"` roots are not checked (E7006) nor \
                 searched (document discovery) from a source string or a file map, \
                 which read no directory.",
    },
    Allowed {
        surfaces: &[
            &[
                "wasm validateSource",
                "wasm ParsedLedger",
                "wasm ParsedLedger fromCache",
                "ffi validate",
            ],
            VFS,
        ],
        check: &[],
        surface: &[(DOC_EXPLICIT, "E8001", 9)],
        reason: "No disk: a relative `document` path resolves next to the ledger's \
                 file, and these surfaces are given no file on disk to resolve it \
                 against (`ffi load` is, by its `filename`, and agrees).",
    },
    Allowed {
        surfaces: &[VFS],
        check: &[
            (PATH_TRAVERSAL, "P0012", ANY_LINE),
            (INCLUDE_CYCLE_INCLUDED, "E0004", 1),
            (INCLUDE_CYCLE_INCLUDED, "E1001", 1),
            (INCLUDE_CYCLE_INCLUDED, "E1001", 3),
        ],
        surface: &[
            (PATH_TRAVERSAL, "E0001", 5),
            (INCLUDE_CYCLE_INCLUDED, "E0001", 1),
        ],
        reason: "The file map holds the files under the ledger's directory, and these \
                 ledgers include a file above it.",
    },
    Allowed {
        surfaces: &[&["ffi validate-file"]],
        check: &[
            (PATH_TRAVERSAL, "P0012", ANY_LINE),
            (INCLUDE_ABSOLUTE, "E0001", 1),
            (INCLUDE_CYCLE_INCLUDED, "E0004", 1),
            (INCLUDE_CYCLE_INCLUDED, "E1001", 1),
            (INCLUDE_CYCLE_INCLUDED, "E1001", 3),
        ],
        surface: &[
            (PATH_TRAVERSAL, "E0003", 0),
            (INCLUDE_ABSOLUTE, "E0003", 0),
            (INCLUDE_CYCLE_INCLUDED, "E0003", 0),
        ],
        reason: "`validate-file` confines includes to the ledger's directory, the \
                 component's safe default; `check` does not. (`load-file` is run with \
                 `allow-unrestricted-includes`, and agrees.)",
    },
    Allowed {
        surfaces: &[VFS],
        check: &[
            (CYCLE_A, "E0002", 2),
            (CYCLE_B, "E0002", 2),
            (MISSING_INCLUDE, "E0001", 2),
            (INCLUDE_ABSOLUTE, "E0001", 1),
            (INCLUDE_CYCLE, "E0004", 1),
            (INCLUDE_DUPLICATE, "E0004", 1),
            (INCLUDE_RELATIVE, "E0001", 1),
            (UC_DUPLICATE_INCLUDE, "E0004", 1),
        ],
        surface: &[
            (CYCLE_A, "E0002", 2),
            (CYCLE_B, "E0002", 2),
            (MISSING_INCLUDE, "E0001", 2),
            (INCLUDE_ABSOLUTE, "E0001", 1),
            (INCLUDE_CYCLE, "E0004", 1),
            (INCLUDE_DUPLICATE, "E0004", 1),
            (INCLUDE_RELATIVE, "E0001", 1),
            (UC_DUPLICATE_INCLUDE, "E0004", 1),
        ],
        reason: "The same load error, code and line, in the file map's words: its \
                 files are named by their keys (`cycle_a.beancount`), not their paths \
                 on disk, and a missing one is `file not found in virtual filesystem`, \
                 not the operating system's error.",
    },
    // OPEN, not a decision: found by the upstream-check case ledgers. A
    // balance assertion `check_closing` synthesizes is located at
    // `<check_closing>`, 0 by `check` (as beancount places it), and in the
    // ledger file, at line 0, by every other surface.
    Allowed {
        surfaces: &[SINGLE_SOURCE, &["lsp"]],
        check: &[(UC_CHECK_CLOSING, "E2001", 0)],
        surface: &[(UC_CHECK_CLOSING, "E2001", 0)],
        reason: "OPEN: `check` names a plugin-synthesized balance's placeholder file \
                 (`<check_closing>`), the other surfaces the ledger file.",
    },
];

/// An [`Item`] line that matches every line: the parse errors of a file that
/// is not a ledger at all.
const ANY_LINE: u32 = u32::MAX;

// The corpus files the allowed differences name.
const UNKNOWN_PLUGIN: &str = "crates/rustledger-loader/tests/fixtures/unknown_plugin.beancount";
const WASM_PLUGIN: &str = "crates/rustledger-loader/tests/fixtures/with_wasm_plugin.beancount";
const GRAMMAR_PLUGIN: &str =
    "tests/fixtures/lima-tests/LexerAndParserErrors.GrammarExceptionsPlugin.beancount";
const PYTHON_PLUGINS: &str = "tests/fixtures/python-plugins/with_plugins.beancount";
const DOC_DISCOVERY: &str = "crates/rustledger-loader/tests/fixtures/doc_discovery.beancount";
const DOC_DISCOVERY_UNKNOWN: &str =
    "crates/rustledger-loader/tests/fixtures/doc_discovery_unknown.beancount";
const DOC_EXPLICIT: &str =
    "crates/rustledger-loader/tests/fixtures/doc_discovery_with_explicit.beancount";
const OPTION_LIST: &str = "tests/fixtures/lima-tests/ParserOptions.OptionListValue.beancount";
const PATH_TRAVERSAL: &str = "crates/rustledger-loader/tests/fixtures/path_traversal.beancount";
const CYCLE_A: &str = "crates/rustledger-loader/tests/fixtures/cycle_a.beancount";
const CYCLE_B: &str = "crates/rustledger-loader/tests/fixtures/cycle_b.beancount";
const MISSING_INCLUDE: &str = "crates/rustledger-loader/tests/fixtures/missing_include.beancount";
const INCLUDE_ABSOLUTE: &str = "tests/fixtures/lima-tests/ParserInclude.IncludeAbsolute.beancount";
const INCLUDE_CYCLE: &str = "tests/fixtures/lima-tests/ParserInclude.IncludeCycle.beancount";
const INCLUDE_CYCLE_INCLUDED: &str =
    "tests/fixtures/lima-tests/ParserInclude.IncludeCycle/Included1.beancount";
// The upstream-check case ledgers (`crates/rustledger/tests/upstream_checks_test.rs`).
const UC_PLUGIN_IMPORT: &str =
    "crates/rustledger/tests/fixtures/upstream-checks/cases/loader-plugin-import-error.beancount";
const UC_DOC_INVALID_DATE: &str =
    "crates/rustledger/tests/fixtures/upstream-checks/cases/documents-invalid-date.beancount";
const UC_DOC_MISSING_ROOT: &str =
    "crates/rustledger/tests/fixtures/upstream-checks/cases/documents-missing-root.beancount";
const UC_DUPLICATE_INCLUDE: &str =
    "crates/rustledger/tests/fixtures/upstream-checks/cases/loader-duplicate-include.beancount";
const UC_CHECK_CLOSING: &str =
    "crates/rustledger/tests/fixtures/upstream-checks/cases/plugin-check-closing.beancount";
const INCLUDE_DUPLICATE: &str =
    "tests/fixtures/lima-tests/ParserInclude.IncludeDuplicate.beancount";
const INCLUDE_RELATIVE: &str =
    "tests/fixtures/lima-tests/ParserInclude.IncludeRelativeFromString.beancount";

/// A legitimate difference in the booked directives: the surfaces book the
/// corpus files' directives differently from `check`, for the reason given.
struct AllowedBooking {
    surfaces: &'static [&'static str],
    files: &'static [&'static str],
    reason: &'static str,
}

/// The legitimate differences in booked directives.
const ALLOWED_BOOKING: &[AllowedBooking] = &[
    AllowedBooking {
        surfaces: &[
            "wasm ParsedLedger",
            "wasm ParsedLedger fromCache",
            "ffi load",
            "wasm Ledger",
            "wasm Ledger fromCache",
        ],
        files: &[DOC_DISCOVERY, DOC_EXPLICIT],
        reason: "No disk: document discovery reads the `option \"documents\"` \
                 directories, which a source string or a file map does not reach.",
    },
    AllowedBooking {
        surfaces: &["wasm Ledger", "wasm Ledger fromCache"],
        files: &[INCLUDE_CYCLE_INCLUDED],
        reason: "The file map holds the files under the ledger's directory, and this \
                 ledger includes a file above it.",
    },
];

// ---------------------------------------------------------------------------
// The corpus
// ---------------------------------------------------------------------------

/// Repo-relative directories of the corpus: the compatibility files, the
/// fixtures (parse, booking, validation, plugin, include and option errors),
/// the regressions, and the loader's and CLI's test ledgers.
const CORPUS_DIRS: &[&str] = &[
    "tests/compatibility/files",
    "tests/fixtures",
    "tests/regressions",
    "crates/rustledger-loader/tests",
    "crates/rustledger/tests",
];

fn workspace_root() -> PathBuf {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    root.canonicalize().unwrap_or(root)
}

fn corpus_files() -> Vec<PathBuf> {
    let root = workspace_root();
    let mut files = Vec::new();
    let mut stack: Vec<PathBuf> = CORPUS_DIRS.iter().map(|d| root.join(d)).collect();
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|e| e == "beancount") {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}

/// `file` relative to `dir` when it is under it.
fn rel(file: &str, dir: &Path) -> String {
    Path::new(file)
        .strip_prefix(dir)
        .map_or_else(|_| file.to_string(), |r| r.display().to_string())
}

/// A file a single-source surface names: `<string>` is the source, named as
/// beancount's `load_string` names it, which is the entry file here.
fn source_name(file: &str, entry: &str, dir: &Path) -> String {
    if file == "<string>" {
        entry.to_string()
    } else {
        rel(file, dir)
    }
}

// ---------------------------------------------------------------------------
// The surfaces
// ---------------------------------------------------------------------------

/// `rledger check --format json`, run in-process through the library entry
/// point the binary runs.
fn cli(dir: &Path, entry: &str) -> Vec<Diag> {
    // The entry as `<dir>/./<entry>`: `check` names a diagnostic with no
    // location by the path it was given, at line 1, and a located one by the
    // loader's normalized path, so the stand-in cannot be mistaken for a real
    // line 1 (the trick of `rustledger/tests/ffi_check_parity_test.rs`).
    let given = dir.join(".").join(entry);
    let given_str = given.display().to_string();
    let args = rustledger::cmd::check::Args::parse_from([
        "check".as_ref(),
        "--no-cache".as_ref(),
        "--format".as_ref(),
        "json".as_ref(),
        given.as_os_str(),
    ]);
    let mut out = Vec::new();
    let mut err = Vec::new();
    // The exit code follows from the diagnostics, which are compared.
    let _exit =
        rustledger::cmd::check::run_with_writer(&args, &mut out, &mut err).expect("rledger check");
    let value: serde_json::Value = serde_json::from_slice(&out).expect("check json");
    value["diagnostics"]
        .as_array()
        .expect("diagnostics")
        .iter()
        .map(|d| {
            let file = d["file"].as_str().expect("file");
            let line = u32::try_from(d["line"].as_u64().expect("line")).expect("u32 line");
            let (file, line) = if file == given_str {
                assert_eq!(line, 1, "{given_str}: the no-location stand-in is line 1");
                (entry.to_string(), 0)
            } else {
                (rel(file, dir), line)
            };
            (
                file,
                line,
                d["code"].as_str().expect("code").to_string(),
                d["message"].as_str().expect("message").to_string(),
                d["severity"].as_str().expect("severity").to_string(),
            )
        })
        .collect()
}

fn wasm(errors: &[rustledger_wasm::types::Error], entry: &str, dir: &Path) -> Vec<Diag> {
    errors
        .iter()
        .map(|e| {
            (
                e.file
                    .as_deref()
                    .map_or_else(|| entry.to_string(), |f| source_name(f, entry, dir)),
                e.line.unwrap_or_default(),
                e.code.clone().unwrap_or_default(),
                e.message.clone(),
                match e.severity {
                    rustledger_wasm::types::Severity::Error => "error",
                    rustledger_wasm::types::Severity::Warning => "warning",
                }
                .to_string(),
            )
        })
        .collect()
}

fn ffi(
    errors: &[rustledger_ffi_component::surface_probe::Error],
    entry: &str,
    dir: &Path,
) -> Vec<Diag> {
    errors
        .iter()
        .map(|e| {
            (
                e.filename
                    .as_deref()
                    .map_or_else(|| entry.to_string(), |f| source_name(f, entry, dir)),
                e.line.unwrap_or_default(),
                e.code.clone().unwrap_or_default(),
                e.message.clone(),
                e.severity.clone(),
            )
        })
        .collect()
}

/// What the LSP publishes for a ledger that includes nothing: the server
/// calls `all_diagnostics` with no ledger state for it.
fn lsp(source: &str, path: &Path, entry: &str) -> Vec<Diag> {
    let parsed = rustledger_parser::parse(source);
    rustledger_lsp::handlers::diagnostics::all_diagnostics(
        &parsed,
        source,
        None,
        None,
        Some(path),
        &[],
        rustledger_lsp::handlers::utils::PositionEncoding::Utf16,
    )
    .into_iter()
    .map(|d| lsp_diag(entry.to_string(), d))
    .collect()
}

/// The real LSP server, loaded with `path` as its journal and with `path`
/// open: what it publishes for every file of the ledger (the open buffer's
/// own diagnostics, and the unopened included files' from the whole-ledger
/// validation).
fn lsp_server(path: &Path, source: &str, dir: &Path) -> Vec<Diag> {
    use lsp_server::{Message, Request, RequestId};
    use lsp_types::PublishDiagnosticsParams;

    let mut client = harness::LspTestClient::spawn_with_journal(Some(path.to_path_buf()));
    client.initialize();
    let uri = harness::uri_for(path);
    client.open_document(&uri, source);
    // The server handles messages in order, so every notification the
    // `didOpen` publishes arrives before the answer to a request sent after it.
    let id: RequestId = client.next_request_id();
    client
        .raw_send_request(Request {
            id: id.clone(),
            method: "textDocument/documentSymbol".to_string(),
            params: serde_json::json!({ "textDocument": { "uri": uri } }),
        })
        .expect("send");
    let mut published: BTreeMap<String, Vec<lsp_types::Diagnostic>> = BTreeMap::new();
    loop {
        match client.recv_with_timeout(harness::DEFAULT_TIMEOUT) {
            Some(Message::Response(r)) if r.id == id => break,
            Some(Message::Notification(n)) if n.method == "textDocument/publishDiagnostics" => {
                let params: PublishDiagnosticsParams =
                    serde_json::from_value(n.params).expect("publishDiagnostics");
                let file = rustledger_lsp::uri_to_path(&params.uri).expect("file uri");
                let file = file.as_path();
                let file = std::fs::canonicalize(file).unwrap_or_else(|_| file.to_path_buf());
                // The latest publication for a file is what the editor shows.
                published.insert(rel(&file.display().to_string(), dir), params.diagnostics);
            }
            Some(_) => {}
            None => panic!("{}: the LSP did not answer", path.display()),
        }
    }
    published
        .into_iter()
        .flat_map(|(file, diags)| diags.into_iter().map(move |d| lsp_diag(file.clone(), d)))
        .collect()
}

/// An LSP diagnostic, normalized.
///
/// A validation diagnostic's message carries, in a fixed layout
/// (`validation_error_to_diagnostic`), what `check`'s JSON puts in fields of
/// their own: `<message> (<date>)`, then `\n  context: ...`, `\n  hint: ...`
/// and `\n  (source location unknown)`. That layout is taken apart exactly,
/// so the message compared is the validator's, as `check` reports it; a
/// message without the date suffix is compared whole. An LSP diagnostic must
/// have a range: one with none is an empty range at the file's start.
fn lsp_diag(file: String, d: lsp_types::Diagnostic) -> Diag {
    use lsp_types::{DiagnosticSeverity, NumberOrString, Position};
    let origin = Position::new(0, 0);
    let unknown = d.message.strip_suffix("\n  (source location unknown)");
    let mut message = unknown.unwrap_or(&d.message);
    let line = if unknown.is_some() || (d.range.start == origin && d.range.end == origin) {
        0
    } else {
        d.range.start.line + 1
    };
    let head = message.split("\n  context: ").next().unwrap_or(message);
    let head = head.split("\n  hint: ").next().unwrap_or(head);
    if let Some(base) = strip_date_suffix(head) {
        message = base;
    }
    (
        file,
        line,
        match d.code {
            Some(NumberOrString::String(s)) => s,
            Some(NumberOrString::Number(n)) => n.to_string(),
            None => String::new(),
        },
        message.to_string(),
        match d.severity {
            Some(DiagnosticSeverity::ERROR) => "error",
            Some(DiagnosticSeverity::WARNING) => "warning",
            Some(DiagnosticSeverity::INFORMATION) => "information",
            Some(DiagnosticSeverity::HINT) => "hint",
            _ => "",
        }
        .to_string(),
    )
}

/// `message` without a trailing ` (YYYY-MM-DD)`, if it has one.
fn strip_date_suffix(message: &str) -> Option<&str> {
    let base = message.strip_suffix(')')?;
    let (base, date) = base.rsplit_once(" (")?;
    let bytes = date.as_bytes();
    let is_date = bytes.len() == 10
        && bytes.iter().enumerate().all(|(i, b)| {
            if i == 4 || i == 7 {
                *b == b'-'
            } else {
                b.is_ascii_digit()
            }
        });
    is_date.then_some(base)
}

/// Every file under `dir`, keyed relative to it, for the file-map surfaces.
fn file_map(dir: &Path) -> HashMap<String, String> {
    let mut map = HashMap::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        for entry in std::fs::read_dir(&d).into_iter().flatten().flatten() {
            let p = entry.path();
            if p.is_dir() {
                stack.push(p);
            } else if let Ok(text) = std::fs::read_to_string(&p) {
                let key = p
                    .strip_prefix(dir)
                    .expect("under dir")
                    .display()
                    .to_string();
                map.insert(key, text);
            }
        }
    }
    map
}

// ---------------------------------------------------------------------------
// Booked directives and query answers
// ---------------------------------------------------------------------------

/// A booked directive, as compared: its kind, date and line, and what booking
/// decides, the postings' accounts, units and costs.
fn core_fingerprint(d: &rustledger_core::Directive) -> String {
    use rustledger_core::{CostNumber, Directive as D};
    let cost_number = |n: CostNumber| match n {
        CostNumber::PerUnit { value } => format!("per-unit {value}"),
        CostNumber::Total { value } => format!("total {value}"),
        CostNumber::PerUnitFromTotal(b) => format!("from-total {} {}", b.per_unit, b.total),
        CostNumber::Compound { per_unit, total } => format!("compound {per_unit} {total}"),
    };
    match d {
        D::Transaction(t) => {
            let postings: Vec<String> = t
                .postings
                .iter()
                .map(|p| {
                    let units = p
                        .units
                        .as_ref()
                        .and_then(|u| u.as_amount())
                        .map(|a| format!("{} {}", a.number, a.currency));
                    let cost = p.cost.as_deref().map(|c| {
                        format!(
                            "{:?} {:?} {:?} {:?}",
                            c.number.map(cost_number),
                            c.currency.as_ref().map(ToString::to_string),
                            c.date.map(|d| d.to_string()),
                            c.label
                        )
                    });
                    format!("{} {units:?} {cost:?}", p.account)
                })
                .collect();
            format!("{} transaction {postings:?}", t.date)
        }
        D::Open(o) => format!("{} open {}", o.date, o.account),
        D::Close(c) => format!("{} close {}", c.date, c.account),
        D::Balance(b) => format!(
            "{} balance {} {} {}",
            b.date, b.account, b.amount.number, b.amount.currency
        ),
        D::Pad(p) => format!("{} pad {} {}", p.date, p.account, p.source_account),
        D::Commodity(c) => format!("{} commodity {}", c.date, c.currency),
        D::Price(p) => format!(
            "{} price {} {} {}",
            p.date, p.currency, p.amount.number, p.amount.currency
        ),
        D::Event(e) => format!("{} event {}", e.date, e.event_type),
        D::Note(n) => format!("{} note {}", n.date, n.account),
        D::Document(d) => format!("{} document {}", d.date, d.account),
        D::Query(q) => format!("{} query {}", q.date, q.name),
        D::Custom(c) => format!("{} custom {}", c.date, c.custom_type),
    }
}

/// [`core_fingerprint`] of an FFI directive.
fn wit_fingerprint(d: &rustledger_ffi_component::surface_probe::Directive) -> String {
    use rustledger_ffi_component::surface_probe::{CostNumber, Directive as D};
    let cost_number = |n: &CostNumber| match n {
        CostNumber::PerUnit(v) => format!("per-unit {v}"),
        CostNumber::Total(v) => format!("total {v}"),
        CostNumber::PerUnitFromTotal((p, t)) => format!("from-total {p} {t}"),
        CostNumber::Compound((p, t)) => format!("compound {p} {t}"),
    };
    match d {
        D::Transaction(t) => {
            let postings: Vec<String> = t
                .postings
                .iter()
                .map(|p| {
                    let units = p
                        .units
                        .as_ref()
                        .map(|a| format!("{} {}", a.number, a.currency));
                    let cost = p.cost.as_ref().map(|c| {
                        format!(
                            "{:?} {:?} {:?} {:?}",
                            c.number.as_ref().map(cost_number),
                            c.currency,
                            c.date,
                            c.label
                        )
                    });
                    format!("{} {units:?} {cost:?}", p.account)
                })
                .collect();
            format!("{} transaction {postings:?}", t.date)
        }
        D::Open(o) => format!("{} open {}", o.date, o.account),
        D::Close(c) => format!("{} close {}", c.date, c.account),
        D::Balance(b) => format!(
            "{} balance {} {} {}",
            b.date, b.account, b.amount.number, b.amount.currency
        ),
        D::Pad(p) => format!("{} pad {} {}", p.date, p.account, p.source_account),
        D::Commodity(c) => format!("{} commodity {}", c.date, c.currency),
        D::Price(p) => format!(
            "{} price {} {} {}",
            p.date, p.currency, p.amount.number, p.amount.currency
        ),
        D::Event(e) => format!("{} event {}", e.date, e.event_type),
        D::Note(n) => format!("{} note {}", n.date, n.account),
        D::Document(d) => format!("{} document {}", d.date, d.account),
        D::Query(q) => format!("{} query {}", q.date, q.name),
        D::Custom(c) => format!("{} custom {}", c.date, c.custom_type),
    }
}

/// The booked directives of the validating load `check` runs.
fn canonical_directives(path: &Path) -> Vec<String> {
    let ledger = rustledger_loader::load(path, &rustledger_loader::LoadOptions::default())
        .expect("canonical load");
    ledger
        .directives
        .iter()
        .map(|d| core_fingerprint(&d.value))
        .collect()
}

/// The query whose answer every query surface must give: per account and
/// currency, the sum of the booked units.
const QUERY: &str = "SELECT account, currency, sum(number) AS total \
                     GROUP BY account, currency ORDER BY account, currency";

/// `rledger query --format json`, in-process: each row's cells as strings.
fn cli_query(path: &Path) -> Vec<Vec<String>> {
    let args = rustledger::cmd::query::Args::parse_from([
        "query".as_ref(),
        "--no-cache".as_ref(),
        "--format".as_ref(),
        "json".as_ref(),
        path.as_os_str(),
        QUERY.as_ref(),
    ]);
    let mut out = Vec::new();
    let mut err = Vec::new();
    rustledger::cmd::query::run_with_writer(&args, &mut out, None, &mut err)
        .expect("rledger query");
    let value: serde_json::Value = serde_json::from_slice(&out).expect("query json");
    value["rows"]
        .as_array()
        .expect("rows")
        .iter()
        .map(|row| {
            row.as_array()
                .expect("row")
                .iter()
                .map(|cell| {
                    cell.as_str()
                        .map_or_else(|| cell.to_string(), str::to_string)
                })
                .collect()
        })
        .collect()
}

/// An FFI query answer: each row's cells as strings. Its `errors` are the
/// load's diagnostics reported beside the rows, as `rledger query` reports
/// them on stderr, so they are not part of the answer; a refusal has no rows.
fn ffi_query(result: &rustledger_ffi_component::surface_probe::QueryResult) -> Vec<Vec<String>> {
    use rustledger_ffi_component::surface_probe::QueryValue as V;
    result
        .rows
        .iter()
        .map(|row| {
            row.iter()
                .map(|cell| match cell {
                    V::Text(s) | V::Number(s) | V::Date(s) => s.clone(),
                    other => format!("{other:?}"),
                })
                .collect()
        })
        .collect()
}

// ---------------------------------------------------------------------------
// The test
// ---------------------------------------------------------------------------

/// One surface's output for one corpus file, set beside `check`'s.
struct Compared<T> {
    surface: &'static str,
    got: T,
}

#[test]
fn every_surface_reports_what_check_reports() {
    let start = std::time::Instant::now();
    let root = workspace_root();
    let files = corpus_files();
    assert!(
        files.len() >= 300,
        "the corpus walk found only {} files: walker or checkout broken",
        files.len()
    );

    let mut failures: Vec<String> = Vec::new();
    let mut used: BTreeSet<(usize, &str, usize, &str)> = BTreeSet::new();
    let mut used_booking: BTreeSet<(usize, &str, String)> = BTreeSet::new();
    let (mut single, mut multi, mut queried) = (0usize, 0usize, 0usize);

    // The hand-written cases every surface's own drift guard runs, each
    // written out as a ledger of its own, after the corpus files.
    let cases = tempfile::tempdir().expect("tempdir");
    let mut inputs: Vec<(PathBuf, Option<String>)> =
        files.iter().map(|f| (f.clone(), None)).collect();
    for (i, case) in SURFACE_CASES.iter().enumerate() {
        let dir = cases.path().join(format!("case{i}"));
        std::fs::create_dir(&dir).expect("case dir");
        let path = dir.join("ledger.beancount");
        std::fs::write(&path, case.source).expect("write case");
        inputs.push((
            path,
            Some(format!("surface_agreement case `{}`", case.name)),
        ));
    }

    for (path, case_name) in &inputs {
        let Ok(source) = std::fs::read_to_string(path) else {
            continue; // not UTF-8: no surface takes it as text
        };
        let path = path.canonicalize().expect("canonical path");
        let dir = path.parent().expect("parent").to_path_buf();
        let entry = path
            .file_name()
            .expect("name")
            .to_string_lossy()
            .to_string();
        let name = case_name.clone().unwrap_or_else(|| {
            path.strip_prefix(&root)
                .unwrap_or(&path)
                .display()
                .to_string()
        });
        let path_str = path.to_str().expect("utf-8 path");
        let has_include = source
            .lines()
            .any(|l| l.trim_start().starts_with("include "));

        let reference = cli(&dir, &entry);
        let mut diagnostics: Vec<Compared<Vec<Diag>>> = Vec::new();
        let mut booked: Vec<Compared<Vec<String>>> = Vec::new();
        let push = |v: &mut Vec<Compared<Vec<Diag>>>, surface, got| {
            v.push(Compared { surface, got });
        };

        // The single-source surfaces and the single-file LSP, for a ledger
        // that includes nothing: a source string cannot include.
        if has_include {
            multi += 1;
            push(
                &mut diagnostics,
                "lsp server",
                lsp_server(&path, &source, &dir),
            );
        } else {
            single += 1;
            let errors = rustledger_wasm::surface_probe::validate_source(&source);
            push(
                &mut diagnostics,
                "wasm validateSource",
                wasm(&errors, &entry, &dir),
            );
            let [fresh, cached] = rustledger_wasm::surface_probe::parsed_ledger(&source);
            push(
                &mut diagnostics,
                "wasm ParsedLedger",
                wasm(&fresh.0, &entry, &dir),
            );
            push(
                &mut diagnostics,
                "wasm ParsedLedger fromCache",
                wasm(&cached.0, &entry, &dir),
            );
            for (surface, (_, directives)) in [
                ("wasm ParsedLedger", fresh),
                ("wasm ParsedLedger fromCache", cached),
            ] {
                let got = directives.iter().map(core_fingerprint).collect();
                booked.push(Compared { surface, got });
            }
            let validated = rustledger_ffi_component::surface_probe::validate(&source);
            push(
                &mut diagnostics,
                "ffi validate",
                ffi(&validated.errors, &entry, &dir),
            );
            // Named by its path, as an embedder names the text it loads.
            let loaded = rustledger_ffi_component::surface_probe::load(&source, path_str, false);
            push(
                &mut diagnostics,
                "ffi load",
                ffi(&loaded.errors, &entry, &dir),
            );
            booked.push(Compared {
                surface: "ffi load",
                got: loaded.entries.iter().map(wit_fingerprint).collect(),
            });
            push(&mut diagnostics, "lsp", lsp(&source, &path, &entry));
        }

        // The file surfaces, for every ledger.
        let map = file_map(&dir);
        match rustledger_wasm::surface_probe::validate_multi_file(map.clone(), &entry) {
            Ok(errors) => push(
                &mut diagnostics,
                "wasm validateMultiFile",
                wasm(&errors, &entry, &dir),
            ),
            Err(e) => failures.push(format!("{name}: validateMultiFile threw {e}")),
        }
        match rustledger_wasm::surface_probe::ledger(map, &entry) {
            Ok([fresh, cached]) => {
                push(
                    &mut diagnostics,
                    "wasm Ledger",
                    wasm(&fresh.0, &entry, &dir),
                );
                push(
                    &mut diagnostics,
                    "wasm Ledger fromCache",
                    wasm(&cached.0, &entry, &dir),
                );
                for (surface, (_, directives)) in
                    [("wasm Ledger", fresh), ("wasm Ledger fromCache", cached)]
                {
                    let got = directives.iter().map(core_fingerprint).collect();
                    booked.push(Compared { surface, got });
                }
            }
            Err(e) => failures.push(format!("{name}: Ledger.fromFiles threw {e}")),
        }
        let validated = rustledger_ffi_component::surface_probe::validate_file(path_str);
        push(
            &mut diagnostics,
            "ffi validate-file",
            ffi(&validated.errors, &entry, &dir),
        );
        let loaded = rustledger_ffi_component::surface_probe::load_file(path_str, true, &[], false);
        push(
            &mut diagnostics,
            "ffi load-file",
            ffi(&loaded.errors, &entry, &dir),
        );
        booked.push(Compared {
            surface: "ffi load-file",
            got: loaded.entries.iter().map(wit_fingerprint).collect(),
        });

        // Diagnostics: exactly `check`'s, but for an allowed difference.
        for Compared { surface, got } in diagnostics {
            let mut want = reference.clone();
            let mut got = got;
            for (i, allowed) in ALLOWED.iter().enumerate() {
                if !allowed.surfaces.iter().any(|g| g.contains(&surface)) {
                    continue;
                }
                for (side, items, diags) in [
                    ("check", allowed.check, &mut want),
                    ("surface", allowed.surface, &mut got),
                ] {
                    for (j, &(file, code, line)) in items.iter().enumerate() {
                        if file != name {
                            continue;
                        }
                        let before = diags.len();
                        diags.retain(|d| !(d.2 == code && (line == ANY_LINE || d.1 == line)));
                        if diags.len() != before {
                            used.insert((i, side, j, surface));
                        }
                    }
                }
            }
            want.sort();
            got.sort();
            if got != want {
                let only_check: Vec<_> = want.iter().filter(|d| !got.contains(d)).collect();
                let only_surface: Vec<_> = got.iter().filter(|d| !want.contains(d)).collect();
                for d in &only_check {
                    println!("DIFF {surface} | {name} | check | {} | {}", d.2, d.1);
                }
                for d in &only_surface {
                    println!("DIFF {surface} | {name} | surface | {} | {}", d.2, d.1);
                }
                failures.push(format!(
                    "{name}: {surface} disagrees with `rledger check`\n  \
                     check only: {only_check:#?}\n  {surface} only: {only_surface:#?}"
                ));
            }
        }

        // Booked directives: those of the validating load `check` runs.
        let canonical = canonical_directives(&path);
        for Compared { surface, got } in booked {
            let allowed = ALLOWED_BOOKING
                .iter()
                .position(|a| a.files.contains(&name.as_str()) && a.surfaces.contains(&surface));
            if got == canonical {
                continue;
            }
            if let Some(i) = allowed {
                used_booking.insert((i, surface, name.clone()));
                continue;
            }
            let first = got
                .iter()
                .zip(&canonical)
                .position(|(a, b)| a != b)
                .unwrap_or_else(|| got.len().min(canonical.len()));
            println!("BOOK {surface} | {name}");
            failures.push(format!(
                "{name}: {surface} books differently from `rledger check` ({} vs {} \
                 directives), first difference at {first}:\n  check: {:?}\n  {surface}: {:?}",
                canonical.len(),
                got.len(),
                canonical.get(first),
                got.get(first),
            ));
        }

        // A query answer, where the ledger has no error, so that `rledger
        // query` answers it (it refuses a ledger with load errors, #1908).
        if !has_include && reference.iter().all(|d| d.4 != "error") {
            queried += 1;
            let want = cli_query(&path);
            for (surface, result) in [
                (
                    "ffi query",
                    rustledger_ffi_component::surface_probe::query(&source, QUERY),
                ),
                (
                    "ffi query-file",
                    rustledger_ffi_component::surface_probe::query_file(path_str, QUERY),
                ),
            ] {
                let got = ffi_query(&result);
                if got != want {
                    failures.push(format!(
                        "{name}: {surface} answers differently from `rledger query`:\n  \
                         check: {want:?}\n  {surface}: {got:?}"
                    ));
                }
            }
        }
    }

    // Every allowed difference must still be one, on every surface it names
    // that ran on its file: a fixed divergence fails here until its entry
    // goes.
    for (i, allowed) in ALLOWED.iter().enumerate() {
        for surface in allowed.surfaces.iter().flat_map(|g| g.iter()) {
            for (side, items) in [("check", allowed.check), ("surface", allowed.surface)] {
                for (j, &(file, code, line)) in items.iter().enumerate() {
                    if surface_ran(surface, file) && !used.contains(&(i, side, j, *surface)) {
                        failures.push(format!(
                            "ALLOWED[{i}] no longer applies: {surface} on {file} agrees with \
                             `check` on {code} at line {line} ({side} side); remove it \
                             ({})",
                            allowed.reason
                        ));
                    }
                }
            }
        }
    }
    for (i, allowed) in ALLOWED_BOOKING.iter().enumerate() {
        for surface in allowed.surfaces {
            for file in allowed.files {
                if surface_ran(surface, file)
                    && !used_booking.contains(&(i, *surface, (*file).to_string()))
                {
                    failures.push(format!(
                        "ALLOWED_BOOKING[{i}] no longer applies: {surface} books {file} as \
                         `check` does; remove it ({})",
                        allowed.reason
                    ));
                }
            }
        }
    }

    let elapsed = start.elapsed();
    println!(
        "surface parity: {} ledgers ({single} single-file, {multi} with includes, {queried} \
         queried) in {elapsed:?}",
        inputs.len()
    );
    assert!(
        failures.is_empty(),
        "{} disagreement(s) with `rledger check`:\n\n{}",
        failures.len(),
        failures.join("\n\n")
    );
}

/// Whether `surface` runs on the corpus file `file`: the single-source
/// surfaces and the single-file LSP on a ledger that includes nothing, the
/// LSP server on one that includes something.
fn surface_ran(surface: &str, file: &str) -> bool {
    let source = std::fs::read_to_string(workspace_root().join(file)).unwrap_or_default();
    let has_include = source
        .lines()
        .any(|l| l.trim_start().starts_with("include "));
    if SINGLE_SOURCE.contains(&surface) || surface == "lsp" {
        !has_include
    } else if surface == "lsp server" {
        has_include
    } else {
        true
    }
}
