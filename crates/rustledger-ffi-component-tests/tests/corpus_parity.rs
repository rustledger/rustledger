//! Corpus-driven CLI↔FFI parity (improvement #2).
//!
//! The hand-written cases in `parity.rs` each pin one behavior; the recurring
//! bug class of the v0.17–v0.19 arc was *drift* between the native load path
//! and the component surface on inputs nobody wrote a case for. This test
//! feeds every self-contained `.beancount` file in the repo through BOTH
//! paths — `rustledger_ffi_wasi::helpers::load_source` (native) and the
//! component's `load` export — and diffs the outcome shape:
//!
//! - entry count, and per-entry (kind, date)
//! - load-phase error count (the component's `load` also runs semantic
//!   validation since #1663, so validation-phase errors are excluded — the
//!   native `load_source` deliberately does not validate)
//!
//! Skipped inputs: files using `include` (a source string has no include
//! root), non-UTF-8, and >200 KB (runtime bound). Skips are counted and
//! printed so a corpus regression (everything suddenly skipped) is visible.

#![allow(missing_docs)]
#![allow(clippy::all, clippy::pedantic, clippy::nursery)]

use anyhow::Result;
use wasmtime::component::{Component, Linker, ResourceTable};
use wasmtime::{Engine, Store};
use wasmtime_wasi::{WasiCtx, WasiCtxBuilder, WasiCtxView, WasiView};

wasmtime::component::bindgen!({
    world: "rustledger",
    path: "../rustledger-ffi-component/wit/world.wit",
});

struct Host {
    table: ResourceTable,
    wasi: WasiCtx,
}

impl WasiView for Host {
    fn ctx(&mut self) -> WasiCtxView<'_> {
        WasiCtxView {
            ctx: &mut self.wasi,
            table: &mut self.table,
        }
    }
}

impl rustledger::ledger::host::Host for Host {
    fn decrypt(&mut self, _ciphertext: Vec<u8>) -> Result<String, String> {
        Err("corpus test host does not decrypt".to_string())
    }
}

fn component_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/wasm32-wasip2/debug/rustledger_ffi_component.wasm")
}

fn instantiate() -> Result<(Store<Host>, Rustledger)> {
    let engine = Engine::default();
    let component = Component::from_file(&engine, component_path())?;
    let mut linker = Linker::<Host>::new(&engine);
    wasmtime_wasi::p2::add_to_linker_sync(&mut linker)?;
    rustledger::ledger::host::add_to_linker::<_, wasmtime::component::HasSelf<Host>>(
        &mut linker,
        |h| h,
    )?;
    let mut store = Store::new(
        &engine,
        Host {
            table: ResourceTable::new(),
            wasi: WasiCtxBuilder::new().build(),
        },
    );
    let inst = Rustledger::instantiate(&mut store, &component, &linker)?;
    Ok((store, inst))
}

/// Repo-relative directories to sweep for `.beancount` corpus files.
const CORPUS_DIRS: &[&str] = &["../../tests", "../../examples", "../../crates"];

const MAX_FILE_BYTES: u64 = 200 * 1024;

fn corpus_files() -> Vec<std::path::PathBuf> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut files = Vec::new();
    let mut stack: Vec<std::path::PathBuf> = CORPUS_DIRS.iter().map(|d| root.join(d)).collect();
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

/// A stable discriminator for a native core directive.
fn native_kind(d: &rustledger_core::Directive) -> (&'static str, String) {
    use rustledger_core::Directive as D;
    match d {
        D::Transaction(t) => ("transaction", t.date.to_string()),
        D::Open(o) => ("open", o.date.to_string()),
        D::Close(c) => ("close", c.date.to_string()),
        D::Balance(b) => ("balance", b.date.to_string()),
        D::Pad(p) => ("pad", p.date.to_string()),
        D::Commodity(c) => ("commodity", c.date.to_string()),
        D::Price(p) => ("price", p.date.to_string()),
        D::Event(e) => ("event", e.date.to_string()),
        D::Note(n) => ("note", n.date.to_string()),
        D::Document(d) => ("document", d.date.to_string()),
        D::Query(q) => ("query", q.date.to_string()),
        D::Custom(c) => ("custom", c.date.to_string()),
    }
}

/// The same discriminator for a component (WIT) directive.
fn wit_kind(d: &rustledger::ledger::types::Directive) -> (&'static str, String) {
    use rustledger::ledger::types::Directive as D;
    match d {
        D::Transaction(t) => ("transaction", t.date.clone()),
        D::Open(o) => ("open", o.date.clone()),
        D::Close(c) => ("close", c.date.clone()),
        D::Balance(b) => ("balance", b.date.clone()),
        D::Pad(p) => ("pad", p.date.clone()),
        D::Commodity(c) => ("commodity", c.date.clone()),
        D::Price(p) => ("price", p.date.clone()),
        D::Event(e) => ("event", e.date.clone()),
        D::Note(n) => ("note", n.date.clone()),
        D::Document(d) => ("document", d.date.clone()),
        D::Query(q) => ("query", q.date.clone()),
        D::Custom(c) => ("custom", c.date.clone()),
    }
}

#[test]
fn corpus_loads_identically_via_native_and_component() -> Result<()> {
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    let files = corpus_files();
    assert!(
        files.len() >= 100,
        "corpus walk found only {} files — walker or checkout broken",
        files.len()
    );

    let (mut store, inst) = instantiate()?;
    let ledger = inst.rustledger_ledger_ledger();

    let mut compared = 0usize;
    let mut skipped = 0usize;
    let mut mismatches: Vec<String> = Vec::new();

    for path in &files {
        let Ok(meta) = std::fs::metadata(path) else {
            skipped += 1;
            continue;
        };
        if meta.len() > MAX_FILE_BYTES {
            skipped += 1;
            continue;
        }
        let Ok(src) = std::fs::read_to_string(path) else {
            skipped += 1; // non-UTF-8
            continue;
        };
        // A bare source string has no include root; those files exercise the
        // loader, not the conversion surface under test here.
        if src.lines().any(|l| l.trim_start().starts_with("include ")) {
            skipped += 1;
            continue;
        }

        let native = rustledger_ffi_wasi::helpers::load_source(&src);
        let loaded = ledger.call_load(&mut store, &src, "<corpus>", false)?;
        compared += 1;

        let rel = path.display().to_string();

        // The component's `load` errors are the native load errors (same
        // order) with #1663's semantic-validation errors appended. Phase
        // can't separate the two sets — native tags booking/process errors
        // "validate" too — so assert the native errors are a message-level
        // PREFIX of the component's. This is exactly the silent-green
        // invariant: nothing the native path reports may vanish through the
        // component.
        if loaded.errors.len() < native.errors.len() {
            mismatches.push(format!(
                "{rel}: component dropped errors: native={} component={}",
                native.errors.len(),
                loaded.errors.len()
            ));
            continue;
        }
        if let Some((i, (ne, we))) = native
            .errors
            .iter()
            .zip(loaded.errors.iter())
            .enumerate()
            .find(|(_, (ne, we))| ne.message != we.message)
        {
            mismatches.push(format!(
                "{rel}: error {i} native={:?} component={:?}",
                ne.message, we.message
            ));
            continue;
        }

        if loaded.entries.len() != native.directives.len() {
            mismatches.push(format!(
                "{rel}: entry count native={} component={}",
                native.directives.len(),
                loaded.entries.len()
            ));
            continue;
        }

        for (i, (nd, wd)) in native
            .directives
            .iter()
            .zip(loaded.entries.iter())
            .enumerate()
        {
            let (nk, ndate) = native_kind(nd);
            let (wk, wdate) = wit_kind(wd);
            if nk != wk || ndate != wdate {
                mismatches.push(format!(
                    "{rel}: entry {i} native=({nk}, {ndate}) component=({wk}, {wdate})"
                ));
                break;
            }
        }
    }

    println!(
        "corpus parity: compared {compared}, skipped {skipped}, files {}",
        files.len()
    );
    assert!(
        mismatches.is_empty(),
        "{} corpus file(s) diverge between native load and the component:\n{}",
        mismatches.len(),
        mismatches
            .iter()
            .take(20)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
    Ok(())
}
