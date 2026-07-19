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
    // Subset of `skipped` attributable to the featureless component's
    // plugin-feature gate (#1809) — surfaced separately so the drop is
    // visible rather than folded silently into the generic skip count.
    let mut skipped_plugin_feature = 0usize;
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

        // Feature-divergence skip (#1809). The component wasm is always built
        // WITHOUT `python-plugins`/`wasm-plugins`, so a fixture declaring such
        // a plugin gets a `requires the …-plugins feature` error from the
        // component. Under `cargo test --workspace`, cargo feature unification
        // compiles the native reference (`load_source`) WITH those features
        // (the `rustledger` CLI enables them by default), so native ATTEMPTS
        // the plugin instead of gating it — same function, two feature builds.
        //
        // Skip only when the divergence is genuinely feature-driven: the
        // component gated AND native did NOT gate. Both halves matter (deep
        // review of this PR):
        //   - Requiring `!native_gated` avoids over-skipping in a FEATURELESS
        //     native build (`-p …-tests`, no unification): there both sides
        //     emit the same gate message and legitimately compare EQUAL, so
        //     the fixture stays covered instead of being dropped.
        //   - Keying the skip on the exact `requires the …-plugins feature`
        //     phrases (not a loose substring, not a source `plugin "…"` scan)
        //     keeps native-Rust-plugin fixtures — which the featureless
        //     component DOES run — in the compared set, and won't misfire on a
        //     `Plugin not found: "…"` message that merely echoes a plugin name.
        // A broad component regression that emitted the gate spuriously would
        // spike `skipped_plugin_feature`, which is bounded by an assert below.
        let gated = |msg: &str| {
            msg.contains("requires the python-plugins feature")
                || msg.contains("requires the wasm-plugins feature")
        };
        let component_gated = loaded.errors.iter().any(|e| gated(&e.message));
        let native_gated = native.errors.iter().any(|e| gated(&e.message));
        if component_gated && !native_gated {
            skipped += 1;
            skipped_plugin_feature += 1;
            continue;
        }
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

        for (i, (native_dir, wit_dir)) in native
            .directives
            .iter()
            .zip(loaded.entries.iter())
            .enumerate()
        {
            let (nk, ndate) = native_kind(native_dir);
            let (wk, wdate) = wit_kind(wit_dir);
            if nk != wk || ndate != wdate {
                mismatches.push(format!(
                    "{rel}: entry {i} native=({nk}, {ndate}) component=({wk}, {wdate})"
                ));
                break;
            }
        }
    }

    println!(
        "corpus parity: compared {compared}, skipped {skipped} \
         (of which {skipped_plugin_feature} for the component's plugin-feature gate), \
         files {}",
        files.len()
    );

    // Collapse guards (deep review of this PR): the plugin-feature skip is
    // decided partly from the component's OWN output, so a component-side
    // regression that emitted the gate broadly could drive `compared` toward
    // zero while `mismatches` stays empty — a silently-passing test. Only a
    // handful of corpus fixtures declare Python/WASM plugins, so cap the skip
    // count, and require most fixtures to actually be compared. Both bounds
    // are far from the current values (skip ≈ 4, compared ≈ 301 of 322) yet
    // trip long before a real collapse.
    const MAX_PLUGIN_FEATURE_SKIPS: usize = 30;
    assert!(
        skipped_plugin_feature <= MAX_PLUGIN_FEATURE_SKIPS,
        "plugin-feature skip count {skipped_plugin_feature} exceeds {MAX_PLUGIN_FEATURE_SKIPS} — \
         the featureless component is gating far more fixtures than expected, which would \
         silently shrink the compared set (possible component regression, or new plugin \
         fixtures that need this bound raised)"
    );
    assert!(
        compared >= files.len() / 2,
        "only {compared} of {} corpus files were compared — too few; the parity check has \
         been hollowed out by skips",
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

/// Drift guard (deep review of #1809 fix): the corpus parity skip keys off the
/// exact `requires the {python,wasm}-plugins feature` phrases emitted by
/// `rustledger-loader`'s plugin pass. If those messages are reworded, the
/// substring match in `corpus_loads_identically_via_native_and_component`
/// silently stops skipping and the corpus test fails spuriously on an
/// unrelated PR. This pins the wording end-to-end: load a source declaring a
/// Python plugin through the FEATURELESS component and assert it still emits
/// the phrase the skip depends on, so a reword fails HERE, loudly, pointing at
/// the coupling.
#[test]
fn plugin_feature_gate_message_is_stable() -> Result<()> {
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    let (mut store, inst) = instantiate()?;
    let ledger = inst.rustledger_ledger_ledger();
    // A dotted module NOT in the native-Rust plugin registry: the featureless
    // component treats it as a Python plugin and gates it. (A native plugin
    // like `auto_accounts` would just run — no error — so it wouldn't pin the
    // gate wording.)
    let src = "plugin \"some.unknown.python.module\"\n\
               2024-01-01 open Assets:Cash\n";
    let loaded = ledger.call_load(&mut store, src, "<drift>", false)?;
    assert!(
        loaded
            .errors
            .iter()
            .any(|e| e.message.contains("requires the python-plugins feature")),
        "featureless component must still gate a Python plugin with the exact phrase the \
         corpus skip matches; if this failed after a rustledger-loader reword, update the \
         sentinel in corpus_loads_identically_via_native_and_component to match. Got: {:?}",
        loaded.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );
    Ok(())
}
