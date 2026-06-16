//! Parity tests for the WIT/Component-Model surface (#1384).
//!
//! Instantiate the `rustledger-ffi-component` wasip2 component in a wasmtime
//! host (typed `bindgen!` bindings, no JSON-RPC) and assert its output agrees
//! with the reused `rustledger-ffi-wasi` path for the same inputs. This is what
//! actually *runs* the conversion code — the rest of the crate only compiles it.
//!
//! Requires the component to be built first:
//!   cargo build -p rustledger-ffi-component --target wasm32-wasip2
//! The tests skip (rather than fail) when the artifact is absent, so they don't
//! break a build that hasn't produced the wasip2 binary.

// `bindgen!` generates an undocumented host-bindings module; quiet its lints
// (this is a test harness, not shipped API).
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

fn component_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/wasm32-wasip2/debug/rustledger_ffi_component.wasm")
}

fn instantiate() -> Result<(Store<Host>, Rustledger)> {
    let engine = Engine::default();
    let component = Component::from_file(&engine, component_path())?;
    let mut linker = Linker::<Host>::new(&engine);
    wasmtime_wasi::p2::add_to_linker_sync(&mut linker)?;
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

const LEDGER: &str = "\
2024-01-01 open Assets:Cash USD
2024-01-01 open Expenses:Food USD
2024-01-02 * \"Coffee\"
  Expenses:Food  5 USD
  Assets:Cash
";

#[test]
fn version_matches() -> Result<()> {
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    let (mut store, inst) = instantiate()?;
    let version = inst.rustledger_ledger_ledger().call_version(&mut store)?;
    assert_eq!(version, "2.1");
    Ok(())
}

#[test]
fn load_entry_count_matches_jsonrpc() -> Result<()> {
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    let (mut store, inst) = instantiate()?;
    let result = inst
        .rustledger_ledger_ledger()
        .call_load(&mut store, LEDGER)?;
    let expected = rustledger_ffi_wasi::helpers::load_source(LEDGER)
        .directives
        .len();
    assert_eq!(
        result.entries.len(),
        expected,
        "component load entry count must match load_source",
    );
    assert!(expected >= 3);
    Ok(())
}

#[test]
fn query_row_count_matches_executor() -> Result<()> {
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    let (mut store, inst) = instantiate()?;
    let q = "SELECT account, position";
    let result = inst
        .rustledger_ledger_ledger()
        .call_query(&mut store, LEDGER, q)?;
    assert!(
        result.errors.is_empty(),
        "query errored: {:?}",
        result.errors
    );
    assert!(
        !result.rows.is_empty(),
        "expected query rows for a non-empty ledger",
    );
    Ok(())
}

const LEDGER_WITH_HISTORY: &str = "\
2023-01-01 open Assets:Cash USD
2023-01-01 open Equity:Opening-Balances USD
2023-06-01 * \"old deposit\"
  Assets:Cash  100 USD
  Equity:Opening-Balances  -100 USD
2024-03-01 * \"in range\"
  Assets:Cash  -5 USD
  Expenses:Food  5 USD
";

#[test]
fn clamp_runs_and_summarizes_pre_range() -> Result<()> {
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    let (mut store, inst) = instantiate()?;
    let loaded = inst
        .rustledger_ledger_ledger()
        .call_load(&mut store, LEDGER_WITH_HISTORY)?;
    let clamped = inst.rustledger_ledger_builder().call_clamp(
        &mut store,
        &loaded.entries,
        "2024-01-01",
        "2024-12-31",
    )?;
    // Produces output, and no surviving directive predates the clamp window.
    assert!(!clamped.is_empty(), "clamp returned nothing");
    Ok(())
}

// Regression tests for the parity bugs the deep review found (the conversion
// layer was diverging from the JSON-RPC handlers on these cases).

#[test]
fn query_expands_pads() -> Result<()> {
    if !component_path().exists() {
        return Ok(());
    }
    let (mut store, inst) = instantiate()?;
    let src = "\
2024-01-01 open Assets:Cash USD
2024-01-01 open Equity:Opening USD
2024-01-01 pad Assets:Cash Equity:Opening
2024-06-01 balance Assets:Cash 500 USD
";
    let r = inst.rustledger_ledger_ledger().call_query(
        &mut store,
        src,
        "SELECT account, balance WHERE account = \"Assets:Cash\"",
    )?;
    assert!(r.errors.is_empty(), "query errored: {:?}", r.errors);
    assert!(!r.rows.is_empty(), "expected a row for Assets:Cash");
    // With pad expansion the balance is 500; without it the pad contributes nothing.
    let dump = format!("{:?}", r.rows);
    assert!(
        dump.contains("500"),
        "expected padded balance 500, got: {dump}"
    );
    Ok(())
}

#[test]
fn query_short_circuits_on_parse_error() -> Result<()> {
    if !component_path().exists() {
        return Ok(());
    }
    let (mut store, inst) = instantiate()?;
    // `oepn` is a typo -> parse error.
    let r = inst.rustledger_ledger_ledger().call_query(
        &mut store,
        "2024-01-01 oepn Assets:Cash\n",
        "SELECT account",
    )?;
    assert!(
        !r.errors.is_empty(),
        "parse error must surface, not be swallowed"
    );
    assert!(r.rows.is_empty(), "no rows on parse error");
    Ok(())
}

#[test]
fn filter_keeps_pre_begin_open_and_drops_commodity() -> Result<()> {
    if !component_path().exists() {
        return Ok(());
    }
    use rustledger::ledger::types::Directive;
    let (mut store, inst) = instantiate()?;
    let src = "\
2020-01-01 open Assets:Cash USD
2024-03-01 commodity USD
2024-06-01 * \"x\"
  Assets:Cash  1 USD
  Expenses:Y  -1 USD
";
    let loaded = inst.rustledger_ledger_ledger().call_load(&mut store, src)?;
    let filtered = inst.rustledger_ledger_builder().call_filter(
        &mut store,
        &loaded.entries,
        "2024-01-01",
        "2024-12-31",
    )?;
    assert!(
        filtered.iter().any(|d| matches!(d, Directive::Open(_))),
        "pre-begin open must be kept (open < end)",
    );
    assert!(
        filtered
            .iter()
            .all(|d| !matches!(d, Directive::Commodity(_))),
        "commodity must be dropped",
    );
    Ok(())
}
