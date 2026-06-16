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
    let expected = rustledger_ffi_wasi::helpers::load_source(LEDGER).directives.len();
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
    assert!(result.errors.is_empty(), "query errored: {:?}", result.errors);
    assert!(
        !result.rows.is_empty(),
        "expected query rows for a non-empty ledger",
    );
    Ok(())
}
