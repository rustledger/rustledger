//! Minimal wasmtime host: loads the wasip2 component built from the same WIT
//! and calls `ledger.version()`. Host side of the #1384 spike — shows that an
//! embedder gets a typed, generated binding (`call_version`) instead of
//! framing JSON-RPC by hand.

use anyhow::Result;
use wasmtime::component::{Component, Linker, ResourceTable};
use wasmtime::{Engine, Store};
use wasmtime_wasi::{WasiCtx, WasiCtxBuilder, WasiCtxView, WasiView};

wasmtime::component::bindgen!({
    world: "ffi",
    path: "../wit",
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

fn main() -> Result<()> {
    let path = std::env::args()
        .nth(1)
        .expect("usage: rustledger-ffi-wit-host <component.wasm>");

    let engine = Engine::default();
    let component = Component::from_file(&engine, &path)?;

    let mut linker = Linker::<Host>::new(&engine);
    wasmtime_wasi::p2::add_to_linker_sync(&mut linker)?;

    let mut store = Store::new(
        &engine,
        Host {
            table: ResourceTable::new(),
            wasi: WasiCtxBuilder::new().build(),
        },
    );

    let ffi = Ffi::instantiate(&mut store, &component, &linker)?;
    let ledger = ffi.rustledger_ffi_ledger();

    let version = ledger.call_version(&mut store)?;
    println!("component reports api_version = {version:?}");
    assert_eq!(version, "2.0");

    // Exercise the tagged variant across the boundary — the risky type-modeling
    // part. The host gets a generated Rust enum, not a JSON object to inspect.
    use exports::rustledger::ffi::ledger::CostNumber;
    for kind in 0u8..3 {
        let cost = ledger.call_sample_cost(&mut store, kind)?;
        println!("cost kind {kind} = {cost:?}");
    }
    assert!(matches!(
        ledger.call_sample_cost(&mut store, 2)?,
        CostNumber::PerUnitFromTotal((ref pu, ref t)) if pu == "100" && t == "1500"
    ));

    println!("\u{2713} WIT host <-> wasip2 component round-trip works (string + variant)");
    Ok(())
}
