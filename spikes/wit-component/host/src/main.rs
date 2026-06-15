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
    let version = ffi.rustledger_ffi_ledger().call_version(&mut store)?;

    println!("component reports api_version = {version:?}");
    assert_eq!(version, "2.0");
    println!("\u{2713} WIT host <-> wasip2 component round-trip works");
    Ok(())
}
