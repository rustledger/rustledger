//! WASI-Preview-2 component implementing the `rustledger:ffi/ledger` WIT
//! interface. Spike for #1384 — demonstrates that the embedding surface can be
//! a typed Component Model export instead of hand-rolled JSON-RPC over stdio.

wit_bindgen::generate!({
    world: "ffi",
    path: "../wit",
});

struct Component;

impl exports::rustledger::ffi::ledger::Guest for Component {
    fn version() -> String {
        // Mirrors `rustledger_ffi_wasi::API_VERSION`. Kept literal so the spike
        // builds for wasm32-wasip2 without pulling the whole engine; the real
        // implementation would call into the loader and return live data.
        "2.0".to_string()
    }
}

export!(Component);
