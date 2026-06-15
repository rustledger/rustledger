//! WASI-Preview-2 component implementing the `rustledger:ffi/ledger` WIT
//! interface. Spike for #1384 — demonstrates that the embedding surface can be
//! a typed Component Model export instead of hand-rolled JSON-RPC over stdio,
//! including a real tagged *variant* (`cost-number`), which is the part of a
//! real migration that carries actual risk.

wit_bindgen::generate!({
    world: "ffi",
    path: "../wit",
});

use exports::rustledger::ffi::ledger::{CostNumber, Guest};

struct Component;

impl Guest for Component {
    fn version() -> String {
        // Mirrors `rustledger_ffi_wasi::API_VERSION`. Kept literal so the spike
        // builds for wasm32-wasip2 without pulling the whole engine; the real
        // implementation would call into the loader and return live data.
        "2.0".to_string()
    }

    fn sample_cost(kind: u8) -> CostNumber {
        // Mirrors the real `CostNumber` variants. wit-bindgen generates a Rust
        // enum here, so the "tagged shape" is type-checked rather than a
        // hand-assembled `{"kind": ...}` JSON object.
        match kind {
            0 => CostNumber::PerUnit("100".to_string()),
            1 => CostNumber::Total("1500".to_string()),
            _ => CostNumber::PerUnitFromTotal(("100".to_string(), "1500".to_string())),
        }
    }
}

export!(Component);
