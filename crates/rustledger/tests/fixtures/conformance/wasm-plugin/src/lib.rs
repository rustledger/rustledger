//! WASM directive plugin for `tests/plugin_conformance.rs`.
//!
//! Tags every transaction `#conformance-wasm` and reports a warning
//! naming how many directives it saw, so every command that runs
//! plugins can show its effect. The `plugin` directive's config string
//! picks a misbehavior for the limit cases: `burn` loops until the time
//! budget stops it, `alloc` asks for more memory than the sandbox allows,
//! `ansi` puts terminal control sequences in its message.

use rustledger_plugin_types::{
    DirectiveData, DirectiveWrapper, PluginError, PluginInput, PluginOp, PluginOutput,
    wasm_plugin_main,
};

fn misbehave(mode: Option<&str>) {
    match mode {
        Some("burn") => {
            let mut x: u64 = 0;
            loop {
                x = std::hint::black_box(x.wrapping_add(1));
            }
        }
        Some("alloc") => {
            let v = vec![1u8; 512 << 20];
            std::hint::black_box(&v);
        }
        _ => {}
    }
}

fn process(input: PluginInput) -> PluginOutput {
    misbehave(input.config.as_deref());
    let n = input.directives.len();
    let mut ops = Vec::with_capacity(n);
    for (i, wrapper) in input.directives.into_iter().enumerate() {
        match wrapper.data {
            DirectiveData::Transaction(mut txn) => {
                txn.tags.push("conformance-wasm".to_string());
                ops.push(PluginOp::Modify(
                    i,
                    DirectiveWrapper {
                        data: DirectiveData::Transaction(txn),
                        ..wrapper
                    },
                ));
            }
            _ => ops.push(PluginOp::Keep(i)),
        }
    }
    let tail = if input.config.as_deref() == Some("ansi") {
        " \u{1b}[2J\u{1b}]0;pwned\u{7}"
    } else {
        ""
    };
    PluginOutput {
        ops,
        errors: vec![PluginError::warning(format!(
            "conformance: WASM plugin ran over {n} directives{tail}"
        ))],
    }
}

wasm_plugin_main! {
    process: process,
}
