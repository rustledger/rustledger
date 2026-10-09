//! WASM importer for `tests/plugin_conformance.rs`.
//!
//! Identifies `*.conformance` files and imports one transaction
//! narrated `conformance import` into the target account, with a warning. A file whose content
//! is `burn` or `alloc` makes it loop until the time budget stops it, or
//! ask for more memory than the sandbox allows; `ansi` puts terminal
//! control sequences in its warning.

use rustledger_plugin_types::{
    AmountData, DirectiveData, DirectiveWrapper, ImporterInput, ImporterOutput, PostingData,
    TransactionData, wasm_importer_main,
};

fn identify(path: &str) -> bool {
    path.ends_with(".conformance")
}

fn extract(input: ImporterInput) -> ImporterOutput {
    let content = String::from_utf8_lossy(&input.content).trim().to_string();
    match content.as_str() {
        "burn" => {
            let mut x: u64 = 0;
            loop {
                x = std::hint::black_box(x.wrapping_add(1));
            }
        }
        "alloc" => {
            let v = vec![1u8; 512 << 20];
            std::hint::black_box(&v);
        }
        _ => {}
    }
    let posting = |account: &str, number: &str| PostingData {
        account: account.to_string(),
        units: Some(AmountData {
            number: number.to_string(),
            currency: "USD".to_string(),
        }),
        cost: None,
        price: None,
        flag: None,
        metadata: vec![],
        span: None,
    };
    let txn = DirectiveWrapper {
        directive_type: String::new(),
        date: "2024-01-15".to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Transaction(TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: "conformance import".to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![
                posting(&input.account, "-12.34"),
                posting("Expenses:Conformance", "12.34"),
            ],
        }),
    };
    let mut out = ImporterOutput::new(vec![txn]);
    let tail = if content == "ansi" {
        " \u{1b}[2J\u{1b}]0;pwned\u{7}"
    } else {
        ""
    };
    out.warnings
        .push(format!("conformance: WASM importer ran{tail}"));
    out
}

wasm_importer_main! {
    name: "conformance",
    description: "conformance-matrix importer",
    identify: identify,
    extract: extract,
}
