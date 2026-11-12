//! The canonical side of the drift guard for what a query lists about the
//! ledger's options (#2911, #2929): `Ledger::query_option_errors` gives
//! exactly the cases' errors. The FFI component and WASM query surfaces run
//! the same cases (`query_option_errors/cases.rs`) and must list the same.

include!("query_option_errors/cases.rs");

use rustledger_loader::{LoadOptions, Loader, VirtualFileSystem, process};

#[test]
fn test_query_option_errors_lists_the_shared_cases() {
    for case in QUERY_OPTION_CASES {
        let mut vfs = VirtualFileSystem::new();
        for (path, text) in case.files {
            vfs.add_file(*path, *text);
        }
        let raw = Loader::new()
            .with_filesystem(Box::new(vfs))
            .load(std::path::Path::new(MAIN))
            .expect("loads");
        let ledger = process(raw, &LoadOptions::default()).expect("processes");
        let got: Vec<_> = ledger
            .query_option_errors()
            .into_iter()
            .map(|e| {
                let location = e.location.expect("located");
                (
                    e.code,
                    e.message,
                    Some(location.file.display().to_string()),
                    Some(location.line as u32),
                )
            })
            .collect();
        // The option diagnostics alone: a case's parse errors are listed by
        // the query surfaces, not by this rule.
        assert_eq!(
            got,
            case.expected_option_errors(Some(MAIN), MAIN),
            "{}",
            case.name
        );
        assert_eq!(ledger.blocks_queries(), !case.answers, "{}", case.name);
    }
}
