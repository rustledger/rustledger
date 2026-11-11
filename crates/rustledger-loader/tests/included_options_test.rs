//! Options in included files are validated as beancount validates them, and
//! every option diagnostic names its file and line (#2925).
//!
//! beancount parses each included file with its own `Builder` and fresh
//! options, so every converter error there is reported at the included
//! file's line (bean-check exits 1), and only the top-level file's values are
//! kept. rledger reported only the E7009 "ignored" warning for those, valid
//! or not, and exited 0; none of its option diagnostics had a location.
//!
//! These load real files through the full pipeline, because the location is
//! the loader's (the file and line of the `option`), and the deviation below
//! is a downstream validation error.

use std::path::{Path, PathBuf};

struct Tree {
    _dir: tempfile::TempDir,
    main: PathBuf,
    sub: PathBuf,
}

/// A main file that includes `sub.beancount` on its first line, then `main`.
fn tree(main: &str, sub: &str) -> Tree {
    let dir = tempfile::Builder::new()
        .prefix("rledger_2925_")
        .tempdir()
        .expect("temp dir");
    let main_path = dir.path().join("main.beancount");
    let sub_path = dir.path().join("sub.beancount");
    std::fs::write(&main_path, format!("include \"sub.beancount\"\n{main}")).expect("write main");
    std::fs::write(&sub_path, sub).expect("write sub");
    Tree {
        _dir: dir,
        main: main_path,
        sub: sub_path,
    }
}

fn load(path: &Path) -> rustledger_loader::Ledger {
    rustledger_loader::load(path, &rustledger_loader::LoadOptions::default()).expect("load")
}

/// `(code, file, line, is_error)` for every option diagnostic.
fn option_diagnostics(ledger: &rustledger_loader::Ledger) -> Vec<(String, String, usize, bool)> {
    ledger
        .options
        .warnings
        .iter()
        .map(|w| {
            let site = w.site.as_ref().expect("every loaded option has a site");
            (
                w.code.to_string(),
                site.file.clone(),
                site.line,
                w.is_error(),
            )
        })
        .collect()
}

/// Each option family with an invalid value in an included file: its
/// converter error, at the included file's line, an error (so `check` exits
/// 1), and the value not applied. bean-check 3.2.3 reports each of these as
/// "Error for option" at `sub.beancount:<line>`.
#[test]
fn test_load_included_invalid_option_is_an_error_at_its_line() {
    let cases: &[(&str, &str, &[&str])] = &[
        ("name_assets", "assets", &["E7008"]),
        ("name_equity", "capital", &["E7008"]),
        ("account_rounding", "bad leaf", &["E7002"]),
        ("account_previous_balances", "bad leaf", &["E7002"]),
        ("account_current_conversions", "bad leaf", &["E7002"]),
        ("inferred_tolerance_default", "USD:-0.01", &["E7002"]),
        // Accumulates across includes, so it was already reported; pinned so
        // it stays reported at its line.
        ("display_precision", "USD:-0.01", &["E7002"]),
        ("tolerance_multiplier", "abc", &["E7002"]),
        ("inferred_tolerance_multiplier", "abc", &["E7004", "E7002"]),
        ("booking_method", "fifo", &["E7002"]),
        ("plugin_processing_mode", "weird", &["E7002"]),
        ("plugin", "x", &["E7005"]),
        ("filename", "x", &["E7005"]),
        ("nosuch", "x", &["E7001"]),
    ];
    for (key, value, expected) in cases {
        let t = tree(
            "2024-01-01 open Assets:A\n",
            &format!("; sub-ledger\n\noption \"{key}\" \"{value}\"\n"),
        );
        let ledger = load(&t.main);
        let sub = t.sub.display().to_string();
        let got = option_diagnostics(&ledger);
        let want: Vec<(String, String, usize, bool)> = expected
            .iter()
            .map(|code| (code.to_string(), sub.clone(), 3, true))
            .collect();
        assert_eq!(got, want, "{key} = {value:?}");
        // An unknown option is kept in `custom` from any file, as before;
        // it governs nothing.
        assert!(
            *key == "nosuch" || !ledger.options.set_options.contains(*key),
            "{key}: an included value is not applied"
        );
        assert!(
            !ledger.blocks_queries(),
            "{key}: an included rejection does not refuse queries; the \
             top-level booking method governs"
        );
    }
}

/// bean-check 3.2.3 on the issue's example: three invalid options in an
/// include are three errors. rledger gave three E7009 warnings and exit 0.
#[test]
fn test_load_issue_example_three_included_errors() {
    let t = tree(
        "2024-01-01 open Assets:A\n",
        "option \"name_equity\" \"capital\"\n\
         option \"booking_method\" \"fifo\"\n\
         option \"inferred_tolerance_default\" \"USD:-0.01\"\n",
    );
    let ledger = load(&t.main);
    let sub = t.sub.display().to_string();
    assert_eq!(
        option_diagnostics(&ledger),
        [
            ("E7008".to_string(), sub.clone(), 1, true),
            ("E7002".to_string(), sub.clone(), 2, true),
            ("E7002".to_string(), sub, 3, true),
        ]
    );
}

/// A value the converter accepts is still ignored in an included file: the
/// E7009 warning at its line, exit 0, and the top-level value governs.
#[test]
fn test_load_included_valid_option_is_still_e7009() {
    let t = tree(
        "option \"booking_method\" \"STRICT\"\n2024-01-01 open Assets:A\n",
        "option \"title\" \"Sub\"\noption \"booking_method\" \"FIFO\"\n",
    );
    let ledger = load(&t.main);
    let sub = t.sub.display().to_string();
    assert_eq!(
        option_diagnostics(&ledger),
        [
            ("E7009".to_string(), sub.clone(), 1, false),
            ("E7009".to_string(), sub, 2, false),
        ]
    );
    assert_eq!(ledger.options.booking_method, "STRICT");
    assert_eq!(ledger.options.title, None);
}

/// Options in the top-level file are located there, the ones raised once
/// every option is set too (E7006, E7010).
#[test]
fn test_load_top_level_option_diagnostics_are_located() {
    let t = tree(
        "option \"title\" \"a\"\n\
         option \"title\" \"b\"\n\
         option \"account_previous_balances\" \"Equity:Opening\"\n\
         option \"documents\" \"no-such-dir\"\n",
        "",
    );
    let ledger = load(&t.main);
    let main = t.main.display().to_string();
    assert_eq!(
        option_diagnostics(&ledger),
        [
            ("E7003".to_string(), main.clone(), 3, false),
            ("E7006".to_string(), main.clone(), 5, true),
            ("E7010".to_string(), main, 4, false),
        ]
    );
}

/// Deliberate deviation (#2925, maintainer decision): an included file's
/// `name_*` root does not govern that file's own accounts.
///
/// beancount checks account roots while parsing each file, with that file's
/// options, so `open Capital:Z` after `option "name_equity" "Capital"` in the
/// same included file loads (with no account type) and bean-check 3.2.3 is
/// clean. rledger keeps one set of roots for the whole tree, the top-level
/// file's, so the `open` is E1005. Stricter than Python; see the comment in
/// `Options::set_scoped_inner`.
#[test]
fn included_name_option_does_not_root_its_own_file() {
    let t = tree(
        "2024-01-01 open Assets:A\n",
        "option \"name_equity\" \"Capital\"\n2024-01-01 open Capital:Z\n",
    );
    let ledger = load(&t.main);
    let sub = t.sub.display().to_string();
    assert_eq!(
        option_diagnostics(&ledger),
        [("E7009".to_string(), sub, 1, false)]
    );
    assert_eq!(ledger.options.name_equity, "Equity");
    let codes: Vec<&str> = ledger.errors.iter().map(|e| e.code.as_str()).collect();
    assert_eq!(codes, ["E1005"], "{:?}", ledger.errors);
}

/// `documents` in an included file is ignored, as in beancount 3.2.3:
/// `loader.load_file` gives `documents == []` for it and bean-check exits 0
/// even when the root is missing. So it is the E7009 warning at its line,
/// never scanned for documents and never checked for existence (no E7006),
/// where rledger accumulated it and reported a missing root as an error.
#[test]
fn test_load_included_documents_is_ignored() {
    let t = tree(
        "2024-01-01 open Assets:A\n",
        "option \"documents\" \"/nonexistent/rledger-2925-docs\"\n",
    );
    let ledger = load(&t.main);
    let sub = t.sub.display().to_string();
    assert_eq!(
        option_diagnostics(&ledger),
        [("E7009".to_string(), sub, 1, false)]
    );
    assert!(ledger.options.documents.is_empty(), "nothing is scanned");
    assert!(ledger.errors.is_empty(), "{:?}", ledger.errors);
}

/// The same root in the top-level file still applies there: one E7006 at
/// the top-level line (bean-check: one error), none for the include's copy.
#[test]
fn test_load_documents_in_both_files_is_one_e7006() {
    let t = tree(
        "option \"documents\" \"/nonexistent/rledger-2925-docs\"\n\
         2024-01-01 open Assets:A\n",
        "option \"documents\" \"/nonexistent/rledger-2925-docs\"\n",
    );
    let ledger = load(&t.main);
    let (main, sub) = (t.main.display().to_string(), t.sub.display().to_string());
    assert_eq!(
        option_diagnostics(&ledger),
        [
            ("E7009".to_string(), sub, 1, false),
            ("E7006".to_string(), main, 2, true),
        ]
    );
}
