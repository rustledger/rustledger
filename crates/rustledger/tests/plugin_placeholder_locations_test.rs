//! Directives the `check_closing` and `close_tree` plugins and document
//! discovery create have the placeholder location beancount gives them, so
//! `rledger check` reports an error on one where `bean-check` does, instead
//! of at `<unknown>` (#2713). Each expected header is `bean-check`'s (beancount
//! 3.2.3) for the same ledger; the messages after it are rledger's own.

use std::path::Path;
use std::process::Command;

fn check(ledger: &Path) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_rledger"))
        .args(["check", "--no-cache", ledger.to_str().unwrap()])
        .output()
        .expect("rledger check should execute");
    assert!(
        !out.status.success(),
        "the ledger has an error: {}",
        String::from_utf8_lossy(&out.stdout)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

/// `bean-check`: `<check_closing>:0: Balance failed for 'Assets:Brokerage'`.
#[test]
fn check_closing_balance_is_reported_at_its_placeholder() {
    let dir = tempfile::tempdir().unwrap();
    let ledger = dir.path().join("ledger.beancount");
    std::fs::write(
        &ledger,
        "plugin \"beancount.plugins.check_closing\"\n\
         2024-01-01 open Assets:Bank\n\
         2024-01-01 open Assets:Brokerage\n\
         2024-01-01 open Income:Gains\n\
         2024-01-15 * \"close out\"\n  \
           Assets:Brokerage  -5 USD\n    \
             closing: TRUE\n  \
           Assets:Bank  10 USD\n  \
           Income:Gains -5 USD\n",
    )
    .unwrap();
    let out = check(&ledger);
    assert!(
        out.contains("<check_closing>:0: error[E2001]: Balance failed for Assets:Brokerage"),
        "{out}"
    );
    assert!(!out.contains("<unknown>"), "{out}");
}

/// `bean-check`: `<beancount.plugins.close_tree>:0: Unopened account
/// Assets:Bank:Sub is being closed`.
#[test]
fn close_tree_close_is_reported_at_its_placeholder() {
    let dir = tempfile::tempdir().unwrap();
    let ledger = dir.path().join("ledger.beancount");
    std::fs::write(
        &ledger,
        "plugin \"beancount.plugins.close_tree\"\n\
         2024-01-01 open Assets:Bank\n\
         2024-03-01 open Assets:Bank:Sub\n\
         2024-02-01 close Assets:Bank\n",
    )
    .unwrap();
    let out = check(&ledger);
    assert!(
        out.contains("<beancount.plugins.close_tree>:0: error[") && out.contains("Assets:Bank:Sub"),
        "{out}"
    );
    assert!(!out.contains("<unknown>"), "{out}");
}

/// `bean-check`: `<main file>:0: Invalid reference to inactive account
/// 'Assets:Bank'` for a document dated before the account opens.
#[test]
fn found_document_is_reported_at_the_main_file_line_zero() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path().canonicalize().unwrap();
    std::fs::create_dir_all(root.join("docs/Assets/Bank")).unwrap();
    std::fs::write(root.join("docs/Assets/Bank/2023-06-01.stmt.pdf"), "").unwrap();
    let ledger = root.join("ledger.beancount");
    std::fs::write(
        &ledger,
        "option \"documents\" \"docs\"\n\
         2024-01-01 open Assets:Bank\n",
    )
    .unwrap();
    let out = check(&ledger);
    let header = format!("{}:0: error[", ledger.display());
    let line = out
        .lines()
        .find(|l| l.contains("2023-06-01.stmt.pdf") || l.contains("Assets:Bank"))
        .unwrap_or_else(|| panic!("the document's error is reported: {out}"));
    assert!(line.starts_with(&header), "{line}\n{out}");
    assert!(!out.contains("<unknown>"), "{out}");
}
