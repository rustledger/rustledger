//! `rledger split` / `rledger merge` through the binary: wiring and exit
//! codes (#2264). The behavior itself is covered by the unit tests in
//! `src/cmd/restructure/tests.rs`.

mod common;

use std::process::Command;

fn ledger_dir() -> tempfile::TempDir {
    let dir = tempfile::Builder::new()
        .prefix("rl-restructure-cli-")
        .tempdir()
        .expect("tempdir");
    std::fs::write(
        dir.path().join("ledger.beancount"),
        "option \"operating_currency\" \"USD\"\n\n\
         2023-01-01 open Assets:Bank\n\
         2023-01-01 open Expenses:Food\n\n\
         2023-05-01 * \"Lunch\"\n  Expenses:Food  10 USD\n  Assets:Bank\n\n\
         2024-05-01 * \"Lunch\"\n  Expenses:Food  11 USD\n  Assets:Bank\n",
    )
    .expect("write ledger");
    dir
}

#[test]
fn split_then_merge_exit_zero_and_round_trip() {
    let bin = require_rledger!();
    let dir = ledger_dir();
    let file = dir.path().join("ledger.beancount");
    let original = std::fs::read_to_string(&file).unwrap();

    let out = Command::new(&bin)
        .args(["split", "--by", "year", "--dry-run"])
        .arg(&file)
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(0), "{out:?}");
    assert!(!dir.path().join("ledger").exists(), "dry run wrote files");

    let out = Command::new(&bin)
        .args(["split", "--by", "year"])
        .arg(&file)
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(0), "{out:?}");
    assert!(dir.path().join("ledger/2023.beancount").exists());
    assert!(dir.path().join("ledger/2024.beancount").exists());

    let check = Command::new(&bin).arg("check").arg(&file).output().unwrap();
    assert!(check.status.success(), "{check:?}");

    let out = Command::new(&bin).arg("merge").arg(&file).output().unwrap();
    assert_eq!(out.status.code(), Some(0), "{out:?}");
    let merged = std::fs::read_to_string(&file).unwrap();
    for line in original.lines() {
        assert!(merged.contains(line), "lost {line:?}");
    }
}

#[test]
fn a_refused_split_exits_one_and_an_error_exits_two() {
    let bin = require_rledger!();
    let dir = ledger_dir();
    std::fs::write(dir.path().join("r.pdf"), "%PDF").unwrap();
    let file = dir.path().join("ledger.beancount");
    let mut text = std::fs::read_to_string(&file).unwrap();
    text.push_str("2024-06-01 document Assets:Bank \"r.pdf\"\n");
    std::fs::write(&file, &text).unwrap();

    let out = Command::new(&bin)
        .args(["split", "--by", "year"])
        .arg(&file)
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(1), "{out:?}");
    assert!(String::from_utf8_lossy(&out.stderr).contains("refusing to split"));
    assert_eq!(std::fs::read_to_string(&file).unwrap(), text);

    let out = Command::new(&bin)
        .args(["split", "--by", "year"])
        .arg(dir.path().join("missing.beancount"))
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(2), "{out:?}");
}
