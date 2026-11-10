//! `rledger query` and `rledger report` refuse a ledger whose
//! `option "booking_method"` was rejected (#2911).
//!
//! The option keeps its previous method (STRICT here), as in beancount, so
//! every figure would be booked with a method the ledger did not ask for.
//! bean-query answers with the STRICT figures; rledger refuses, deliberately
//! (see `Options::query_refusal`). Another rejected option keeps its default
//! and answers. `query` is also pinned, with every other surface, by the
//! shared `query_answer_rule` cases; `report` is pinned here.

mod common;

use std::process::{Command, Output};

const LEDGER: &str = "2024-01-01 open Assets:Cash
2024-01-01 open Income:Salary
2024-01-02 * \"pay\"
  Assets:Cash  100 USD
  Income:Salary
";

/// Write `option` then the ledger, and run `rledger <args> <file> <tail>`.
fn run(bin: &std::path::Path, option: &str, args: &[&str], tail: &[&str]) -> (Output, String) {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("main.beancount");
    std::fs::write(&path, format!("{option}\n{LEDGER}")).expect("write");
    let out = Command::new(bin)
        .args(args)
        .arg("--no-cache")
        .arg(&path)
        .args(tail)
        .output()
        .expect("run rledger");
    (out, path.display().to_string())
}

fn query(bin: &std::path::Path, option: &str) -> (Output, String) {
    run(bin, option, &["query"], &["SELECT account, sum(position)"])
}

fn report(bin: &std::path::Path, option: &str) -> (Output, String) {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("main.beancount");
    std::fs::write(&path, format!("{option}\n{LEDGER}")).expect("write");
    let out = Command::new(bin)
        .args(["report", "--no-cache", "--no-pager"])
        .arg(&path)
        .arg("balances")
        .output()
        .expect("run rledger report");
    (out, path.display().to_string())
}

/// The refusal: exit 1 (the existing refusal's code, not a panic's 101), no
/// figures, and a message naming the option, its value, its `file:line`, and
/// the method the figures would have been booked with.
fn assert_refused(out: &Output, path: &str, surface: &str) {
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    let context = format!(
        "{surface}: {:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
        out.status
    );
    assert_eq!(out.status.code(), Some(1), "{context}");
    assert!(
        stderr.contains(&format!(
            "option \"booking_method\" \"fifo\" at {path}:1 is invalid (E7002)"
        )),
        "{context}"
    );
    assert!(stderr.contains("refusing"), "{context}");
    assert!(stderr.contains("booked with STRICT"), "{context}");
    assert!(
        !stdout.contains("100"),
        "a refusal prints no figures: {context}"
    );
}

fn assert_answered(out: &Output, surface: &str) {
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    let context = format!(
        "{surface}: {:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
        out.status
    );
    assert!(out.status.success(), "{context}");
    assert!(stdout.contains("100"), "{context}");
    assert!(!stderr.contains("refusing"), "{context}");
}

#[test]
fn test_query_invalid_booking_method_refuses() {
    let bin = require_rledger!();
    let (out, path) = query(&bin, "option \"booking_method\" \"fifo\"");
    assert_refused(&out, &path, "query");
}

#[test]
fn test_report_invalid_booking_method_refuses() {
    let bin = require_rledger!();
    let (out, path) = report(&bin, "option \"booking_method\" \"fifo\"");
    assert_refused(&out, &path, "report balances");
}

#[test]
fn test_query_and_report_valid_booking_method_answer() {
    let bin = require_rledger!();
    let (out, _) = query(&bin, "option \"booking_method\" \"FIFO\"");
    assert_answered(&out, "query");
    let (out, _) = report(&bin, "option \"booking_method\" \"FIFO\"");
    assert_answered(&out, "report balances");
}

#[test]
fn test_query_and_report_other_rejected_option_answers() {
    let bin = require_rledger!();
    let (out, _) = query(&bin, "option \"account_rounding\" \"bad:leaf\"");
    assert_answered(&out, "query");
    let (out, _) = report(&bin, "option \"account_rounding\" \"bad:leaf\"");
    assert_answered(&out, "report balances");
}
