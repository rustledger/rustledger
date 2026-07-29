//! Ledger input must never panic the CLI, and must never be answered with a
//! clamped number (#1863).
//!
//! `rust_decimal` is a 96-bit type with a hard ~±7.9e28 ceiling whose `+`/`*`
//! PANIC on overflow. Inventory and weight arithmetic runs in the loader's
//! booking phase, so a ledger holding large amounts aborted EVERY command —
//! including `check`, the command you run to find out what is wrong with your
//! file.
//!
//! # Why these tests assert on the message, not just the exit code
//!
//! The obvious fix — saturate instead of panicking — was implemented and
//! REJECTED (PR #1890). `Decimal::MIN == -Decimal::MAX` exactly, so a clamped
//! debit and a clamped credit cancel to a residual of *precisely zero*: a
//! ledger off by 1e40 passed `check` with exit 0. Asserting only "doesn't
//! panic" would have passed that build. Every test here therefore pins WHAT is
//! reported, and `unbalanced_reports_the_exact_residual_like_beancount` pins
//! the exact figure Python beancount computes.

mod common;

use std::process::Command;

/// Run `rledger check` on `source`, returning `(exit_code, combined_output)`.
///
/// `--no-cache` is deliberate: a cached parse can mask a booking-phase change,
/// which has hidden a fix in this area before.
fn check(source: &str) -> (Option<i32>, String) {
    let dir = std::env::temp_dir().join(format!(
        "rledger-overflow-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let path = dir.join("ledger.beancount");
    std::fs::write(&path, source).expect("write fixture");

    let Some(bin) = common::rledger_binary() else {
        eprintln!("Skipping: rledger binary not found");
        return (None, String::new());
    };
    let out = Command::new(bin)
        .args(["check", "--no-cache"])
        .arg(&path)
        .output()
        .expect("run rledger check");
    let _ = std::fs::remove_dir_all(&dir);

    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    (Some(out.status.code().unwrap_or(-1)), combined)
}

/// Run `rledger query` and return `(exit_code, combined_output)`.
fn query(source: &str, sql: &str) -> (Option<i32>, String) {
    let dir = std::env::temp_dir().join(format!(
        "rledger-overflow-q-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let path = dir.join("ledger.beancount");
    std::fs::write(&path, source).expect("write fixture");
    let Some(bin) = common::rledger_binary() else {
        eprintln!("Skipping: rledger binary not found");
        return (None, String::new());
    };
    let out = Command::new(bin)
        .arg("query")
        .arg(&path)
        .arg(sql)
        .output()
        .expect("run rledger query");
    let _ = std::fs::remove_dir_all(&dir);
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    (Some(out.status.code().unwrap_or(-1)), combined)
}

/// The process survived and said something about it.
fn assert_reported_not_panicked(code: Option<i32>, output: &str, what: &str) {
    let Some(code) = code else { return }; // binary unavailable; already logged
    assert!(
        !output.contains("panicked"),
        "{what}: ledger input must never panic the CLI\n{output}"
    );
    assert_ne!(code, 101, "{what}: exit 101 is a Rust panic\n{output}");
    assert_eq!(code, 1, "{what}: expected a reported error\n{output}");
}

/// Two postings whose sum needs 29 digits.
///
/// The residual is computed in `BigDecimal` (the escalation tier), so the
/// reported figure is exact rather than an overflow complaint.
#[test]
fn oversized_sum_reports_the_exact_residual() {
    let (code, out) = check(
        "2024-01-01 open Assets:A\n\
         2024-01-01 open Assets:B\n\
         2024-02-01 * \"two big plain postings\"\n\
        \x20 Assets:A   40000000000000000000000000000 USD\n\
        \x20 Assets:B   40000000000000000000000000000 USD\n",
    );
    assert_reported_not_panicked(code, &out, "oversized sum");
    if code.is_none() {
        return;
    }
    assert!(
        out.contains("80000000000000000000000000000"),
        "the residual must be reported exactly (8e28, past the Decimal \
         ceiling) — a clamped one would read 7.92...e28 or zero:\n{out}"
    );
}

/// THE case that killed the saturating design.
///
/// Python beancount computes this residual as `-1.000000000000000000000000000E+40`
/// (its `decimal` context keeps 28 significant digits but has effectively
/// unbounded magnitude — `Emax` is 999999). rledger must agree.
///
/// Under saturation both weights clamped, cancelled to zero, and `check`
/// printed `✓ No errors found` with exit 0 for a ledger off by 1e40.
#[test]
fn unbalanced_reports_the_exact_residual_like_beancount() {
    let (code, out) = check(
        "2020-01-01 open Assets:A\n\
         2020-01-01 open Assets:B\n\
         2020-02-01 * \"off by 1e40 USD\"\n\
        \x20 Assets:A   100000000000000000000 HOOL {100000000000000000000 USD}\n\
        \x20 Assets:B  -100000000000000000000 HOOL {200000000000000000000 USD}\n",
    );
    assert_reported_not_panicked(code, &out, "1e40 imbalance");
    if code.is_none() {
        return;
    }
    assert!(
        !out.contains("No errors found"),
        "a ledger off by 1e40 must never certify as balanced — this is the \
         exact regression that closed PR #1890:\n{out}"
    );
    assert!(
        out.contains("does not balance"),
        "expected the balance diagnostic:\n{out}"
    );
    assert!(
        out.contains("-10000000000000000000000000000000000000000"),
        "the residual must match Python beancount's -1e40 exactly, which is \
         only possible via the BigDecimal escalation tier:\n{out}"
    );
}

/// An elided posting whose amount cannot be represented.
///
/// Here there is no correct number to report — the amount would be WRITTEN
/// INTO the posting and thereafter indistinguishable from user input — so this
/// is the case that must be refused rather than escalated.
#[test]
fn unrepresentable_interpolation_is_refused() {
    let (code, out) = check(
        "2024-01-01 open Assets:Stock\n\
         2024-01-01 open Assets:Cash\n\
         2024-02-01 * \"elided counter-posting\"\n\
        \x20 Assets:Stock  10000000000000000 HOOL {10000000000000.00 USD}\n\
        \x20 Assets:Cash\n",
    );
    assert_reported_not_panicked(code, &out, "unrepresentable interpolation");
    if code.is_none() {
        return;
    }
    assert!(
        out.contains("representable range") || out.contains("cannot be computed"),
        "expected an out-of-range diagnostic naming the limit:\n{out}"
    );
    assert!(
        !out.contains("79228162514264337593543950335"),
        "a clamped Decimal::MAX must never reach the user as a posting \
         amount:\n{out}"
    );
}

/// Selling a lot whose cost basis (`units × cost`) leaves the range.
///
/// Reaches `Inventory::reduce`'s cost-basis accumulation — a site the earlier
/// attempt left panicking, because its integration test used these very
/// numbers but only exercised `at_cost`, never the sell side.
#[test]
fn oversized_cost_basis_on_reduction_is_reported() {
    let (code, out) = check(
        "2024-01-01 open Assets:Stock\n\
         2024-01-01 open Assets:Cash\n\
         2024-02-01 * \"buy\"\n\
        \x20 Assets:Stock  10000000000000000 HOOL {10000000000000.00 USD}\n\
        \x20 Assets:Cash  -10000000000000000 CASHU\n\
         2024-03-01 * \"sell\"\n\
        \x20 Assets:Stock -10000000000000000 HOOL {}\n\
        \x20 Assets:Cash   10000000000000000 CASHU\n",
    );
    assert_reported_not_panicked(code, &out, "oversized cost basis");
    if code.is_none() {
        return;
    }
    assert!(
        out.contains("representable range"),
        "expected the out-of-range diagnostic from the reduce path:\n{out}"
    );
}

/// The whole point of the ceiling being far above real ledgers: ordinary input
/// must be completely unaffected.
///
/// Without this, "report an overflow" could be satisfied by reporting one for
/// every ledger.
#[test]
fn ordinary_amounts_are_untouched() {
    let (code, out) = check(
        "2024-01-01 open Assets:Stock\n\
         2024-01-01 open Assets:Cash\n\
         2024-02-01 * \"buy\"\n\
        \x20 Assets:Stock  10 HOOL {150.00 USD}\n\
        \x20 Assets:Cash\n\
         2024-03-01 * \"sell\"\n\
        \x20 Assets:Stock -10 HOOL {}\n\
        \x20 Assets:Cash   1600.00 USD\n\
        \x20 Income:Gains\n",
    );
    let Some(code) = code else { return };
    assert!(!out.contains("panicked"), "{out}");
    assert!(
        !out.contains("representable range"),
        "a ledger that fits must never see an overflow diagnostic:\n{out}"
    );
    // `Income:Gains` is unopened, so this reports E1001 — the point is only
    // that it is NOT an arithmetic complaint.
    assert!(
        code == 0 || out.contains("E1001"),
        "unexpected output:\n{out}"
    );
}

/// A pad that cannot be applied must leave NEITHER account changed.
///
/// A pad is two halves of one entry. When the source half overflows after the
/// target half succeeded, an earlier version left the target credited, emitted
/// no synthetic transaction, and reported the error — so a LATER assertion on
/// the target passed off a pad that never happened. Sabotage-verified: dropping
/// the undo makes the final assertion report
/// `expected 0 USD, got 40000000000000000000000000000 USD`.
#[test]
fn a_failed_pad_credits_neither_account() {
    let (code, out) = check(
        "2024-01-01 open Assets:A\n\
         2024-01-01 open Assets:Big\n\
         2024-01-01 open Equity:O\n\
         2024-01-05 * \"load the pad source close to the ceiling\"\n\
        \x20 Assets:Big   70000000000000000000000000000 USD\n\
        \x20 Equity:O    -70000000000000000000000000000 USD\n\
         2024-02-01 pad Assets:A Equity:O\n\
         2024-03-01 balance Assets:A  40000000000000000000000000000 USD\n\
         2024-04-01 balance Assets:A  0 USD\n",
    );
    assert_reported_not_panicked(code, &out, "unappliable pad");
    if code.is_none() {
        return;
    }
    assert!(
        out.contains("E4004"),
        "the pad that could not be applied must be reported:\n{out}"
    );
    assert!(
        !out.contains("E2001") && !out.contains("Balance failed"),
        "the target must not keep a credit from a pad that was never emitted — \
         the closing `balance Assets:A 0 USD` proves it was undone:\n{out}"
    );
}

/// A transaction that BALANCES but whose running sum overflows partway.
///
/// Accumulation is order-dependent: `[+7e28, +7e28, -7e28, -7e28]` leaves
/// `Decimal`'s range at the second posting even though the total is exactly
/// zero. The fast tier therefore has no answer, and the only correct response
/// is to escalate — reporting an error here would condemn a perfectly good
/// transaction.
///
/// This is the sharpest test of the escalation: a fix that merely refused on
/// overflow (rather than recomputing in `BigDecimal`) passes every other test
/// in this file and fails this one.
#[test]
fn intermediate_overflow_in_a_balanced_transaction_is_clean() {
    let (code, out) = check(
        "2024-01-01 open Assets:A\n\
         2024-01-01 open Assets:B\n\
         2024-01-01 open Assets:C\n\
         2024-01-01 open Assets:D\n\
         2024-02-01 * \"balances exactly; the running sum does not\"\n\
        \x20 Assets:A   70000000000000000000000000000 USD\n\
        \x20 Assets:B   70000000000000000000000000000 USD\n\
        \x20 Assets:C  -70000000000000000000000000000 USD\n\
        \x20 Assets:D  -70000000000000000000000000000 USD\n",
    );
    let Some(code) = code else { return };
    assert!(!out.contains("panicked"), "{out}");
    assert_eq!(
        code, 0,
        "the true residual is zero, so this must pass cleanly — the fast tier \
         overflowing is not evidence of an imbalance:\n{out}"
    );
    assert!(
        !out.contains("representable range"),
        "a balanced transaction must never draw an overflow diagnostic:\n{out}"
    );
}

/// A compound cost `{a # b}`, whose `N*a + b` normalization multiplies two
/// user-supplied numbers.
///
/// Found only after the panic sweep was rebuilt: the first sweep assigned its
/// binary path with `BIN=$(cargo build ...; echo path)`, which captured the
/// build banner, so every invocation failed with "command not found" and the
/// run reported zero panics while testing nothing.
#[test]
fn compound_cost_normalization_is_reported() {
    let (code, out) = check(
        "2024-01-01 open Assets:S\n\
         2024-01-01 open Assets:C\n\
         2024-02-01 * \"compound cost\"\n\
        \x20 Assets:S  10000000000000000 HOOL {10000000000000.00 # 40000000000000000000000000000 USD}\n\
        \x20 Assets:C\n",
    );
    assert_reported_not_panicked(code, &out, "compound cost");
}

/// BQL surfaces are reachable from ledger input too, and a query cell showing
/// a clamped total is indistinguishable from a real one.
///
/// `cost()` over an aggregated inventory and `value()` (which multiplies by a
/// price) were both still panicking after the first pass.
#[test]
fn bql_cost_and_value_report_instead_of_panicking() {
    let src = "2024-01-01 open Assets:S\n\
               2024-01-01 open Assets:C\n\
               2024-02-01 * \"buy\"\n\
              \x20 Assets:S  10000000000000000 HOOL {10000000000000.00 USD}\n\
              \x20 Assets:C  -10000000000000000 CASHU\n";
    for sql in [
        "SELECT account, cost(sum(position))",
        "SELECT account, value(sum(position))",
        "SELECT account, sum(position) AT COST",
        "SELECT sum(cost(position))",
    ] {
        let (code, out) = query(src, sql);
        let Some(code) = code else { return };
        assert!(
            !out.contains("panicked"),
            "`{sql}` must not panic the CLI:\n{out}"
        );
        assert_ne!(code, 101, "`{sql}` exited 101 (a panic):\n{out}");
    }
}
