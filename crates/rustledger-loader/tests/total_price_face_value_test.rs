//! A total price (`@@`) is weighed at the total the author wrote, so a total
//! that does not divide evenly by the units still balances (#2831).
//!
//! Beancount turns `3 HOOL @@ 1000 USD` into a per-unit price (`1000 / 3`,
//! rounded to 28 significant digits) and multiplies it back when weighing, so
//! the posting weighs `999.9999999999999999999999999 USD` and, with a zero
//! tolerance, bean-check 3.2.3 reports `Transaction does not balance:
//! (-0.0000000000000000000000001 USD)` on a transaction balanced to the cent.
//! rledger weighs the written total (#2031), which is exact: a deliberate
//! deviation for correctness, documented in `docs/reference/compatibility.md`
//! ("Total Prices That Do Not Divide Evenly").

use rustledger_loader::{Ledger, LoadOptions, load};
use std::io::Write;

fn load_source(source: &str) -> Ledger {
    let mut f = tempfile::Builder::new()
        .prefix("total-price-face-value-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(source.as_bytes()).expect("write fixture");
    load(f.path(), &LoadOptions::default()).expect("the ledger loads")
}

fn errors(source: &str) -> Vec<String> {
    load_source(source)
        .errors
        .iter()
        .map(|e| e.message.clone())
        .collect()
}

const OPENS: &str = "\
2024-01-01 open Assets:Stock
2024-01-01 open Assets:Bank
";

/// The issue's ledger, with and without the explicit zero tolerance (all
/// whole-number legs infer a zero tolerance anyway).
#[test]
fn test_load_balances_a_total_price_that_does_not_divide_evenly() {
    let txn =
        "2024-01-02 * \"buy\"\n  Assets:Stock  3 HOOL @@ 1000 USD\n  Assets:Bank  -1000 USD\n";
    for options in ["option \"inferred_tolerance_default\" \"*:0\"\n", ""] {
        let errs = errors(&format!("{options}{OPENS}{txn}"));
        assert!(errs.is_empty(), "{options:?}: {errs:#?}");
    }
}

/// The same on the credit side, and with more units than the total's digits.
#[test]
fn test_load_balances_an_uneven_total_price_on_a_sale_and_a_large_count() {
    for postings in [
        "  Assets:Bank  1000 USD\n  Assets:Stock  -3 HOOL @@ 1000 USD\n",
        "  Assets:Stock  7 HOOL @@ 100 USD\n  Assets:Bank  -100 USD\n",
        "  Assets:Stock  30001 HOOL @@ 1 USD\n  Assets:Bank  -1 USD\n",
    ] {
        let errs = errors(&format!("{OPENS}2024-01-02 * \"t\"\n{postings}"));
        assert!(errs.is_empty(), "{postings:?}: {errs:#?}");
    }
}

/// Face value is exact, not lenient: a total that really is a cent off is
/// still refused.
#[test]
fn test_load_refuses_a_total_price_that_is_really_off() {
    let errs = errors(&format!(
        "{OPENS}2024-01-02 * \"buy\"\n  Assets:Stock  3 HOOL @@ 1000 USD\n  Assets:Bank  -999.99 USD\n"
    ));
    assert!(
        errs.iter().any(|m| m.contains("does not balance")),
        "{errs:#?}"
    );
}
