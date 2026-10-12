//! A cost written on an AVERAGE sale is checked through the whole load
//! pipeline, and reported once (#2603).
//!
//! Booking refuses a sale whose spec states a cost its pool is not. The
//! validator's own inventory walk and BQL's replay see only booked postings,
//! so the refusal must come from booking, once, and not a second time from
//! the validator.

use rustledger_loader::{LoadOptions, load};
use std::io::Write;

/// 10 X at 10.00 and 10 X at 12.00 EUR: a pool at 11.00 EUR. `{SPEC}` is the
/// sale's cost spec.
const SOURCE: &str = r#"2024-01-01 open Assets:Brokerage X "AVERAGE"
2024-01-01 open Assets:Cash
2024-01-01 open Equity:Opening
2024-01-01 open Income:Gains

2024-01-02 * "buy"
  Assets:Brokerage  10 X {10.00 EUR}
  Equity:Opening

2024-01-03 * "buy"
  Assets:Brokerage  10 X {12.00 EUR}
  Equity:Opening

2024-03-01 * "sell"
  Assets:Brokerage  -1 X {SPEC}
  Assets:Cash  12.00 EUR
  Income:Gains
"#;

fn errors_for(spec: &str) -> Vec<String> {
    let source = SOURCE.replace("{SPEC}", &format!("{{{spec}}}"));
    assert!(
        source.contains(&format!("-1 X {{{spec}}}")),
        "fixture edit must apply"
    );
    let mut f = tempfile::Builder::new()
        .prefix("average-claim-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(source.as_bytes()).expect("write fixture");
    let ledger = load(f.path(), &LoadOptions::default()).expect("the ledger loads");
    ledger.errors.iter().map(|e| e.message.clone()).collect()
}

#[test]
fn a_cost_the_pool_is_not_is_one_error_naming_the_pool() {
    let errors = errors_for("99.00 EUR");
    assert_eq!(errors.len(), 1, "reported once: {errors:?}");
    assert!(
        errors[0].contains("AVERAGE pool of X costs 11.00 EUR per unit, not the 99.00 EUR"),
        "{errors:?}"
    );
}

#[test]
fn the_pools_cost_and_an_empty_spec_load_clean() {
    for spec in ["11.00 EUR", "11 EUR", "", "EUR"] {
        let errors = errors_for(spec);
        assert!(errors.is_empty(), "{{{spec}}}: {errors:?}");
    }
}

/// `infer_tolerance_from_cost` does not widen the check: with it, the stated
/// cost of a sale of 1.5 units feeds a EUR tolerance of 0.1 × 0.5 × 11.30 =
/// 0.565, which a tolerance-based rule let 11.30 through for a pool at 11.00.
/// A claim is held to its own written precision, so 11.30 is refused and
/// 11.00 holds, with the option on or off.
#[test]
fn infer_tolerance_from_cost_does_not_widen_the_claim() {
    for (option, claim, ok) in [
        (true, "11.30", false),
        (false, "11.30", false),
        (true, "11.00", true),
        (true, "11.0", true),
    ] {
        let source = format!(
            "{}{}",
            if option {
                "option \"infer_tolerance_from_cost\" \"TRUE\"\n"
            } else {
                ""
            },
            SOURCE.replace(
                "  Assets:Brokerage  -1 X {SPEC}\n  Assets:Cash  12.00 EUR",
                &format!("  Assets:Brokerage  -1.5 X {{{claim} EUR}}\n  Assets:Cash  18.00 EUR"),
            )
        );
        assert!(source.contains("-1.5 X"), "fixture edit must apply");
        let mut f = tempfile::Builder::new()
            .prefix("average-claim-itfc-")
            .suffix(".beancount")
            .tempfile()
            .expect("create tempfile");
        f.write_all(source.as_bytes()).expect("write fixture");
        let ledger = load(f.path(), &LoadOptions::default()).expect("the ledger loads");
        let refused = ledger
            .errors
            .iter()
            .any(|e| e.message.contains("AVERAGE pool of X costs 11.00"));
        assert_eq!(
            !refused, ok,
            "{claim} (option {option}): {:?}",
            ledger.errors
        );
    }
}
