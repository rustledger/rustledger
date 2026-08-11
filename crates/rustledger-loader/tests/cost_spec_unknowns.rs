//! Cost specs with no number the author wrote must stay UNKNOWN (#2008).
//!
//! Two booking-layer halves of #2008, which share one root cause: the parser
//! invented a number where the author wrote none, and every downstream layer
//! then treated the invention as fact.
//!
//! - **Case 5** (`{USD}` / `{ # USD}`) loaded clean. beancount rejects it with
//!   *"Too many missing numbers for currency group"*. Interpolation already
//!   enforces "at most one unknown per currency group", but `{ # USD}` was
//!   parsed as `Compound { per_unit: 0, total: 0 }` — a perfectly determinable
//!   zero cost — so the rule never saw an unknown to count.
//! - **The misdiagnosis**: a malformed spec like `{, 100.0 USD, , }` had its
//!   `100.0` scraped out, and `rledger check` then reported
//!   `E3001 does not balance: residual 980.10 USD` — an arithmetic complaint
//!   about a typo, whose number this parser produced rather than the author.
//!
//! These run through `load` + `process` rather than the parser alone, because
//! the behavior under test is what the *pipeline* concludes: the parser change
//! is only interesting if interpolation and validation then reach beancount's
//! verdict.

use rustledger_loader::{LoadOptions, process};

/// Load an in-memory ledger and return every error code the pipeline produced.
fn codes(source: &str) -> Vec<String> {
    let mut vfs = rustledger_loader::VirtualFileSystem::new();
    vfs.add_file("/mem/ledger.bean", source);
    let raw = rustledger_loader::Loader::new()
        .with_filesystem(Box::new(vfs))
        .load(std::path::Path::new("/mem/ledger.bean"))
        .expect("in-memory ledger loads");

    let mut out: Vec<String> = raw.errors.iter().map(|e| format!("PARSE:{e}")).collect();
    match process(raw, &LoadOptions::default()) {
        // Code AND message: an interpolation rejection arrives as a generic
        // `BOOK` code, so asserting on the code alone could not tell the
        // too-many-unknowns rule from any other booking failure.
        Ok(ledger) => out.extend(
            ledger
                .errors
                .iter()
                .map(|e| format!("{}:{}", e.code, e.message)),
        ),
        // An interpolation failure is a process-level error, not a per-directive
        // one — case 5 lands here.
        Err(e) => out.push(format!("PROCESS:{e}")),
    }
    out
}

const OPENS: &str = "2014-01-01 open Assets:Invest:AAPL\n\
                     2014-01-01 open Assets:Invest:Cash\n";

/// #2008 case 5, verbatim from `test-cases_ParseLots.CostTotalJustCurrency`.
///
/// Two cost specs with no numbers in one currency group. beancount: *"Too many
/// missing numbers for currency group 'USD'"*.
#[test]
fn two_numberless_cost_specs_in_one_group_are_rejected() {
    let got = codes(&format!(
        "{OPENS}\
         2014-01-01 *\n\
         \x20 Assets:Invest:AAPL   20 AAPL {{USD}}\n\
         \x20 Assets:Invest:AAPL   20 AAPL {{ # USD}}\n\
         \x20 Assets:Invest:Cash    0 USD\n"
    ));
    assert!(
        got.iter().any(|c| c.contains("multiple postings missing")),
        "expected the too-many-unknowns rejection, got {got:?}"
    );
}

/// The other side of that rule, and the one that would break real ledgers if
/// the count were off by one: a SINGLE numberless spec is solvable and must
/// still load. beancount interpolates it too.
#[test]
fn a_single_numberless_cost_spec_still_interpolates() {
    for spec in ["{USD}", "{ # USD}", "{}"] {
        let got = codes(&format!(
            "{OPENS}\
             2014-01-01 *\n\
             \x20 Assets:Invest:AAPL       20 AAPL {spec}\n\
             \x20 Assets:Invest:Cash  -2000.00 USD\n"
        ));
        assert!(
            got.is_empty(),
            "a single unknown is solvable and must load clean: {spec} -> {got:?}"
        );
    }
}

/// `{ # USD}` must not be read as a zero cost. Before #2008 it parsed as
/// `Compound { per_unit: 0, total: 0 }`, which is why the case above loaded
/// clean AND why this transaction used to be reported unbalanced: a 20-unit
/// lot at zero cost leaves the whole 2000.00 as residual.
#[test]
fn hash_with_no_numbers_is_not_a_zero_cost() {
    let got = codes(&format!(
        "{OPENS}\
         2014-01-01 *\n\
         \x20 Assets:Invest:AAPL       20 AAPL {{ # USD}}\n\
         \x20 Assets:Invest:Cash  -2000.00 USD\n"
    ));
    assert!(
        !got.iter().any(|c| c.starts_with("E3001")),
        "a numberless `#` spec must be solved, not treated as zero cost: {got:?}"
    );
}

/// #2008 cases 1 and 2: a malformed spec must not produce a balance complaint
/// built from a number this parser scraped out of the wreckage.
///
/// The parse error must still be reported — the point is to name the real
/// cause, not to fall silent.
#[test]
fn a_malformed_cost_spec_does_not_produce_a_balance_error() {
    for spec in ["{, 100.0 USD, , }", "{45.23 USD / 2015-07-16 / \"blabla\"}"] {
        let got = codes(&format!(
            "{OPENS}\
             2014-01-01 *\n\
             \x20 Assets:Invest:AAPL      10 AAPL {spec}\n\
             \x20 Assets:Invest:Cash  -19.90 USD\n"
        ));
        assert!(
            !got.iter().any(|c| c.starts_with("E3001")),
            "malformed spec must not draw an invented-number balance error: \
             {spec} -> {got:?}"
        );
        assert!(
            got.iter().any(|c| c.starts_with("PARSE:")),
            "the real cause must still be reported: {spec} -> {got:?}"
        );
    }
}

/// The control: a WELL-FORMED spec that genuinely does not balance must still
/// be reported. Without this, "no E3001" above would be satisfied by having
/// broken the balance validator entirely.
#[test]
fn a_well_formed_spec_that_does_not_balance_is_still_reported() {
    let got = codes(&format!(
        "{OPENS}\
         2014-01-01 *\n\
         \x20 Assets:Invest:AAPL      10 AAPL {{100.00 USD}}\n\
         \x20 Assets:Invest:Cash  -19.90 USD\n"
    ));
    assert!(
        got.iter().any(|c| c.starts_with("E3001")),
        "a real imbalance must still be reported: {got:?}"
    );
}
