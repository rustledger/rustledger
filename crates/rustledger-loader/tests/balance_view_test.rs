//! Integration tests for `Ledger::balance_view()`.
//!
//! Pins the two architectural guarantees:
//!
//! 1. `Ledger.directives` is **source-faithful**: `Pad` directives
//!    survive the load pipeline as `Pad` directives.
//! 2. `Ledger.balance_view()` returns a **derived view**: pads are
//!    merged with synthesized `P`-flag transactions suitable for
//!    inventory math.
//!
//! Together these tests pin the source-vs-derived split that the
//! `refactor/pad-source-faithful-directives` architecture rests on.
//! A regression that pre-expands at the loader (PR #1301's step 10)
//! would fail (1); a regression that drops the expansion entirely
//! would fail (2).

use rustledger_core::Directive;
use rustledger_loader::{LoadOptions, load};
use std::io::Write;

/// The canonical #1288 fixture: one pad+balance pair, expected
/// `Assets:Wallet` ends at 965 USD = 1000 (opening) - 10 (Jun 1
/// expense) - 15 (pad: 990 → 975) - 10 (Jun 2 expense).
const PADDED_SOURCE: &str = r#"option "operating_currency" "USD"

2026-01-01 open Assets:Wallet USD
2026-01-01 open Equity:Void USD
2026-01-01 open Expenses:Expense USD

2026-01-01 * "opening"
  Assets:Wallet  1000 USD
  Equity:Void

2026-06-01 * "expense"
  Expenses:Expense  10 USD
  Assets:Wallet

2026-06-01 pad Assets:Wallet Equity:Void
2026-06-02 balance Assets:Wallet 975 USD

2026-06-02 * "expense"
  Expenses:Expense  10 USD
  Assets:Wallet
"#;

fn write_fixture(content: &str) -> tempfile::NamedTempFile {
    let mut f = tempfile::Builder::new()
        .prefix("balance-view-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(content.as_bytes()).expect("write fixture");
    f
}

/// `Ledger.directives` keeps `Pad` directives as `Pad`. The loader
/// must NOT pre-expand them into synthesized transactions — that's
/// what `balance_view()` is for.
#[test]
fn directives_field_keeps_pads_as_pads() {
    let fixture = write_fixture(PADDED_SOURCE);
    let opts = LoadOptions {
        validate: false,
        ..Default::default()
    };
    let ledger = load(fixture.path(), &opts).expect("load");

    let pad_count = ledger
        .directives
        .iter()
        .filter(|s| matches!(s.value, Directive::Pad(_)))
        .count();
    assert_eq!(
        pad_count, 1,
        "Ledger.directives must keep Pads as Pads (source-faithful). \
         A loader-side expansion regression would make this 0."
    );

    // Synth P-flag transactions must NOT be in the source view.
    let p_flag_count = ledger
        .directives
        .iter()
        .filter(|s| matches!(&s.value, Directive::Transaction(t) if t.flag == 'P'))
        .count();
    assert_eq!(
        p_flag_count, 0,
        "Ledger.directives must NOT contain synth P-flag transactions \
         (those are the derived view). A loader-side pre-expansion \
         would put one here."
    );
}

/// `Ledger.balance_view()` returns the merged view: original
/// directives preserved verbatim, AND synthesized P-flag
/// transactions added for each pad-balance pair.
///
/// Preserving Pads in the view matters for BQL queries that filter
/// on `WHERE type = 'pad'` (Python-compat) and for the multi-pad
/// shadowing correctness (#1300). Inventory-walking consumers
/// iterate `Directive::Transaction` and ignore Pads, so the
/// preserved Pads are invisible to balance math.
#[test]
fn balance_view_adds_synth_transaction_alongside_original_pad() {
    let fixture = write_fixture(PADDED_SOURCE);
    let opts = LoadOptions {
        validate: false,
        ..Default::default()
    };
    let ledger = load(fixture.path(), &opts).expect("load");
    let view = ledger.balance_view();

    let pad_count = view
        .iter()
        .filter(|d| matches!(d, Directive::Pad(_)))
        .count();
    assert_eq!(
        pad_count, 1,
        "balance_view() must preserve the original Pad directive so \
         BQL `WHERE type = 'pad'` queries continue to match it.",
    );

    let synth_count = view
        .iter()
        .filter(|d| matches!(d, Directive::Transaction(t) if t.flag == 'P'))
        .count();
    assert_eq!(
        synth_count, 1,
        "balance_view() must contain exactly one synthesized P-flag \
         transaction representing the pad's effect."
    );
}

/// `balance_view()` is a pure function of `directives`: calling it
/// repeatedly yields equivalent results, and the source view is
/// unchanged after the call.
#[test]
fn balance_view_does_not_mutate_source_directives() {
    let fixture = write_fixture(PADDED_SOURCE);
    let opts = LoadOptions {
        validate: false,
        ..Default::default()
    };
    let ledger = load(fixture.path(), &opts).expect("load");

    let len_before = ledger.directives.len();
    let _ = ledger.balance_view();
    let len_after = ledger.directives.len();

    assert_eq!(
        len_before, len_after,
        "balance_view() must not change the length of self.directives"
    );
    let pads_after = ledger
        .directives
        .iter()
        .filter(|s| matches!(s.value, Directive::Pad(_)))
        .count();
    assert_eq!(
        pads_after, 1,
        "balance_view() must not remove or transform Pads in self.directives"
    );
}

/// On a pad-free ledger, `balance_view()` returns the same shape as
/// `directives` (modulo Spanned stripping): no spurious synth
/// transactions, no dropped directives. This guards against an
/// expand-pads regression that emits ghost transactions on
/// pad-free input.
#[test]
fn balance_view_on_pad_free_ledger_is_equivalent_to_directives() {
    const PAD_FREE: &str = r#"option "operating_currency" "USD"

2026-01-01 open Assets:Wallet USD
2026-01-01 open Equity:Void USD

2026-01-01 * "opening"
  Assets:Wallet  1000 USD
  Equity:Void
"#;
    let fixture = write_fixture(PAD_FREE);
    let opts = LoadOptions {
        validate: false,
        ..Default::default()
    };
    let ledger = load(fixture.path(), &opts).expect("load");
    let view = ledger.balance_view();

    assert_eq!(
        view.len(),
        ledger.directives.len(),
        "balance_view() must have the same length as directives on \
         pad-free input (no spurious synth, no drops)."
    );

    let synth_count = view
        .iter()
        .filter(|d| matches!(d, Directive::Transaction(t) if t.flag == 'P'))
        .count();
    assert_eq!(
        synth_count, 0,
        "balance_view() must not emit synth P-flag transactions on \
         pad-free input."
    );
}
