//! Pipeline-boundary property test for native plugins (#1235).
//!
//! Plugin-process determinism: running a plugin twice on the same input
//! must produce byte-identical output. A nondeterministic plugin (e.g. one
//! that iterates a `HashMap` and emits ops in hash order, or folds errors
//! in nondeterministic order) silently corrupts the whole load pipeline —
//! two runs of the same ledger would disagree. This guards that boundary
//! across a broad sample of the regular-plugin registry.
//!
//! `PluginOutput` deliberately does not implement `PartialEq` (it carries
//! op payloads whose equality is delicate), so we compare via its
//! `serde_json` serialization — an exact-bytes check that is strictly
//! stronger than the pre-existing `ops.len()`-only determinism test in
//! `tla_proptest.rs`.
//!
//! Full cross-plugin *commutativity* (`apply([a,b]) == apply([b,a])` for
//! plugins declared commutative) from #1235 needs a deliberate
//! `COMMUTATIVE` trait-marker design plus per-plugin correctness analysis;
//! it is left as a follow-up. Per-plugin determinism is the safe,
//! verifiable subset and a prerequisite for any commutativity claim.

use proptest::prelude::*;
use rust_decimal::Decimal;
use rustledger_core::{Amount, Directive, NaiveDate, Open, Posting, PriceAnnotation, Transaction};
use rustledger_plugin::{
    NativePluginRegistry, PluginInput, PluginOptions, PluginOutput, directives_to_wrappers,
};

/// Regular plugins exercised for determinism — a broad slice of the
/// registry spanning synthesizers, validators, and mutators, weighted
/// toward those that fold internal `HashSet`/`HashMap` state into their
/// output (the nondeterminism risk this test targets). Names that fail to
/// resolve are skipped (so the list survives registry churn), but at least
/// one must resolve or the test fails as vacuous.
const PLUGINS: &[&str] = &[
    "implicit_prices",
    "check_commodity",
    "onecommodity",
    "noduplicates",
    "unique_prices",
    "leafonly",
    "pedantic",
    "auto_tag",
    "coherent_cost",
    "split_expenses",
    "check_average_cost",
    "close_tree",
    "currency_accounts",
    "generate_base_ccy_prices",
    "check_drained",
    "effective_date",
    "zerosum",
    "valuation",
    "nounused",
    "unrealized",
    "long_short",
    "gain_loss",
];

fn date(day: u32) -> NaiveDate {
    rustledger_core::naive_date(2024, 1, day).unwrap()
}

const ACCOUNTS: &[&str] = &[
    "Assets:Stock",
    "Expenses:Fees",
    "Income:Gains",
    "Assets:Cash",
];

fn amount(currency: &'static str) -> impl Strategy<Value = Amount> {
    (1i64..1_000_000, 0u32..3)
        .prop_map(move |(n, scale)| Amount::new(Decimal::new(n, scale), currency))
}

/// A transaction with a priced posting (so `implicit_prices` has work to
/// do) plus a plain balancing posting.
fn txn() -> impl Strategy<Value = Transaction> {
    (
        1u32..28,
        0usize..ACCOUNTS.len(),
        0usize..ACCOUNTS.len(),
        amount("HOOL"),
        amount("USD"),
        amount("USD"),
    )
        .prop_map(|(day, a, b, units, price, cash)| {
            Transaction::new(date(day), "trade")
                .with_synthesized_posting(
                    Posting::new(ACCOUNTS[a], units).with_price(PriceAnnotation::unit(price)),
                )
                .with_synthesized_posting(Posting::new(ACCOUNTS[b], cash))
        })
}

fn ledger() -> impl Strategy<Value = Vec<Directive>> {
    prop::collection::vec(txn(), 1..8).prop_map(|txns| {
        let mut ds: Vec<Directive> = ACCOUNTS
            .iter()
            .map(|a| Directive::Open(Open::new(date(1), *a)))
            .collect();
        ds.extend(txns.into_iter().map(Directive::Transaction));
        ds
    })
}

fn make_input(directives: &[Directive]) -> PluginInput {
    PluginInput {
        directives: directives_to_wrappers(directives),
        options: PluginOptions {
            operating_currencies: vec!["USD".to_string()],
            title: None,
        },
        config: None,
    }
}

/// Serialize an output to a canonical string for exact comparison.
fn fingerprint(output: &PluginOutput) -> String {
    serde_json::to_string(output).expect("PluginOutput serializes")
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    #[test]
    fn plugin_process_is_deterministic(directives in ledger()) {
        let registry = NativePluginRegistry::global();
        let input = make_input(&directives);

        let mut resolved = 0usize;
        for &name in PLUGINS {
            let Some(plugin) = registry.find_regular(name) else { continue };
            resolved += 1;

            let first = fingerprint(&plugin.process(input.clone()));
            let second = fingerprint(&plugin.process(input.clone()));
            prop_assert_eq!(
                first,
                second,
                "plugin `{}` produced different output across two identical runs",
                name
            );
        }

        prop_assert!(resolved > 0, "no candidate plugins resolved from the registry");
    }
}
