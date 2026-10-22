//! Integration tests for native plugins.
//!
//! Tests are converted from beancount's plugin test suite.

use rustledger_plugin::native::{
    AutoTagPlugin, BoxAccrualPlugin, CapitalGainsGainLossPlugin, CapitalGainsLongShortPlugin,
    CheckAverageCostPlugin, CheckCommodityPlugin, CheckDrainedPlugin, CommodityAttrPlugin,
    CurrencyAccountsPlugin, EffectiveDatePlugin, ForecastPlugin, GenerateBaseCcyPricesPlugin,
    ImplicitPricesPlugin, LeafOnlyPlugin, NativePlugin, NativePluginRegistry, NoDuplicatesPlugin,
    NoUnusedPlugin, OneCommodityPlugin, PedanticPlugin, RenameAccountsPlugin, RxTxnPlugin,
    SellGainsPlugin, SplitExpensesPlugin, UniquePricesPlugin, UnrealizedPlugin, ZerosumPlugin,
};
use rustledger_plugin::test_helpers::materialize_ops;
use rustledger_plugin::types::*;

// ============================================================================
// Helper Functions
// ============================================================================

/// Test-only `PluginOutput` shim that fronts the ops protocol with the
/// pre-refactor `directives` getter. Lets us migrate `output.directives`
/// sites incrementally without inverting the input/output flow in every
/// individual assertion. Computed once at the `let output = ...` site.
struct ProcessedOutput {
    directives: Vec<DirectiveWrapper>,
    errors: Vec<PluginError>,
}

#[allow(dead_code)]
fn process_and_materialize<P: NativePlugin + ?Sized>(
    plugin: &P,
    input: PluginInput,
) -> ProcessedOutput {
    let input_dirs = input.directives.clone();
    let out = plugin.process(input);
    let directives = materialize_ops(&input_dirs, &out);
    ProcessedOutput {
        directives,
        errors: out.errors,
    }
}

fn make_input(directives: Vec<DirectiveWrapper>) -> PluginInput {
    PluginInput {
        directives,
        options: PluginOptions {
            operating_currencies: vec!["USD".to_string()],
            title: None,
            ..Default::default()
        },
        config: None,
    }
}

fn make_open(date: &str, account: &str) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: "open".to_string(),
        date: date.to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Open(OpenData {
            account: account.to_string(),
            currencies: vec![],
            booking: None,
            metadata: vec![],
        }),
    }
}

fn make_transaction(
    date: &str,
    narration: &str,
    postings: Vec<(&str, &str, &str)>,
) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: "transaction".to_string(),
        date: date.to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Transaction(TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: narration.to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: postings
                .into_iter()
                .map(|(account, number, currency)| PostingData {
                    account: account.to_string(),
                    units: Some(AmountData {
                        number: number.to_string(),
                        currency: currency.to_string(),
                    }),
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                })
                .collect(),
        }),
    }
}

fn make_transaction_with_cost(
    date: &str,
    narration: &str,
    account: &str,
    units: (&str, &str),
    cost: (&str, &str),
    other_account: &str,
) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: "transaction".to_string(),
        date: date.to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Transaction(TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: narration.to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![
                PostingData {
                    account: account.to_string(),
                    units: Some(AmountData {
                        number: units.0.to_string(),
                        currency: units.1.to_string(),
                    }),
                    cost: Some(CostData {
                        number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                            value: cost.0.to_string(),
                        }),
                        currency: Some(cost.1.to_string()),
                        date: None,
                        label: None,
                        merge: false,
                    }),
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
                PostingData {
                    account: other_account.to_string(),
                    units: None,
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
            ],
        }),
    }
}

fn make_price(date: &str, currency: &str, amount: &str, quote_currency: &str) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: "price".to_string(),
        date: date.to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Price(PriceData {
            currency: currency.to_string(),
            amount: AmountData {
                number: amount.to_string(),
                currency: quote_currency.to_string(),
            },
            metadata: vec![],
        }),
    }
}

/// Create a transaction with BOTH cost and a `@@` total price annotation.
/// Used by the zero-units-fall-through-to-cost test which exercises the
/// currency-pairing fix (see `test_implicit_prices_zero_unit_total_falls_through_to_cost_currency`).
fn make_transaction_with_cost_and_price_total(
    date: &str,
    narration: &str,
    account: &str,
    units: (&str, &str),
    cost: (&str, &str),
    price_total: (&str, &str),
    other_account: &str,
) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: "transaction".to_string(),
        date: date.to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Transaction(TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: narration.to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![
                PostingData {
                    account: account.to_string(),
                    units: Some(AmountData {
                        number: units.0.to_string(),
                        currency: units.1.to_string(),
                    }),
                    cost: Some(CostData {
                        number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                            value: cost.0.to_string(),
                        }),
                        currency: Some(cost.1.to_string()),
                        date: None,
                        label: None,
                        merge: false,
                    }),
                    price: Some(PriceAnnotationData {
                        is_total: true, // ← @@
                        amount: Some(AmountData {
                            number: price_total.0.to_string(),
                            currency: price_total.1.to_string(),
                        }),
                        number: None,
                        currency: None,
                    }),
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
                PostingData {
                    account: other_account.to_string(),
                    units: None,
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
            ],
        }),
    }
}

/// Create a transaction with BOTH cost and price (for capital gains on sales).
fn make_transaction_with_cost_and_price(
    date: &str,
    narration: &str,
    account: &str,
    units: (&str, &str),
    cost: (&str, &str),
    price: (&str, &str),
    other_account: &str,
) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: "transaction".to_string(),
        date: date.to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Transaction(TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: narration.to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![
                PostingData {
                    account: account.to_string(),
                    units: Some(AmountData {
                        number: units.0.to_string(),
                        currency: units.1.to_string(),
                    }),
                    cost: Some(CostData {
                        number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                            value: cost.0.to_string(),
                        }),
                        currency: Some(cost.1.to_string()),
                        date: None,
                        label: None,
                        merge: false,
                    }),
                    price: Some(PriceAnnotationData {
                        is_total: false,
                        amount: Some(AmountData {
                            number: price.0.to_string(),
                            currency: price.1.to_string(),
                        }),
                        number: None,
                        currency: None,
                    }),
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
                PostingData {
                    account: other_account.to_string(),
                    units: None,
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
            ],
        }),
    }
}

fn make_commodity(date: &str, currency: &str) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: "commodity".to_string(),
        date: date.to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Commodity(CommodityData {
            currency: currency.to_string(),
            metadata: vec![],
        }),
    }
}

// ============================================================================
// LeafOnlyPlugin Tests (from leafonly_test.py)
// ============================================================================

/// Test posting to non-leaf account generates error.
/// Converted from: `test_leaf_only1`
#[test]
fn test_leafonly_error_on_parent_account() {
    let plugin = LeafOnlyPlugin;

    // Create ledger with parent (Expenses:Food) and child (Expenses:Food:Restaurant)
    let input = make_input(vec![
        make_open("2024-01-01", "Expenses:Food"),
        make_open("2024-01-01", "Expenses:Food:Restaurant"),
        make_open("2024-01-01", "Assets:Cash"),
        // Post to child account - OK
        make_transaction(
            "2024-01-15",
            "Good lunch",
            vec![
                ("Expenses:Food:Restaurant", "25.00", "USD"),
                ("Assets:Cash", "-25.00", "USD"),
            ],
        ),
        // Post to parent account - ERROR
        make_transaction(
            "2024-01-16",
            "Bad posting to parent",
            vec![
                ("Expenses:Food", "30.00", "USD"),
                ("Assets:Cash", "-30.00", "USD"),
            ],
        ),
    ]);

    let output = process_and_materialize(&plugin, input);

    // Should have 1 error for posting to Expenses:Food
    assert_eq!(
        output.errors.len(),
        1,
        "expected 1 error for parent posting"
    );
    assert!(
        output.errors[0].message.contains("Expenses:Food"),
        "error should mention the parent account"
    );
}

/// A parent whose only child is opened (or named by another directive)
/// and never posted to is still a parent, as in beancount's realization
/// (#2500 review: native leafonly missed it; bean-check reports it).
#[test]
fn test_leafonly_error_on_parent_whose_child_is_only_opened() {
    let plugin = LeafOnlyPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Assets:Bank:Sub:Deeper"),
        make_open("2024-01-01", "Expenses:Food"),
        make_transaction(
            "2024-01-15",
            "Lunch",
            vec![
                ("Expenses:Food", "25.00", "USD"),
                ("Assets:Bank", "-25.00", "USD"),
            ],
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(output.errors.len(), 1, "{:?}", output.errors);
    assert!(output.errors[0].message.contains("'Assets:Bank'"));
}

/// Test all postings to leaf accounts - no errors.
/// Converted from: `test_leaf_only3` behavior
#[test]
fn test_leafonly_ok_on_leaf_accounts() {
    let plugin = LeafOnlyPlugin;

    let input = make_input(vec![
        make_open("2024-01-01", "Expenses:Food"),
        make_open("2024-01-01", "Expenses:Food:Restaurant"),
        make_open("2024-01-01", "Assets:Cash"),
        // Only post to leaf accounts
        make_transaction(
            "2024-01-15",
            "Lunch",
            vec![
                ("Expenses:Food:Restaurant", "25.00", "USD"),
                ("Assets:Cash", "-25.00", "USD"),
            ],
        ),
    ]);

    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty(), "expected no errors");
}

// ============================================================================
// NoDuplicatesPlugin Tests (from noduplicates_test.py)
// ============================================================================

/// Test duplicate transactions are detected.
/// Converted from: `test_validate_no_duplicates__transaction`
#[test]
fn test_noduplicates_transaction() {
    let plugin = NoDuplicatesPlugin;

    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        // First transaction
        make_transaction(
            "2024-01-15",
            "Grocery Store",
            vec![
                ("Expenses:Food", "50.00", "USD"),
                ("Assets:Bank", "-50.00", "USD"),
            ],
        ),
        // Duplicate transaction - same date, payee, amounts
        make_transaction(
            "2024-01-15",
            "Grocery Store",
            vec![
                ("Expenses:Food", "50.00", "USD"),
                ("Assets:Bank", "-50.00", "USD"),
            ],
        ),
    ]);

    let output = process_and_materialize(&plugin, input);

    assert_eq!(output.errors.len(), 1, "expected 1 duplicate error");
    assert!(
        output.errors[0].message.contains("Duplicate"),
        "error should mention duplicate"
    );
}

/// Test non-duplicate transactions pass.
#[test]
fn test_noduplicates_ok_different_amounts() {
    let plugin = NoDuplicatesPlugin;

    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        make_transaction(
            "2024-01-15",
            "Grocery Store",
            vec![
                ("Expenses:Food", "50.00", "USD"),
                ("Assets:Bank", "-50.00", "USD"),
            ],
        ),
        // Different amount - not a duplicate
        make_transaction(
            "2024-01-15",
            "Grocery Store",
            vec![
                ("Expenses:Food", "75.00", "USD"),
                ("Assets:Bank", "-75.00", "USD"),
            ],
        ),
    ]);

    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty(), "expected no errors");
}

/// Regression for issue #746: transactions that share date, narration, and
/// postings but have **distinct `^link` values** must not be flagged as
/// duplicates. This mirrors Python beancount's `hash_entry`, which folds
/// `links` into the transaction hash, and is the idiomatic beancount way
/// to disambiguate legitimate identical postings (e.g. two $100 ATM
/// withdrawals on the same day imported from a bank statement).
#[test]
fn test_noduplicates_distinct_links_are_not_duplicates() {
    let plugin = NoDuplicatesPlugin;

    let mut txn_a = make_transaction(
        "2024-06-11",
        "ATM Withdrawal",
        vec![
            ("Assets:Checking:Test", "-100.00", "USD"),
            ("Expenses:ATM", "100.00", "USD"),
        ],
    );
    if let DirectiveData::Transaction(t) = &mut txn_a.data {
        t.links = vec!["stmt-2024-06-seq1".to_string()];
    }

    let mut txn_b = make_transaction(
        "2024-06-11",
        "ATM Withdrawal",
        vec![
            ("Assets:Checking:Test", "-100.00", "USD"),
            ("Expenses:ATM", "100.00", "USD"),
        ],
    );
    if let DirectiveData::Transaction(t) = &mut txn_b.data {
        t.links = vec!["stmt-2024-06-seq2".to_string()];
    }

    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Checking:Test"),
        make_open("2024-01-01", "Expenses:ATM"),
        txn_a,
        txn_b,
    ]);

    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "distinct ^link values should disambiguate otherwise-identical transactions, got: {:?}",
        output.errors
    );
}

/// Regression for issue #746: tags are also part of structural identity
/// per beancount's `hash_entry`, so distinct tags on otherwise-identical
/// transactions must disambiguate them.
#[test]
fn test_noduplicates_distinct_tags_are_not_duplicates() {
    let plugin = NoDuplicatesPlugin;

    let mut txn_a = make_transaction(
        "2024-01-15",
        "Coffee",
        vec![
            ("Assets:Bank", "-5.00", "USD"),
            ("Expenses:Food", "5.00", "USD"),
        ],
    );
    if let DirectiveData::Transaction(t) = &mut txn_a.data {
        t.tags = vec!["morning".to_string()];
    }

    let mut txn_b = make_transaction(
        "2024-01-15",
        "Coffee",
        vec![
            ("Assets:Bank", "-5.00", "USD"),
            ("Expenses:Food", "5.00", "USD"),
        ],
    );
    if let DirectiveData::Transaction(t) = &mut txn_b.data {
        t.tags = vec!["afternoon".to_string()];
    }

    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        txn_a,
        txn_b,
    ]);

    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "distinct tags should disambiguate otherwise-identical transactions, got: {:?}",
        output.errors
    );
}

/// Tags and links are beancount `frozenset`s, so a tag that appears twice
/// in a `Vec<String>` (which the parser could emit) must collapse to a
/// single member for hashing purposes.
#[test]
fn test_noduplicates_duplicate_tags_collapse_to_set() {
    let plugin = NoDuplicatesPlugin;

    let mut txn_a = make_transaction(
        "2024-01-15",
        "Coffee",
        vec![
            ("Assets:Bank", "-5.00", "USD"),
            ("Expenses:Food", "5.00", "USD"),
        ],
    );
    if let DirectiveData::Transaction(t) = &mut txn_a.data {
        t.tags = vec!["morning".to_string(), "morning".to_string()];
    }

    let mut txn_b = make_transaction(
        "2024-01-15",
        "Coffee",
        vec![
            ("Assets:Bank", "-5.00", "USD"),
            ("Expenses:Food", "5.00", "USD"),
        ],
    );
    if let DirectiveData::Transaction(t) = &mut txn_b.data {
        t.tags = vec!["morning".to_string()];
    }

    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        txn_a,
        txn_b,
    ]);

    let output = process_and_materialize(&plugin, input);
    assert_eq!(
        output.errors.len(),
        1,
        "a tag repeated in the Vec must collapse to a set member and hash \
         equal to a single occurrence, got: {:?}",
        output.errors
    );
}

/// Regression: the tag and link hash streams are separated by length
/// prefixes so `tags={a,b}, links={}` must NOT collide with
/// `tags={a}, links={b}`. Without the boundary the concatenated
/// sort-and-hash approach silently folded these two distinct inputs
/// together.
#[test]
fn test_noduplicates_tag_link_boundary_no_collision() {
    let plugin = NoDuplicatesPlugin;

    let mut txn_a = make_transaction(
        "2024-01-15",
        "Coffee",
        vec![
            ("Assets:Bank", "-5.00", "USD"),
            ("Expenses:Food", "5.00", "USD"),
        ],
    );
    if let DirectiveData::Transaction(t) = &mut txn_a.data {
        t.tags = vec!["a".to_string(), "b".to_string()];
        t.links = vec![];
    }

    let mut txn_b = make_transaction(
        "2024-01-15",
        "Coffee",
        vec![
            ("Assets:Bank", "-5.00", "USD"),
            ("Expenses:Food", "5.00", "USD"),
        ],
    );
    if let DirectiveData::Transaction(t) = &mut txn_b.data {
        t.tags = vec!["a".to_string()];
        t.links = vec!["b".to_string()];
    }

    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        txn_a,
        txn_b,
    ]);

    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "tags=[a,b] with no links must NOT collide with tags=[a] links=[b], \
         got: {:?}",
        output.errors
    );
}

/// Tags and links are beancount sets — the order the parser emits them
/// must not influence the duplicate hash.
#[test]
fn test_noduplicates_tag_order_independent() {
    let plugin = NoDuplicatesPlugin;

    let mut txn_a = make_transaction(
        "2024-01-15",
        "Coffee",
        vec![
            ("Assets:Bank", "-5.00", "USD"),
            ("Expenses:Food", "5.00", "USD"),
        ],
    );
    if let DirectiveData::Transaction(t) = &mut txn_a.data {
        t.tags = vec!["morning".to_string(), "caffeine".to_string()];
    }

    let mut txn_b = make_transaction(
        "2024-01-15",
        "Coffee",
        vec![
            ("Assets:Bank", "-5.00", "USD"),
            ("Expenses:Food", "5.00", "USD"),
        ],
    );
    if let DirectiveData::Transaction(t) = &mut txn_b.data {
        // Same tags, reversed order.
        t.tags = vec!["caffeine".to_string(), "morning".to_string()];
    }

    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        txn_a,
        txn_b,
    ]);

    let output = process_and_materialize(&plugin, input);
    assert_eq!(
        output.errors.len(),
        1,
        "reordered but identical tag sets should hash equal and be flagged as duplicate, got: {:?}",
        output.errors
    );
}

/// Transactions differing only in cost spec must not collide in the
/// duplicate hash. Cost is part of a posting's structural identity per
/// beancount's `hash_entry`.
#[test]
fn test_noduplicates_distinct_costs_are_not_duplicates() {
    let plugin = NoDuplicatesPlugin;

    let txn_a = make_transaction_with_cost(
        "2024-01-15",
        "Buy stock",
        "Assets:Stock",
        ("10", "AAPL"),
        ("150.00", "USD"),
        "Assets:Cash",
    );
    let txn_b = make_transaction_with_cost(
        "2024-01-15",
        "Buy stock",
        "Assets:Stock",
        ("10", "AAPL"),
        ("160.00", "USD"), // different cost
        "Assets:Cash",
    );

    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Stock"),
        make_open("2024-01-01", "Assets:Cash"),
        txn_a,
        txn_b,
    ]);

    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "distinct cost specs should disambiguate otherwise-identical transactions, got: {:?}",
        output.errors
    );
}

/// Transactions differing only in price annotation must not collide in
/// the duplicate hash.
#[test]
fn test_noduplicates_distinct_prices_are_not_duplicates() {
    let plugin = NoDuplicatesPlugin;

    let txn_a = make_transaction_with_price(
        "2024-01-15",
        "Sell stock",
        "Assets:Stock",
        ("-5", "AAPL"),
        ("200.00", "USD"),
        "Assets:Cash",
    );
    let txn_b = make_transaction_with_price(
        "2024-01-15",
        "Sell stock",
        "Assets:Stock",
        ("-5", "AAPL"),
        ("210.00", "USD"), // different price
        "Assets:Cash",
    );

    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Stock"),
        make_open("2024-01-01", "Assets:Cash"),
        txn_a,
        txn_b,
    ]);

    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "distinct prices should disambiguate otherwise-identical transactions, got: {:?}",
        output.errors
    );
}

/// Metadata is intentionally NOT part of the duplicate hash — matches
/// Python beancount's `hash_entry(exclude_meta=True)` default for the
/// noduplicates plugin. Two transactions that differ only on metadata
/// must still be flagged as duplicates.
#[test]
fn test_noduplicates_metadata_differences_are_still_duplicates() {
    use rustledger_plugin_types::MetaValueData;

    let plugin = NoDuplicatesPlugin;

    let mut txn_a = make_transaction(
        "2024-01-15",
        "Grocery Store",
        vec![
            ("Expenses:Food", "50.00", "USD"),
            ("Assets:Bank", "-50.00", "USD"),
        ],
    );
    if let DirectiveData::Transaction(t) = &mut txn_a.data {
        t.metadata = vec![(
            "reference".to_string(),
            MetaValueData::String("A".to_string()),
        )];
    }

    let mut txn_b = make_transaction(
        "2024-01-15",
        "Grocery Store",
        vec![
            ("Expenses:Food", "50.00", "USD"),
            ("Assets:Bank", "-50.00", "USD"),
        ],
    );
    if let DirectiveData::Transaction(t) = &mut txn_b.data {
        t.metadata = vec![(
            "reference".to_string(),
            MetaValueData::String("B".to_string()),
        )];
    }

    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        txn_a,
        txn_b,
    ]);

    let output = process_and_materialize(&plugin, input);
    assert_eq!(
        output.errors.len(),
        1,
        "metadata-only differences must not disambiguate (matches beancount \
         exclude_meta=True), got: {:?}",
        output.errors
    );
}

/// Transactions differing only in flag (`*` vs `!`) are structurally
/// different and must not collide in the duplicate hash.
#[test]
fn test_noduplicates_distinct_flags_are_not_duplicates() {
    let plugin = NoDuplicatesPlugin;

    let mut txn_a = make_transaction(
        "2024-01-15",
        "Coffee",
        vec![
            ("Assets:Bank", "-5.00", "USD"),
            ("Expenses:Food", "5.00", "USD"),
        ],
    );
    if let DirectiveData::Transaction(t) = &mut txn_a.data {
        t.flag = "*".to_string();
    }

    let mut txn_b = make_transaction(
        "2024-01-15",
        "Coffee",
        vec![
            ("Assets:Bank", "-5.00", "USD"),
            ("Expenses:Food", "5.00", "USD"),
        ],
    );
    if let DirectiveData::Transaction(t) = &mut txn_b.data {
        t.flag = "!".to_string();
    }

    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        txn_a,
        txn_b,
    ]);

    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "distinct flags should disambiguate otherwise-identical transactions, got: {:?}",
        output.errors
    );
}

// ============================================================================
// NoDuplicatesPlugin — exhaustive edge-case coverage (issue #746)
// ============================================================================
//
// The noduplicates plugin mirrors Python beancount's
// `beancount.core.compare.hash_entry`. The tests below walk every field
// that contributes to structural identity (or is deliberately excluded)
// and pin the expected behavior, so any future change to the hash
// function is caught immediately.

/// Shorthand: build a simple 2-posting transaction, apply a per-field
/// mutation via a closure, and return the wrapper. Lets each test
/// express "identical to baseline except for X" in a single expression.
fn make_txn_with<F: FnOnce(&mut TransactionData)>(
    date: &str,
    narration: &str,
    postings: Vec<(&str, &str, &str)>,
    mutate: F,
) -> DirectiveWrapper {
    let mut wrapper = make_transaction(date, narration, postings);
    if let DirectiveData::Transaction(t) = &mut wrapper.data {
        mutate(t);
    }
    wrapper
}

// ---------- Transaction-level identity ----------

/// Different dates must never collide, even with otherwise-identical
/// fields.
#[test]
fn test_noduplicates_distinct_dates_are_not_duplicates() {
    let plugin = NoDuplicatesPlugin;
    let postings = vec![
        ("Expenses:Food", "5.00", "USD"),
        ("Assets:Bank", "-5.00", "USD"),
    ];
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        make_transaction("2024-01-15", "Coffee", postings.clone()),
        make_transaction("2024-01-16", "Coffee", postings),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "different dates must not collide, got: {:?}",
        output.errors
    );
}

/// Distinct narration text disambiguates duplicates.
#[test]
fn test_noduplicates_distinct_narration_are_not_duplicates() {
    let plugin = NoDuplicatesPlugin;
    let postings = vec![
        ("Expenses:Food", "5.00", "USD"),
        ("Assets:Bank", "-5.00", "USD"),
    ];
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        make_transaction("2024-01-15", "Coffee", postings.clone()),
        make_transaction("2024-01-15", "Lunch", postings),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "different narration must not collide, got: {:?}",
        output.errors
    );
}

/// Distinct payees disambiguate duplicates.
#[test]
fn test_noduplicates_distinct_payees_are_not_duplicates() {
    let plugin = NoDuplicatesPlugin;
    let postings = vec![
        ("Expenses:Food", "5.00", "USD"),
        ("Assets:Bank", "-5.00", "USD"),
    ];
    let txn_a = make_txn_with("2024-01-15", "Coffee", postings.clone(), |t| {
        t.payee = Some("Starbucks".to_string());
    });
    let txn_b = make_txn_with("2024-01-15", "Coffee", postings, |t| {
        t.payee = Some("Blue Bottle".to_string());
    });
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        txn_a,
        txn_b,
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "different payees must not collide, got: {:?}",
        output.errors
    );
}

/// `None` payee is distinct from `Some("")` — Rust's derived
/// `Option::hash` already discriminates them, but pin it so a future
/// custom hash can't regress.
#[test]
fn test_noduplicates_none_vs_empty_payee_differ() {
    let plugin = NoDuplicatesPlugin;
    let postings = vec![
        ("Expenses:Food", "5.00", "USD"),
        ("Assets:Bank", "-5.00", "USD"),
    ];
    let txn_a = make_txn_with("2024-01-15", "Coffee", postings.clone(), |t| {
        t.payee = None;
    });
    let txn_b = make_txn_with("2024-01-15", "Coffee", postings, |t| {
        t.payee = Some(String::new());
    });
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        txn_a,
        txn_b,
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "None payee must not collide with Some(\"\"), got: {:?}",
        output.errors
    );
}

/// Links are a set, just like tags — order-independence test.
#[test]
fn test_noduplicates_link_order_independent() {
    let plugin = NoDuplicatesPlugin;
    let postings = vec![
        ("Expenses:Food", "5.00", "USD"),
        ("Assets:Bank", "-5.00", "USD"),
    ];
    let txn_a = make_txn_with("2024-01-15", "Coffee", postings.clone(), |t| {
        t.links = vec!["stmt-a".to_string(), "stmt-b".to_string()];
    });
    let txn_b = make_txn_with("2024-01-15", "Coffee", postings, |t| {
        t.links = vec!["stmt-b".to_string(), "stmt-a".to_string()];
    });
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        txn_a,
        txn_b,
    ]);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(
        output.errors.len(),
        1,
        "reordered link sets should hash equal, got: {:?}",
        output.errors
    );
}

/// Empty tags/links vectors should be indistinguishable from absent
/// tags/links. Matches beancount `frozenset()` == `frozenset([])`.
#[test]
fn test_noduplicates_empty_vs_absent_tags_are_duplicates() {
    let plugin = NoDuplicatesPlugin;
    let postings = vec![
        ("Expenses:Food", "5.00", "USD"),
        ("Assets:Bank", "-5.00", "USD"),
    ];
    let txn_a = make_transaction("2024-01-15", "Coffee", postings.clone());
    let txn_b = make_txn_with("2024-01-15", "Coffee", postings, |t| {
        t.tags = vec![];
        t.links = vec![];
    });
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        txn_a,
        txn_b,
    ]);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(
        output.errors.len(),
        1,
        "empty tags/links must hash equal to absent tags/links, got: {:?}",
        output.errors
    );
}

// ---------- Posting-level identity ----------

/// Different account on a posting must disambiguate.
#[test]
fn test_noduplicates_distinct_accounts_are_not_duplicates() {
    let plugin = NoDuplicatesPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Expenses:Food"),
        make_transaction(
            "2024-01-15",
            "Coffee",
            vec![
                ("Assets:Bank", "-5.00", "USD"),
                ("Expenses:Food", "5.00", "USD"),
            ],
        ),
        make_transaction(
            "2024-01-15",
            "Coffee",
            vec![
                ("Assets:Cash", "-5.00", "USD"), // different account
                ("Expenses:Food", "5.00", "USD"),
            ],
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "different account must not collide, got: {:?}",
        output.errors
    );
}

/// Different number of postings must disambiguate.
#[test]
fn test_noduplicates_distinct_posting_count_are_not_duplicates() {
    let plugin = NoDuplicatesPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        make_open("2024-01-01", "Expenses:Fee"),
        make_transaction(
            "2024-01-15",
            "Coffee",
            vec![
                ("Assets:Bank", "-5.00", "USD"),
                ("Expenses:Food", "5.00", "USD"),
            ],
        ),
        make_transaction(
            "2024-01-15",
            "Coffee",
            vec![
                ("Assets:Bank", "-5.00", "USD"),
                ("Expenses:Food", "4.50", "USD"),
                ("Expenses:Fee", "0.50", "USD"),
            ],
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "different posting counts must not collide, got: {:?}",
        output.errors
    );
}

/// Posting order is NOT part of structural identity: beancount's
/// `stable_hash_namedtuple` hashes a list element-wise and sorts the
/// hashes, so bean-check reports the same postings in another order as a
/// duplicate (#2599; this test asserted the opposite before, which the
/// oracle contradicts).
#[test]
fn test_noduplicates_reordered_postings_are_duplicates() {
    let plugin = NoDuplicatesPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        make_transaction(
            "2024-01-15",
            "Coffee",
            vec![
                ("Assets:Bank", "-5.00", "USD"),
                ("Expenses:Food", "5.00", "USD"),
            ],
        ),
        make_transaction(
            "2024-01-15",
            "Coffee",
            vec![
                ("Expenses:Food", "5.00", "USD"),
                ("Assets:Bank", "-5.00", "USD"),
            ],
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(
        output.errors.len(),
        1,
        "reordered postings are a duplicate, as bean-check reports, got: {:?}",
        output.errors
    );
}

/// A posting with `units: None` (auto-balancing) is structurally
/// different from one with explicit units.
#[test]
fn test_noduplicates_none_vs_some_units_differ() {
    let plugin = NoDuplicatesPlugin;
    // txn_a: both postings have units
    let txn_a = make_transaction(
        "2024-01-15",
        "Coffee",
        vec![
            ("Expenses:Food", "5.00", "USD"),
            ("Assets:Bank", "-5.00", "USD"),
        ],
    );
    // txn_b: auto-balancing second posting
    let mut txn_b = make_transaction(
        "2024-01-15",
        "Coffee",
        vec![
            ("Expenses:Food", "5.00", "USD"),
            ("Assets:Bank", "-5.00", "USD"),
        ],
    );
    if let DirectiveData::Transaction(t) = &mut txn_b.data {
        t.postings[1].units = None;
    }
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        txn_a,
        txn_b,
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "None units must not collide with Some units, got: {:?}",
        output.errors
    );
}

/// A cost with a lot date is structurally different from one without.
#[test]
fn test_noduplicates_cost_with_date_differs() {
    let plugin = NoDuplicatesPlugin;
    let mut txn_a = make_transaction_with_cost(
        "2024-01-15",
        "Buy",
        "Assets:Stock",
        ("10", "AAPL"),
        ("150.00", "USD"),
        "Assets:Cash",
    );
    let mut txn_b = make_transaction_with_cost(
        "2024-01-15",
        "Buy",
        "Assets:Stock",
        ("10", "AAPL"),
        ("150.00", "USD"),
        "Assets:Cash",
    );
    if let DirectiveData::Transaction(t) = &mut txn_b.data
        && let Some(cost) = &mut t.postings[0].cost
    {
        cost.date = Some("2024-01-10".to_string());
    }
    // Keep the tests independent of any posting-level expansion logic.
    let _ = &mut txn_a;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Stock"),
        make_open("2024-01-01", "Assets:Cash"),
        txn_a,
        txn_b,
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "cost with date must not collide with cost without date, got: {:?}",
        output.errors
    );
}

/// A cost with a lot label is structurally different from one without.
#[test]
fn test_noduplicates_cost_with_label_differs() {
    let plugin = NoDuplicatesPlugin;
    let txn_a = make_transaction_with_cost(
        "2024-01-15",
        "Buy",
        "Assets:Stock",
        ("10", "AAPL"),
        ("150.00", "USD"),
        "Assets:Cash",
    );
    let mut txn_b = make_transaction_with_cost(
        "2024-01-15",
        "Buy",
        "Assets:Stock",
        ("10", "AAPL"),
        ("150.00", "USD"),
        "Assets:Cash",
    );
    if let DirectiveData::Transaction(t) = &mut txn_b.data
        && let Some(cost) = &mut t.postings[0].cost
    {
        cost.label = Some("lot-42".to_string());
    }
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Stock"),
        make_open("2024-01-01", "Assets:Cash"),
        txn_a,
        txn_b,
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "cost with label must not collide with cost without label, got: {:?}",
        output.errors
    );
}

/// Total cost (`number_total`) vs per-unit cost (`number_per`) are
/// structurally different even when the cost spec otherwise matches.
#[test]
fn test_noduplicates_total_vs_per_unit_cost_differ() {
    let plugin = NoDuplicatesPlugin;
    let txn_a = make_transaction_with_cost(
        "2024-01-15",
        "Buy",
        "Assets:Stock",
        ("10", "AAPL"),
        ("150.00", "USD"), // per-unit cost
        "Assets:Cash",
    );
    let mut txn_b = make_transaction_with_cost(
        "2024-01-15",
        "Buy",
        "Assets:Stock",
        ("10", "AAPL"),
        ("150.00", "USD"),
        "Assets:Cash",
    );
    if let DirectiveData::Transaction(t) = &mut txn_b.data
        && let Some(cost) = &mut t.postings[0].cost
    {
        // Swap to total cost form
        cost.number = Some(rustledger_plugin_types::CostNumberData::Total {
            value: "1500.00".to_string(),
        });
    }
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Stock"),
        make_open("2024-01-01", "Assets:Cash"),
        txn_a,
        txn_b,
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "per-unit cost must not collide with total cost, got: {:?}",
        output.errors
    );
}

/// `@@` is compared as the per-unit price it stands for, as beancount's
/// parser rewrites it before plugins run: `-5 AAPL @@ 875.00 USD` is
/// `-5 AAPL @ 175.00 USD`, a duplicate in bean-check (#2599; this test
/// asserted the opposite before). `@@ 875 USD` is `@ 175 USD`, not
/// `@ 175.00 USD`: numbers keep their scale.
#[test]
fn test_noduplicates_total_price_is_its_per_unit_price() {
    let plugin = NoDuplicatesPlugin;
    let mut txn_a = make_transaction(
        "2024-01-15",
        "Sell",
        vec![
            ("Assets:Stock", "-5", "AAPL"),
            ("Assets:Cash", "875.00", "USD"),
        ],
    );
    if let DirectiveData::Transaction(t) = &mut txn_a.data {
        t.postings[0].price = Some(PriceAnnotationData {
            is_total: false,
            amount: Some(AmountData {
                number: "175.00".to_string(),
                currency: "USD".to_string(),
            }),
            number: None,
            currency: None,
        });
    }
    let mut txn_b = make_transaction(
        "2024-01-15",
        "Sell",
        vec![
            ("Assets:Stock", "-5", "AAPL"),
            ("Assets:Cash", "875.00", "USD"),
        ],
    );
    if let DirectiveData::Transaction(t) = &mut txn_b.data {
        t.postings[0].price = Some(PriceAnnotationData {
            is_total: true, // @@
            amount: Some(AmountData {
                number: "875.00".to_string(),
                currency: "USD".to_string(),
            }),
            number: None,
            currency: None,
        });
    }
    let mut txn_c = txn_b.clone();
    if let DirectiveData::Transaction(t) = &mut txn_c.data {
        t.postings[0]
            .price
            .as_mut()
            .unwrap()
            .amount
            .as_mut()
            .unwrap()
            .number = "875".to_string();
    }
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Stock"),
        make_open("2024-01-01", "Assets:Cash"),
        txn_a,
        txn_b,
        txn_c,
    ]);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(
        output.errors.len(),
        1,
        "`@@ 875.00` is `@ 175.00`; `@@ 875` is neither, got: {:?}",
        output.errors
    );
}

/// An incomplete price (currency only, no number) is structurally
/// different from a complete one.
#[test]
fn test_noduplicates_incomplete_vs_complete_price_differ() {
    let plugin = NoDuplicatesPlugin;
    let mut txn_a = make_transaction(
        "2024-01-15",
        "Sell",
        vec![
            ("Assets:Stock", "-5", "AAPL"),
            ("Assets:Cash", "0.00", "USD"),
        ],
    );
    if let DirectiveData::Transaction(t) = &mut txn_a.data {
        t.postings[0].price = Some(PriceAnnotationData {
            is_total: false,
            amount: None,
            number: None,
            currency: Some("USD".to_string()),
        });
    }
    let mut txn_b = make_transaction(
        "2024-01-15",
        "Sell",
        vec![
            ("Assets:Stock", "-5", "AAPL"),
            ("Assets:Cash", "0.00", "USD"),
        ],
    );
    if let DirectiveData::Transaction(t) = &mut txn_b.data {
        t.postings[0].price = Some(PriceAnnotationData {
            is_total: false,
            amount: Some(AmountData {
                number: "175.00".to_string(),
                currency: "USD".to_string(),
            }),
            number: None,
            currency: None,
        });
    }
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Stock"),
        make_open("2024-01-01", "Assets:Cash"),
        txn_a,
        txn_b,
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "incomplete and complete prices must not collide, got: {:?}",
        output.errors
    );
}

/// Posting-level flag (`!` on a single posting) is part of structural
/// identity, matching `Posting.flag` in beancount.
#[test]
fn test_noduplicates_distinct_posting_flags_differ() {
    let plugin = NoDuplicatesPlugin;
    let txn_a = make_transaction(
        "2024-01-15",
        "Coffee",
        vec![
            ("Expenses:Food", "5.00", "USD"),
            ("Assets:Bank", "-5.00", "USD"),
        ],
    );
    let mut txn_b = make_transaction(
        "2024-01-15",
        "Coffee",
        vec![
            ("Expenses:Food", "5.00", "USD"),
            ("Assets:Bank", "-5.00", "USD"),
        ],
    );
    if let DirectiveData::Transaction(t) = &mut txn_b.data {
        t.postings[0].flag = Some("!".to_string());
    }
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        txn_a,
        txn_b,
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "distinct posting flags must not collide, got: {:?}",
        output.errors
    );
}

/// Posting-level metadata is excluded from the hash, matching
/// `hash_entry(exclude_meta=True)`.
#[test]
fn test_noduplicates_posting_metadata_does_not_disambiguate() {
    use rustledger_plugin_types::MetaValueData;

    let plugin = NoDuplicatesPlugin;

    let txn_a = make_transaction(
        "2024-01-15",
        "Coffee",
        vec![
            ("Expenses:Food", "5.00", "USD"),
            ("Assets:Bank", "-5.00", "USD"),
        ],
    );
    let mut txn_b = make_transaction(
        "2024-01-15",
        "Coffee",
        vec![
            ("Expenses:Food", "5.00", "USD"),
            ("Assets:Bank", "-5.00", "USD"),
        ],
    );
    if let DirectiveData::Transaction(t) = &mut txn_b.data {
        t.postings[0].metadata =
            vec![("ref".to_string(), MetaValueData::String("abc".to_string()))];
    }
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        txn_a,
        txn_b,
    ]);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(
        output.errors.len(),
        1,
        "posting-level metadata must not disambiguate (exclude_meta=True), \
         got: {:?}",
        output.errors
    );
}

// ---------- Multi-transaction & structural scenarios ----------

/// Three identical transactions produce exactly two duplicate errors
/// (one per extra occurrence).
#[test]
fn test_noduplicates_three_identical_reports_two_duplicates() {
    let plugin = NoDuplicatesPlugin;
    let postings = vec![
        ("Expenses:Food", "5.00", "USD"),
        ("Assets:Bank", "-5.00", "USD"),
    ];
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        make_transaction("2024-01-15", "Coffee", postings.clone()),
        make_transaction("2024-01-15", "Coffee", postings.clone()),
        make_transaction("2024-01-15", "Coffee", postings),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(
        output.errors.len(),
        2,
        "three identical transactions should produce two duplicate errors, got: {:?}",
        output.errors
    );
}

/// Non-transaction directives are compared too, as bean-check compares
/// them (#2599; this test asserted they were ignored before): two
/// identical opens are a duplicate, and an open between two transactions
/// does not collide with either.
#[test]
fn test_noduplicates_compares_non_transaction_directives() {
    let plugin = NoDuplicatesPlugin;
    let postings = vec![
        ("Expenses:Food", "5.00", "USD"),
        ("Assets:Bank", "-5.00", "USD"),
    ];
    let input = make_input(vec![
        // Two identical opens: a duplicate, as in bean-check.
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        make_transaction("2024-01-15", "Coffee", postings.clone()),
        // An Open directive between the two transactions shouldn't
        // cause any hash collision with either.
        make_open("2024-02-01", "Assets:Savings"),
        make_transaction("2024-01-15", "Coffee", postings),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(
        output.errors.len(),
        2,
        "the second open and the second transaction, got: {:?}",
        output.errors
    );
}

/// A transaction with zero postings (edge case) must still be
/// processed without panicking, and two such transactions hash equal.
#[test]
fn test_noduplicates_empty_postings_edge_case() {
    let plugin = NoDuplicatesPlugin;
    let txn_a = make_txn_with("2024-01-15", "placeholder", vec![], |_| {});
    let txn_b = make_txn_with("2024-01-15", "placeholder", vec![], |_| {});
    let input = make_input(vec![txn_a, txn_b]);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(
        output.errors.len(),
        1,
        "two empty-posting transactions should hash equal and be flagged, got: {:?}",
        output.errors
    );
}

/// Duplicates separated by many unrelated transactions are still
/// detected — the plugin's `HashSet` lookup is independent of position.
#[test]
fn test_noduplicates_detects_duplicates_across_distance() {
    let plugin = NoDuplicatesPlugin;
    let target_postings = vec![
        ("Expenses:Food", "5.00", "USD"),
        ("Assets:Bank", "-5.00", "USD"),
    ];
    let mut directives = vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        make_transaction("2024-01-15", "Coffee", target_postings.clone()),
    ];
    // Fill with 50 distinct transactions on different dates.
    for day in 16..=65 {
        directives.push(make_transaction(
            &format!("2024-01-{day:02}"),
            "Distinct",
            vec![
                ("Expenses:Food", &format!("{day}.00"), "USD"),
                ("Assets:Bank", &format!("-{day}.00"), "USD"),
            ],
        ));
    }
    // Duplicate of the first Coffee transaction, 50 entries later.
    directives.push(make_transaction("2024-01-15", "Coffee", target_postings));
    let input = make_input(directives);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(
        output.errors.len(),
        1,
        "duplicates should be detected regardless of distance in the \
         directive stream, got: {:?}",
        output.errors
    );
}

/// Two transactions with identical content but different filename/
/// lineno (source locations) are still duplicates — location is not
/// part of structural identity.
#[test]
fn test_noduplicates_source_location_not_part_of_identity() {
    let plugin = NoDuplicatesPlugin;
    let postings = vec![
        ("Expenses:Food", "5.00", "USD"),
        ("Assets:Bank", "-5.00", "USD"),
    ];
    let mut txn_a = make_transaction("2024-01-15", "Coffee", postings.clone());
    txn_a.filename = Some("a.beancount".to_string());
    txn_a.lineno = Some(10);
    let mut txn_b = make_transaction("2024-01-15", "Coffee", postings);
    txn_b.filename = Some("b.beancount".to_string());
    txn_b.lineno = Some(42);
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        txn_a,
        txn_b,
    ]);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(
        output.errors.len(),
        1,
        "source filename/lineno must not influence the hash, got: {:?}",
        output.errors
    );
}

// ============================================================================
// OneCommodityPlugin Tests (from onecommodity_test.py)
// ============================================================================

/// Test account with multiple currencies generates error.
/// Converted from: `test_one_commodity_transaction`
#[test]
fn test_onecommodity_error_multiple_currencies() {
    let plugin = OneCommodityPlugin;

    let input = make_input(vec![
        make_open("2024-01-01", "Expenses:Restaurant"),
        make_open("2024-01-01", "Assets:Cash"),
        // First transaction in USD
        make_transaction(
            "2024-01-15",
            "Lunch",
            vec![
                ("Expenses:Restaurant", "25.00", "USD"),
                ("Assets:Cash", "-25.00", "USD"),
            ],
        ),
        // Second transaction in CAD - ERROR
        make_transaction(
            "2024-01-16",
            "Dinner",
            vec![
                ("Expenses:Restaurant", "30.00", "CAD"),
                ("Assets:Cash", "-30.00", "CAD"),
            ],
        ),
    ]);

    let output = process_and_materialize(&plugin, input);

    // Both Expenses:Restaurant and Assets:Cash use USD and CAD
    assert_eq!(
        output.errors.len(),
        2,
        "expected 2 errors for mixed currencies (one per account)"
    );

    // Check that errors mention the accounts and currencies
    let error_text: String = output.errors.iter().map(|e| e.message.clone()).collect();
    assert!(
        error_text.contains("USD") && error_text.contains("CAD"),
        "errors should mention both currencies"
    );
}

/// Test account with single currency passes.
#[test]
fn test_onecommodity_ok_single_currency() {
    let plugin = OneCommodityPlugin;

    let input = make_input(vec![
        make_open("2024-01-01", "Expenses:Restaurant"),
        make_open("2024-01-01", "Assets:Cash"),
        make_transaction(
            "2024-01-15",
            "Lunch",
            vec![
                ("Expenses:Restaurant", "25.00", "USD"),
                ("Assets:Cash", "-25.00", "USD"),
            ],
        ),
        make_transaction(
            "2024-01-16",
            "Dinner",
            vec![
                ("Expenses:Restaurant", "30.00", "USD"),
                ("Assets:Cash", "-30.00", "USD"),
            ],
        ),
    ]);

    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty(), "expected no errors");
}

/// Empty input → no errors. Pins the "no directives" baseline.
#[test]
fn test_onecommodity_empty_input() {
    let plugin = OneCommodityPlugin;
    let output = process_and_materialize(&plugin, make_input(vec![]));
    assert_eq!(output.errors.len(), 0);
}

/// Auto-balanced postings (`units = None`) are skipped — they don't have
/// a currency to record or check, so they can't violate the rule.
///
/// The plugin's `if let Some(units) = &posting.units` branch should fall
/// through for the None posting: the account is neither tracked nor checked.
/// We prove this by following up with a different currency on the same
/// account in a later transaction — if the None posting had been treated as
/// "first seen", we'd see a mismatch error; instead the later currency is
/// the first recorded and produces no error.
#[test]
fn test_onecommodity_skips_auto_balanced_posting() {
    let plugin = OneCommodityPlugin;

    // Transaction with one explicit-USD posting on Assets:Cash and one
    // auto-balanced (`units = None`) posting on Expenses:Misc. The None
    // posting must NOT contribute to currency tracking.
    let txn_with_none_posting = DirectiveWrapper {
        directive_type: "transaction".to_string(),
        date: "2024-01-15".to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Transaction(TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: "Auto-balanced".to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![
                PostingData {
                    account: "Assets:Cash".to_string(),
                    units: Some(AmountData {
                        number: "-10.00".to_string(),
                        currency: "USD".to_string(),
                    }),
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
                PostingData {
                    // units = None → must hit the skip branch.
                    account: "Expenses:Misc".to_string(),
                    units: None,
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
            ],
        }),
    };

    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Expenses:Misc"),
        txn_with_none_posting,
        // Now use Expenses:Misc with EUR. If the prior None posting had been
        // tracked (in any form), this would mismatch and produce an error.
        // With the skip working correctly, EUR is the FIRST currency
        // recorded for Expenses:Misc → no error.
        make_transaction(
            "2024-01-16",
            "EUR follow-up",
            vec![("Expenses:Misc", "20.00", "EUR")],
        ),
    ]);

    let output = process_and_materialize(&plugin, input);
    assert_eq!(
        output.errors.len(),
        0,
        "None posting should be skipped (no currency recorded for that account); got: {:?}",
        output.errors
    );
}

/// Different accounts using different currencies → no error. The rule is
/// per-account; cross-account currency mismatches are fine.
#[test]
fn test_onecommodity_independent_accounts_ok() {
    let plugin = OneCommodityPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:USD"),
        make_open("2024-01-01", "Assets:EUR"),
        make_open("2024-01-01", "Equity:Open"),
        make_transaction(
            "2024-01-15",
            "USD deposit",
            vec![
                ("Assets:USD", "100.00", "USD"),
                ("Equity:Open", "-100.00", "USD"),
            ],
        ),
        make_transaction(
            "2024-01-15",
            "EUR deposit",
            vec![
                ("Assets:EUR", "50.00", "EUR"),
                ("Equity:Open", "-50.00", "EUR"),
            ],
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    // Equity:Open uses both USD and EUR → 1 error for Equity:Open.
    // Assets:USD and Assets:EUR are each single-currency — no errors.
    assert_eq!(output.errors.len(), 1);
    assert!(output.errors[0].message.contains("Equity:Open"));
}

/// Three different currencies in one account → one error naming all three,
/// sorted, located at the last entry that added a currency (beancount's
/// `onecommodity`, #2539; before, every posting after the first that did
/// not match was an error of its own).
#[test]
fn test_onecommodity_three_currencies_cascade() {
    let plugin = OneCommodityPlugin;
    let mut gbp = make_transaction("2024-01-17", "GBP", vec![("Assets:Mixed", "30.00", "GBP")]);
    gbp.filename = Some("ledger.beancount".to_string());
    gbp.lineno = Some(9);
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Mixed"),
        make_transaction("2024-01-15", "USD", vec![("Assets:Mixed", "100.00", "USD")]),
        make_transaction("2024-01-16", "EUR", vec![("Assets:Mixed", "50.00", "EUR")]),
        gbp,
    ]);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(output.errors.len(), 1, "got: {:?}", output.errors);
    assert_eq!(
        output.errors[0].message,
        "More than one currency in account 'Assets:Mixed': EUR,GBP,USD"
    );
    assert_eq!(output.errors[0].line_number, Some(9));
}

/// Non-Transaction directives are ignored. Pins the "only Transaction
/// matters" branch — Open / Balance / Price / commodity / etc don't
/// contribute to the per-account currency tracking.
#[test]
fn test_onecommodity_ignores_non_transaction_directives() {
    let plugin = OneCommodityPlugin;
    let input = make_input(vec![
        make_commodity("2024-01-01", "USD"),
        make_commodity("2024-01-01", "EUR"),
        make_open("2024-01-01", "Assets:Cash"),
        make_price("2024-01-15", "USD", "0.85", "EUR"),
        // No Transactions at all → no errors.
    ]);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(output.errors.len(), 0);
}

// ============================================================================
// CheckCommodityPlugin Tests (from check_commodity_test.py)
// ============================================================================

/// Test undeclared commodity generates warning.
/// Converted from: `test_check_commodity_transaction`
#[test]
fn test_check_commodity_undeclared() {
    let plugin = CheckCommodityPlugin;

    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        // Use USD without declaring it
        make_transaction(
            "2024-01-15",
            "Groceries",
            vec![
                ("Expenses:Food", "50.00", "USD"),
                ("Assets:Bank", "-50.00", "USD"),
            ],
        ),
    ]);

    let output = process_and_materialize(&plugin, input);

    assert_eq!(
        output.errors.len(),
        1,
        "exactly one warning for the single undeclared currency"
    );
    assert!(
        output.errors[0].message.contains("USD"),
        "warning should mention USD"
    );
}

/// Test declared commodity passes.
/// Converted from: `test_check_commodity_okay`
#[test]
fn test_check_commodity_declared_ok() {
    let plugin = CheckCommodityPlugin;

    let input = make_input(vec![
        make_commodity("2024-01-01", "USD"),
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        make_transaction(
            "2024-01-15",
            "Groceries",
            vec![
                ("Expenses:Food", "50.00", "USD"),
                ("Assets:Bank", "-50.00", "USD"),
            ],
        ),
    ]);

    let output = process_and_materialize(&plugin, input);

    // Should not have warning about USD since it's declared
    let has_usd_warning = output.errors.iter().any(|e| e.message.contains("USD"));
    assert!(!has_usd_warning, "should not warn about declared USD");
}

/// Empty input → no errors, no directives. Pins the baseline.
#[test]
fn test_check_commodity_empty_input() {
    let plugin = CheckCommodityPlugin;
    let output = process_and_materialize(&plugin, make_input(vec![]));
    assert_eq!(output.errors.len(), 0);
    assert_eq!(output.directives.len(), 0);
}

/// `check_commodity` reports an undeclared commodity as an error, as
/// beancount's does (bean-check exits 1). It was a warning before #2539, so
/// the native and Python implementations disagreed on the same ledger.
#[test]
fn test_check_commodity_severity_is_error() {
    let plugin = CheckCommodityPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        make_transaction(
            "2024-01-15",
            "Lunch",
            vec![
                ("Expenses:Food", "10.00", "USD"),
                ("Assets:Bank", "-10.00", "USD"),
            ],
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(output.errors.len(), 1);
    assert_eq!(
        output.errors[0].severity,
        PluginErrorSeverity::Error,
        "check_commodity diagnostics are errors, as in beancount"
    );
    assert_eq!(
        output.errors[0].message,
        "Missing Commodity directive for 'USD' in 'Assets:Bank'"
    );
}

/// Plugin is read-only — input directives flow through unchanged in length
/// and order.
#[test]
fn test_check_commodity_passthrough_unchanged() {
    let plugin = CheckCommodityPlugin;
    let input_directives = vec![
        make_commodity("2024-01-01", "USD"),
        make_open("2024-01-01", "Assets:Bank"),
        make_transaction("2024-01-15", "Test", vec![("Assets:Bank", "10.00", "USD")]),
    ];
    let input = make_input(input_directives.clone());
    let output = process_and_materialize(&plugin, input);
    assert_eq!(output.directives.len(), input_directives.len());
    for (a, b) in output.directives.iter().zip(input_directives.iter()) {
        assert_eq!(a.directive_type, b.directive_type);
        assert_eq!(a.date, b.date);
    }
}

/// Cost currency on a posting (`posting.cost.currency`) is also checked.
/// An undeclared cost currency triggers a warning even if the units
/// currency is declared.
#[test]
fn test_check_commodity_undeclared_cost_currency() {
    let plugin = CheckCommodityPlugin;
    let input = make_input(vec![
        make_commodity("2024-01-01", "HOOL"),
        // USD is intentionally undeclared.
        make_open("2024-01-01", "Assets:Brokerage"),
        make_open("2024-01-01", "Equity:Open"),
        DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: "2024-02-01".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: None,
                narration: "Buy with cost".to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings: vec![
                    PostingData {
                        account: "Assets:Brokerage".to_string(),
                        units: Some(AmountData {
                            number: "5".to_string(),
                            currency: "HOOL".to_string(),
                        }),
                        cost: Some(CostData {
                            number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                                value: "100.00".to_string(),
                            }),
                            currency: Some("USD".to_string()),
                            date: None,
                            label: None,
                            merge: false,
                        }),
                        price: None,
                        flag: None,
                        metadata: vec![],
                        span: None,
                    },
                    PostingData {
                        account: "Equity:Open".to_string(),
                        units: None,
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                        span: None,
                    },
                ],
            }),
        },
    ]);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(output.errors.len(), 1, "got: {:?}", output.errors);
    assert!(output.errors[0].message.contains("USD"));
}

/// A posting with `cost = Some(...)` but `cost.currency = None` should not
/// contribute to `used_commodities` — the plugin's inner `if let Some(ref
/// currency) = cost.currency` guard skips the insert. Pins that None-skip.
#[test]
fn test_check_commodity_cost_with_none_currency_skipped() {
    let plugin = CheckCommodityPlugin;
    let input = make_input(vec![
        make_commodity("2024-01-01", "HOOL"),
        make_open("2024-01-01", "Assets:Brokerage"),
        make_open("2024-01-01", "Equity:Open"),
        DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: "2024-02-01".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: None,
                narration: "Cost with no currency".to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings: vec![
                    PostingData {
                        account: "Assets:Brokerage".to_string(),
                        units: Some(AmountData {
                            number: "5".to_string(),
                            currency: "HOOL".to_string(),
                        }),
                        // Cost present but with currency = None — must NOT
                        // be added to the used-commodities set.
                        cost: Some(CostData {
                            number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                                value: "100.00".to_string(),
                            }),
                            currency: None,
                            date: None,
                            label: None,
                            merge: false,
                        }),
                        price: None,
                        flag: None,
                        metadata: vec![],
                        span: None,
                    },
                    PostingData {
                        account: "Equity:Open".to_string(),
                        units: None,
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                        span: None,
                    },
                ],
            }),
        },
    ]);
    let output = process_and_materialize(&plugin, input);
    // Only HOOL is used and it's declared → zero warnings. If the cost.currency
    // = None branch were misimplemented (e.g., inserting an empty string), we'd
    // see a spurious warning here.
    assert_eq!(output.errors.len(), 0, "got: {:?}", output.errors);
}

/// Currency in a Balance directive is also tracked. Undeclared → warning.
#[test]
fn test_check_commodity_undeclared_in_balance_directive() {
    let plugin = CheckCommodityPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        DirectiveWrapper {
            directive_type: "balance".to_string(),
            date: "2024-01-15".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Balance(BalanceData {
                account: "Assets:Bank".to_string(),
                amount: AmountData {
                    number: "100.00".to_string(),
                    currency: "GBP".to_string(),
                },
                tolerance: None,
                metadata: vec![],
            }),
        },
    ]);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(output.errors.len(), 1);
    assert!(output.errors[0].message.contains("GBP"));
}

/// Both `price.currency` and `price.amount.currency` are checked. A Price
/// directive with two undeclared currencies produces two warnings.
#[test]
fn test_check_commodity_undeclared_in_price_directive() {
    let plugin = CheckCommodityPlugin;
    // Neither HOOL nor USD declared → 2 warnings.
    let input = make_input(vec![make_price("2024-01-15", "HOOL", "520.00", "USD")]);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(output.errors.len(), 2, "got: {:?}", output.errors);
    let messages: Vec<_> = output.errors.iter().map(|e| e.message.clone()).collect();
    assert!(messages.iter().any(|m| m.contains("HOOL")));
    assert!(messages.iter().any(|m| m.contains("USD")));
}

/// The same undeclared currency used in many places produces one warning,
/// not many — `used_commodities` is a `HashSet`.
#[test]
fn test_check_commodity_dedupes_repeated_undeclared() {
    let plugin = CheckCommodityPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        // Same undeclared USD used in three transactions.
        make_transaction(
            "2024-01-15",
            "T1",
            vec![
                ("Expenses:Food", "10.00", "USD"),
                ("Assets:Bank", "-10.00", "USD"),
            ],
        ),
        make_transaction(
            "2024-01-16",
            "T2",
            vec![
                ("Expenses:Food", "20.00", "USD"),
                ("Assets:Bank", "-20.00", "USD"),
            ],
        ),
        make_transaction(
            "2024-01-17",
            "T3",
            vec![
                ("Expenses:Food", "30.00", "USD"),
                ("Assets:Bank", "-30.00", "USD"),
            ],
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(output.errors.len(), 1, "deduped to one warning");
    assert!(output.errors[0].message.contains("USD"));
}

/// Multiple distinct undeclared currencies → one warning per unique currency.
/// Declared ones are excluded.
#[test]
fn test_check_commodity_mixed_declared_and_undeclared() {
    let plugin = CheckCommodityPlugin;
    let input = make_input(vec![
        // USD declared, EUR + GBP not.
        make_commodity("2024-01-01", "USD"),
        make_open("2024-01-01", "Assets:USD"),
        make_open("2024-01-01", "Assets:EUR"),
        make_open("2024-01-01", "Assets:GBP"),
        make_transaction("2024-01-15", "USD", vec![("Assets:USD", "10.00", "USD")]),
        make_transaction("2024-01-16", "EUR", vec![("Assets:EUR", "20.00", "EUR")]),
        make_transaction("2024-01-17", "GBP", vec![("Assets:GBP", "30.00", "GBP")]),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(output.errors.len(), 2, "EUR and GBP undeclared, USD ok");
    let messages: Vec<_> = output.errors.iter().map(|e| e.message.clone()).collect();
    assert!(messages.iter().any(|m| m.contains("EUR")));
    assert!(messages.iter().any(|m| m.contains("GBP")));
    assert!(!messages.iter().any(|m| m.contains("USD")));
}

// ============================================================================
// UniquePricesPlugin Tests (from unique_prices_test.py)
// ============================================================================

/// Test duplicate prices on same day generate error.
#[test]
fn test_unique_prices_duplicate_error() {
    let plugin = UniquePricesPlugin;

    let input = make_input(vec![
        make_price("2024-01-15", "HOOL", "520.00", "USD"),
        make_price("2024-01-15", "HOOL", "525.00", "USD"), // Duplicate
    ]);

    let output = process_and_materialize(&plugin, input);

    assert_eq!(output.errors.len(), 1, "expected 1 duplicate price error");
    assert_eq!(output.errors[0].message, "Disagreeing price entries");
}

/// Prices of one pair on one day that agree are allowed, as in beancount's
/// `unique_prices`; only disagreeing ones are an error (#2539: a repeated,
/// identical price was an error before).
#[test]
fn test_unique_prices_agreeing_duplicates_are_allowed() {
    let plugin = UniquePricesPlugin;
    let input = make_input(vec![
        make_price("2024-01-15", "HOOL", "520.00", "USD"),
        make_price("2024-01-15", "HOOL", "520", "USD"),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty(), "{:?}", output.errors);
}

/// Test prices on different days pass.
#[test]
fn test_unique_prices_different_days_ok() {
    let plugin = UniquePricesPlugin;

    let input = make_input(vec![
        make_price("2024-01-15", "HOOL", "520.00", "USD"),
        make_price("2024-01-16", "HOOL", "525.00", "USD"),
    ]);

    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty(), "expected no errors");
}

/// Test prices for different currency pairs on same day pass.
#[test]
fn test_unique_prices_different_pairs_ok() {
    let plugin = UniquePricesPlugin;

    let input = make_input(vec![
        make_price("2024-01-15", "HOOL", "520.00", "USD"),
        make_price("2024-01-15", "GOOG", "150.00", "USD"),
    ]);

    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty(), "expected no errors");
}

// ============================================================================
// ImplicitPricesPlugin Tests (from implicit_prices_test.py)
// ============================================================================

/// Helper that returns plugin-generated price directives only,
/// as a `Vec<(currency, number, quote_currency)>` for strict equality
/// assertions.
///
/// Computed as `output_prices − input_prices` so explicit input
/// `price` directives don't get counted as plugin output. Pre-fix
/// (Copilot review on PR #997) the previous version filtered on
/// `filename: None`, but the test fixture's `make_price` helper also
/// sets `filename: None` — so any test that included an explicit input
/// price would have miscounted.
///
/// Use this instead of `assert!(price_count >= N)` — the original test
/// shape silently masked issue #992 because `>= 1` accepted both the
/// correct emission AND the spurious extra one.
fn implicit_prices_emitted(
    input: &PluginInput,
    output: &ProcessedOutput,
) -> Vec<(String, String, String)> {
    fn extract(directives: &[DirectiveWrapper]) -> Vec<(String, String, String)> {
        directives
            .iter()
            .filter(|d| d.directive_type == "price")
            .filter_map(|d| match &d.data {
                DirectiveData::Price(p) => Some((
                    p.currency.clone(),
                    p.amount.number.clone(),
                    p.amount.currency.clone(),
                )),
                _ => None,
            })
            .collect()
    }
    let input_prices = extract(&input.directives);
    let mut output_prices = extract(&output.directives);
    // Remove one occurrence of each input price from output (multiset
    // difference). What remains is the plugin's contribution.
    for ip in &input_prices {
        if let Some(pos) = output_prices.iter().position(|p| p == ip) {
            output_prices.remove(pos);
        }
    }
    output_prices
}

/// Build a transaction where the priced posting carries a price annotation
/// (`@` or `@@`). Used by the implicit-prices tests below.
fn make_txn_with_price_annotation(
    date: &str,
    narration: &str,
    units: (&str, &str),
    price: (&str, &str),
    is_total: bool,
) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: "transaction".to_string(),
        date: date.to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Transaction(TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: narration.to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![
                PostingData {
                    account: "Assets:Brokerage".to_string(),
                    units: Some(AmountData {
                        number: units.0.to_string(),
                        currency: units.1.to_string(),
                    }),
                    cost: None,
                    price: Some(PriceAnnotationData {
                        amount: Some(AmountData {
                            number: price.0.to_string(),
                            currency: price.1.to_string(),
                        }),
                        is_total,
                        number: None,
                        currency: None,
                    }),
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
                PostingData {
                    account: "Assets:Cash".to_string(),
                    units: None,
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
            ],
        }),
    }
}

/// Cost-only path. Pinned with strict `assert_eq!` — replaces an earlier
/// `>= 1` assertion that silently passed even when the plugin emitted
/// extra spurious prices (issue #992).
#[test]
fn test_implicit_prices_from_cost() {
    let plugin = ImplicitPricesPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Brokerage"),
        make_open("2024-01-01", "Assets:Cash"),
        make_transaction_with_cost(
            "2024-01-15",
            "Buy stock",
            "Assets:Brokerage",
            ("10", "HOOL"),
            ("520.00", "USD"),
            "Assets:Cash",
        ),
    ]);
    let output = process_and_materialize(&plugin, input.clone());
    assert_eq!(
        implicit_prices_emitted(&input, &output),
        vec![("HOOL".into(), "520.00".into(), "USD".into())]
    );
}

/// `cost.number_total` (`{{TOTAL CURRENCY}}` syntax) divides by units to
/// produce a per-unit price. Pre-fix (Copilot review on PR #997) the
/// plugin handled this branch but no test exercised it, so the
/// string-parsing path was un-pinned.
#[test]
fn test_implicit_prices_from_cost_total() {
    let plugin = ImplicitPricesPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Brokerage"),
        make_open("2024-01-01", "Assets:Cash"),
        // 10 ABC {{500 USD}} → per-unit = 500 / 10 = 50 USD.
        // Built inline because no helper exists for cost_total.
        DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: "2024-01-15".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: None,
                narration: "Buy with total cost".to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings: vec![
                    PostingData {
                        account: "Assets:Brokerage".to_string(),
                        units: Some(AmountData {
                            number: "10".to_string(),
                            currency: "ABC".to_string(),
                        }),
                        cost: Some(CostData {
                            number: Some(rustledger_plugin_types::CostNumberData::Total {
                                value: "500".to_string(),
                            }),
                            currency: Some("USD".to_string()),
                            date: None,
                            label: None,
                            merge: false,
                        }),
                        price: None,
                        flag: None,
                        metadata: vec![],
                        span: None,
                    },
                    PostingData {
                        account: "Assets:Cash".to_string(),
                        units: None,
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                        span: None,
                    },
                ],
            }),
        },
    ]);
    let output = process_and_materialize(&plugin, input.clone());
    assert_eq!(
        implicit_prices_emitted(&input, &output),
        vec![("ABC".into(), "50".into(), "USD".into())],
        "{{TOTAL CURRENCY}} cost spec must divide by units.abs()"
    );
}

/// `@` per-unit annotation: the annotation amount is used directly.
#[test]
fn test_implicit_prices_from_unit_annotation() {
    let plugin = ImplicitPricesPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Brokerage"),
        make_open("2024-01-01", "Assets:Cash"),
        make_txn_with_price_annotation(
            "2024-01-15",
            "Sell at unit price",
            ("-5", "HOOL"),
            ("530", "USD"),
            false, // is_total = false → @
        ),
    ]);
    let output = process_and_materialize(&plugin, input.clone());
    assert_eq!(
        implicit_prices_emitted(&input, &output),
        vec![("HOOL".into(), "530".into(), "USD".into())]
    );
}

/// `@@` total annotation: the total is divided by `units.abs()` to produce
/// a per-unit price. THIS IS THE ISSUE #992 REGRESSION TEST — pre-fix the
/// plugin emitted the total amount directly as a per-unit price (off by
/// a factor of `units`).
#[test]
fn test_implicit_prices_from_total_annotation_issue_992() {
    let plugin = ImplicitPricesPlugin;
    let input = make_input(vec![
        make_open("2020-01-01", "Assets:Insurance"),
        make_txn_with_price_annotation(
            "2025-01-23",
            "insurance matured",
            ("-27204.53", "BAM"),
            ("15152.07", "EUR"),
            true, // is_total = true → @@
        ),
    ]);
    let output = process_and_materialize(&plugin, input.clone());
    let prices = implicit_prices_emitted(&input, &output);
    // Exactly one price, NOT two (one of which used to be 15152.07
    // emitted as a per-unit price — the original bug).
    assert_eq!(prices.len(), 1, "exactly one price per posting");
    let (base, num_str, quote) = &prices[0];
    assert_eq!(base, "BAM");
    assert_eq!(quote, "EUR");
    // The per-unit price is 15152.07 / 27204.53 ≈ 0.5569...
    let parsed: rust_decimal::Decimal = num_str.parse().expect("price parses");
    assert!(
        parsed > rust_decimal_macros::dec!(0.55) && parsed < rust_decimal_macros::dec!(0.56),
        "@@ total must be divided by units.abs(); got {num_str}"
    );
}

/// Posting with BOTH `{cost}` AND `@` annotation: the annotation wins,
/// AND the plugin must emit exactly one price (not two). Pre-fix the
/// plugin double-emitted: one from the annotation block, one from the
/// cost block immediately after. This is the secondary bug from #992.
#[test]
fn test_implicit_prices_annotation_and_cost_emits_one_not_two() {
    let plugin = ImplicitPricesPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Brokerage"),
        make_open("2024-01-01", "Assets:Cash"),
        // 5 ABC {1.25 EUR} @ 1.40 EUR
        make_transaction_with_cost_and_price(
            "2024-01-15",
            "Sell with both cost and price",
            "Assets:Brokerage",
            ("-5", "ABC"),
            ("1.25", "EUR"), // cost
            ("1.40", "EUR"), // price annotation (per-unit)
            "Assets:Cash",
        ),
    ]);
    let output = process_and_materialize(&plugin, input.clone());
    let prices = implicit_prices_emitted(&input, &output);
    assert_eq!(prices.len(), 1, "exactly one price (annotation wins)");
    assert_eq!(
        prices[0],
        ("ABC".into(), "1.40".into(), "EUR".into()),
        "annotation amount wins over cost"
    );
}

/// Currency-pairing regression: `0 ABC @@ 100 EUR` with `{50 USD}` cost.
/// Zero units make the @@ unusable; the helper falls through to the
/// cost spec for the per-unit value (50). Pre-fix (Copilot review on
/// PR #997), the plugin paired that 50 with the annotation's currency
/// (EUR) instead of the cost's (USD), producing a mismatched
/// `(50, EUR)` instead of the correct `(50, USD)`. The fix: the helper
/// returns an `ImplicitPriceSource` discriminator, and the caller pairs
/// the currency with the same source.
#[test]
fn test_implicit_prices_zero_unit_total_falls_through_to_cost_currency() {
    let plugin = ImplicitPricesPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Brokerage"),
        make_open("2024-01-01", "Assets:Cash"),
        make_transaction_with_cost_and_price_total(
            "2024-01-15",
            "Closing position with @@",
            "Assets:Brokerage",
            ("0", "ABC"), // ← zero units make @@ unusable
            ("50", "USD"),
            ("100", "EUR"), // total annotation
            "Assets:Cash",
        ),
    ]);
    let output = process_and_materialize(&plugin, input.clone());
    let prices = implicit_prices_emitted(&input, &output);
    assert_eq!(prices.len(), 1, "exactly one price");
    assert_eq!(
        prices[0],
        ("ABC".into(), "50".into(), "USD".into()),
        "currency must come from the same source as the per-unit value (cost = USD), \
         NOT the annotation (EUR). Pre-fix this returned (50, EUR)."
    );
}

/// Reducing-sell gate: a sell whose cost spec resolves to an existing
/// lot (Python's `MatchResult.REDUCED`) must NOT emit an extra price.
/// Pre-fix this plugin emitted one phantom price per matched lot, so a
/// `Sell -50 X {1 USD}` against a prior `Buy +100 X {1 USD}` would
/// produce a duplicate `1 USD` price entry, and a `Sell -250 X {}` that
/// FIFO-matched three different cost lots would produce three phantom
/// prices. Python's `implicit_prices` plugin gates the cost-derived
/// emit on `Inventory.add_position` returning anything except
/// `MatchResult.REDUCED`; we mirror that here with a per-account lot
/// tracker. Closes the residual ~5 over-emit cases left behind by
/// #1048 (e.g. fava-portfolio-returns/example_stock: py=6 rs=10).
#[test]
fn test_implicit_prices_skips_reducing_sell_with_cost() {
    let plugin = ImplicitPricesPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Brokerage"),
        make_open("2024-01-01", "Assets:Cash"),
        // Buy 100 X {1 USD} on 2024-02-01 — augmenting, emit price.
        make_transaction_with_cost(
            "2024-02-01",
            "Buy 100 X",
            "Assets:Brokerage",
            ("100", "X"),
            ("1", "USD"),
            "Assets:Cash",
        ),
        // Sell -50 X {1 USD} on 2024-03-01 — reduces the buy's lot,
        // must NOT emit an extra price.
        make_transaction_with_cost(
            "2024-03-01",
            "Sell 50 X",
            "Assets:Brokerage",
            ("-50", "X"),
            ("1", "USD"),
            "Assets:Cash",
        ),
    ]);
    let output = process_and_materialize(&plugin, input.clone());
    let prices = implicit_prices_emitted(&input, &output);
    assert_eq!(
        prices,
        vec![("X".into(), "1".into(), "USD".into())],
        "exactly one implicit price (from the buy); the sell must not \
         re-emit the same lot's cost as a price"
    );
}

/// Companion to the above: a reducing sell with both `{cost}` AND a
/// `@` price annotation still emits the *annotation* price (Python's
/// `from_price` branch fires regardless of REDUCED). The cost-derived
/// emit is suppressed, but the annotation isn't.
#[test]
fn test_implicit_prices_reducing_sell_with_annotation_emits_from_price() {
    let plugin = ImplicitPricesPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Brokerage"),
        make_open("2024-01-01", "Assets:Cash"),
        make_transaction_with_cost(
            "2024-02-01",
            "Buy",
            "Assets:Brokerage",
            ("10", "X"),
            ("100", "USD"),
            "Assets:Cash",
        ),
        // -5 X {100 USD} @ 110 USD: reducing, but the annotation
        // should still produce a 110 USD price.
        make_transaction_with_cost_and_price(
            "2024-03-01",
            "Sell with explicit price",
            "Assets:Brokerage",
            ("-5", "X"),
            ("100", "USD"), // cost (matches the lot)
            ("110", "USD"), // @ annotation
            "Assets:Cash",
        ),
    ]);
    let output = process_and_materialize(&plugin, input.clone());
    let prices = implicit_prices_emitted(&input, &output);
    // Two emits: 100 from the buy's cost, 110 from the sell's annotation.
    // Crucially NOT three (no extra 100 from the sell's cost-from-REDUCED).
    assert_eq!(prices.len(), 2, "exactly two emits: buy-cost + sell-@");
    assert!(prices.contains(&("X".into(), "100".into(), "USD".into())));
    assert!(prices.contains(&("X".into(), "110".into(), "USD".into())));
}

/// Same-day dedup: two augmenting buys on the same day at the same
/// per-unit cost emit ONE price, not two. Mirrors Python's
/// `new_price_entry_map` keyed by `(date, base_currency, number,
/// quote_currency)`. Without this gate, fixtures with multi-asset
/// portfolio buys (where the same fund is bought across several
/// accounts on the same date at the same NAV) inflate `#prices`'s
/// row count compared to bean-check. Concrete impact on
/// `beangrow/example_ledger.beancount`: 854 → 782 rows after dedup,
/// matching bean-query exactly.
#[test]
fn test_implicit_prices_dedup_same_day_same_price() {
    let plugin = ImplicitPricesPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:RetirementA"),
        make_open("2024-01-01", "Assets:RetirementB"),
        make_open("2024-01-01", "Assets:Cash"),
        // Two buys on the same day at the same per-unit price.
        make_transaction_with_cost(
            "2024-02-01",
            "Buy in account A",
            "Assets:RetirementA",
            ("10", "FUND"),
            ("100", "USD"),
            "Assets:Cash",
        ),
        make_transaction_with_cost(
            "2024-02-01",
            "Buy in account B",
            "Assets:RetirementB",
            ("20", "FUND"),
            ("100", "USD"),
            "Assets:Cash",
        ),
    ]);
    let output = process_and_materialize(&plugin, input.clone());
    let prices = implicit_prices_emitted(&input, &output);
    assert_eq!(
        prices,
        vec![("FUND".into(), "100".into(), "USD".into())],
        "two same-day same-price buys should dedup to one emit"
    );
}

/// Scale-insensitivity of the REDUCED gate AND same-day dedup.
/// Numerically equal costs / prices written with different scales
/// (`"100"` vs `"100.00"`) must produce the same lot key and the same
/// dedup key, matching Python's `(date, base, number, quote)`
/// Decimal-value comparison. Pre-fix the keys used raw `.to_string()`,
/// so `"100"` and `"100.00"` were distinct keys — a reducing sell at
/// `{100 USD}` against a prior buy at `{100.00 USD}` would NOT
/// classify as REDUCED, slipping the phantom price emit back in.
/// Caught by Copilot review on PR #1061.
#[test]
fn test_implicit_prices_reduced_gate_and_dedup_are_scale_insensitive() {
    let plugin = ImplicitPricesPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Brokerage"),
        make_open("2024-01-01", "Assets:Cash"),
        // Buy: cost spec written with scale 2 ("100.00").
        make_transaction_with_cost(
            "2024-02-01",
            "Buy",
            "Assets:Brokerage",
            ("10", "X"),
            ("100.00", "USD"),
            "Assets:Cash",
        ),
        // Buy again on the same day at the same numeric price, but
        // written with scale 0 ("100"). Pre-fix the dedup key
        // ("100" vs "100.00") would treat these as distinct and emit
        // BOTH prices. Post-fix only one emit.
        make_transaction_with_cost(
            "2024-02-01",
            "Buy more",
            "Assets:Brokerage",
            ("5", "X"),
            ("100", "USD"),
            "Assets:Cash",
        ),
        // Sell using the scale-0 form ("100") against the scale-2
        // existing lot. Pre-fix REDUCED gate would miss this and emit
        // a phantom price. Post-fix it classifies as REDUCED → no emit.
        make_transaction_with_cost(
            "2024-03-01",
            "Sell",
            "Assets:Brokerage",
            ("-5", "X"),
            ("100", "USD"),
            "Assets:Cash",
        ),
    ]);
    let output = process_and_materialize(&plugin, input.clone());
    let prices = implicit_prices_emitted(&input, &output);
    assert_eq!(
        prices.len(),
        1,
        "exactly one emit: the first buy. Second buy dedups, sell is \
         REDUCED. Got: {prices:?}"
    );
    assert_eq!(prices[0].0, "X", "base currency carries through");
    assert_eq!(prices[0].2, "USD", "quote currency carries through");
    // The emitted number string is whatever the FIRST buy's cost spec
    // produced (scale 2 here, since the buy was written "100.00").
    // The dedup key normalizes for comparison but doesn't normalize
    // the user-facing emitted form.
    assert_eq!(
        prices[0].1, "100.00",
        "emitted price preserves the first-emit cost's intrinsic scale"
    );
}

/// Over-sell crossing zero: the booker pre-splits a `-150` sell against
/// a `+100` lot into two postings — a fully-reducing `-100` leg matched
/// to the existing lot, and an augmenting `-50` leg creating a new
/// short position. Our inline inventory update sees them in order, so
/// the first leg classifies REDUCED (no emit) and the second leg sees
/// `prior=0` and classifies CREATED (emit). Hard-coded here to lock in
/// the assumption that this plugin runs on post-booking input —
/// regression-guards against future pipeline reordering that would
/// hand us un-split crossing postings.
#[test]
fn test_implicit_prices_oversell_crossing_zero_emits_for_residual_leg() {
    let plugin = ImplicitPricesPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Brokerage"),
        make_open("2024-01-01", "Assets:Cash"),
        // Initial buy of 100 X at 1 USD.
        make_transaction_with_cost(
            "2024-02-01",
            "Buy",
            "Assets:Brokerage",
            ("100", "X"),
            ("1", "USD"),
            "Assets:Cash",
        ),
        // Booker's split form of "sell -150 X": leg 1 fully reduces
        // the existing lot at the same cost. No emit expected.
        make_transaction_with_cost(
            "2024-03-01",
            "Reducing leg",
            "Assets:Brokerage",
            ("-100", "X"),
            ("1", "USD"),
            "Assets:Cash",
        ),
        // Leg 2 creates a -50 short position at a (hypothetical) new
        // cost basis. Emit expected.
        make_transaction_with_cost(
            "2024-03-01",
            "New-short leg",
            "Assets:Brokerage",
            ("-50", "X"),
            ("2", "USD"),
            "Assets:Cash",
        ),
    ]);
    let output = process_and_materialize(&plugin, input.clone());
    let prices = implicit_prices_emitted(&input, &output);
    assert_eq!(
        prices.len(),
        2,
        "buy + residual short leg emit; reducing leg suppressed. Got: {prices:?}"
    );
    assert!(prices.contains(&("X".into(), "1".into(), "USD".into())));
    assert!(prices.contains(&("X".into(), "2".into(), "USD".into())));
}

/// Posting with NO price annotation and NO cost: emits nothing.
#[test]
fn test_implicit_prices_emits_nothing_for_plain_transfer() {
    let plugin = ImplicitPricesPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:A"),
        make_open("2024-01-01", "Assets:B"),
        make_transaction(
            "2024-01-15",
            "Plain transfer",
            vec![("Assets:A", "100", "USD"), ("Assets:B", "-100", "USD")],
        ),
    ]);
    let output = process_and_materialize(&plugin, input.clone());
    assert!(implicit_prices_emitted(&input, &output).is_empty());
}

/// Test-isolation regression: explicit input `price` directives MUST
/// NOT be counted as plugin output. Pre-fix (Copilot review on PR #997)
/// the helper filtered by `filename: None`, but the test fixture's
/// `make_price` also sets that field to None — so any test that
/// included an input price would have miscounted.
#[test]
fn test_implicit_prices_emitted_excludes_input_price_directives() {
    let plugin = ImplicitPricesPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Brokerage"),
        make_open("2024-01-01", "Assets:Cash"),
        // Pre-existing explicit price directive
        make_price("2024-01-10", "HOOL", "500.00", "USD"),
        // Transaction that triggers the plugin
        make_transaction_with_cost(
            "2024-01-15",
            "Buy stock",
            "Assets:Brokerage",
            ("10", "HOOL"),
            ("520.00", "USD"),
            "Assets:Cash",
        ),
    ]);
    let output = process_and_materialize(&plugin, input.clone());
    // The explicit price (500.00) must NOT appear in plugin output.
    // Only the cost-derived 520.00 should.
    assert_eq!(
        implicit_prices_emitted(&input, &output),
        vec![("HOOL".into(), "520.00".into(), "USD".into())]
    );
}

// Property test: emitted per-unit price equals the generated per-unit
// price under both `@` and `@@` annotations.
//
// For any units N, per-unit price P, and annotation form:
//   - `@` (is_total=false): posting `N C @ P Q` → emitted Price `C @ P Q`
//     (identity — emitted price equals annotation amount directly)
//   - `@@` (is_total=true): posting `N C @@ (N*P) Q` → emitted Price `C @ P Q`
//     (round-trip — emitted per-unit = total / N exactly)
//
// The `@@` case is the EXACT regression test for the #992 bug, where the
// plugin emitted the total amount as a per-unit price (off by a factor
// of N). The `@` case pins the trivial-but-still-mutable identity path.
//
// Generators are in cents so fractional dollar prices like $5.27 are
// covered; integer units (1..=1000) keep `total = per_unit * units`
// exactly representable.
proptest::proptest! {
    #![proptest_config(proptest::prelude::ProptestConfig::with_cases(64))]

    #[test]
    fn prop_implicit_prices_emits_per_unit_for_both_annotation_forms(
        units in 1u32..1000,
        per_unit_cents in 1u32..1_000_000,
        is_total in proptest::bool::ANY,
    ) {
        use rust_decimal::Decimal;
        use std::str::FromStr;

        let units_d = Decimal::from(units);
        let per_unit = Decimal::new(i64::from(per_unit_cents), 2);
        // For `@`, the annotation carries the per-unit price directly;
        // for `@@`, it carries the total. The plugin's helper divides
        // total by units when is_total=true.
        let annotation_amount = if is_total { per_unit * units_d } else { per_unit };

        let plugin = ImplicitPricesPlugin;
        let input = make_input(vec![
            make_open("2024-01-01", "Assets:Brokerage"),
            make_open("2024-01-01", "Assets:Cash"),
            make_txn_with_price_annotation(
                "2024-01-15",
                "Buy",
                (&units.to_string(), "HOOL"),
                (&annotation_amount.to_string(), "USD"),
                is_total,
            ),
        ]);

        let output = process_and_materialize(&plugin, input.clone());
        let emitted = implicit_prices_emitted(&input, &output);

        // Exactly one price emitted (one priced posting).
        proptest::prop_assert_eq!(
            emitted.len(), 1,
            "expected 1 emitted price for units={} annotation={} is_total={}",
            units, annotation_amount, is_total
        );
        let (currency, number_str, quote) = &emitted[0];
        proptest::prop_assert_eq!(currency, "HOOL");
        proptest::prop_assert_eq!(quote, "USD");

        // The emitted per-unit price must equal `per_unit` exactly,
        // regardless of which annotation form was used. Under `@@`,
        // a pre-fix #992-style bug would have emitted the total instead.
        let emitted_d = Decimal::from_str(number_str)
            .expect("emitted number must be a valid Decimal");
        proptest::prop_assert_eq!(
            emitted_d, per_unit,
            "emitted {} must equal per-unit {} (is_total={})",
            emitted_d, per_unit, is_total
        );
    }
}

// ============================================================================
// NativePluginRegistry Tests
// ============================================================================

#[test]
fn test_registry_finds_all_plugins() {
    let registry = NativePluginRegistry::global();

    // All 14 built-in plugins should be findable
    let plugin_names = [
        "implicit_prices",
        "check_commodity",
        "auto_accounts",
        "leafonly",
        "noduplicates",
        "onecommodity",
        "unique_prices",
        "check_closing",
        "close_tree",
        "coherent_cost",
        "sellgains",
        "pedantic",
        "unrealized",
    ];

    for name in &plugin_names {
        assert!(registry.has(name), "should find plugin: {name}");
    }
}

#[test]
fn test_registry_finds_with_beancount_prefix() {
    let registry = NativePluginRegistry::global();

    assert!(registry.has("beancount.plugins.leafonly"));
    assert!(registry.has("beancount.plugins.noduplicates"));
}

#[test]
fn test_registry_iter_all() {
    let registry = NativePluginRegistry::global();
    let count = registry.iter().count();

    // Should have at least 13 plugins (14 minus auto_tag which might be different).
    // allow weak-count: registry-shape test — count grows as plugins are added,
    // pinning to a specific value would force every plugin addition to update
    // this test. See scripts/check-plugin-test-quality.sh.
    assert!(count >= 13, "should have at least 13 plugins, got {count}");
}

#[test]
fn test_auto_accounts_generates_opens() {
    use rustledger_plugin::types::*;
    use rustledger_plugin::*;

    let registry = NativePluginRegistry::global();
    let plugin: &dyn NativePlugin = registry.find_synth("auto_accounts").unwrap();

    // Create test input with transaction using unopened accounts
    let input = PluginInput {
        directives: vec![DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: "2020-01-01".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: None,
                narration: "Test".to_string(),
                tags: vec![],
                links: vec![],
                postings: vec![
                    PostingData {
                        account: "Expenses:Food".to_string(),
                        units: Some(AmountData {
                            number: "100".to_string(),
                            currency: "USD".to_string(),
                        }),
                        cost: None,
                        price: None,
                        metadata: vec![],
                        flag: None,
                        span: None,
                    },
                    PostingData {
                        account: "Assets:Cash".to_string(),
                        units: Some(AmountData {
                            number: "-100".to_string(),
                            currency: "USD".to_string(),
                        }),
                        cost: None,
                        price: None,
                        metadata: vec![],
                        flag: None,
                        span: None,
                    },
                ],
                metadata: vec![],
            }),
        }],
        options: PluginOptions::default(),
        config: None,
    };

    let output = process_and_materialize(plugin, input);

    eprintln!("Output directives: {}", output.directives.len());
    for d in &output.directives {
        eprintln!("  {}: {}", d.directive_type, d.date);
    }

    // Should have 3 directives: 2 Open + 1 Transaction
    assert_eq!(
        output.directives.len(),
        3,
        "expected 2 opens + 1 transaction"
    );

    // First two should be Open directives
    let open_count = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "open")
        .count();
    assert_eq!(open_count, 2, "expected 2 open directives");

    // Now test the full round-trip: convert back to Directive and validate
    let directives = wrappers_to_directives(&output.directives).unwrap();
    eprintln!("Converted directives: {}", directives.len());
    for d in &directives {
        match d {
            rustledger_core::Directive::Open(o) => {
                eprintln!("  Open: {}", o.account);
            }
            rustledger_core::Directive::Transaction(t) => {
                eprintln!("  Transaction: {}", t.narration);
            }
            _ => eprintln!("  Other"),
        }
    }

    // Should have 2 Open + 1 Transaction
    let open_count = directives
        .iter()
        .filter(|d| matches!(d, rustledger_core::Directive::Open(_)))
        .count();
    assert_eq!(open_count, 2, "expected 2 Open directives after conversion");
}

#[test]
fn test_auto_accounts_same_date_ordering() {
    // Test case: Open directive should come before Transaction on same date
    use rustledger_plugin::types::*;
    use rustledger_plugin::*;

    let registry = NativePluginRegistry::global();
    let plugin: &dyn NativePlugin = registry.find_synth("auto_accounts").unwrap();

    // Input: existing open + transaction that uses new account on same date as first use
    let input = PluginInput {
        directives: vec![
            DirectiveWrapper {
                directive_type: "open".to_string(),
                date: "1900-01-01".to_string(),
                filename: None,
                lineno: None,
                data: DirectiveData::Open(OpenData {
                    account: "Liabilities:Credit-Card".to_string(),
                    currencies: vec![],
                    booking: None,
                    metadata: vec![],
                }),
            },
            DirectiveWrapper {
                directive_type: "transaction".to_string(),
                date: "2016-08-30".to_string(),
                filename: None,
                lineno: None,
                data: DirectiveData::Transaction(TransactionData {
                    flag: "*".to_string(),
                    payee: Some("Amazon".to_string()),
                    narration: "Order".to_string(),
                    tags: vec![],
                    links: vec![],
                    postings: vec![
                        PostingData {
                            account: "Expenses:FIXME:A".to_string(),
                            units: Some(AmountData {
                                number: "14.99".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                            metadata: vec![],
                            flag: None,
                            span: None,
                        },
                        PostingData {
                            account: "Liabilities:Credit-Card".to_string(),
                            units: Some(AmountData {
                                number: "-14.99".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                            metadata: vec![],
                            flag: None,
                            span: None,
                        },
                    ],
                    metadata: vec![],
                }),
            },
        ],
        options: PluginOptions::default(),
        config: None,
    };

    let mut output = process_and_materialize(plugin, input);
    // Plugins under the ops protocol no longer sort their own output —
    // the loader's `apply_plugin_ops` re-sorts after the plugin pass.
    // For unit tests that bypass the loader, apply the same sort here
    // so we exercise the post-pipeline directive order.
    sort_directives(&mut output.directives);

    eprintln!("\n=== Output directives (ordered) ===");
    for (i, d) in output.directives.iter().enumerate() {
        eprintln!("  [{}] {}: {}", i, d.directive_type, d.date);
        if let DirectiveData::Open(open) = &d.data {
            eprintln!("       account: {}", open.account);
        }
    }

    // Should have 3 directives total: 2 Open + 1 Transaction
    assert_eq!(output.directives.len(), 3);

    // The Open for Expenses:FIXME:A should come BEFORE the Transaction on 2016-08-30
    let idx_open_fixme = output
        .directives
        .iter()
        .position(|d| {
            d.directive_type == "open"
                && matches!(&d.data, DirectiveData::Open(o) if o.account == "Expenses:FIXME:A")
        })
        .expect("should have Open for Expenses:FIXME:A");

    let idx_txn = output
        .directives
        .iter()
        .position(|d| d.directive_type == "transaction" && d.date == "2016-08-30")
        .expect("should have Transaction on 2016-08-30");

    eprintln!("\nOpen Expenses:FIXME:A at index {idx_open_fixme}, Transaction at index {idx_txn}");

    assert!(
        idx_open_fixme < idx_txn,
        "Open for Expenses:FIXME:A should come before Transaction on same date"
    );

    // Now convert back to Directive and check order is preserved
    let directives = wrappers_to_directives(&output.directives).unwrap();
    eprintln!("\n=== Converted directives ===");
    for (i, d) in directives.iter().enumerate() {
        match d {
            rustledger_core::Directive::Open(o) => {
                eprintln!("  [{}] Open: {} on {}", i, o.account, o.date);
            }
            rustledger_core::Directive::Transaction(t) => {
                eprintln!("  [{}] Transaction on {}", i, t.date);
            }
            _ => {}
        }
    }

    // Check order is preserved: Open for Expenses:FIXME:A before Transaction
    let converted_idx_open = directives
        .iter()
        .position(|d| {
            matches!(d, rustledger_core::Directive::Open(o) if o.account.as_str() == "Expenses:FIXME:A")
        })
        .expect("should have Open after conversion");

    let converted_idx_txn = directives
        .iter()
        .position(|d| matches!(d, rustledger_core::Directive::Transaction(_)))
        .expect("should have Transaction after conversion");

    eprintln!(
        "\nAfter conversion: Open at {converted_idx_open}, Transaction at {converted_idx_txn}"
    );

    assert!(
        converted_idx_open < converted_idx_txn,
        "Open should still come before Transaction after conversion"
    );
}

// ============================================================================
// CheckClosingPlugin Tests
// ============================================================================

use rustledger_plugin::native::CheckClosingPlugin;

fn make_transaction_with_closing_metadata(
    date: &str,
    narration: &str,
    account: &str,
    units: (&str, &str),
    other_account: &str,
) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: "transaction".to_string(),
        date: date.to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Transaction(TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: narration.to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![
                PostingData {
                    account: account.to_string(),
                    units: Some(AmountData {
                        number: units.0.to_string(),
                        currency: units.1.to_string(),
                    }),
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![("closing".to_string(), MetaValueData::Bool(true))],
                    span: None,
                },
                PostingData {
                    account: other_account.to_string(),
                    units: None,
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
            ],
        }),
    }
}

/// Test `check_closing` adds balance assertion after closing posting.
#[test]
fn test_check_closing_adds_balance_assertion() {
    let plugin = CheckClosingPlugin;

    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Final"),
        make_transaction_with_closing_metadata(
            "2024-01-15",
            "Close out account",
            "Assets:Bank",
            ("-500.00", "USD"),
            "Expenses:Final",
        ),
    ]);

    let output = process_and_materialize(&plugin, input);

    assert!(output.errors.is_empty(), "expected no errors");

    // Should have a balance directive for the day after
    let balance = output
        .directives
        .iter()
        .find(|d| d.directive_type == "balance");
    assert!(balance.is_some(), "expected balance assertion to be added");

    let balance = balance.unwrap();
    assert_eq!(balance.date, "2024-01-16", "balance should be on next day");

    if let DirectiveData::Balance(b) = &balance.data {
        assert_eq!(b.account, "Assets:Bank");
        assert_eq!(b.amount.number, "0");
    } else {
        panic!("expected balance directive");
    }
}

/// Test `check_closing` does nothing without closing metadata.
#[test]
fn test_check_closing_no_metadata() {
    let plugin = CheckClosingPlugin;

    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        make_transaction(
            "2024-01-15",
            "Normal transaction",
            vec![
                ("Expenses:Food", "50.00", "USD"),
                ("Assets:Bank", "-50.00", "USD"),
            ],
        ),
    ]);

    let output = process_and_materialize(&plugin, input);

    assert!(output.errors.is_empty(), "expected no errors");

    // Should NOT have any balance directives
    let balance_count = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "balance")
        .count();
    assert_eq!(
        balance_count, 0,
        "should not add balance without closing metadata"
    );
}

/// Empty input → no errors, no directives. Pins the baseline.
#[test]
fn test_check_closing_empty_input() {
    let plugin = CheckClosingPlugin;
    let output = process_and_materialize(&plugin, make_input(vec![]));
    assert!(output.errors.is_empty());
    assert_eq!(output.directives.len(), 0);
}

/// `closing: FALSE` is treated the same as no metadata — only `Bool(true)`
/// triggers emission. Pins the boolean-value branch.
#[test]
fn test_check_closing_false_value_no_emission() {
    let plugin = CheckClosingPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Final"),
        DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: "2024-01-15".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: None,
                narration: "Not really closing".to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings: vec![
                    PostingData {
                        account: "Assets:Bank".to_string(),
                        units: Some(AmountData {
                            number: "-100.00".to_string(),
                            currency: "USD".to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![("closing".to_string(), MetaValueData::Bool(false))],
                        span: None,
                    },
                    PostingData {
                        account: "Expenses:Final".to_string(),
                        units: None,
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                        span: None,
                    },
                ],
            }),
        },
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    let balance_count = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "balance")
        .count();
    assert_eq!(balance_count, 0);
}

/// Any truthy `closing` value marks the posting, as beancount reads it
/// (`posting.meta.get("closing", False)`): a non-empty string emits the
/// balance and the marker is removed from the posting (#2600; only `TRUE`
/// did before, and the marker stayed).
#[test]
fn test_check_closing_non_bool_metadata_no_emission() {
    let plugin = CheckClosingPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Final"),
        DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: "2024-01-15".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: None,
                narration: "String closing".to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings: vec![
                    PostingData {
                        account: "Assets:Bank".to_string(),
                        units: Some(AmountData {
                            number: "-100.00".to_string(),
                            currency: "USD".to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![(
                            "closing".to_string(),
                            MetaValueData::String("yes".to_string()),
                        )],
                        span: None,
                    },
                    PostingData {
                        account: "Expenses:Final".to_string(),
                        units: None,
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                        span: None,
                    },
                ],
            }),
        },
    ]);
    let output = process_and_materialize(&plugin, input);
    let balance_count = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "balance")
        .count();
    assert_eq!(balance_count, 1);
    let marker_left = output.directives.iter().any(|d| match &d.data {
        DirectiveData::Transaction(t) => t
            .postings
            .iter()
            .any(|p| p.metadata.iter().any(|(k, _)| k == "closing")),
        _ => false,
    });
    assert!(!marker_left, "the closing marker is removed once expanded");
}

/// Closing posting with `units = None` uses the first operating currency.
/// Here `make_input` sets `operating_currencies = ["USD"]`, so the emitted
/// balance asserts USD.
#[test]
fn test_check_closing_units_none_uses_operating_currency_usd() {
    let plugin = CheckClosingPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Final"),
        DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: "2024-01-15".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: None,
                narration: "Auto-balanced close".to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings: vec![
                    PostingData {
                        // Closing posting with units=None — picks up operating_currencies[0].
                        account: "Assets:Bank".to_string(),
                        units: None,
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![("closing".to_string(), MetaValueData::Bool(true))],
                        span: None,
                    },
                    PostingData {
                        account: "Expenses:Final".to_string(),
                        units: Some(AmountData {
                            number: "100.00".to_string(),
                            currency: "USD".to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                        span: None,
                    },
                ],
            }),
        },
    ]);
    let output = process_and_materialize(&plugin, input);
    let balance = output
        .directives
        .iter()
        .find(|d| d.directive_type == "balance")
        .expect("should have balance assertion");
    assert_eq!(balance.date, "2024-01-16");
    if let DirectiveData::Balance(b) = &balance.data {
        assert_eq!(b.account, "Assets:Bank");
        assert_eq!(b.amount.number, "0");
        assert_eq!(b.amount.currency, "USD");
    } else {
        panic!("expected Balance directive");
    }
}

/// Closing posting with `units = None` and `operating_currencies = ["EUR"]`
/// emits a balance assertion in EUR — NOT USD. This is the fix for #1039:
/// previously the fallback was hardcoded to "USD" regardless of the user's
/// operating currency.
#[test]
fn test_check_closing_units_none_uses_operating_currency_eur() {
    let plugin = CheckClosingPlugin;
    let input = PluginInput {
        directives: vec![
            make_open("2024-01-01", "Assets:Bank"),
            make_open("2024-01-01", "Expenses:Final"),
            DirectiveWrapper {
                directive_type: "transaction".to_string(),
                date: "2024-01-15".to_string(),
                filename: None,
                lineno: None,
                data: DirectiveData::Transaction(TransactionData {
                    flag: "*".to_string(),
                    payee: None,
                    narration: "Auto-balanced close".to_string(),
                    tags: vec![],
                    links: vec![],
                    metadata: vec![],
                    postings: vec![
                        PostingData {
                            account: "Assets:Bank".to_string(),
                            units: None,
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![("closing".to_string(), MetaValueData::Bool(true))],
                            span: None,
                        },
                        PostingData {
                            account: "Expenses:Final".to_string(),
                            units: Some(AmountData {
                                number: "100.00".to_string(),
                                currency: "EUR".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
                        },
                    ],
                }),
            },
        ],
        options: PluginOptions {
            operating_currencies: vec!["EUR".to_string()],
            title: None,
            ..Default::default()
        },
        config: None,
    };
    let output = process_and_materialize(&plugin, input);
    let balance = output
        .directives
        .iter()
        .find(|d| d.directive_type == "balance")
        .expect("should have balance assertion");
    if let DirectiveData::Balance(b) = &balance.data {
        assert_eq!(b.account, "Assets:Bank");
        assert_eq!(b.amount.number, "0");
        assert_eq!(
            b.amount.currency, "EUR",
            "operating_currencies[0] (EUR) should win over the USD literal fallback"
        );
    } else {
        panic!("expected Balance directive");
    }
}

/// Closing posting with `units = None` and `operating_currencies = []`
/// (no operating currencies configured) falls back to "USD" for backward
/// compatibility. Pins the `unwrap_or_else(|| "USD")` branch.
#[test]
fn test_check_closing_units_none_falls_back_to_usd_when_no_operating_ccy() {
    let plugin = CheckClosingPlugin;
    let input = PluginInput {
        directives: vec![
            make_open("2024-01-01", "Assets:Bank"),
            DirectiveWrapper {
                directive_type: "transaction".to_string(),
                date: "2024-01-15".to_string(),
                filename: None,
                lineno: None,
                data: DirectiveData::Transaction(TransactionData {
                    flag: "*".to_string(),
                    payee: None,
                    narration: "Auto-balanced close".to_string(),
                    tags: vec![],
                    links: vec![],
                    metadata: vec![],
                    postings: vec![PostingData {
                        account: "Assets:Bank".to_string(),
                        units: None,
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![("closing".to_string(), MetaValueData::Bool(true))],
                        span: None,
                    }],
                }),
            },
        ],
        options: PluginOptions {
            operating_currencies: vec![],
            title: None,
            ..Default::default()
        },
        config: None,
    };
    let output = process_and_materialize(&plugin, input);
    let balance = output
        .directives
        .iter()
        .find(|d| d.directive_type == "balance")
        .expect("should have balance assertion");
    if let DirectiveData::Balance(b) = &balance.data {
        assert_eq!(b.amount.currency, "USD", "fallback when no operating ccy");
    } else {
        panic!("expected Balance directive");
    }
}

/// Multiple closing postings in a single transaction → one balance assertion
/// per closing posting, all dated the day after.
#[test]
fn test_check_closing_multiple_closings_in_one_txn() {
    let plugin = CheckClosingPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:USD"),
        make_open("2024-01-01", "Assets:EUR"),
        make_open("2024-01-01", "Equity:Close"),
        DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: "2024-06-30".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: None,
                narration: "Close both accounts".to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings: vec![
                    PostingData {
                        account: "Assets:USD".to_string(),
                        units: Some(AmountData {
                            number: "-100.00".to_string(),
                            currency: "USD".to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![("closing".to_string(), MetaValueData::Bool(true))],
                        span: None,
                    },
                    PostingData {
                        account: "Assets:EUR".to_string(),
                        units: Some(AmountData {
                            number: "-50.00".to_string(),
                            currency: "EUR".to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![("closing".to_string(), MetaValueData::Bool(true))],
                        span: None,
                    },
                    PostingData {
                        account: "Equity:Close".to_string(),
                        units: None,
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                        span: None,
                    },
                ],
            }),
        },
    ]);
    let output = process_and_materialize(&plugin, input);
    let balances: Vec<_> = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "balance")
        .collect();
    assert_eq!(balances.len(), 2, "one balance per closing posting");
    for b in &balances {
        assert_eq!(b.date, "2024-07-01");
    }
    // Each balance should reference the correct account+currency.
    let mut by_account: std::collections::HashMap<&str, &str> = std::collections::HashMap::new();
    for b in &balances {
        if let DirectiveData::Balance(bal) = &b.data {
            by_account.insert(bal.account.as_str(), bal.amount.currency.as_str());
        }
    }
    assert_eq!(by_account.get("Assets:USD"), Some(&"USD"));
    assert_eq!(by_account.get("Assets:EUR"), Some(&"EUR"));
}

/// Non-Transaction directives (Open, Balance, Price, etc.) flow through
/// unchanged — no emission.
#[test]
fn test_check_closing_ignores_non_transaction_directives() {
    let plugin = CheckClosingPlugin;
    let input = make_input(vec![
        make_commodity("2024-01-01", "USD"),
        make_open("2024-01-01", "Assets:Bank"),
        make_price("2024-01-15", "USD", "1.10", "EUR"),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    let balance_count = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "balance")
        .count();
    assert_eq!(balance_count, 0);
    // All inputs preserved.
    assert_eq!(output.directives.len(), 3);
}

/// Malformed transaction date → `increment_date()` returns `None` → the
/// plugin defensively skips emission rather than panicking.
///
/// Unreachable from parser-loaded ledgers (the parser validates date format
/// upstream), but reachable from any caller constructing `DirectiveWrapper`
/// programmatically — including other plugins in a chain, transformation
/// passes that synthesize directives, and tests like this one. The source
/// code guards against it, so we pin the guard.
#[test]
fn test_check_closing_invalid_date_skips_emission() {
    let plugin = CheckClosingPlugin;
    let input = make_input(vec![DirectiveWrapper {
        directive_type: "transaction".to_string(),
        // Month "13" is rejected by `increment_date` (the days-in-month
        // match returns None for any month outside 1..=12).
        date: "2024-13-01".to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Transaction(TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: "Bad date".to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![PostingData {
                account: "Assets:Bank".to_string(),
                units: Some(AmountData {
                    number: "-100.00".to_string(),
                    currency: "USD".to_string(),
                }),
                cost: None,
                price: None,
                flag: None,
                metadata: vec![("closing".to_string(), MetaValueData::Bool(true))],
                span: None,
            }],
        }),
    }]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    let balance_count = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "balance")
        .count();
    assert_eq!(
        balance_count, 0,
        "no balance emitted when date can't be incremented"
    );
    // The input transaction itself must still pass through unchanged — a
    // regression that early-returned and dropped the input would slip past
    // the balance-count check above.
    assert_eq!(
        output.directives.len(),
        1,
        "original transaction should pass through; got: {:?}",
        output.directives
    );
}

/// Mixed posting metadata: a closing posting alongside a posting carrying
/// a non-`closing` key should still emit exactly one balance.
#[test]
fn test_check_closing_unrelated_metadata_doesnt_trigger() {
    let plugin = CheckClosingPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Final"),
        DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: "2024-01-15".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: None,
                narration: "Mixed metadata".to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings: vec![
                    PostingData {
                        account: "Assets:Bank".to_string(),
                        units: Some(AmountData {
                            number: "-100.00".to_string(),
                            currency: "USD".to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![("closing".to_string(), MetaValueData::Bool(true))],
                        span: None,
                    },
                    PostingData {
                        // Non-`closing` metadata key — should NOT trigger emission.
                        account: "Expenses:Final".to_string(),
                        units: Some(AmountData {
                            number: "100.00".to_string(),
                            currency: "USD".to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![("note".to_string(), MetaValueData::Bool(true))],
                        span: None,
                    },
                ],
            }),
        },
    ]);
    let output = process_and_materialize(&plugin, input);
    let balances: Vec<_> = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "balance")
        .collect();
    assert_eq!(balances.len(), 1, "only the `closing` key triggers");
    if let DirectiveData::Balance(b) = &balances[0].data {
        assert_eq!(b.account, "Assets:Bank");
    }
}

// ============================================================================
// CloseTreePlugin Tests
// ============================================================================

use rustledger_plugin::native::CloseTreePlugin;

fn make_close(date: &str, account: &str) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: "close".to_string(),
        date: date.to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Close(CloseData {
            account: account.to_string(),
            metadata: vec![],
        }),
    }
}

/// Test `close_tree` closes child accounts when parent is closed.
#[test]
fn test_close_tree_closes_children() {
    let plugin = CloseTreePlugin;

    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Assets:Bank:Checking"),
        make_open("2024-01-01", "Assets:Bank:Savings"),
        make_transaction(
            "2024-01-15",
            "Deposit",
            vec![
                ("Assets:Bank:Checking", "100.00", "USD"),
                ("Assets:Bank:Savings", "-100.00", "USD"),
            ],
        ),
        make_close("2024-12-31", "Assets:Bank"),
    ]);

    let output = process_and_materialize(&plugin, input);

    assert!(output.errors.is_empty(), "expected no errors");

    // Should have close directives for both child accounts
    let close_directives: Vec<_> = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "close")
        .collect();

    assert_eq!(
        close_directives.len(),
        3,
        "expected 3 close directives (parent + 2 children)"
    );

    // Verify child accounts are closed
    let closed_accounts: Vec<String> = close_directives
        .iter()
        .filter_map(|d| {
            if let DirectiveData::Close(c) = &d.data {
                Some(c.account.clone())
            } else {
                None
            }
        })
        .collect();

    assert!(closed_accounts.contains(&"Assets:Bank".to_string()));
    assert!(closed_accounts.contains(&"Assets:Bank:Checking".to_string()));
    assert!(closed_accounts.contains(&"Assets:Bank:Savings".to_string()));
}

/// Test `close_tree` does not duplicate already closed accounts.
#[test]
fn test_close_tree_no_duplicate_close() {
    let plugin = CloseTreePlugin;

    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Assets:Bank:Checking"),
        make_close("2024-06-30", "Assets:Bank:Checking"), // Already closed
        make_close("2024-12-31", "Assets:Bank"),
    ]);

    let output = process_and_materialize(&plugin, input);

    // Count close directives for Checking
    let checking_closes = output
        .directives
        .iter()
        .filter(|d| {
            d.directive_type == "close"
                && matches!(&d.data, DirectiveData::Close(c) if c.account == "Assets:Bank:Checking")
        })
        .count();

    assert_eq!(
        checking_closes, 1,
        "should not duplicate close for already-closed account"
    );
}

// ============================================================================
// CoherentCostPlugin Tests
// ============================================================================

use rustledger_plugin::native::CoherentCostPlugin;

fn make_transaction_with_price(
    date: &str,
    narration: &str,
    account: &str,
    units: (&str, &str),
    price: (&str, &str),
    other_account: &str,
) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: "transaction".to_string(),
        date: date.to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Transaction(TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: narration.to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![
                PostingData {
                    account: account.to_string(),
                    units: Some(AmountData {
                        number: units.0.to_string(),
                        currency: units.1.to_string(),
                    }),
                    cost: None,
                    price: Some(PriceAnnotationData {
                        amount: Some(AmountData {
                            number: price.0.to_string(),
                            currency: price.1.to_string(),
                        }),
                        is_total: false,
                        number: None,
                        currency: None,
                    }),
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
                PostingData {
                    account: other_account.to_string(),
                    units: None,
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
            ],
        }),
    }
}

/// Test `coherent_cost` detects currency used with both cost and price.
#[test]
fn test_coherent_cost_mixed_usage_error() {
    let plugin = CoherentCostPlugin;

    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Stock"),
        make_open("2024-01-01", "Assets:Cash"),
        // Use HOOL with cost notation
        make_transaction_with_cost(
            "2024-01-15",
            "Buy stock",
            "Assets:Stock",
            ("10", "HOOL"),
            ("100", "USD"),
            "Assets:Cash",
        ),
        // Use HOOL with price notation
        make_transaction_with_price(
            "2024-02-15",
            "Convert",
            "Assets:Stock",
            ("5", "HOOL"),
            ("110", "USD"),
            "Assets:Cash",
        ),
    ]);

    let output = process_and_materialize(&plugin, input);

    assert_eq!(
        output.errors.len(),
        1,
        "expected error for mixed cost/price usage"
    );
    assert!(
        output.errors[0].message.contains("HOOL"),
        "error should mention the currency"
    );
}

/// Test `coherent_cost` passes when currency uses only cost.
#[test]
fn test_coherent_cost_only_cost_ok() {
    let plugin = CoherentCostPlugin;

    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Stock"),
        make_open("2024-01-01", "Assets:Cash"),
        make_transaction_with_cost(
            "2024-01-15",
            "Buy stock",
            "Assets:Stock",
            ("10", "HOOL"),
            ("100", "USD"),
            "Assets:Cash",
        ),
        make_transaction_with_cost(
            "2024-02-15",
            "Buy more",
            "Assets:Stock",
            ("5", "HOOL"),
            ("110", "USD"),
            "Assets:Cash",
        ),
    ]);

    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "expected no errors when using only cost"
    );
}

/// Test `coherent_cost` passes when currency uses only price.
#[test]
fn test_coherent_cost_only_price_ok() {
    let plugin = CoherentCostPlugin;

    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Forex"),
        make_open("2024-01-01", "Assets:Cash"),
        make_transaction_with_price(
            "2024-01-15",
            "Exchange",
            "Assets:Forex",
            ("100", "EUR"),
            ("1.10", "USD"),
            "Assets:Cash",
        ),
        make_transaction_with_price(
            "2024-02-15",
            "Exchange more",
            "Assets:Forex",
            ("50", "EUR"),
            ("1.12", "USD"),
            "Assets:Cash",
        ),
    ]);

    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "expected no errors when using only price"
    );
}

/// Test `coherent_cost` passes when posting has BOTH cost AND price (capital gains).
/// Regression test for issue #516.
#[test]
fn test_coherent_cost_cost_and_price_ok() {
    let plugin = CoherentCostPlugin;

    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Stock"),
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Income:CapitalGains"),
        // Buy with cost
        make_transaction_with_cost(
            "2024-01-15",
            "Buy stock",
            "Assets:Stock",
            ("10", "HOOL"),
            ("100", "USD"),
            "Assets:Cash",
        ),
        // Sell with BOTH cost AND price (standard capital gains recording)
        make_transaction_with_cost_and_price(
            "2024-06-15",
            "Sell stock",
            "Assets:Stock",
            ("-10", "HOOL"),
            ("100", "USD"), // cost basis
            ("150", "USD"), // sale price
            "Assets:Cash",
        ),
    ]);

    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "expected no errors when using cost+price on same posting (capital gains)"
    );
}

// ============================================================================
// Helper: make_input with config
// ============================================================================

fn make_input_with_config(directives: Vec<DirectiveWrapper>, config: &str) -> PluginInput {
    PluginInput {
        directives,
        options: PluginOptions {
            operating_currencies: vec!["USD".to_string()],
            title: None,
            ..Default::default()
        },
        config: Some(config.to_string()),
    }
}

fn make_transaction_with_tag(
    date: &str,
    narration: &str,
    tags: Vec<&str>,
    postings: Vec<(&str, &str, &str)>,
) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: "transaction".to_string(),
        date: date.to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Transaction(TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: narration.to_string(),
            tags: tags.into_iter().map(String::from).collect(),
            links: vec![],
            metadata: vec![],
            postings: postings
                .into_iter()
                .map(|(account, number, currency)| PostingData {
                    account: account.to_string(),
                    units: Some(AmountData {
                        number: number.to_string(),
                        currency: currency.to_string(),
                    }),
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                })
                .collect(),
        }),
    }
}

fn make_transaction_with_metadata(
    date: &str,
    narration: &str,
    metadata: Vec<(&str, MetaValueData)>,
    postings: Vec<(&str, &str, &str)>,
) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: "transaction".to_string(),
        date: date.to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Transaction(TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: narration.to_string(),
            tags: vec![],
            links: vec![],
            metadata: metadata
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect(),
            postings: postings
                .into_iter()
                .map(|(account, number, currency)| PostingData {
                    account: account.to_string(),
                    units: Some(AmountData {
                        number: number.to_string(),
                        currency: currency.to_string(),
                    }),
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                })
                .collect(),
        }),
    }
}

fn make_open_with_currencies(date: &str, account: &str, currencies: Vec<&str>) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: "open".to_string(),
        date: date.to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Open(OpenData {
            account: account.to_string(),
            currencies: currencies.into_iter().map(String::from).collect(),
            booking: None,
            metadata: vec![],
        }),
    }
}

// Property test: emitted error count equals the size of the
// `currencies_with_cost ∩ currencies_with_price_only` intersection.
//
// The plugin's invariant is purely set-theoretic: for any sequence of
// postings, an error is emitted for every currency that appears in
// BOTH the "with cost" and "price-only" buckets. Generators produce a
// list of (currency_id, posting_kind) — kind is one of (cost, price-
// only, both). The reference computation in the test mirrors the
// plugin's bookkeeping; any drift in classification (e.g., a bug that
// counts a `cost+price` posting in the price-only bucket) would make
// the assertion fail.
proptest::proptest! {
    #![proptest_config(proptest::prelude::ProptestConfig::with_cases(64))]

    #[test]
    fn prop_coherent_cost_errors_match_intersection(
        // Up to 8 postings, each with a currency_id ∈ 0..4 and a
        // kind ∈ 0..3 (0=cost-only, 1=price-only, 2=both cost+price).
        postings in proptest::collection::vec(
            (0u32..4, 0u32..3),
            1..=8,
        ),
    ) {
        use std::collections::HashSet;

        let plugin = CoherentCostPlugin;

        // Build the synthetic transaction. Each posting goes into a
        // separate transaction to avoid balance constraints; the
        // plugin treats each posting independently anyway.
        let mut directives: Vec<DirectiveWrapper> = vec![
            make_open("2020-01-01", "Assets:Bank"),
        ];
        for (i, (cid, kind)) in postings.iter().enumerate() {
            let currency = format!("C{cid}");
            let has_cost = matches!(kind, 0 | 2);
            let has_price = matches!(kind, 1 | 2);
            directives.push(DirectiveWrapper {
                directive_type: "transaction".to_string(),
                date: format!("2024-01-{:02}", (i % 28) + 1),
                filename: None,
                lineno: None,
                data: DirectiveData::Transaction(TransactionData {
                    flag: "*".to_string(),
                    payee: None,
                    narration: "p".to_string(),
                    tags: vec![],
                    links: vec![],
                    metadata: vec![],
                    postings: vec![PostingData {
                        account: "Assets:Bank".to_string(),
                        units: Some(AmountData {
                            number: "1".to_string(),
                            currency: currency.clone(),
                        }),
                        cost: if has_cost {
                            Some(CostData {
                                number: Some(rustledger_plugin_types::CostNumberData::PerUnit { value: "100".to_string() }),
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            })
                        } else {
                            None
                        },
                        price: if has_price {
                            Some(PriceAnnotationData {
                                is_total: false,
                                amount: Some(AmountData {
                                    number: "100".to_string(),
                                    currency: "USD".to_string(),
                                }),
                                number: None,
                                currency: None,
                            })
                        } else {
                            None
                        },
                        flag: None,
                        metadata: vec![],
                                            span: None,
                    }],
                }),
            });
        }
        let input = make_input(directives);

        // Reference computation: mirror the plugin's classification.
        // A posting with cost goes to with_cost; one with price-only
        // (no cost) goes to price_only. `cost+price` (kind=2) is
        // explicitly NOT problematic per the plugin's docstring.
        let mut with_cost: HashSet<u32> = HashSet::new();
        let mut price_only: HashSet<u32> = HashSet::new();
        for (cid, kind) in &postings {
            match kind {
                0 | 2 => { with_cost.insert(*cid); }
                1     => { price_only.insert(*cid); }
                _ => {}
            }
        }
        let expected_errors = with_cost.intersection(&price_only).count();

        let output = process_and_materialize(&plugin, input);
        proptest::prop_assert_eq!(
            output.errors.len(), expected_errors,
            "expected {} error(s) (currencies in both cost and price-only sets); \
             postings={:?}",
            expected_errors, postings
        );
    }
}

// ============================================================================
// AutoTagPlugin Tests
// ============================================================================

#[test]
fn test_auto_tag_adds_tag_for_expense() {
    let plugin = AutoTagPlugin::new();
    let input = make_input(vec![
        make_open("2024-01-01", "Expenses:Food:Restaurant"),
        make_open("2024-01-01", "Assets:Cash"),
        make_transaction(
            "2024-01-15",
            "Lunch",
            vec![
                ("Expenses:Food:Restaurant", "25", "USD"),
                ("Assets:Cash", "-25", "USD"),
            ],
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    // Verify a tag was added to the transaction
    let txn = output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction")
        .unwrap();
    let DirectiveData::Transaction(data) = &txn.data else {
        panic!(
            "directive_type was 'transaction' but data variant is {:?} — impossible state",
            txn.data
        );
    };
    assert_eq!(
        data.tags.len(),
        1,
        "auto_tag should add exactly one tag for the single matching posting"
    );
}

// ============================================================================
// NoUnusedPlugin Tests
// ============================================================================

#[test]
fn test_no_unused_warns_on_unused_account() {
    let plugin = NoUnusedPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Used"),
        make_open("2024-01-01", "Assets:Unused"),
        make_open("2024-01-01", "Equity:Opening"),
        make_transaction(
            "2024-01-15",
            "Use it",
            vec![
                ("Assets:Used", "100", "USD"),
                ("Equity:Opening", "-100", "USD"),
            ],
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(
        output.errors.len(),
        1,
        "exactly one error for the single unused account"
    );
    assert!(
        output.errors[0].message.contains("Unused"),
        "error should mention the unused account"
    );
}

#[test]
fn test_no_unused_ok_when_all_used() {
    let plugin = NoUnusedPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Expenses:Food"),
        make_transaction(
            "2024-01-15",
            "Lunch",
            vec![
                ("Expenses:Food", "25", "USD"),
                ("Assets:Cash", "-25", "USD"),
            ],
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty(), "no unused accounts");
}

// ============================================================================
// PedanticPlugin Tests
// ============================================================================

#[test]
fn test_pedantic_runs_multiple_validators() {
    let plugin = PedanticPlugin;
    // Create a scenario with a leaf-only violation
    let input = make_input(vec![
        make_open("2024-01-01", "Expenses:Food"),
        make_open("2024-01-01", "Expenses:Food:Restaurant"),
        make_open("2024-01-01", "Assets:Cash"),
        make_transaction(
            "2024-01-15",
            "Bad",
            vec![
                ("Expenses:Food", "25", "USD"), // leaf violation
                ("Assets:Cash", "-25", "USD"),
            ],
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    let messages: Vec<&str> = output.errors.iter().map(|e| e.message.as_str()).collect();
    // In beancount's plugin order: the undeclared commodity, the leaf-only
    // violation (`Expenses:Food:Restaurant` is only opened, but makes
    // `Expenses:Food` a parent, as in bean-check), and the unused account
    // (`nounused` is one of the nine; rledger ran four before #2600).
    assert_eq!(
        messages,
        [
            "Missing Commodity directive for 'USD' in 'Assets:Cash'",
            "Non-leaf account 'Expenses:Food' has postings on it",
            "Unused account 'Expenses:Food:Restaurant'",
        ]
    );
}

// ============================================================================
// RxTxnPlugin Tests
// ============================================================================
//
// `rx_txn` finds transactions tagged `#rx_txn` and adds default
// metadata (`final = "None"`, `roll = "True"`) when those keys are
// not already set. Existing values are preserved.

/// Tagged transaction → both `final` and `roll` metadata added.
/// Pre-fix this test asserted only "`has_final` OR `has_roll`" — weak
/// because either metadata addition alone passed it. Now strict.
#[test]
fn test_rx_txn_adds_metadata_to_tagged_transaction() {
    let plugin = RxTxnPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Expenses:Rent"),
        make_transaction_with_tag(
            "2024-01-15",
            "Monthly rent",
            vec!["rx_txn"],
            vec![
                ("Expenses:Rent", "1000", "USD"),
                ("Assets:Cash", "-1000", "USD"),
            ],
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    let txn = output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction")
        .expect("transaction must be present");
    let DirectiveData::Transaction(data) = &txn.data else {
        panic!(
            "non-Transaction data on transaction directive: {:?}",
            txn.data
        );
    };
    let final_meta = data.metadata.iter().find(|(k, _)| k == "final");
    let roll_meta = data.metadata.iter().find(|(k, _)| k == "roll");
    assert!(final_meta.is_some(), "rx_txn must add 'final' metadata");
    assert!(roll_meta.is_some(), "rx_txn must add 'roll' metadata");
    // Verify defaults specifically.
    if let Some((_, MetaValueData::String(v))) = final_meta {
        assert_eq!(v, "None", "default 'final' value is 'None'");
    } else {
        panic!("'final' metadata should be a string 'None'");
    }
    if let Some((_, MetaValueData::String(v))) = roll_meta {
        assert_eq!(v, "True", "default 'roll' value is 'True'");
    } else {
        panic!("'roll' metadata should be a string 'True'");
    }
}

/// Untagged transaction → no metadata mutation. Pins the
/// `tags.contains("rx_txn")` filter.
#[test]
fn test_rx_txn_ignores_untagged_transaction() {
    let plugin = RxTxnPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Expenses:Food"),
        make_transaction(
            "2024-01-15",
            "Lunch",
            vec![
                ("Expenses:Food", "25", "USD"),
                ("Assets:Cash", "-25", "USD"),
            ],
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    let txn = output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction")
        .expect("transaction must be present");
    let DirectiveData::Transaction(data) = &txn.data else {
        panic!(
            "non-Transaction data on transaction directive: {:?}",
            txn.data
        );
    };
    assert!(
        data.metadata.is_empty(),
        "untagged transaction should have NO metadata added"
    );
}

/// Existing `final` / `roll` metadata is preserved (not overwritten).
/// Pins the `has_final` / `has_roll` precondition checks in the
/// plugin.
#[test]
fn test_rx_txn_preserves_existing_metadata() {
    let plugin = RxTxnPlugin;
    let mut txn = make_transaction_with_tag(
        "2024-01-15",
        "Recurring with explicit metadata",
        vec!["rx_txn"],
        vec![
            ("Expenses:Rent", "1000", "USD"),
            ("Assets:Cash", "-1000", "USD"),
        ],
    );
    if let DirectiveData::Transaction(ref mut data) = txn.data {
        data.metadata.push((
            "final".to_string(),
            MetaValueData::String("2024-12-31".to_string()),
        ));
        data.metadata.push((
            "roll".to_string(),
            MetaValueData::String("False".to_string()),
        ));
    }
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Expenses:Rent"),
        txn,
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    let DirectiveData::Transaction(data) = &output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction")
        .expect("transaction must be present")
        .data
    else {
        panic!("non-Transaction data on transaction directive");
    };
    assert_eq!(
        data.metadata.len(),
        2,
        "existing metadata preserved, no defaults added (got {} entries)",
        data.metadata.len()
    );
    let final_val = data
        .metadata
        .iter()
        .find(|(k, _)| k == "final")
        .map(|(_, v)| v);
    if let Some(MetaValueData::String(v)) = final_val {
        assert_eq!(v, "2024-12-31", "existing 'final' value preserved");
    } else {
        panic!("'final' metadata should remain as '2024-12-31'");
    }
    // Also pin `roll` — if the plugin overwrote `roll` while leaving
    // `final` intact, the count check above would still pass (both
    // keys still present, length 2), so we have to assert the value.
    let roll_val = data
        .metadata
        .iter()
        .find(|(k, _)| k == "roll")
        .map(|(_, v)| v);
    if let Some(MetaValueData::String(v)) = roll_val {
        assert_eq!(
            v, "False",
            "existing 'roll' value preserved (not overwritten)"
        );
    } else {
        panic!("'roll' metadata should remain as 'False'");
    }
}

/// Only ONE of `final` / `roll` is set on the input → plugin adds
/// the missing one without touching the existing.
#[test]
fn test_rx_txn_fills_in_missing_metadata_only() {
    let plugin = RxTxnPlugin;
    let mut txn = make_transaction_with_tag(
        "2024-01-15",
        "Half-configured rx",
        vec!["rx_txn"],
        vec![
            ("Expenses:Rent", "1000", "USD"),
            ("Assets:Cash", "-1000", "USD"),
        ],
    );
    if let DirectiveData::Transaction(ref mut data) = txn.data {
        // Only `final` is pre-set; `roll` should still get defaulted.
        data.metadata.push((
            "final".to_string(),
            MetaValueData::String("2024-12-31".to_string()),
        ));
    }
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Expenses:Rent"),
        txn,
    ]);
    let output = process_and_materialize(&plugin, input);
    let DirectiveData::Transaction(data) = &output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction")
        .expect("transaction must be present")
        .data
    else {
        panic!("non-Transaction data on transaction directive");
    };
    assert_eq!(
        data.metadata.len(),
        2,
        "got existing 'final' + defaulted 'roll'"
    );

    let final_val = data
        .metadata
        .iter()
        .find(|(k, _)| k == "final")
        .map(|(_, v)| v);
    if let Some(MetaValueData::String(v)) = final_val {
        assert_eq!(v, "2024-12-31", "pre-existing 'final' is untouched");
    } else {
        panic!("'final' metadata should be a string");
    }

    let roll_val = data
        .metadata
        .iter()
        .find(|(k, _)| k == "roll")
        .map(|(_, v)| v);
    if let Some(MetaValueData::String(v)) = roll_val {
        assert_eq!(v, "True", "missing 'roll' is filled with default");
    } else {
        panic!("'roll' metadata should be a string default");
    }
}

/// `#rx_txn` alongside other tags still triggers the plugin.
#[test]
fn test_rx_txn_works_alongside_other_tags() {
    let plugin = RxTxnPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Expenses:Rent"),
        make_transaction_with_tag(
            "2024-01-15",
            "Mixed tags",
            vec!["rx_txn", "monthly", "essential"],
            vec![
                ("Expenses:Rent", "1000", "USD"),
                ("Assets:Cash", "-1000", "USD"),
            ],
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    let DirectiveData::Transaction(data) = &output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction")
        .expect("transaction must be present")
        .data
    else {
        panic!("non-Transaction data on transaction directive");
    };
    assert!(
        data.metadata.iter().any(|(k, _)| k == "final"),
        "rx_txn applies even when other tags are present (final missing)"
    );
    assert!(
        data.metadata.iter().any(|(k, _)| k == "roll"),
        "rx_txn applies even when other tags are present (roll missing)"
    );
    assert_eq!(data.tags.len(), 3, "all tags preserved");
}

// ============================================================================
// SellGainsPlugin Tests
// ============================================================================
//
// `sellgains` is beancount's: for a transaction whose postings at cost all
// carry a price, the priced value of those postings (`-units × price`) must
// match, per currency and within twice the transaction's tolerance, the
// weight of its Assets/Liabilities/Equity/Expenses postings. Income is left
// out (it is the gain the check lets you elide). The error is beancount's
// message, at the transaction (#2600; rledger's own check only warned when
// a priced sale had no Income or Expenses posting at all).

/// A posting of `number currency` to `account`.
fn sg_posting(account: &str, number: &str, currency: &str) -> PostingData {
    PostingData {
        account: account.to_string(),
        units: Some(AmountData {
            number: number.to_string(),
            currency: currency.to_string(),
        }),
        cost: None,
        price: None,
        flag: None,
        metadata: vec![],
        span: None,
    }
}

/// A posting of `units` held at `cost` USD per unit, priced at `price` USD
/// when given.
fn sg_lot(units: &str, cost: &str, price: Option<&str>) -> PostingData {
    let mut posting = sg_posting("Assets:Stock", units, "AAPL");
    posting.cost = Some(CostData {
        number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
            value: cost.to_string(),
        }),
        currency: Some("USD".to_string()),
        date: None,
        label: None,
        merge: false,
    });
    posting.price = price.map(|p| PriceAnnotationData {
        is_total: false,
        amount: Some(AmountData {
            number: p.to_string(),
            currency: "USD".to_string(),
        }),
        number: None,
        currency: None,
    });
    posting
}

/// A transaction of `postings`, located at `ledger.beancount:10`.
fn sg_txn(postings: Vec<PostingData>) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: "transaction".to_string(),
        date: "2024-06-15".to_string(),
        filename: Some("ledger.beancount".to_string()),
        lineno: Some(10),
        data: DirectiveData::Transaction(TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: "Sell".to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings,
        }),
    }
}

fn sg_messages(postings: Vec<PostingData>) -> Vec<String> {
    let output = process_and_materialize(&SellGainsPlugin, make_input(vec![sg_txn(postings)]));
    output.errors.iter().map(|e| e.message.clone()).collect()
}

/// Proceeds matching the price, the gain posted to Income → nothing.
#[test]
fn test_sell_gains_silent_when_proceeds_match_price() {
    assert!(
        sg_messages(vec![
            sg_lot("-10", "100", Some("150")),
            sg_posting("Assets:Cash", "1500.00", "USD"),
            sg_posting("Income:Gains", "-500.00", "USD"),
        ])
        .is_empty()
    );
}

/// A typo in the proceeds is the error beancount gives, at the
/// transaction: `(1500 USD)` priced against `(1600.00 USD)` received.
#[test]
fn test_sell_gains_reports_proceeds_that_do_not_match_the_price() {
    let output = process_and_materialize(
        &SellGainsPlugin,
        make_input(vec![sg_txn(vec![
            sg_lot("-10", "100", Some("150")),
            sg_posting("Assets:Cash", "1600.00", "USD"),
            sg_posting("Income:Gains", "-600.00", "USD"),
        ])]),
    );
    assert_eq!(output.errors.len(), 1);
    let error = &output.errors[0];
    assert_eq!(
        error.message,
        "Invalid price vs. proceeds/gains: (1500 USD) vs. (1600.00 USD); difference: (-100.00 USD)"
    );
    assert_eq!(error.severity, PluginErrorSeverity::Error);
    assert_eq!(error.source_file.as_deref(), Some("ledger.beancount"));
    assert_eq!(error.line_number, Some(10));
}

/// Fees are Expenses, so they count toward the proceeds.
#[test]
fn test_sell_gains_counts_expenses_toward_proceeds() {
    assert!(
        sg_messages(vec![
            sg_lot("-10", "100", Some("150")),
            sg_posting("Assets:Cash", "1490.00", "USD"),
            sg_posting("Expenses:Fees", "10.00", "USD"),
            sg_posting("Income:Gains", "-500.00", "USD"),
        ])
        .is_empty()
    );
}

/// A lot at cost without a price → the transaction is not checked at all.
#[test]
fn test_sell_gains_skips_a_transaction_with_an_unpriced_lot() {
    assert!(
        sg_messages(vec![
            sg_lot("-10", "100", Some("150")),
            sg_lot("-1", "100", None),
            sg_posting("Assets:Cash", "1.00", "USD"),
            sg_posting("Income:Gains", "-1.00", "USD"),
        ])
        .is_empty()
    );
}

/// Proceeds in a currency the price is not in → reported.
#[test]
fn test_sell_gains_reports_proceeds_in_another_currency() {
    assert_eq!(
        sg_messages(vec![
            sg_lot("-1", "10", Some("13")),
            sg_posting("Assets:Cash", "13", "USD"),
            sg_posting("Assets:Cash", "1", "EUR"),
            sg_posting("Income:Gains", "-1", "EUR"),
            sg_posting("Income:Gains", "-3", "USD"),
        ]),
        ["Invalid price vs. proceeds/gains: (13 USD) vs. (13 USD, 1 EUR); difference: (-1 EUR)"]
    );
}

/// A buy has no price to check against here (its lot has no price).
#[test]
fn test_sell_gains_silent_for_unpriced_buy() {
    assert!(
        sg_messages(vec![
            sg_lot("10", "100", None),
            sg_posting("Assets:Cash", "-1000", "USD"),
        ])
        .is_empty()
    );
}

/// `sg_messages` with the ledger's `options`.
fn sg_messages_with(options: PluginOptions, postings: Vec<PostingData>) -> Vec<String> {
    let mut input = make_input(vec![sg_txn(postings)]);
    input.options = options;
    let output = process_and_materialize(&SellGainsPlugin, input);
    output.errors.iter().map(|e| e.message.clone()).collect()
}

/// The ledger's tolerance options decide the tolerance, as in beancount
/// (#2653): proceeds 4 cents off fail on the defaults (twice 0.005) and
/// pass with `tolerance_multiplier` 5, with `inferred_tolerance_default`
/// `USD:0.05`, or with `infer_tolerance_from_cost` on units written to one
/// place (bean-check agrees on all four). Plugins used to get beancount's
/// default options whatever the ledger set.
#[test]
fn test_sell_gains_uses_the_ledgers_tolerance_options() {
    let postings = |units: &str| {
        vec![
            sg_lot(units, "100", Some("150")),
            sg_posting("Assets:Cash", "300.04", "USD"),
            sg_posting("Income:Gains", "-100.04", "USD"),
        ]
    };
    let off =
        ["Invalid price vs. proceeds/gains: (300 USD) vs. (300.04 USD); difference: (-0.04 USD)"];
    assert_eq!(
        sg_messages_with(PluginOptions::default(), postings("-2")),
        off
    );
    assert_eq!(
        sg_messages_with(PluginOptions::default(), postings("-2.0")),
        ["Invalid price vs. proceeds/gains: (300.0 USD) vs. (300.04 USD); difference: (-0.04 USD)"]
    );
    for (what, options, units) in [
        (
            "tolerance_multiplier",
            PluginOptions {
                tolerance_multiplier: "5".to_string(),
                ..Default::default()
            },
            "-2",
        ),
        (
            "inferred_tolerance_default",
            PluginOptions {
                inferred_tolerance_default: vec![("USD".to_string(), "0.05".to_string())],
                ..Default::default()
            },
            "-2",
        ),
        (
            "infer_tolerance_from_cost",
            PluginOptions {
                infer_tolerance_from_cost: true,
                ..Default::default()
            },
            "-2.0",
        ),
    ] {
        assert!(
            sg_messages_with(options, postings(units)).is_empty(),
            "{what} must widen the tolerance"
        );
    }
}

/// A posting booking interpolated is left out of the tolerance, as in
/// beancount (#2653): cash booking computed as `40.0` gives no slack, so
/// 39.99 priced against 40.0 received fails, while the same `40.0` written
/// by hand allows 0.1 and passes (bean-check agrees on both).
#[test]
fn test_sell_gains_leaves_an_interpolated_posting_out_of_the_tolerance() {
    let postings = |interpolated: bool| {
        let mut cash = sg_posting("Assets:Cash", "40.0", "USD");
        if interpolated {
            cash.metadata.push((
                rustledger_plugin_types::AUTOMATIC_META.to_string(),
                MetaValueData::Bool(true),
            ));
        }
        vec![
            sg_lot("-3", "10.0", Some("13.33")),
            cash,
            sg_posting("Income:Gains", "-10", "USD"),
        ]
    };
    assert!(sg_messages(postings(false)).is_empty());
    assert_eq!(
        sg_messages(postings(true)),
        ["Invalid price vs. proceeds/gains: (39.99 USD) vs. (40.0 USD); difference: (-0.01 USD)"]
    );
}

proptest::proptest! {
    #![proptest_config(proptest::prelude::ProptestConfig::with_cases(64))]

    /// Proceeds off by `delta` cents from `units × price`: an error iff
    /// `|delta|` exceeds twice the tolerance the cash posting's two decimal
    /// places give (2 × 0.005 USD = 1 cent).
    #[test]
    fn prop_sell_gains_reports_iff_proceeds_miss_price_beyond_tolerance(
        units in 1u32..1000,
        cost_cents in 1u32..1_000_000,
        sale_cents in 1u32..1_000_000,
        delta_cents in -300i64..300,
    ) {
        use rust_decimal::Decimal;
        let sale = Decimal::new(i64::from(sale_cents), 2);
        let cost = Decimal::new(i64::from(cost_cents), 2);
        let units_d = Decimal::from(units);
        let cash = units_d * sale + Decimal::new(delta_cents, 2);
        let gain = units_d * cost - cash;
        let messages = sg_messages(vec![
            sg_lot(&format!("-{units}"), &cost.to_string(), Some(&sale.to_string())),
            sg_posting("Assets:Cash", &cash.to_string(), "USD"),
            sg_posting("Income:Gains", &gain.to_string(), "USD"),
        ]);
        proptest::prop_assert_eq!(messages.len(), usize::from(delta_cents.abs() > 1), "{:?}", messages);
    }
}

// ============================================================================
// CheckDrainedPlugin Tests
// ============================================================================

#[test]
fn test_check_drained_adds_balance_assertions_on_close() {
    let plugin = CheckDrainedPlugin;
    let input = make_input(vec![
        make_open_with_currencies("2024-01-01", "Assets:Bank", vec!["USD"]),
        make_transaction(
            "2024-06-15",
            "Deposit",
            vec![
                ("Assets:Bank", "100", "USD"),
                ("Income:Salary", "-100", "USD"),
            ],
        ),
        make_close("2024-12-31", "Assets:Bank"),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    // Should have added a balance assertion per (closed account,
    // currency). Here: one Close on Assets:Bank (USD only) → 1 balance.
    assert_eq!(
        output
            .directives
            .iter()
            .filter(|d| d.directive_type == "balance")
            .count(),
        1,
        "exactly one balance assertion for the single closed account+currency"
    );
}

// ============================================================================
// CommodityAttrPlugin Tests
// ============================================================================

#[test]
fn test_commodity_attr_ok_with_no_config() {
    let plugin = CommodityAttrPlugin::new();
    let input = make_input(vec![make_commodity("2024-01-01", "USD")]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
}

#[test]
fn test_commodity_attr_error_with_missing_required_attr() {
    let plugin = CommodityAttrPlugin::new();
    let input =
        make_input_with_config(vec![make_commodity("2024-01-01", "AAPL")], "{'name': null}");
    let output = process_and_materialize(&plugin, input);
    assert_eq!(
        output.errors.len(),
        1,
        "exactly one error for the single commodity missing required 'name'"
    );
}

// ============================================================================
// CurrencyAccountsPlugin Tests
// ============================================================================

#[test]
fn test_currency_accounts_single_currency_no_change() {
    let plugin = CurrencyAccountsPlugin::new();
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Expenses:Food"),
        make_transaction(
            "2024-01-15",
            "Lunch",
            vec![
                ("Expenses:Food", "25", "USD"),
                ("Assets:Cash", "-25", "USD"),
            ],
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    // Single-currency transaction should not add currency account postings
    let txn = output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction")
        .unwrap();
    if let DirectiveData::Transaction(data) = &txn.data {
        assert_eq!(
            data.postings.len(),
            2,
            "single-currency transaction should not gain extra postings"
        );
    }
}

// ============================================================================
// EffectiveDatePlugin Tests
// ============================================================================
//
// `effective_date` finds postings with `effective_date` metadata and
// rewrites the transaction into:
//   1. The original txn (modified) where the posting goes through a
//      holding account on the entry date.
//   2. A NEW txn at the effective date that moves from the holding
//      account to the original target account.
//   3. Open directives for the new holding accounts.
//
// Default config maps `Expenses:` and `Income:` prefixes to default
// holding accounts. Other prefixes need a custom config or the
// posting passes through unchanged.

/// Helper: make a transaction with a single posting tagged with an
/// `effective_date`. The `target_account` can be any account
/// (Expenses, Income, Liabilities, etc.) — the plugin's behavior
/// depends on whether the prefix matches the configured holding-
/// account map. Used by several tests below.
fn make_txn_with_effective_date(
    entry_date: &str,
    effective_date: &str,
    target_account: &str,
) -> DirectiveWrapper {
    let mut txn = make_transaction(
        entry_date,
        "Deferred",
        vec![(target_account, "25", "USD"), ("Assets:Cash", "-25", "USD")],
    );
    if let DirectiveData::Transaction(ref mut data) = txn.data {
        data.postings[0].metadata.push((
            "effective_date".to_string(),
            MetaValueData::Date(effective_date.to_string()),
        ));
    }
    txn
}

/// No `effective_date` metadata anywhere → directives pass through
/// unchanged (count and content). Pins the
/// `has_effective_date_posting → false` filter.
#[test]
fn test_effective_date_no_metadata_passthrough() {
    let plugin = EffectiveDatePlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Expenses:Food"),
        make_transaction(
            "2024-01-15",
            "No effective date",
            vec![
                ("Expenses:Food", "25", "USD"),
                ("Assets:Cash", "-25", "USD"),
            ],
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    assert_eq!(output.directives.len(), 3);
}

/// Effective date in the FUTURE (later than entry) → uses the
/// 'later' holding account. For Expenses in the default config
/// that's `Assets:Hold:Expenses`.
#[test]
fn test_effective_date_future_uses_later_holding_account() {
    let plugin = EffectiveDatePlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Expenses:Food"),
        make_txn_with_effective_date("2024-01-15", "2024-02-15", "Expenses:Food"),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());

    // Should emit an Open directive for `Assets:Hold:Expenses:Food`.
    let opens: Vec<_> = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "open")
        .collect();
    let new_open = opens.iter().find(|d| {
        if let DirectiveData::Open(o) = &d.data {
            o.account == "Assets:Hold:Expenses:Food"
        } else {
            false
        }
    });
    assert!(
        new_open.is_some(),
        "future effective_date should generate Open for 'later' holding (Assets:Hold:Expenses:Food); \
         got opens: {:?}",
        opens
            .iter()
            .filter_map(|d| {
                if let DirectiveData::Open(o) = &d.data {
                    Some(&o.account)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>()
    );

    // And there must be a transaction at the effective date.
    let effective_txns: Vec<_> = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "transaction" && d.date == "2024-02-15")
        .collect();
    assert_eq!(
        effective_txns.len(),
        1,
        "exactly one new transaction at the effective date"
    );

    // The effective-date txn's hold posting must be the SIGN-FLIPPED
    // version of the original target posting. The plugin's
    // `create_opposite_posting` is what produces this; if it ever
    // becomes a copy instead of a negate, the new transaction would
    // be unbalanced and the test below would catch it.
    let DirectiveData::Transaction(eff_data) = &effective_txns[0].data else {
        panic!("effective-date directive has non-Transaction data");
    };
    let hold_posting = eff_data
        .postings
        .iter()
        .find(|p| p.account == "Assets:Hold:Expenses:Food")
        .expect("effective-date txn must have a hold posting");
    let hold_units = hold_posting.units.as_ref().expect("hold has units");
    assert_eq!(
        hold_units.number, "-25",
        "hold posting must be sign-flipped from the original (+25 → -25)"
    );
    assert_eq!(hold_units.currency, "USD");

    // Both transactions (original-on-entry-date and the new
    // effective-date txn) must share a link tying them together.
    // Plugin generates this in `generate_link()` and pushes onto
    // the original + sets it on the new one.
    let original_txn = output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction" && d.date == "2024-01-15")
        .expect("original transaction must remain");
    let DirectiveData::Transaction(orig_data) = &original_txn.data else {
        panic!("original directive has non-Transaction data");
    };
    assert_eq!(
        orig_data.links.len(),
        1,
        "plugin should attach exactly one link to the original txn"
    );
    assert_eq!(
        eff_data.links.len(),
        1,
        "plugin should attach exactly one link to the effective-date txn"
    );
    assert_eq!(
        orig_data.links[0], eff_data.links[0],
        "the same link should appear on both transactions"
    );
    assert!(
        orig_data.links[0].starts_with("edate-"),
        "link should follow the `edate-<date>-<id>` shape; got '{}'",
        orig_data.links[0]
    );
}

/// Effective date in the PAST (earlier than entry) → uses the
/// 'earlier' holding account. For Expenses that's
/// `Liabilities:Hold:Expenses`.
#[test]
fn test_effective_date_past_uses_earlier_holding_account() {
    let plugin = EffectiveDatePlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Expenses:Food"),
        make_txn_with_effective_date("2024-02-15", "2024-01-15", "Expenses:Food"),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());

    let opens: Vec<_> = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "open")
        .collect();
    let new_open = opens.iter().find(|d| {
        if let DirectiveData::Open(o) = &d.data {
            o.account == "Liabilities:Hold:Expenses:Food"
        } else {
            false
        }
    });
    assert!(
        new_open.is_some(),
        "past effective_date should generate Open for 'earlier' holding (Liabilities:Hold:Expenses:Food)"
    );

    assert_eq!(
        output
            .directives
            .iter()
            .filter(|d| d.directive_type == "transaction" && d.date == "2024-01-15")
            .count(),
        1
    );
}

/// Account prefix not in the default config (e.g. `Liabilities:`): the
/// posting cannot be moved, so it is reported, naming the account, and the
/// whole transaction stays as written. It used to be kept silently, while
/// any sibling posting the config did cover was moved.
#[test]
fn test_effective_date_unconfigured_prefix_is_reported_and_entry_kept() {
    let plugin = EffectiveDatePlugin;
    let mut txn =
        make_txn_with_effective_date("2024-01-15", "2024-02-15", "Liabilities:CreditCard");
    // A sibling the default config does cover: it must not move either.
    if let DirectiveData::Transaction(ref mut data) = txn.data {
        let mut food = data.postings[1].clone();
        food.account = "Expenses:Food".to_string();
        food.metadata.push((
            "effective_date".to_string(),
            MetaValueData::Date("2024-02-15".to_string()),
        ));
        data.postings.push(food);
    }
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Liabilities:CreditCard"),
        make_open("2024-01-01", "Expenses:Food"),
        txn.clone(),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(output.errors.len(), 1, "{:?}", output.errors);
    assert!(
        output.errors[0].message.contains("Liabilities:CreditCard"),
        "{}",
        output.errors[0].message
    );

    // The transaction is exactly as written; nothing new was made.
    assert!(
        output.directives.contains(&txn),
        "the entry must be left as written"
    );
    assert!(
        !output.directives.iter().any(|d| {
            d.directive_type == "open"
                && matches!(
                    &d.data,
                    DirectiveData::Open(o) if o.account.contains(":Hold:")
                )
        }),
        "nothing moved, so no holding-account Opens"
    );
    assert_eq!(
        output
            .directives
            .iter()
            .filter(|d| d.directive_type == "transaction" && d.date == "2024-02-15")
            .count(),
        0,
        "nothing moved, so no effective-date transaction"
    );
}

/// Custom config with a different prefix mapping → that prefix is
/// honored instead of the defaults. Pins the config-parse branch.
#[test]
fn test_effective_date_custom_config_remaps_prefix() {
    let plugin = EffectiveDatePlugin;
    let input = make_input_with_config(
        vec![
            make_open("2024-01-01", "Assets:Cash"),
            make_open("2024-01-01", "Liabilities:Pay"),
            make_txn_with_effective_date("2024-01-15", "2024-02-15", "Liabilities:Pay"),
        ],
        "{'Liabilities': {'earlier': 'Assets:Hold:Liab', 'later': 'Liabilities:Hold:Liab'}}",
    );
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());

    // (a) An Open for the remapped holding account is emitted.
    assert!(
        output.directives.iter().any(|d| matches!(
            &d.data,
            DirectiveData::Open(o) if o.account.starts_with("Liabilities:Hold:Liab")
        )),
        "custom config should map Liabilities: → Liabilities:Hold:Liab"
    );

    // (b) Exactly one effective-date transaction is spawned.
    let effective_txns: Vec<_> = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "transaction" && d.date == "2024-02-15")
        .collect();
    assert_eq!(
        effective_txns.len(),
        1,
        "custom config should spawn exactly one effective-date transaction"
    );

    // (c) That transaction's postings reference the remapped holding
    //     account, not the original account or the default mapping.
    let DirectiveData::Transaction(eff_data) = &effective_txns[0].data else {
        panic!(
            "effective-date directive has non-Transaction data: {:?}",
            effective_txns[0].data
        );
    };
    assert!(
        eff_data
            .postings
            .iter()
            .any(|p| p.account.starts_with("Liabilities:Hold:Liab")),
        "effective-date txn should post to the remapped 'later' holding account; got: {:?}",
        eff_data
            .postings
            .iter()
            .map(|p| &p.account)
            .collect::<Vec<_>>()
    );
}

// ============================================================================
// ForecastPlugin Tests
// ============================================================================
//
// `forecast` finds transactions with `flag == "#"` and a recurrence
// pattern `[INTERVAL [SKIP n TIMES] [REPEAT n TIMES] [UNTIL yyyy-mm-dd]]`
// in the narration, then replicates the transaction at each
// generated date with the bracketed pattern stripped.
//
// Plugin-internal unit tests (`forecast.rs::tests`) already cover
// the date-arithmetic branches (monthly/weekly/until/skip). These
// integration tests pin the end-to-end behavior with the actual
// integration-test fixture helpers.

/// Build a forecast (#-flagged) transaction inline. The integration
/// test helpers don't cover #-flag transactions, so this builder is
/// local to the forecast section.
fn make_forecast_txn(date: &str, narration: &str) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: "transaction".to_string(),
        date: date.to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Transaction(TransactionData {
            flag: "#".to_string(),
            payee: None,
            narration: narration.to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![
                PostingData {
                    account: "Expenses:Rent".to_string(),
                    units: Some(AmountData {
                        number: "1000".to_string(),
                        currency: "USD".to_string(),
                    }),
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
                PostingData {
                    account: "Assets:Cash".to_string(),
                    units: Some(AmountData {
                        number: "-1000".to_string(),
                        currency: "USD".to_string(),
                    }),
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
            ],
        }),
    }
}

/// `*`-flagged transactions are not forecast templates and pass
/// through untouched. Pins the `flag == "#"` filter.
#[test]
fn test_forecast_no_forecast_flag_passthrough() {
    let plugin = ForecastPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Expenses:Rent"),
        make_transaction(
            "2024-01-15",
            "Regular rent",
            vec![
                ("Expenses:Rent", "1000", "USD"),
                ("Assets:Cash", "-1000", "USD"),
            ],
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    assert_eq!(output.directives.len(), 3);
}

/// `[MONTHLY REPEAT 3 TIMES]` → exactly 3 dated copies, monthly
/// stride. Strict count was previously `>= 3` (a weak-count shape
/// the lint should catch on multi-line — see follow-up note in PR).
#[test]
fn test_forecast_monthly_repeat_emits_exactly_n_transactions() {
    let plugin = ForecastPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Expenses:Rent"),
        make_forecast_txn("2024-01-15", "Rent [MONTHLY REPEAT 3 TIMES]"),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    let txns: Vec<_> = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "transaction")
        .collect();
    assert_eq!(txns.len(), 3, "MONTHLY REPEAT 3 TIMES emits exactly 3 txns");
    let dates: Vec<&str> = txns.iter().map(|t| t.date.as_str()).collect();
    assert_eq!(dates, vec!["2024-01-15", "2024-02-15", "2024-03-15"]);
    // Each emitted transaction must preserve the original postings
    // verbatim (account/units/cost/price/flag/metadata) and have the
    // bracketed pattern stripped from the narration. A bug that
    // dropped or mangled postings while replicating dates would
    // otherwise pass the count+dates checks above.
    for txn in &txns {
        let DirectiveData::Transaction(data) = &txn.data else {
            panic!("transaction directive_type with non-Transaction data");
        };
        assert_eq!(
            data.narration, "Rent",
            "bracketed pattern should be stripped from narration"
        );
        assert_eq!(data.flag, "#", "forecast flag preserved across replication");
        assert_eq!(
            data.postings.len(),
            2,
            "original posting count preserved (Expenses:Rent + Assets:Cash)"
        );
        assert_eq!(data.postings[0].account, "Expenses:Rent");
        let units_0 = data.postings[0]
            .units
            .as_ref()
            .expect("first posting has units");
        assert_eq!(units_0.number, "1000");
        assert_eq!(units_0.currency, "USD");
        assert_eq!(data.postings[1].account, "Assets:Cash");
        let units_1 = data.postings[1]
            .units
            .as_ref()
            .expect("second posting has units");
        assert_eq!(units_1.number, "-1000");
        assert_eq!(units_1.currency, "USD");
    }
}

/// `[WEEKLY REPEAT 4 TIMES]` → 4 dates 7 days apart.
#[test]
fn test_forecast_weekly_repeat() {
    let plugin = ForecastPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Expenses:Rent"),
        make_forecast_txn("2024-01-01", "Groceries [WEEKLY REPEAT 4 TIMES]"),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    let txns: Vec<_> = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "transaction")
        .collect();
    assert_eq!(txns.len(), 4);
    let dates: Vec<&str> = txns.iter().map(|t| t.date.as_str()).collect();
    assert_eq!(
        dates,
        vec!["2024-01-01", "2024-01-08", "2024-01-15", "2024-01-22"]
    );
}

/// `[DAILY REPEAT 5 TIMES]` → 5 consecutive days.
#[test]
fn test_forecast_daily_repeat() {
    let plugin = ForecastPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Expenses:Rent"),
        make_forecast_txn("2024-01-15", "Coffee [DAILY REPEAT 5 TIMES]"),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    let txns: Vec<_> = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "transaction")
        .collect();
    assert_eq!(txns.len(), 5);
    let dates: Vec<&str> = txns.iter().map(|t| t.date.as_str()).collect();
    assert_eq!(
        dates,
        vec![
            "2024-01-15",
            "2024-01-16",
            "2024-01-17",
            "2024-01-18",
            "2024-01-19",
        ]
    );
}

/// `[MONTHLY UNTIL 2024-04-15]` → all dates from start through end
/// inclusive. Pins the until-date inclusive boundary.
#[test]
fn test_forecast_monthly_until_inclusive() {
    let plugin = ForecastPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Expenses:Rent"),
        make_forecast_txn("2024-01-15", "Rent [MONTHLY UNTIL 2024-04-15]"),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    let txns: Vec<_> = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "transaction")
        .collect();
    assert_eq!(txns.len(), 4, "until is inclusive: Jan, Feb, Mar, Apr");
    let dates: Vec<&str> = txns.iter().map(|t| t.date.as_str()).collect();
    assert_eq!(
        dates,
        vec!["2024-01-15", "2024-02-15", "2024-03-15", "2024-04-15"]
    );
}

/// `[MONTHLY SKIP 1 TIME REPEAT 3 TIMES]` → bi-monthly (every 2nd
/// month). SKIP n TIMES means stride = n+1.
#[test]
fn test_forecast_skip_increases_stride() {
    let plugin = ForecastPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Expenses:Rent"),
        make_forecast_txn(
            "2024-01-01",
            "Quarterly insurance [MONTHLY SKIP 1 TIME REPEAT 3 TIMES]",
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    let txns: Vec<_> = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "transaction")
        .collect();
    assert_eq!(txns.len(), 3);
    let dates: Vec<&str> = txns.iter().map(|t| t.date.as_str()).collect();
    assert_eq!(
        dates,
        vec!["2024-01-01", "2024-03-01", "2024-05-01"],
        "SKIP 1 TIME = bi-monthly stride"
    );
}

/// `#`-flagged transaction without a recurrence pattern → kept as
/// a single-instance `#` transaction (no expansion). Pins the
/// no-match path.
#[test]
fn test_forecast_no_pattern_in_narration_kept_unchanged() {
    let plugin = ForecastPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Expenses:Rent"),
        make_forecast_txn("2024-01-15", "Forecast with no recurrence pattern"),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    let txns: Vec<_> = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "transaction")
        .collect();
    assert_eq!(
        txns.len(),
        1,
        "no recurrence pattern in narration → no expansion"
    );
    assert_eq!(txns[0].date, "2024-01-15");
}

// ============================================================================
// GenerateBaseCcyPricesPlugin Tests
// ============================================================================
//
// `generate_base_ccy_prices` reads existing price directives, looks for
// chains where a `(C, X)` price exists alongside an `(X, base)` price,
// and emits a derived `(C, base) = (C, X) * (X, base)` entry. The
// plugin name (and config) provides the base currency.
//
// Matrix below covers: passthrough w/o config, simple chain,
// duplicate-target suppression, base-currency short-circuit. Plus a
// proptest pinning the multiplicative invariant.

/// No config → plugin returns input unchanged. Pins the early-return
/// when no base currency is configured.
#[test]
fn test_generate_base_ccy_prices_no_config_passthrough() {
    let plugin = GenerateBaseCcyPricesPlugin;
    let input = make_input(vec![
        make_price("2024-01-01", "EUR", "1.10", "USD"),
        make_price("2024-01-01", "ETH", "2000", "EUR"),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    let price_count = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "price")
        .count();
    assert_eq!(
        price_count, 2,
        "no config → input passes through with no derived prices"
    );
}

/// Two-leg chain: ETH→EUR + EUR→USD → emit ETH→USD = 2000 * 1.10 = 2200.
/// Strict assertions on count, currency, and computed amount.
#[test]
fn test_generate_base_ccy_prices_emits_derived_chain() {
    let plugin = GenerateBaseCcyPricesPlugin;
    let input = make_input_with_config(
        vec![
            make_price("2024-01-01", "EUR", "1.10", "USD"),
            make_price("2024-01-01", "ETH", "2000", "EUR"),
        ],
        "USD",
    );
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());

    // Exactly 3 prices: 2 originals + 1 derived.
    let prices: Vec<_> = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "price")
        .collect();
    assert_eq!(
        prices.len(),
        3,
        "input prices + exactly one derived ETH→USD"
    );

    // Find the derived ETH→USD entry and pin its amount.
    let derived = prices
        .iter()
        .find_map(|d| match &d.data {
            DirectiveData::Price(p) if p.currency == "ETH" && p.amount.currency == "USD" => Some(p),
            _ => None,
        })
        .expect("derived ETH→USD price must be emitted");
    assert_eq!(
        derived.amount.number, "2200",
        "derived = 2000 EUR * 1.10 USD/EUR = 2200 USD"
    );
}

/// Only the INVERSE pair is declared — upstream's `issue122` fixture.
///
/// ```beancount
/// plugin "tariochbctools.plugins.generate_base_ccy_prices" "EUR"
/// 2020-01-01 price USD  10 TUG
/// 2020-01-01 price EUR 100 TUG
/// ```
///
/// To express `USD 10 TUG` in EUR the plugin needs TUG→EUR, and the ledger
/// declares only EUR→TUG. beancount finds it because `build_price_map`
/// inserts `(quote, base) = ONE / price` for every forward pair; rledger
/// looked up one direction and silently emitted nothing (#1980) — no error,
/// just a price missing from what every market valuation then reads.
///
/// Upstream's expected output is `price USD 0.10 EUR`, and the arithmetic is
/// beancount's: invert (1/100 = 0.01), then multiply (10 * 0.01).
#[test]
fn test_generate_base_ccy_prices_uses_an_inverse_rate() {
    let plugin = GenerateBaseCcyPricesPlugin;
    let input = make_input_with_config(
        vec![
            make_price("2020-01-01", "USD", "10", "TUG"),
            make_price("2020-01-01", "EUR", "100", "TUG"),
        ],
        "EUR",
    );
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty(), "{:?}", output.errors);

    let prices: Vec<_> = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "price")
        .collect();
    assert_eq!(
        prices.len(),
        3,
        "two inputs plus the derived USD->EUR; 2 means the inverse rate was \
         not found and the entry was silently skipped",
    );

    let derived = prices
        .iter()
        .find_map(|d| match &d.data {
            DirectiveData::Price(p) if p.currency == "USD" && p.amount.currency == "EUR" => Some(p),
            _ => None,
        })
        .expect("derived USD->EUR price must be emitted");
    // Upstream renders `0.10`; this plugin's `format_decimal` trims trailing
    // zeros, so the string is `0.1`. Assert the VALUE, which is what the
    // fixture is about — and what the compat oracle compares, since
    // `_num_agrees` quantizes before comparing. Pinning the string here would
    // be pinning a formatting choice that has nothing to do with #1980.
    assert_eq!(
        derived
            .amount
            .number
            .parse::<rust_decimal::Decimal>()
            .unwrap(),
        "0.10".parse::<rust_decimal::Decimal>().unwrap(),
        "10 TUG * (1/100 EUR/TUG) = 0.10 EUR, matching upstream's fixture; \
         got {}",
        derived.amount.number,
    );
}

/// A ZERO reverse rate yields no derived price, and does not panic.
///
/// Zero prices are legitimate — a gifted option books at zero cost — so the
/// inverse fallback meets them, and `1/0` has no answer. Review asked for
/// coverage of the zero branch; the branch turned out to be redundant, because
/// `Decimal::checked_div` already returns `None` for a zero divisor, so an
/// explicit `is_zero()` test ahead of it could never change the outcome. It was
/// removed rather than tested.
///
/// This pins the BEHAVIOR instead, which is not redundant: switching to bare
/// `Decimal::ONE / rate` would panic on this input rather than skip the entry.
#[test]
fn test_generate_base_ccy_prices_skips_a_zero_inverse_rate() {
    let plugin = GenerateBaseCcyPricesPlugin;
    let input = make_input_with_config(
        vec![
            make_price("2020-01-01", "USD", "10", "TUG"),
            make_price("2020-01-01", "EUR", "0", "TUG"),
        ],
        "EUR",
    );
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty(), "{:?}", output.errors);

    let prices: Vec<_> = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "price")
        .collect();
    assert_eq!(
        prices.len(),
        2,
        "a zero reverse rate has no reciprocal, so no USD->EUR price can be \
         derived; the two inputs must pass through unchanged",
    );
    assert!(
        !prices.iter().any(|d| matches!(&d.data,
            DirectiveData::Price(p) if p.currency == "USD" && p.amount.currency == "EUR")),
        "no derived USD->EUR price may be emitted from a zero rate",
    );
}

/// A DECLARED direction must win over the inverse of the other.
///
/// With both `A -> B` and `B -> A` on the books, the rate the ledger wrote is
/// the rate to use; falling through to a reciprocal would silently prefer
/// derived data over stated data. Rates chosen so the two disagree — a
/// reciprocal of 0.5 is 2, not 3 — otherwise the test cannot tell them apart.
#[test]
fn test_generate_base_ccy_prices_prefers_a_declared_rate_over_an_inverse() {
    let plugin = GenerateBaseCcyPricesPlugin;
    let input = make_input_with_config(
        vec![
            make_price("2020-01-01", "TUG", "3", "EUR"),
            make_price("2020-01-01", "EUR", "0.5", "TUG"),
            make_price("2020-01-01", "USD", "10", "TUG"),
        ],
        "EUR",
    );
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty(), "{:?}", output.errors);

    let derived = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "price")
        .find_map(|d| match &d.data {
            DirectiveData::Price(p) if p.currency == "USD" && p.amount.currency == "EUR" => Some(p),
            _ => None,
        })
        .expect("derived USD->EUR price must be emitted");
    assert_eq!(
        derived.amount.number, "30",
        "10 TUG * 3 EUR/TUG (DECLARED) = 30; the inverse of EUR 0.5 TUG would \
         give 20 and would mean derived data beat stated data",
    );
}

/// Target price already exists (ETH→USD already given) → plugin
/// must NOT emit a duplicate. Pins the `already_existing_price`
/// short-circuit.
#[test]
fn test_generate_base_ccy_prices_skips_when_target_already_exists() {
    let plugin = GenerateBaseCcyPricesPlugin;
    let input = make_input_with_config(
        vec![
            make_price("2024-01-01", "EUR", "1.10", "USD"),
            make_price("2024-01-01", "ETH", "2000", "EUR"),
            // Pre-existing ETH→USD; plugin must not duplicate.
            make_price("2024-01-01", "ETH", "1900", "USD"),
        ],
        "USD",
    );
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());

    let eth_usd_prices: Vec<_> = output
        .directives
        .iter()
        .filter_map(|d| match &d.data {
            DirectiveData::Price(p) if p.currency == "ETH" && p.amount.currency == "USD" => Some(p),
            _ => None,
        })
        .collect();
    assert_eq!(
        eth_usd_prices.len(),
        1,
        "pre-existing ETH→USD suppresses derivation (no duplicate)"
    );
    assert_eq!(
        eth_usd_prices[0].amount.number, "1900",
        "pre-existing price preserved verbatim, NOT replaced by 2200"
    );
}

/// Price already in the base currency (EUR→USD when base is USD) →
/// plugin skips because the price is already in the target form.
#[test]
fn test_generate_base_ccy_prices_skips_prices_already_in_base() {
    let plugin = GenerateBaseCcyPricesPlugin;
    let input = make_input_with_config(
        vec![
            // Both prices are quoted in USD already; nothing to derive.
            make_price("2024-01-01", "EUR", "1.10", "USD"),
            make_price("2024-01-01", "GBP", "1.30", "USD"),
        ],
        "USD",
    );
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    let price_count = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "price")
        .count();
    assert_eq!(
        price_count, 2,
        "no derivation when all prices are already in base currency"
    );
}

// Property test: when a chain (C→X, X→base) exists, the derived
// (C→base) price equals exact `(C→X rate) * (X→base rate)`. Pre-fix
// the lone integration test only checked `price_count > 2` — a
// rounding bug in the multiplication would still pass.
proptest::proptest! {
    #![proptest_config(proptest::prelude::ProptestConfig::with_cases(64))]

    #[test]
    fn prop_generate_base_ccy_prices_multiplies_chain_exactly(
        // Both rates in cents (any rate from $0.01 to $100,000).
        c_to_x_cents in 1u32..10_000_000,
        x_to_base_cents in 1u32..10_000_000,
    ) {
        use rust_decimal::Decimal;

        let to_dollars = |cents: u32| Decimal::new(i64::from(cents), 2);
        let c_x = to_dollars(c_to_x_cents);
        let x_b = to_dollars(x_to_base_cents);
        let expected = c_x * x_b;

        let plugin = GenerateBaseCcyPricesPlugin;
        let input = make_input_with_config(
            vec![
                make_price("2024-01-01", "X", &x_b.to_string(), "USD"),
                make_price("2024-01-01", "C", &c_x.to_string(), "X"),
            ],
            "USD",
        );
        let output = process_and_materialize(&plugin, input);
        proptest::prop_assert!(output.errors.is_empty());

        let derived = output
            .directives
            .iter()
            .find_map(|d| match &d.data {
                DirectiveData::Price(p)
                    if p.currency == "C" && p.amount.currency == "USD" =>
                {
                    Some(p)
                }
                _ => None,
            });
        proptest::prop_assert!(derived.is_some(), "derived C→USD must be emitted");
        let derived = derived.unwrap();
        let got: Decimal = derived.amount.number.parse().expect("derived parses");
        proptest::prop_assert_eq!(
            got, expected,
            "derived rate must equal C→X * X→base exactly; got {} expected {}",
            got, expected
        );
    }
}

// ============================================================================
// RenameAccountsPlugin Tests
// ============================================================================

#[test]
fn test_rename_accounts_renames_in_transaction() {
    let plugin = RenameAccountsPlugin;
    let input = make_input_with_config(
        vec![
            make_open("2024-01-01", "Expenses:OldName"),
            make_open("2024-01-01", "Assets:Cash"),
            make_transaction(
                "2024-01-15",
                "Test",
                vec![
                    ("Expenses:OldName", "25", "USD"),
                    ("Assets:Cash", "-25", "USD"),
                ],
            ),
        ],
        "{'Expenses:OldName': 'Expenses:NewName'}",
    );
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    // Check that account was renamed
    let has_new_name = output.directives.iter().any(|d| {
        if let DirectiveData::Transaction(txn) = &d.data {
            txn.postings.iter().any(|p| p.account == "Expenses:NewName")
        } else {
            false
        }
    });
    assert!(has_new_name, "should rename account to Expenses:NewName");
}

// ============================================================================
// SplitExpensesPlugin Tests
// ============================================================================
//
// `split_expenses` reads a member list from the config string and
// splits any Expenses:* posting (whose account doesn't already
// contain a member name) into N proportional sub-postings, one per
// member. Each new posting carries `__automatic__: True` metadata
// to mark it as plugin-generated. Open directives are emitted for
// the new sub-accounts.
//
// Skip conditions (posting passes through unchanged):
//   - no config / empty member list
//   - non-Expenses account
//   - account name already contains a member name (already split)

/// No config → plugin returns input unchanged. Pins early-return.
#[test]
fn test_split_expenses_no_config_passthrough() {
    let plugin = SplitExpensesPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Expenses:Food"),
        make_open("2024-01-01", "Assets:Cash"),
        make_transaction(
            "2024-01-15",
            "Lunch",
            vec![
                ("Expenses:Food", "100", "USD"),
                ("Assets:Cash", "-100", "USD"),
            ],
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    assert_eq!(output.directives.len(), 3, "no config → unchanged");
}

/// Config = "Alice Bob" + Expenses:Food $100 → emit two sub-postings
/// (one per member), each with split amount 50 USD. Pre-fix this
/// test only checked `expense_postings.len() >= 2`, accepting any
/// number from 2 upward.
#[test]
fn test_split_expenses_divides_amount_evenly_between_two_members() {
    let plugin = SplitExpensesPlugin;
    let input = make_input_with_config(
        vec![
            make_open("2024-01-01", "Expenses:Food"),
            make_open("2024-01-01", "Assets:Cash"),
            make_transaction(
                "2024-01-15",
                "Group dinner",
                vec![
                    ("Expenses:Food", "100", "USD"),
                    ("Assets:Cash", "-100", "USD"),
                ],
            ),
        ],
        "Alice Bob",
    );
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());

    let txn = output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction")
        .expect("transaction must remain");
    let DirectiveData::Transaction(data) = &txn.data else {
        panic!("non-Transaction data");
    };

    // Original Expenses:Food posting must be REPLACED by exactly two
    // per-member postings; none should still be at the bare account.
    assert_eq!(
        data.postings
            .iter()
            .filter(|p| p.account == "Expenses:Food")
            .count(),
        0,
        "original bare Expenses:Food posting must be replaced"
    );

    let alice = data
        .postings
        .iter()
        .find(|p| p.account == "Expenses:Food:Alice")
        .expect("Alice's split must be present");
    let bob = data
        .postings
        .iter()
        .find(|p| p.account == "Expenses:Food:Bob")
        .expect("Bob's split must be present");

    let alice_units = alice.units.as_ref().expect("Alice has units");
    let bob_units = bob.units.as_ref().expect("Bob has units");
    assert_eq!(alice_units.number, "50", "100 / 2 members = 50");
    assert_eq!(bob_units.number, "50");
    assert_eq!(alice_units.currency, "USD");
    assert_eq!(bob_units.currency, "USD");

    // `__automatic__: True` metadata marks the plugin-generated
    // postings so downstream tools can distinguish them from
    // hand-written ones.
    for p in [alice, bob] {
        assert!(
            p.metadata.iter().any(|(k, v)| k == "__automatic__"
                && matches!(v, MetaValueData::String(s) if s == "True")),
            "split posting must carry __automatic__: True metadata"
        );
    }

    // Plugin emits Open directives for the new sub-accounts.
    let opens: std::collections::BTreeSet<&str> = output
        .directives
        .iter()
        .filter_map(|d| match &d.data {
            DirectiveData::Open(o) if o.account.starts_with("Expenses:Food:") => {
                Some(o.account.as_str())
            }
            _ => None,
        })
        .collect();
    assert!(
        opens.contains("Expenses:Food:Alice") && opens.contains("Expenses:Food:Bob"),
        "Open directives for both sub-accounts must be emitted; got: {opens:?}"
    );
}

/// Account already contains a member name (e.g. `Expenses:Food:Alice`)
/// → no split needed, posting passes through. Pins the
/// `has_member` short-circuit.
#[test]
fn test_split_expenses_skips_already_split_account() {
    let plugin = SplitExpensesPlugin;
    let input = make_input_with_config(
        vec![
            make_open("2024-01-01", "Expenses:Food:Alice"),
            make_open("2024-01-01", "Assets:Cash"),
            make_transaction(
                "2024-01-15",
                "Alice's lunch",
                vec![
                    ("Expenses:Food:Alice", "20", "USD"),
                    ("Assets:Cash", "-20", "USD"),
                ],
            ),
        ],
        "Alice Bob",
    );
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());

    let txn = output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction")
        .expect("transaction must remain");
    let DirectiveData::Transaction(data) = &txn.data else {
        panic!("non-Transaction data");
    };
    assert_eq!(
        data.postings.len(),
        2,
        "already-split posting must NOT be re-split"
    );
    let alice = data
        .postings
        .iter()
        .find(|p| p.account == "Expenses:Food:Alice")
        .expect("Alice posting preserved");
    assert_eq!(
        alice.units.as_ref().unwrap().number,
        "20",
        "amount unchanged"
    );
    // No __automatic__ metadata since plugin didn't touch this posting.
    assert!(
        alice.metadata.iter().all(|(k, _)| k != "__automatic__"),
        "untouched posting must not get __automatic__ metadata"
    );
}

/// Non-Expenses posting (Assets, Income, Liabilities) → plugin
/// leaves it untouched. Pins the `is_expense` filter.
#[test]
fn test_split_expenses_skips_non_expenses_postings() {
    let plugin = SplitExpensesPlugin;
    let input = make_input_with_config(
        vec![
            make_open("2024-01-01", "Assets:Cash"),
            make_open("2024-01-01", "Income:Salary"),
            make_transaction(
                "2024-01-15",
                "Paycheck",
                vec![
                    ("Income:Salary", "-1000", "USD"),
                    ("Assets:Cash", "1000", "USD"),
                ],
            ),
        ],
        "Alice Bob",
    );
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    let txn = output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction")
        .expect("transaction must remain");
    let DirectiveData::Transaction(data) = &txn.data else {
        panic!("non-Transaction data");
    };
    assert_eq!(
        data.postings.len(),
        2,
        "non-Expenses postings are not split"
    );
}

// Property test: for any positive amount and 1..=5 members, the
// sum of split amounts equals the original amount exactly. Pins
// the division-and-rounding invariant under random inputs.
proptest::proptest! {
    #![proptest_config(proptest::prelude::ProptestConfig::with_cases(64))]

    #[test]
    fn prop_split_expenses_sum_preserves_total(
        amount_cents in 1u32..1_000_000,
        member_count in 1usize..=5,
    ) {
        use rust_decimal::Decimal;
        use std::str::FromStr;

        let amount = Decimal::new(i64::from(amount_cents), 2);
        let members: Vec<String> = (0..member_count).map(|i| format!("M{i}")).collect();
        let config = members.join(" ");

        let plugin = SplitExpensesPlugin;
        let input = make_input_with_config(
            vec![
                make_open("2024-01-01", "Expenses:Food"),
                make_open("2024-01-01", "Assets:Cash"),
                make_transaction(
                    "2024-01-15",
                    "Group meal",
                    vec![
                        ("Expenses:Food", &amount.to_string(), "USD"),
                        ("Assets:Cash", &(-amount).to_string(), "USD"),
                    ],
                ),
            ],
            &config,
        );
        let output = process_and_materialize(&plugin, input);
        proptest::prop_assert!(output.errors.is_empty());

        let txn = output
            .directives
            .iter()
            .find(|d| d.directive_type == "transaction")
            .expect("transaction must remain");
        let DirectiveData::Transaction(data) = &txn.data else {
            panic!("non-Transaction data");
        };

        // Sum of all Expenses:Food:* postings must equal the
        // original amount. The plugin uses a simple divide which
        // can produce repeating decimals (e.g. 100/3) that rust_decimal
        // truncates — verify the sum matches what the plugin's own
        // arithmetic would produce: (amount / N) * N.
        let split_sum: Decimal = data
            .postings
            .iter()
            .filter(|p| p.account.starts_with("Expenses:Food:"))
            .filter_map(|p| p.units.as_ref())
            .filter_map(|u| Decimal::from_str(&u.number).ok())
            .sum();
        let expected = (amount / Decimal::from(member_count)) * Decimal::from(member_count);
        proptest::prop_assert_eq!(
            split_sum, expected,
            "sum of {} splits must equal (amount/N)*N for amount={}, N={}",
            member_count, amount, member_count
        );

        // Posting count: original 2 → (1 expense replaced by N splits) + 1 cash = N+1.
        proptest::prop_assert_eq!(
            data.postings.len(), member_count + 1,
            "posting count after split should be N+1 (split×N + cash)"
        );
    }
}

// ============================================================================
// UnrealizedPlugin Tests
// ============================================================================
//
// `unrealized` walks every Transaction posting, accumulates units +
// cost basis per (account, currency), then for each non-zero position
// looks up a price entry to USD and emits a *warning* (NOT a directive)
// when the market value (`units * market_price`) differs from
// cost_basis by more than 0.01 USD.
//
// Coverage matrix below pins each branch: gain, loss, no-price,
// zero-position, threshold, multi-buy aggregation. Note the plugin
// hardcodes USD as the quote currency — non-USD positions are
// silently skipped (test pins this).

/// Single buy at 100, market jumps to 150 → unrealized gain of 500 USD.
/// Pre-fix this test only checked "doesn't error out" — that would
/// pass even if the plugin emitted no warnings at all.
#[test]
fn test_unrealized_warns_on_unrealized_gain() {
    let plugin = UnrealizedPlugin::new();
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Stock"),
        make_open("2024-01-01", "Assets:Cash"),
        make_commodity("2024-01-01", "AAPL"),
        make_transaction_with_cost(
            "2024-01-15",
            "Buy",
            "Assets:Stock",
            ("10", "AAPL"),
            ("100", "USD"),
            "Assets:Cash",
        ),
        make_price("2024-06-15", "AAPL", "150", "USD"),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(
        output.errors.len(),
        1,
        "exactly one warning for the single position with a market price"
    );
    let msg = &output.errors[0].message;
    assert!(
        msg.contains("500") && msg.contains("AAPL"),
        "warning should report 500 USD gain on AAPL; got: {msg}"
    );
    assert_eq!(
        output.errors[0].severity,
        PluginErrorSeverity::Warning,
        "unrealized changes are warnings, never errors"
    );
}

/// Symmetric to the gain case: market drops below cost → negative
/// unrealized number in the warning text.
#[test]
fn test_unrealized_warns_on_unrealized_loss() {
    let plugin = UnrealizedPlugin::new();
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Stock"),
        make_open("2024-01-01", "Assets:Cash"),
        make_commodity("2024-01-01", "AAPL"),
        make_transaction_with_cost(
            "2024-01-15",
            "Buy",
            "Assets:Stock",
            ("10", "AAPL"),
            ("100", "USD"),
            "Assets:Cash",
        ),
        make_price("2024-06-15", "AAPL", "50", "USD"),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(output.errors.len(), 1, "exactly one warning");
    let msg = &output.errors[0].message;
    assert!(
        msg.contains("-500") && msg.contains("AAPL"),
        "warning should report -500 USD (loss) on AAPL; got: {msg}"
    );
}

/// Market price equals cost basis → no unrealized change → no warning.
/// Pins the threshold logic (warning fires only on |Δ| > 0.01).
#[test]
fn test_unrealized_silent_when_market_equals_cost() {
    let plugin = UnrealizedPlugin::new();
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Stock"),
        make_open("2024-01-01", "Assets:Cash"),
        make_commodity("2024-01-01", "AAPL"),
        make_transaction_with_cost(
            "2024-01-15",
            "Buy",
            "Assets:Stock",
            ("10", "AAPL"),
            ("100", "USD"),
            "Assets:Cash",
        ),
        make_price("2024-06-15", "AAPL", "100", "USD"),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "no warning when market price equals cost basis (got {} warnings)",
        output.errors.len()
    );
}

/// Position exists but no price directive → plugin can't compute
/// unrealized, silently skips. Pins this fall-through.
#[test]
fn test_unrealized_silent_without_price_directive() {
    let plugin = UnrealizedPlugin::new();
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Stock"),
        make_open("2024-01-01", "Assets:Cash"),
        make_commodity("2024-01-01", "AAPL"),
        make_transaction_with_cost(
            "2024-01-15",
            "Buy",
            "Assets:Stock",
            ("10", "AAPL"),
            ("100", "USD"),
            "Assets:Cash",
        ),
        // Note: no price directive
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "no warning emitted when there's no current price (got {} warnings)",
        output.errors.len()
    );
}

/// Buy then fully sell → net position is zero → plugin skips even
/// if a price exists. Pins the `units == ZERO` short-circuit.
#[test]
fn test_unrealized_silent_for_zero_position() {
    let plugin = UnrealizedPlugin::new();
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Stock"),
        make_open("2024-01-01", "Assets:Cash"),
        make_commodity("2024-01-01", "AAPL"),
        make_transaction_with_cost(
            "2024-01-15",
            "Buy",
            "Assets:Stock",
            ("10", "AAPL"),
            ("100", "USD"),
            "Assets:Cash",
        ),
        make_transaction_with_cost(
            "2024-03-15",
            "Sell",
            "Assets:Stock",
            ("-10", "AAPL"),
            ("100", "USD"),
            "Assets:Cash",
        ),
        make_price("2024-06-15", "AAPL", "150", "USD"),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "no warning when position is fully closed (got {} warnings)",
        output.errors.len()
    );
}

/// Two buys at different cost bases. Market price chosen to land
/// the average exactly at the weighted-average cost (no unrealized
/// change). Documents that the plugin tracks aggregate cost basis,
/// not per-lot.
#[test]
fn test_unrealized_aggregates_multiple_buys_into_position() {
    let plugin = UnrealizedPlugin::new();
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Stock"),
        make_open("2024-01-01", "Assets:Cash"),
        make_commodity("2024-01-01", "AAPL"),
        // 5 @ 100 = 500 cost basis
        make_transaction_with_cost(
            "2024-01-15",
            "Buy",
            "Assets:Stock",
            ("5", "AAPL"),
            ("100", "USD"),
            "Assets:Cash",
        ),
        // 5 @ 200 = 1000 cost basis
        make_transaction_with_cost(
            "2024-02-15",
            "Buy",
            "Assets:Stock",
            ("5", "AAPL"),
            ("200", "USD"),
            "Assets:Cash",
        ),
        // total: 10 units, $1500 cost. At market $150/unit, value =
        // $1500. unrealized = 0 → no warning.
        make_price("2024-06-15", "AAPL", "150", "USD"),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "weighted-average cost basis: 10 units at avg $150 cost = $1500; \
         market 10 × $150 = $1500; unrealized = 0 (got {} warnings)",
        output.errors.len()
    );
}

/// Position priced in a non-USD quote currency is silently skipped.
/// Pins the hardcoded USD assumption in the plugin
/// (`prices.get(&(currency, "USD"))`); a refactor that adds quote-
/// currency configurability should also update this test.
#[test]
fn test_unrealized_silent_when_quote_currency_is_not_usd() {
    let plugin = UnrealizedPlugin::new();
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Stock"),
        make_open("2024-01-01", "Assets:Cash"),
        make_commodity("2024-01-01", "ABC"),
        make_transaction_with_cost(
            "2024-01-15",
            "Buy",
            "Assets:Stock",
            ("10", "ABC"),
            ("100", "EUR"),
            "Assets:Cash",
        ),
        // Price quoted in EUR, not USD. Plugin ignores it.
        make_price("2024-06-15", "ABC", "150", "EUR"),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "non-USD quote currencies are skipped today (got {} warnings)",
        output.errors.len()
    );
}

// Property test: unrealized gain reported in the warning equals
// `units * (market_price - cost_per)` for any single-buy + market-
// price scenario.
//
// This is the algebraic invariant of the plugin's core math.
// Generators are expressed in *cents* (cost_cents, market_cents) so
// the test actually exercises:
//   - fractional prices (any cent value not divisible by 100 is
//     fractional in dollar units)
//   - threshold-boundary cases (delta_cents in 0..2 ⇒ gain of 0,
//     0.01, or above when multiplied by units)
//   - large unit counts (up to 1000)
proptest::proptest! {
    #![proptest_config(proptest::prelude::ProptestConfig::with_cases(64))]

    #[test]
    fn prop_unrealized_warning_amount_matches_units_times_delta(
        // Units stay integer so cost_basis = cost_per * units is exact.
        units in 1u32..1000,
        // Cost and market in *cents*. Range covers values up to
        // $10,000 with 0.01 USD precision, including fractional
        // cent counts that make `cost_per` non-integer in dollars.
        cost_cents in 1u32..1_000_000,
        market_cents in 1u32..1_000_000,
    ) {
        use rust_decimal::Decimal;

        // cents -> dollars: divide by 100.
        let to_dollars = |cents: u32| -> Decimal {
            Decimal::new(i64::from(cents), 2)
        };
        let cost_d = to_dollars(cost_cents);
        let market_d = to_dollars(market_cents);

        let plugin = UnrealizedPlugin::new();
        let input = make_input(vec![
            make_open("2024-01-01", "Assets:Stock"),
            make_open("2024-01-01", "Assets:Cash"),
            make_commodity("2024-01-01", "AAPL"),
            make_transaction_with_cost(
                "2024-01-15",
                "Buy",
                "Assets:Stock",
                (&units.to_string(), "AAPL"),
                (&cost_d.to_string(), "USD"),
                "Assets:Cash",
            ),
            make_price("2024-06-15", "AAPL", &market_d.to_string(), "USD"),
        ]);
        let output = process_and_materialize(&plugin, input);

        let units_d = Decimal::from(units);
        let expected_gain = (market_d - cost_d) * units_d;
        // Threshold is `> Decimal::new(1, 2)` = 0.01.
        let above_threshold = expected_gain.abs() > Decimal::new(1, 2);

        if above_threshold {
            proptest::prop_assert_eq!(
                output.errors.len(), 1,
                "expected 1 warning for expected_gain={}", expected_gain
            );
            let msg = &output.errors[0].message;
            proptest::prop_assert!(
                msg.contains(&expected_gain.to_string()),
                "warning '{}' should contain the exact gain {}",
                msg, expected_gain
            );
        } else {
            proptest::prop_assert!(
                output.errors.is_empty(),
                "no warning expected for expected_gain={} (≤ 0.01 threshold)",
                expected_gain
            );
        }
    }

    /// Two buys at different cost bases — the position aggregates,
    /// and the unrealized gain at any market price is
    ///
    ///   (units_a + units_b) * market - (cost_a*units_a + cost_b*units_b)
    ///
    /// Pins the position-aggregation invariant. Pre-fix
    /// `prop_unrealized_warning_amount_matches_units_times_delta` only
    /// covered single buys, so weighted-average rounding bugs in
    /// multi-buy aggregation would have slipped through.
    #[test]
    fn prop_unrealized_aggregates_two_buys_correctly(
        units_a in 1u32..500,
        units_b in 1u32..500,
        cost_a_cents in 1u32..1_000_000,
        cost_b_cents in 1u32..1_000_000,
        market_cents in 1u32..1_000_000,
    ) {
        use rust_decimal::Decimal;

        let to_dollars = |cents: u32| Decimal::new(i64::from(cents), 2);
        let cost_a_d = to_dollars(cost_a_cents);
        let cost_b_d = to_dollars(cost_b_cents);
        let market_d = to_dollars(market_cents);
        let units_a_d = Decimal::from(units_a);
        let units_b_d = Decimal::from(units_b);

        let plugin = UnrealizedPlugin::new();
        let input = make_input(vec![
            make_open("2024-01-01", "Assets:Stock"),
            make_open("2024-01-01", "Assets:Cash"),
            make_commodity("2024-01-01", "AAPL"),
            make_transaction_with_cost(
                "2024-01-15",
                "Buy A",
                "Assets:Stock",
                (&units_a.to_string(), "AAPL"),
                (&cost_a_d.to_string(), "USD"),
                "Assets:Cash",
            ),
            make_transaction_with_cost(
                "2024-02-15",
                "Buy B",
                "Assets:Stock",
                (&units_b.to_string(), "AAPL"),
                (&cost_b_d.to_string(), "USD"),
                "Assets:Cash",
            ),
            make_price("2024-06-15", "AAPL", &market_d.to_string(), "USD"),
        ]);
        let output = process_and_materialize(&plugin, input);

        // Expected aggregate gain across both lots.
        let total_units = units_a_d + units_b_d;
        let total_cost = cost_a_d * units_a_d + cost_b_d * units_b_d;
        let expected_gain = total_units * market_d - total_cost;
        let above_threshold = expected_gain.abs() > Decimal::new(1, 2);

        if above_threshold {
            proptest::prop_assert_eq!(
                output.errors.len(), 1,
                "expected 1 aggregated warning; expected_gain={}", expected_gain
            );
            let msg = &output.errors[0].message;
            proptest::prop_assert!(
                msg.contains(&expected_gain.to_string()),
                "warning '{}' should contain aggregate gain {}",
                msg, expected_gain
            );
        } else {
            proptest::prop_assert!(
                output.errors.is_empty(),
                "no warning expected for aggregate gain={} (≤ 0.01)",
                expected_gain
            );
        }
    }
}

/// Custom `gains_account` is stored on the plugin but never appears in
/// the output today (the plugin emits warnings, not directives, so
/// the account name is unused). Pins this so a future change to
/// emit actual transactions to the account is caught by the test.
#[test]
fn test_unrealized_custom_gains_account_currently_unused_in_output() {
    let plugin = UnrealizedPlugin::with_account("Income:Custom-Unrealized".to_string());
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Stock"),
        make_open("2024-01-01", "Assets:Cash"),
        make_commodity("2024-01-01", "AAPL"),
        make_transaction_with_cost(
            "2024-01-15",
            "Buy",
            "Assets:Stock",
            ("10", "AAPL"),
            ("100", "USD"),
            "Assets:Cash",
        ),
        make_price("2024-06-15", "AAPL", "150", "USD"),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(
        output.errors.len(),
        1,
        "warning still fires regardless of account customization"
    );
    // Today the warning text doesn't mention the gains_account at all.
    // If a future change makes it do so, this test should be updated
    // to assert on the new behavior.
    assert!(
        !output.errors[0]
            .message
            .contains("Income:Custom-Unrealized"),
        "current behavior: gains_account is not surfaced in warnings"
    );
}

// ============================================================================
// CheckAverageCostPlugin Tests
// ============================================================================
//
// `check_average_cost` is a safety net for accounts opened with the
// NONE booking method (where the ledger author manages lots manually
// and there's no booker enforcing them). It tracks per-account
// running average cost and warns if a reducing posting uses a cost
// that differs from the average by more than `tolerance` (default
// 1%).
//
// Importantly: accounts opened with any other booking method
// (STRICT, FIFO, etc.) are SKIPPED — those bookers already enforce
// lot matching, so re-checking here would produce false positives
// (#907).

/// Build an Open directive with a specific booking method. The
/// default `make_open` helper sets `booking: None`; this plugin
/// only checks accounts with `booking: Some("NONE")`.
fn make_open_with_booking(date: &str, account: &str, booking: &str) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: "open".to_string(),
        date: date.to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Open(OpenData {
            account: account.to_string(),
            currencies: vec![],
            booking: Some(booking.to_string()),
            metadata: vec![],
        }),
    }
}

/// Buy + sale at exactly the average cost → no warning. The account
/// is opened with NONE booking so the plugin actually runs its
/// check on it.
#[test]
fn test_check_average_cost_silent_on_correct_sale() {
    let plugin = CheckAverageCostPlugin::new();
    let input = make_input(vec![
        make_open_with_booking("2024-01-01", "Assets:Stock", "NONE"),
        make_open("2024-01-01", "Assets:Cash"),
        make_transaction_with_cost(
            "2024-01-15",
            "Buy",
            "Assets:Stock",
            ("10", "AAPL"),
            ("100", "USD"),
            "Assets:Cash",
        ),
        make_transaction_with_cost(
            "2024-06-15",
            "Sell at avg cost",
            "Assets:Stock",
            ("-5", "AAPL"),
            ("100", "USD"),
            "Assets:Cash",
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "sale at exact average cost is fine; got {} warnings",
        output.errors.len()
    );
}

/// Sale uses a cost that differs from the running average by more
/// than tolerance → exactly one warning, mentioning the account.
#[test]
fn test_check_average_cost_warns_when_sale_cost_diverges_from_average() {
    let plugin = CheckAverageCostPlugin::new();
    let input = make_input(vec![
        make_open_with_booking("2024-01-01", "Assets:Stock", "NONE"),
        make_open("2024-01-01", "Assets:Cash"),
        // Two buys at different prices: 5 @ 100 + 5 @ 200 → avg 150.
        make_transaction_with_cost(
            "2024-01-15",
            "Buy 1",
            "Assets:Stock",
            ("5", "AAPL"),
            ("100", "USD"),
            "Assets:Cash",
        ),
        make_transaction_with_cost(
            "2024-02-15",
            "Buy 2",
            "Assets:Stock",
            ("5", "AAPL"),
            ("200", "USD"),
            "Assets:Cash",
        ),
        // Sale at 100 — that's 33% off the average 150 → > 1% tolerance.
        make_transaction_with_cost(
            "2024-06-15",
            "Sell below average",
            "Assets:Stock",
            ("-3", "AAPL"),
            ("100", "USD"),
            "Assets:Cash",
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    // beancount's message and severity (#2600).
    assert_eq!(
        output.errors.len(),
        1,
        "exactly one error for the diverging sale"
    );
    assert_eq!(
        output.errors[0].message,
        "Cost basis on reducing posting is too far from the average cost (100 vs. 150)"
    );
    assert_eq!(output.errors[0].severity, PluginErrorSeverity::Error);
}

/// Account is NOT opened with NONE booking → plugin skips it
/// entirely, no warning even if the sale cost is wildly off.
/// Pins the issue-#907 false-positive guard.
#[test]
fn test_check_average_cost_skips_strict_booking_account() {
    let plugin = CheckAverageCostPlugin::new();
    let input = make_input(vec![
        // STRICT booking → plugin should skip this account.
        make_open_with_booking("2024-01-01", "Assets:Stock", "STRICT"),
        make_open("2024-01-01", "Assets:Cash"),
        make_transaction_with_cost(
            "2024-01-15",
            "Buy",
            "Assets:Stock",
            ("10", "AAPL"),
            ("100", "USD"),
            "Assets:Cash",
        ),
        // Sale at completely wrong cost — but plugin doesn't touch
        // this account.
        make_transaction_with_cost(
            "2024-06-15",
            "Sell at very wrong cost",
            "Assets:Stock",
            ("-5", "AAPL"),
            ("999", "USD"),
            "Assets:Cash",
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "STRICT-booking account is skipped; got {} warnings",
        output.errors.len()
    );
}

/// Account is opened with no booking method specified → plugin
/// also skips it (only NONE-booking is checked). Pins the
/// `is_some + eq_ignore_ascii_case("NONE")` filter chain.
#[test]
fn test_check_average_cost_skips_account_without_booking_specified() {
    let plugin = CheckAverageCostPlugin::new();
    let input = make_input(vec![
        // make_open() leaves booking = None.
        make_open("2024-01-01", "Assets:Stock"),
        make_open("2024-01-01", "Assets:Cash"),
        make_transaction_with_cost(
            "2024-01-15",
            "Buy",
            "Assets:Stock",
            ("10", "AAPL"),
            ("100", "USD"),
            "Assets:Cash",
        ),
        make_transaction_with_cost(
            "2024-06-15",
            "Sell at wrong cost",
            "Assets:Stock",
            ("-5", "AAPL"),
            ("500", "USD"),
            "Assets:Cash",
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "account without explicit NONE booking is not checked"
    );
}

/// Custom tolerance is honored. With a tolerance of 0.5 (50%),
/// a sale at 50% of average is at the boundary — set sale cost to
/// 0.51 below avg so it just exceeds. With default 1% tolerance
/// the same sale would have warned.
#[test]
fn test_check_average_cost_respects_custom_tolerance() {
    use rust_decimal::Decimal;

    // 50% tolerance plugin instance.
    let plugin = CheckAverageCostPlugin::with_tolerance(Decimal::new(5, 1)); // 0.5
    let input = make_input(vec![
        make_open_with_booking("2024-01-01", "Assets:Stock", "NONE"),
        make_open("2024-01-01", "Assets:Cash"),
        make_transaction_with_cost(
            "2024-01-15",
            "Buy",
            "Assets:Stock",
            ("10", "AAPL"),
            ("100", "USD"),
            "Assets:Cash",
        ),
        // Sale at 60 — that's 40% off average 100, BELOW the 50% tolerance.
        make_transaction_with_cost(
            "2024-06-15",
            "Sell at -40% (within tolerance)",
            "Assets:Stock",
            ("-3", "AAPL"),
            ("60", "USD"),
            "Assets:Cash",
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(
        output.errors.is_empty(),
        "40% deviation is within 50% custom tolerance; got {} warnings",
        output.errors.len()
    );
}

// Property test: selling at the exact weighted-average cost basis
// produces no warning, regardless of how many buys at how many prices
// preceded the sale.
//
// The plugin's invariant is the standard weighted-mean formula:
//
//   avg = Σ(units_i * price_i) / Σ(units_i)
//
// We compute that mean in the test using `rust_decimal` (the same
// crate the plugin uses) and pass it as the `cost_per` of the sale
// leg. With identical arithmetic on both sides the difference is
// exactly zero, well within any tolerance, so no warning is expected.
// A rounding bug or off-by-one in the running totals would surface
// as an unexpected warning.
proptest::proptest! {
    #![proptest_config(proptest::prelude::ProptestConfig::with_cases(64))]

    #[test]
    fn prop_check_average_cost_sell_at_weighted_mean_produces_no_warning(
        // 1..=5 buys, each (units, price-in-cents). Small ranges keep
        // arithmetic well inside Decimal precision.
        buys in proptest::collection::vec(
            (1u32..100, 1u32..1_000_000),
            1..=5,
        ),
    ) {
        use rust_decimal::Decimal;

        // Compute the expected weighted mean using the same arithmetic
        // the plugin uses internally: `total_cost / total_units`, with
        // each price already represented in dollars via
        // `Decimal::new(price_cents, 2)` (scale 2 ⇒ value = cents/100).
        // Identical operation order on both sides guarantees that any
        // precision loss is identical too — a real bug, not a precision
        // artifact, would be required to make the assertion fail.
        let total_units: Decimal = buys.iter()
            .map(|(u, _)| Decimal::from(*u))
            .sum();
        let total_cost: Decimal = buys.iter()
            .map(|(u, p)| Decimal::from(*u) * Decimal::new(i64::from(*p), 2))
            .sum();
        let avg = total_cost / total_units;

        // Build directives: open with NONE booking, then one buy txn
        // per generated entry, then a single sell at the weighted mean.
        let mut directives: Vec<DirectiveWrapper> = vec![
            DirectiveWrapper {
                directive_type: "open".to_string(),
                date: "2024-01-01".to_string(),
                filename: None,
                lineno: None,
                data: DirectiveData::Open(OpenData {
                    account: "Assets:Broker".to_string(),
                    currencies: vec![],
                    booking: Some("NONE".to_string()),
                    metadata: vec![],
                }),
            },
        ];
        for (i, (units, price_cents)) in buys.iter().enumerate() {
            let price = Decimal::new(i64::from(*price_cents), 2);
            directives.push(make_transaction_with_cost(
                &format!("2024-01-{:02}", (i % 28) + 1),
                "Buy",
                "Assets:Broker",
                (&units.to_string(), "AAPL"),
                (&price.to_string(), "USD"),
                "Assets:Cash",
            ));
        }
        // Sell 1 unit at exactly the weighted-mean cost.
        directives.push(make_transaction_with_cost(
            "2024-12-01",
            "Sell at average",
            "Assets:Broker",
            ("-1", "AAPL"),
            (&avg.to_string(), "USD"),
            "Assets:Cash",
        ));

        let plugin = CheckAverageCostPlugin::new();
        let input = make_input(directives);
        let output = process_and_materialize(&plugin, input);

        proptest::prop_assert_eq!(
            output.errors.len(), 0,
            "selling at computed weighted mean {} should produce 0 warnings; \
             buys={:?}, errors={:?}",
            avg, buys, output.errors
        );
    }
}

// ============================================================================
// ZerosumPlugin Tests
// ============================================================================
//
// `zerosum` finds postings in the configured "zerosum" accounts that
// net to zero (within tolerance) and within a configurable date
// range, then moves them to a "matched" account. Useful for tracking
// in-flight transfers that haven't yet been reconciled.
//
// Config format (Python-dict-as-string):
//   {
//     'zerosum_accounts': {
//       'Assets:ZeroSum:Transfers': ('Assets:ZeroSum-Matched:Transfers', 30),
//     },
//     'account_name_replace': ('ZeroSum', 'ZeroSum-Matched'),
//     'tolerance': 0.01,
//   }
//
// Skip / error conditions:
//   - missing config → error
//   - malformed config → error

const ZEROSUM_CFG: &str =
    "{'zerosum_accounts': {'Assets:ZeroSum': ('Assets:ZeroSum-Matched', 30)}}";

/// Missing config → one error reported. Existing test, kept.
#[test]
fn test_zerosum_requires_config() {
    let plugin = ZerosumPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_transaction("2024-01-15", "Test", vec![("Assets:Cash", "100", "USD")]),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert_eq!(
        output.errors.len(),
        1,
        "exactly one error for missing required config"
    );
    assert!(output.errors[0].message.contains("requires configuration"));
}

/// A pair of postings to the zerosum account that net to zero —
/// within the date window — gets moved to the matched account.
/// Pins the core "match and rewrite" branch.
#[test]
fn test_zerosum_matches_pair_within_window() {
    let plugin = ZerosumPlugin;
    let input = make_input_with_config(
        vec![
            make_open("2024-01-01", "Assets:Cash"),
            make_open("2024-01-01", "Assets:ZeroSum"),
            // Two transfers that net to zero within 30 days.
            make_transaction(
                "2024-01-05",
                "Outgoing transfer",
                vec![
                    ("Assets:Cash", "-100", "USD"),
                    ("Assets:ZeroSum", "100", "USD"),
                ],
            ),
            make_transaction(
                "2024-01-15",
                "Incoming transfer",
                vec![
                    ("Assets:Cash", "100", "USD"),
                    ("Assets:ZeroSum", "-100", "USD"),
                ],
            ),
        ],
        ZEROSUM_CFG,
    );
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());

    // After matching, NO posting should remain in `Assets:ZeroSum` —
    // both got moved to `Assets:ZeroSum-Matched`.
    let zerosum_count: usize = output
        .directives
        .iter()
        .filter_map(|d| match &d.data {
            DirectiveData::Transaction(t) => Some(
                t.postings
                    .iter()
                    .filter(|p| p.account == "Assets:ZeroSum")
                    .count(),
            ),
            _ => None,
        })
        .sum();
    let matched_count: usize = output
        .directives
        .iter()
        .filter_map(|d| match &d.data {
            DirectiveData::Transaction(t) => Some(
                t.postings
                    .iter()
                    .filter(|p| p.account == "Assets:ZeroSum-Matched")
                    .count(),
            ),
            _ => None,
        })
        .sum();
    assert_eq!(
        zerosum_count, 0,
        "matched postings should leave the zerosum account"
    );
    assert_eq!(
        matched_count, 2,
        "both halves of the pair land in the matched account"
    );
}

/// Pair of zero-summing postings spaced beyond the date window →
/// plugin does NOT match them. They stay in the zerosum account.
/// Pins the date-range filter.
#[test]
fn test_zerosum_does_not_match_pair_outside_window() {
    let plugin = ZerosumPlugin;
    let input = make_input_with_config(
        vec![
            make_open("2024-01-01", "Assets:Cash"),
            make_open("2024-01-01", "Assets:ZeroSum"),
            make_transaction(
                "2024-01-05",
                "Outgoing",
                vec![
                    ("Assets:Cash", "-100", "USD"),
                    ("Assets:ZeroSum", "100", "USD"),
                ],
            ),
            // 60 days later — outside the 30-day window.
            make_transaction(
                "2024-03-10",
                "Incoming far in the future",
                vec![
                    ("Assets:Cash", "100", "USD"),
                    ("Assets:ZeroSum", "-100", "USD"),
                ],
            ),
        ],
        ZEROSUM_CFG,
    );
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());

    let zerosum_count: usize = output
        .directives
        .iter()
        .filter_map(|d| match &d.data {
            DirectiveData::Transaction(t) => Some(
                t.postings
                    .iter()
                    .filter(|p| p.account == "Assets:ZeroSum")
                    .count(),
            ),
            _ => None,
        })
        .sum();
    let matched_count: usize = output
        .directives
        .iter()
        .filter_map(|d| match &d.data {
            DirectiveData::Transaction(t) => Some(
                t.postings
                    .iter()
                    .filter(|p| p.account == "Assets:ZeroSum-Matched")
                    .count(),
            ),
            _ => None,
        })
        .sum();
    assert_eq!(
        zerosum_count, 2,
        "out-of-window pair stays in the zerosum account"
    );
    assert_eq!(matched_count, 0, "no postings moved to matched account");
}

/// Single unmatched posting (no counterpart) → stays in the
/// zerosum account. Pins the "no pair found → leave alone" branch.
#[test]
fn test_zerosum_leaves_unmatched_posting_alone() {
    let plugin = ZerosumPlugin;
    let input = make_input_with_config(
        vec![
            make_open("2024-01-01", "Assets:Cash"),
            make_open("2024-01-01", "Assets:ZeroSum"),
            make_transaction(
                "2024-01-05",
                "Lonely outgoing",
                vec![
                    ("Assets:Cash", "-100", "USD"),
                    ("Assets:ZeroSum", "100", "USD"),
                ],
            ),
        ],
        ZEROSUM_CFG,
    );
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());

    let zerosum_count: usize = output
        .directives
        .iter()
        .filter_map(|d| match &d.data {
            DirectiveData::Transaction(t) => Some(
                t.postings
                    .iter()
                    .filter(|p| p.account == "Assets:ZeroSum")
                    .count(),
            ),
            _ => None,
        })
        .sum();
    assert_eq!(
        zerosum_count, 1,
        "unmatched posting remains in zerosum account"
    );
}

// ============================================================================
// BoxAccrualPlugin Tests
// ============================================================================
//
// `box_accrual` finds transactions with `synthetic_loan_expiry`
// metadata and splits a single `:Capital-Losses` posting
// proportionally across years (by day count). The final segment is
// `total - sum(rounded_segments)` so the total is preserved exactly.
// Each split posting carries an `effective_date` metadata for the
// last day of its year segment (the final segment uses the actual
// expiry date).
//
// Skip conditions (transaction passes through unchanged):
//   - no `synthetic_loan_expiry` metadata
//   - no posting whose account ends with `:Capital-Losses`
//   - more than one such posting (the plugin only handles exactly 1)
//   - same-year start and expiry (no split needed)
//   - unparsable dates / non-decimal amount

/// No `synthetic_loan_expiry` metadata → directives unchanged. Pins
/// the early-skip when expiry metadata is absent.
#[test]
fn test_box_accrual_no_metadata_passthrough() {
    let plugin = BoxAccrualPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Expenses:Food"),
        make_transaction(
            "2024-01-15",
            "Normal transaction",
            vec![
                ("Expenses:Food", "25", "USD"),
                ("Assets:Cash", "-25", "USD"),
            ],
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    assert_eq!(output.directives.len(), 3);
}

/// Multi-year span → exactly one Capital-Losses posting per year,
/// each tagged with the year's `effective_date`, and the segment
/// amounts sum exactly to the original total. Pins the core
/// preservation invariant.
#[test]
fn test_box_accrual_multi_year_splits_preserve_total() {
    use rust_decimal::Decimal;
    use std::str::FromStr;

    let plugin = BoxAccrualPlugin;
    // 2024-07-01 → 2026-06-30 spans 3 calendar years (2024, 2025, 2026).
    let input = make_input(vec![
        make_open("2024-01-01", "Income:Capital-Losses"),
        make_open("2024-01-01", "Assets:Broker"),
        make_transaction_with_metadata(
            "2024-07-01",
            "Sell synthetic spanning 3 years",
            vec![(
                "synthetic_loan_expiry",
                MetaValueData::Date("2026-06-30".to_string()),
            )],
            vec![
                ("Income:Capital-Losses", "-1000.00", "USD"),
                ("Assets:Broker", "1000.00", "USD"),
            ],
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());

    let txn = output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction")
        .expect("transaction must remain");
    let DirectiveData::Transaction(data) = &txn.data else {
        panic!("non-Transaction data on transaction directive");
    };

    let losses_iter = || {
        data.postings
            .iter()
            .filter(|p| p.account.ends_with(":Capital-Losses"))
    };
    assert_eq!(
        losses_iter().count(),
        3,
        "3-year span yields 3 Capital-Losses postings"
    );

    // Each split must carry an `effective_date`.
    for p in losses_iter() {
        assert!(
            p.metadata.iter().any(|(k, _)| k == "effective_date"),
            "every split should carry effective_date metadata"
        );
    }

    // Sum of split amounts = original total (-1000.00). Pins the
    // "final segment is remainder" invariant.
    let sum: Decimal = losses_iter()
        .filter_map(|p| p.units.as_ref())
        .filter_map(|u| Decimal::from_str(&u.number).ok())
        .sum();
    assert_eq!(
        sum,
        Decimal::from_str("-1000.00").unwrap(),
        "split amounts must sum exactly to the original total"
    );
}

/// Same year for start and expiry → plugin skips the split (no
/// reason to slice a single-year position). Transaction passes
/// through with its original single Capital-Losses posting intact.
#[test]
fn test_box_accrual_same_year_no_split() {
    let plugin = BoxAccrualPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Income:Capital-Losses"),
        make_open("2024-01-01", "Assets:Broker"),
        make_transaction_with_metadata(
            "2024-03-01",
            "Same-year span",
            vec![(
                "synthetic_loan_expiry",
                MetaValueData::Date("2024-12-31".to_string()),
            )],
            vec![
                ("Income:Capital-Losses", "-365", "USD"),
                ("Assets:Broker", "365", "USD"),
            ],
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    let txn = output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction")
        .expect("transaction must remain");
    let DirectiveData::Transaction(data) = &txn.data else {
        panic!("non-Transaction data on transaction directive");
    };
    let loss_postings: Vec<_> = data
        .postings
        .iter()
        .filter(|p| p.account.ends_with(":Capital-Losses"))
        .collect();
    assert_eq!(
        loss_postings.len(),
        1,
        "same-year transaction is left with its original single posting"
    );
    // And no effective_date metadata was added.
    assert!(
        !loss_postings[0]
            .metadata
            .iter()
            .any(|(k, _)| k == "effective_date"),
        "single-year passthrough should not add effective_date metadata"
    );
}

/// Metadata present but no `:Capital-Losses` posting → plugin can't
/// split anything, transaction passes through. Pins the
/// `losses.len() != 1` skip.
#[test]
fn test_box_accrual_no_capital_losses_posting_unchanged() {
    let plugin = BoxAccrualPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Expenses:Food"),
        make_transaction_with_metadata(
            "2024-07-01",
            "Lunch with stray expiry metadata",
            vec![(
                "synthetic_loan_expiry",
                MetaValueData::Date("2026-06-30".to_string()),
            )],
            vec![
                ("Expenses:Food", "25", "USD"),
                ("Assets:Cash", "-25", "USD"),
            ],
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    let txn = output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction")
        .expect("transaction must remain");
    let DirectiveData::Transaction(data) = &txn.data else {
        panic!("non-Transaction data on transaction directive");
    };
    assert_eq!(
        data.postings.len(),
        2,
        "no Capital-Losses → original postings preserved exactly"
    );
}

/// More than one `:Capital-Losses` posting → plugin can't decide
/// which to split, transaction passes through. Pins the
/// `losses.len() != 1` skip in the multi-loss direction.
#[test]
fn test_box_accrual_two_capital_losses_postings_unchanged() {
    let plugin = BoxAccrualPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Income:Capital-Losses"),
        make_open("2024-01-01", "Income:Other:Capital-Losses"),
        make_open("2024-01-01", "Assets:Broker"),
        make_transaction_with_metadata(
            "2024-07-01",
            "Two loss accounts",
            vec![(
                "synthetic_loan_expiry",
                MetaValueData::Date("2026-06-30".to_string()),
            )],
            vec![
                ("Income:Capital-Losses", "-500", "USD"),
                ("Income:Other:Capital-Losses", "-500", "USD"),
                ("Assets:Broker", "1000", "USD"),
            ],
        ),
    ]);
    let output = process_and_materialize(&plugin, input);
    let txn = output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction")
        .expect("transaction must remain");
    let DirectiveData::Transaction(data) = &txn.data else {
        panic!("non-Transaction data on transaction directive");
    };
    assert_eq!(
        data.postings
            .iter()
            .filter(|p| p.account.ends_with(":Capital-Losses"))
            .count(),
        2,
        "ambiguous case → both loss postings kept untouched"
    );
}

// Property test: regardless of (total_loss, start_date, expiry_date)
// the sum of split posting amounts equals the original total
// exactly. The plugin's "final segment is remainder" math is
// what guarantees this; a rounding bug in the per-year split
// arithmetic would break it. The example test
// `test_box_accrual_multi_year_splits_preserve_total` pins one
// specific case; this catches the surrounding input space.
proptest::proptest! {
    #![proptest_config(proptest::prelude::ProptestConfig::with_cases(64))]

    #[test]
    fn prop_box_accrual_split_amounts_preserve_total(
        // Total loss in cents (negative; -1 to -10_000_000 = -$0.01 to -$100,000).
        total_cents in 1u32..10_000_000,
        // Start in 2024 to give us a known year.
        start_month in 1u32..=12,
        start_day in 1u32..=28,
        // Number of additional years to span (1 = 2-year, ..., 5 = 6-year).
        extra_years in 1u32..=5,
        // Expiry month/day (any valid in that year).
        expiry_month in 1u32..=12,
        expiry_day in 1u32..=28,
    ) {
        use rust_decimal::Decimal;
        use std::str::FromStr;

        let start_date = format!("2024-{start_month:02}-{start_day:02}");
        let expiry_year = 2024 + extra_years;
        let expiry_date = format!("{expiry_year:04}-{expiry_month:02}-{expiry_day:02}");
        let total_loss = -Decimal::new(i64::from(total_cents), 2);

        let plugin = BoxAccrualPlugin;
        let input = make_input(vec![
            make_open("2024-01-01", "Income:Capital-Losses"),
            make_open("2024-01-01", "Assets:Broker"),
            make_transaction_with_metadata(
                &start_date,
                "Synthetic with random expiry",
                vec![(
                    "synthetic_loan_expiry",
                    MetaValueData::Date(expiry_date.clone()),
                )],
                vec![
                    ("Income:Capital-Losses", &total_loss.to_string(), "USD"),
                    ("Assets:Broker", &(-total_loss).to_string(), "USD"),
                ],
            ),
        ]);
        let output = process_and_materialize(&plugin, input);
        proptest::prop_assert!(output.errors.is_empty());

        let txn = output
            .directives
            .iter()
            .find(|d| d.directive_type == "transaction")
            .expect("transaction must remain");
        let DirectiveData::Transaction(data) = &txn.data else {
            panic!("non-Transaction data");
        };
        let split_sum: Decimal = data
            .postings
            .iter()
            .filter(|p| p.account.ends_with(":Capital-Losses"))
            .filter_map(|p| p.units.as_ref())
            .filter_map(|u| Decimal::from_str(&u.number).ok())
            .sum();

        // Split sum must equal the original total exactly. The plugin
        // achieves this by setting the final segment to total minus
        // sum-of-rounded-prior-segments; if that branch breaks under
        // a particular (total, days) combination, this test catches it.
        proptest::prop_assert_eq!(
            split_sum, total_loss,
            "split sum ({}) must equal original total ({}) for {} -> {}",
            split_sum, total_loss, start_date, expiry_date
        );
    }
}

// ============================================================================
// CapitalGainsLongShortPlugin Tests
// ============================================================================
//
// `long_short` rebooks generic `Income:.*Capital-Gains` postings into
// `:Short` / `:Long` accounts based on holding period. The plugin
// classifies as long-term when the sale date is after the lot's one-year
// anniversary (held more than one calendar year), the same rule as the
// `capgains` report.
//
// Config format:
//   {'pattern': ['account_to_replace', 'short_replacement', 'long_replacement']}
//
// The plugin needs cost_date on each reduction posting to classify;
// without a cost date the transaction is left unchanged.

/// Build a sale transaction with cost.date set, plus a generic
/// `Income:Capital-Gains` posting that `long_short` can rewrite. The
/// asset, cash, and gain postings all live on one transaction
/// dated `entry_date`; the cost basis was acquired on `cost_date`.
fn make_long_short_sale(
    entry_date: &str,
    cost_date: &str,
    asset: (&str, &str), // (units, currency)
    cost: (&str, &str),  // (per, currency)
    price: (&str, &str), // (per, currency)
    gain_account: &str,
    gain_amount: (&str, &str),
) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: "transaction".to_string(),
        date: entry_date.to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Transaction(TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: "Sell with cost-dated lot".to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![
                PostingData {
                    account: "Assets:Stock".to_string(),
                    units: Some(AmountData {
                        number: asset.0.to_string(),
                        currency: asset.1.to_string(),
                    }),
                    cost: Some(CostData {
                        number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                            value: cost.0.to_string(),
                        }),
                        currency: Some(cost.1.to_string()),
                        date: Some(cost_date.to_string()),
                        label: None,
                        merge: false,
                    }),
                    price: Some(PriceAnnotationData {
                        is_total: false,
                        amount: Some(AmountData {
                            number: price.0.to_string(),
                            currency: price.1.to_string(),
                        }),
                        number: None,
                        currency: None,
                    }),
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
                PostingData {
                    account: "Assets:Cash".to_string(),
                    units: None,
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
                PostingData {
                    account: gain_account.to_string(),
                    units: Some(AmountData {
                        number: gain_amount.0.to_string(),
                        currency: gain_amount.1.to_string(),
                    }),
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
            ],
        }),
    }
}

const LONG_SHORT_CFG: &str =
    "{'Income:Capital-Gains': [':Capital-Gains', ':Capital-Gains:Short', ':Capital-Gains:Long']}";

/// No config string → plugin is a no-op (returns input unchanged).
#[test]
fn test_capital_gains_long_short_no_config_passthrough() {
    let plugin = CapitalGainsLongShortPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_transaction("2024-01-15", "Simple", vec![("Assets:Cash", "100", "USD")]),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    assert_eq!(output.directives.len(), 2);
}

/// Malformed config → the plugin changes nothing and says why, as
/// beancount's raises on a config `literal_eval` cannot read (#2601;
/// before, it passed the input through silently).
#[test]
fn test_capital_gains_long_short_invalid_config_passthrough() {
    let plugin = CapitalGainsLongShortPlugin;
    let input = make_input_with_config(
        vec![
            make_open("2024-01-01", "Assets:Cash"),
            make_transaction("2024-01-15", "Simple", vec![("Assets:Cash", "100", "USD")]),
        ],
        "this is not valid plugin config",
    );
    let output = process_and_materialize(&plugin, input);
    assert_eq!(output.errors.len(), 1, "{:?}", output.errors);
    assert!(
        output.errors[0]
            .message
            .starts_with("Invalid configuration for long_short"),
        "{}",
        output.errors[0].message
    );
    assert_eq!(output.directives.len(), 2);
}

/// Config valid but no posting matches the pattern → transaction
/// passes through unchanged (only the original directives, no
/// new Open directives).
#[test]
fn test_capital_gains_long_short_no_matching_postings_unchanged() {
    let plugin = CapitalGainsLongShortPlugin;
    let input = make_input_with_config(
        vec![
            make_open("2024-01-01", "Assets:Cash"),
            make_open("2024-01-01", "Expenses:Food"),
            make_transaction(
                "2024-01-15",
                "Buy lunch",
                vec![
                    ("Expenses:Food", "10", "USD"),
                    ("Assets:Cash", "-10", "USD"),
                ],
            ),
        ],
        LONG_SHORT_CFG,
    );
    let output = process_and_materialize(&plugin, input);
    assert_eq!(output.errors.len(), 0);
    assert_eq!(
        output.directives.len(),
        3,
        "no matching posting → no new Open directives, count unchanged"
    );
}

/// Sale held < 1 year → gain rebooks to `:Capital-Gains:Short`.
/// 6 months hold (Jan 15 → Jul 15) is well under the threshold.
#[test]
fn test_capital_gains_long_short_classifies_short_term() {
    let plugin = CapitalGainsLongShortPlugin;
    let input = make_input_with_config(
        vec![
            make_open("2024-01-01", "Assets:Stock"),
            make_open("2024-01-01", "Assets:Cash"),
            make_open("2024-01-01", "Income:Capital-Gains"),
            make_long_short_sale(
                "2024-07-15", // sold mid-year
                "2024-01-15", // bought 6 months earlier
                ("-10", "AAPL"),
                ("100", "USD"),
                ("150", "USD"),
                "Income:Capital-Gains",
                ("-500", "USD"),
            ),
        ],
        LONG_SHORT_CFG,
    );
    let output = process_and_materialize(&plugin, input);
    assert_eq!(output.errors.len(), 0);

    let txn = output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction")
        .expect("rewritten transaction should still be present");
    let DirectiveData::Transaction(data) = &txn.data else {
        panic!(
            "transaction directive_type with non-Transaction data: {:?}",
            txn.data
        );
    };

    let short_postings: Vec<&PostingData> = data
        .postings
        .iter()
        .filter(|p| p.account.contains(":Capital-Gains:Short"))
        .collect();
    assert_eq!(short_postings.len(), 1, "short_term gain rebooks to :Short");
    assert_eq!(
        data.postings
            .iter()
            .filter(|p| p.account.contains(":Capital-Gains:Long"))
            .count(),
        0,
        "no long-term posting expected"
    );

    // Pin the posting AMOUNT, not just the account. Plugin computes
    // gain = (cost - price) * |units| = (100 - 150) * 10 = -500.
    // Currency must come from the original generic posting.
    let short_units = short_postings[0]
        .units
        .as_ref()
        .expect("short posting must have units");
    assert_eq!(
        short_units.number, "-500",
        "short_term gain amount = (cost - price) * |units| = -500"
    );
    assert_eq!(short_units.currency, "USD");

    // Verify a new Open directive was generated for the new account.
    assert!(
        output.directives.iter().any(|d| {
            if let DirectiveData::Open(o) = &d.data {
                o.account.contains(":Capital-Gains:Short")
            } else {
                false
            }
        }),
        "plugin should emit Open for the new short-term account"
    );
}

/// Sale held > 1 year → gain rebooks to `:Capital-Gains:Long`.
/// Full 2-year hold removes any month/day boundary ambiguity.
#[test]
fn test_capital_gains_long_short_classifies_long_term() {
    let plugin = CapitalGainsLongShortPlugin;
    let input = make_input_with_config(
        vec![
            make_open("2022-01-01", "Assets:Stock"),
            make_open("2022-01-01", "Assets:Cash"),
            make_open("2022-01-01", "Income:Capital-Gains"),
            make_long_short_sale(
                "2024-07-15",
                "2022-01-15", // ~2.5 years held
                ("-10", "AAPL"),
                ("100", "USD"),
                ("150", "USD"),
                "Income:Capital-Gains",
                ("-500", "USD"),
            ),
        ],
        LONG_SHORT_CFG,
    );
    let output = process_and_materialize(&plugin, input);
    assert_eq!(output.errors.len(), 0);

    let txn = output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction")
        .expect("rewritten transaction should still be present");
    let DirectiveData::Transaction(data) = &txn.data else {
        panic!(
            "transaction directive_type with non-Transaction data: {:?}",
            txn.data
        );
    };

    let long_postings: Vec<&PostingData> = data
        .postings
        .iter()
        .filter(|p| p.account.contains(":Capital-Gains:Long"))
        .collect();
    assert_eq!(long_postings.len(), 1, "long_term gain rebooks to :Long");
    assert_eq!(
        data.postings
            .iter()
            .filter(|p| p.account.contains(":Capital-Gains:Short"))
            .count(),
        0,
        "no short-term posting expected"
    );

    // Pin the posting AMOUNT, not just the account. Plugin computes
    // gain = (cost - price) * |units| = (100 - 150) * 10 = -500.
    let long_units = long_postings[0]
        .units
        .as_ref()
        .expect("long posting must have units");
    assert_eq!(
        long_units.number, "-500",
        "long_term gain amount = (cost - price) * |units| = -500"
    );
    assert_eq!(long_units.currency, "USD");
}

/// Classify one sale and return which bucket its gain landed in.
fn long_short_bucket(entry_date: &str, cost_date: &str) -> &'static str {
    let plugin = CapitalGainsLongShortPlugin;
    let input = make_input_with_config(
        vec![
            make_open("2020-01-01", "Assets:Stock"),
            make_open("2020-01-01", "Assets:Cash"),
            make_open("2020-01-01", "Income:Capital-Gains"),
            make_long_short_sale(
                entry_date,
                cost_date,
                ("-10", "AAPL"),
                ("100", "USD"),
                ("150", "USD"),
                "Income:Capital-Gains",
                ("-500", "USD"),
            ),
        ],
        LONG_SHORT_CFG,
    );
    let output = process_and_materialize(&plugin, input);
    assert_eq!(output.errors.len(), 0);
    let DirectiveData::Transaction(data) = &output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction")
        .expect("transaction present")
        .data
    else {
        panic!("not a transaction");
    };
    let short = data
        .postings
        .iter()
        .filter(|p| p.account.ends_with(":Short"))
        .count();
    let long = data
        .postings
        .iter()
        .filter(|p| p.account.ends_with(":Long"))
        .count();
    match (short, long) {
        (1, 0) => "short",
        (0, 1) => "long",
        other => panic!("expected exactly one bucket, got (short, long) = {other:?}"),
    }
}

/// Long-term means held MORE than one calendar year: the sale must fall
/// after the acquisition's one-year anniversary. Pins the boundary on both
/// sides, a sale in the calendar year after the anniversary year (which a
/// month/day-only comparison misreads), and a leap-day acquisition.
#[test]
fn test_capital_gains_long_short_one_year_boundary() {
    let cases = [
        // (sold, acquired, expected)
        ("2025-09-02", "2024-09-03", "short"), // day before anniversary
        ("2025-09-03", "2024-09-03", "short"), // anniversary: exactly one year
        ("2025-09-04", "2024-09-03", "long"),  // day after anniversary
        ("2026-01-16", "2024-09-03", "long"),  // 500 days, earlier month-day
        ("2026-09-02", "2024-09-03", "long"),  // just under two years
        ("2025-12-31", "2025-01-15", "short"), // same calendar year span
        ("2025-12-31", "2024-01-15", "long"),  // 716 days, later month-day
        ("2025-02-28", "2024-02-29", "short"), // leap day: anniversary is Feb 28
        ("2025-03-01", "2024-02-29", "long"),
        ("2024-02-29", "2023-02-28", "long"), // sold on a leap day: 366 days, past Feb 28
        ("2025-01-31", "2024-01-31", "short"), // 31-day month end: anniversary
        ("2025-02-01", "2024-01-31", "long"), // 31-day month end: day after
        ("2024-09-03", "2024-09-03", "short"), // same-day sale
    ];
    // Collect every mismatch so one run reports all of them.
    let mismatches: Vec<String> = cases
        .iter()
        .filter_map(|&(sold, acquired, expected)| {
            let got = long_short_bucket(sold, acquired);
            (got != expected).then(|| {
                format!("acquired {acquired}, sold {sold}: expected {expected}, got {got}")
            })
        })
        .collect();
    assert!(mismatches.is_empty(), "{}", mismatches.join("\n"));
}

/// Reduction posting with NO cost date, generic `Income:Capital-Gains`
/// posting present. The plugin reaches the classification loop but
/// can't compute holding period from a date-less cost.
///
/// FIXED behavior (issue #1010): the plugin now falls through the
/// entire transaction unchanged when any reduction lacks a parseable
/// cost date. Pre-fix it would silently drop the generic Income:
/// Capital-Gains posting in the post-loop filter, leaving the
/// transaction unbalanced. This test pins the corrected behavior:
/// the original transaction (with the Income:Capital-Gains posting
/// intact) is preserved and no :Short/:Long replacement is emitted.
#[test]
fn test_capital_gains_long_short_no_cost_date_passes_through_unchanged() {
    let plugin = CapitalGainsLongShortPlugin;
    // Build a transaction with:
    //   - a reduction posting (cost+units+price), but cost.date = None
    //   - an Income:Capital-Gains posting (matches pattern → has_generic)
    //   - the cash leg
    // make_transaction_with_cost_and_price doesn't set cost.date and
    // produces only asset+cash, so we build inline to add the third
    // posting.
    let txn = DirectiveWrapper {
        directive_type: "transaction".to_string(),
        date: "2024-07-15".to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Transaction(TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: "Sell with no-date cost".to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![
                PostingData {
                    account: "Assets:Stock".to_string(),
                    units: Some(AmountData {
                        number: "-10".to_string(),
                        currency: "AAPL".to_string(),
                    }),
                    cost: Some(CostData {
                        number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                            value: "100".to_string(),
                        }),
                        currency: Some("USD".to_string()),
                        date: None, // ← the branch under test
                        label: None,
                        merge: false,
                    }),
                    price: Some(PriceAnnotationData {
                        is_total: false,
                        amount: Some(AmountData {
                            number: "150".to_string(),
                            currency: "USD".to_string(),
                        }),
                        number: None,
                        currency: None,
                    }),
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
                PostingData {
                    account: "Assets:Cash".to_string(),
                    units: None,
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
                PostingData {
                    account: "Income:Capital-Gains".to_string(),
                    units: Some(AmountData {
                        number: "-500".to_string(),
                        currency: "USD".to_string(),
                    }),
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
            ],
        }),
    };
    let input = make_input_with_config(
        vec![
            make_open("2024-01-01", "Assets:Stock"),
            make_open("2024-01-01", "Assets:Cash"),
            make_open("2024-01-01", "Income:Capital-Gains"),
            txn,
        ],
        LONG_SHORT_CFG,
    );
    let output = process_and_materialize(&plugin, input);
    assert_eq!(output.errors.len(), 0);

    let txn = output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction")
        .expect("transaction still present");
    let DirectiveData::Transaction(data) = &txn.data else {
        panic!(
            "non-Transaction data on transaction directive: {:?}",
            txn.data
        );
    };

    // No :Short or :Long replacement is emitted — the plugin now
    // falls through entirely when classification is impossible.
    assert_eq!(
        data.postings
            .iter()
            .filter(|p| p.account.contains(":Capital-Gains:Short")
                || p.account.contains(":Capital-Gains:Long"))
            .count(),
        0,
        "no Short/Long postings emitted when cost_date is missing"
    );

    // The generic Income:Capital-Gains posting is PRESERVED — the
    // pre-fix behavior of silently dropping it (issue #1010) would
    // leave the transaction unbalanced. The fix: skip the whole
    // transaction when any reduction lacks a cost date.
    assert_eq!(
        data.postings
            .iter()
            .filter(|p| p.account == "Income:Capital-Gains")
            .count(),
        1,
        "generic Income:Capital-Gains posting must be preserved when \
         the plugin falls through (issue #1010 fix)"
    );

    // The full transaction is unchanged — same number of postings as
    // input (asset + cash + Income:Capital-Gains = 3).
    assert_eq!(
        data.postings.len(),
        3,
        "all three input postings preserved on fall-through"
    );
}

// ============================================================================
// CapitalGainsGainLossPlugin Tests
// ============================================================================
//
// `gain_loss` rebooks postings whose account matches the configured
// pattern: NEGATIVE units → `gains_replacement` (income is -ve in
// double-entry), POSITIVE units → `losses_replacement`.
//
// Config:
//   {'pattern': ['account_to_replace', 'gains_replacement', 'losses_replacement']}
//
// Doesn't compute amounts — just renames accounts.

const GAIN_LOSS_CFG: &str =
    "{'Income:Capital-Gains:Long': [':Long', ':Long:Gains', ':Long:Losses']}";

#[test]
fn test_capital_gains_gain_loss_no_config_passthrough() {
    let plugin = CapitalGainsGainLossPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_transaction("2024-01-15", "Simple", vec![("Assets:Cash", "100", "USD")]),
    ]);
    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty());
    assert_eq!(output.directives.len(), 2);
}

/// Malformed config → the plugin changes nothing and says why (#2601).
#[test]
fn test_capital_gains_gain_loss_invalid_config_passthrough() {
    let plugin = CapitalGainsGainLossPlugin;
    let input = make_input_with_config(
        vec![
            make_open("2024-01-01", "Assets:Cash"),
            make_transaction("2024-01-15", "Simple", vec![("Assets:Cash", "100", "USD")]),
        ],
        "{ malformed",
    );
    let output = process_and_materialize(&plugin, input);
    assert_eq!(output.errors.len(), 1, "{:?}", output.errors);
    assert!(
        output.errors[0]
            .message
            .starts_with("Invalid configuration for gain_loss"),
        "{}",
        output.errors[0].message
    );
    assert_eq!(output.directives.len(), 2);
}

/// Negative posting on a matching account → renamed to gains
/// replacement (`:Long` → `:Long:Gains`).
#[test]
fn test_capital_gains_gain_loss_negative_renames_to_gains() {
    let plugin = CapitalGainsGainLossPlugin;
    let input = make_input_with_config(
        vec![
            make_open("2024-01-01", "Assets:Broker"),
            make_open("2024-01-01", "Income:Capital-Gains:Long"),
            make_transaction(
                "2024-01-15",
                "Sell with gain",
                vec![
                    ("Assets:Broker", "1000", "USD"),
                    ("Income:Capital-Gains:Long", "-100", "USD"),
                ],
            ),
        ],
        GAIN_LOSS_CFG,
    );
    let output = process_and_materialize(&plugin, input);
    assert_eq!(output.errors.len(), 0);

    let txn = output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction")
        .expect("transaction still present");
    let DirectiveData::Transaction(data) = &txn.data else {
        panic!(
            "non-Transaction data on transaction directive: {:?}",
            txn.data
        );
    };
    let renamed = data
        .postings
        .iter()
        .find(|p| p.account == "Income:Capital-Gains:Long:Gains")
        .unwrap_or_else(|| {
            panic!(
                "negative posting should rebook to ...:Gains; got: {:?}",
                data.postings.iter().map(|p| &p.account).collect::<Vec<_>>()
            )
        });
    // Plugin only renames the account — units must be preserved
    // exactly. Pinning the amount catches any future "rename + reset"
    // bug where the account changes but the value is dropped or
    // mutated.
    let renamed_units = renamed
        .units
        .as_ref()
        .expect("renamed posting must keep its units");
    assert_eq!(
        renamed_units.number, "-100",
        "rename preserves the original units value"
    );
    assert_eq!(renamed_units.currency, "USD");
    assert!(
        !data
            .postings
            .iter()
            .any(|p| p.account == "Income:Capital-Gains:Long"),
        "original posting should have been renamed away"
    );
}

/// Positive posting on a matching account → renamed to losses
/// replacement.
#[test]
fn test_capital_gains_gain_loss_positive_renames_to_losses() {
    let plugin = CapitalGainsGainLossPlugin;
    let input = make_input_with_config(
        vec![
            make_open("2024-01-01", "Assets:Broker"),
            make_open("2024-01-01", "Income:Capital-Gains:Long"),
            make_transaction(
                "2024-01-15",
                "Sell at loss",
                vec![
                    ("Assets:Broker", "-100", "USD"),
                    ("Income:Capital-Gains:Long", "100", "USD"),
                ],
            ),
        ],
        GAIN_LOSS_CFG,
    );
    let output = process_and_materialize(&plugin, input);
    assert_eq!(output.errors.len(), 0);

    let txn = output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction")
        .expect("transaction still present");
    let DirectiveData::Transaction(data) = &txn.data else {
        panic!(
            "non-Transaction data on transaction directive: {:?}",
            txn.data
        );
    };
    let renamed = data
        .postings
        .iter()
        .find(|p| p.account == "Income:Capital-Gains:Long:Losses")
        .unwrap_or_else(|| {
            panic!(
                "positive posting should rebook to ...:Losses; got: {:?}",
                data.postings.iter().map(|p| &p.account).collect::<Vec<_>>()
            )
        });
    let renamed_units = renamed
        .units
        .as_ref()
        .expect("renamed posting must keep its units");
    assert_eq!(
        renamed_units.number, "100",
        "rename preserves the original units value"
    );
    assert_eq!(renamed_units.currency, "USD");
}

/// Posting on a non-matching account → unchanged. Pins that the
/// pattern is required for any rewriting.
#[test]
fn test_capital_gains_gain_loss_pattern_no_match_unchanged() {
    let plugin = CapitalGainsGainLossPlugin;
    // Pattern matches `Income:Capital-Gains:Long`, but our posting
    // is on `Income:Capital-Gains:Short`.
    let input = make_input_with_config(
        vec![
            make_open("2024-01-01", "Assets:Broker"),
            make_open("2024-01-01", "Income:Capital-Gains:Short"),
            make_transaction(
                "2024-01-15",
                "Short-term sale",
                vec![
                    ("Assets:Broker", "1000", "USD"),
                    ("Income:Capital-Gains:Short", "-100", "USD"),
                ],
            ),
        ],
        GAIN_LOSS_CFG,
    );
    let output = process_and_materialize(&plugin, input);

    let txn = output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction")
        .expect("transaction still present");
    let DirectiveData::Transaction(data) = &txn.data else {
        panic!(
            "non-Transaction data on transaction directive: {:?}",
            txn.data
        );
    };
    assert!(
        data.postings
            .iter()
            .any(|p| p.account == "Income:Capital-Gains:Short"),
        "non-matching account should be left untouched"
    );
}

/// Zero units on a matching account → renamed to losses (the plugin
/// treats `>= 0` as the losses branch). Pins the boundary so a
/// future "treat zero as no-op" change is caught.
#[test]
fn test_capital_gains_gain_loss_zero_renames_to_losses() {
    let plugin = CapitalGainsGainLossPlugin;
    let input = make_input_with_config(
        vec![
            make_open("2024-01-01", "Assets:Broker"),
            make_open("2024-01-01", "Income:Capital-Gains:Long"),
            make_transaction(
                "2024-01-15",
                "Zero-amount edge case",
                vec![
                    ("Assets:Broker", "0", "USD"),
                    ("Income:Capital-Gains:Long", "0", "USD"),
                ],
            ),
        ],
        GAIN_LOSS_CFG,
    );
    let output = process_and_materialize(&plugin, input);

    let txn = output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction")
        .expect("transaction still present");
    let DirectiveData::Transaction(data) = &txn.data else {
        panic!(
            "non-Transaction data on transaction directive: {:?}",
            txn.data
        );
    };
    let renamed = data
        .postings
        .iter()
        .find(|p| p.account == "Income:Capital-Gains:Long:Losses")
        .unwrap_or_else(|| {
            panic!(
                "zero posting goes to :Losses (the >= 0 branch); got: {:?}",
                data.postings.iter().map(|p| &p.account).collect::<Vec<_>>()
            )
        });
    let renamed_units = renamed
        .units
        .as_ref()
        .expect("renamed posting must keep its units");
    assert_eq!(
        renamed_units.number, "0",
        "zero amount preserved through the rename"
    );
}

/// `split_expenses` must split on a RENAMED expense root (#1964).
///
/// It previously classified with `account_type(..) == "expenses"`, which
/// hardcodes the English roots — so on `option "name_expenses" "Depenses"`
/// nothing was an expense, nothing split, and the plugin exited cleanly having
/// done nothing. There was no error to notice.
///
/// The neighboring test above is the same scenario on an UNRENAMED ledger, so
/// the pair separates "splitting works" from "splitting works on this ledger".
#[test]
fn test_split_expenses_splits_a_renamed_expense_root() {
    let plugin = SplitExpensesPlugin;
    let mut input = make_input_with_config(
        vec![
            make_open("2024-01-01", "Depenses:Food"),
            make_open("2024-01-01", "Assets:Cash"),
            make_transaction(
                "2024-01-15",
                "Lunch",
                vec![
                    ("Depenses:Food", "100", "USD"),
                    ("Assets:Cash", "-100", "USD"),
                ],
            ),
        ],
        "Alice Bob",
    );
    input.options.account_types = PluginAccountTypes {
        expenses: "Depenses".to_string(),
        ..PluginAccountTypes::default()
    };

    let output = process_and_materialize(&plugin, input);
    assert!(output.errors.is_empty(), "{:?}", output.errors);

    let expense_postings = output
        .directives
        .iter()
        .filter_map(|d| match &d.data {
            DirectiveData::Transaction(t) => Some(t),
            _ => None,
        })
        .flat_map(|t| t.postings.iter())
        .filter(|p| p.account.starts_with("Depenses:"))
        .count();

    assert_eq!(
        expense_postings, 2,
        "one sub-posting per member; 1 means the renamed root was not \
         recognized and nothing split",
    );
}

// ============================================================================
// Alignment with beancount's implementations (#2539)
// ============================================================================
//
// Each message below is the text bean-check prints for the same input,
// checked against beancount 3.

/// `w` with a source location.
fn located(mut w: DirectiveWrapper, line: u32) -> DirectiveWrapper {
    w.filename = Some("ledger.beancount".to_string());
    w.lineno = Some(line);
    w
}

fn messages(output: &PluginOutput) -> Vec<&str> {
    output.errors.iter().map(|e| e.message.as_str()).collect()
}

fn wrap(date: &str, directive_type: &str, data: DirectiveData) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: directive_type.to_string(),
        date: date.to_string(),
        filename: None,
        lineno: None,
        data,
    }
}

/// An `open`'s currencies, a price annotation's currency, and a cost's
/// count as uses; each currency is reported once, with the first account
/// (sorted) using it, or the price context; and the config exempts a
/// currency in matching accounts.
#[test]
fn check_commodity_reports_as_beancount_does() {
    let input = make_input(vec![
        make_open_with_currencies("2024-01-01", "Assets:Broker", vec!["CAD"]),
        make_transaction_with_price(
            "2024-01-02",
            "fx",
            "Assets:Bank",
            ("10", "EUR"),
            ("1.1", "USD"),
            "Assets:Cash",
        ),
        make_transaction_with_cost(
            "2024-01-03",
            "buy",
            "Assets:Stock",
            ("1", "HOOL"),
            ("5", "GBP"),
            "Assets:Cash",
        ),
        make_price("2024-01-04", "JPY", "0.01", "CHF"),
        make_commodity("2024-01-01", "EUR"),
    ]);
    let output = CheckCommodityPlugin.process(input);
    assert_eq!(
        messages(&output),
        [
            "Missing Commodity directive for 'USD' in 'Assets:Bank'",
            "Missing Commodity directive for 'CAD' in 'Assets:Broker'",
            "Missing Commodity directive for 'GBP' in 'Assets:Stock'",
            "Missing Commodity directive for 'HOOL' in 'Assets:Stock'",
            "Missing Commodity directive for 'CHF' in 'Price Directive Context'",
            "Missing Commodity directive for 'JPY' in 'Price Directive Context'",
        ]
    );
    assert!(
        output
            .errors
            .iter()
            .all(|e| e.severity == PluginErrorSeverity::Error)
    );

    let input = make_input_with_config(
        vec![
            make_transaction(
                "2024-01-02",
                "x",
                vec![
                    ("Assets:Options", "1", "SPX_1P"),
                    ("Assets:Cash", "-1", "SPX_1P"),
                ],
            ),
            make_price("2024-01-04", "SPX_1P", "1", "USD"),
        ],
        "{'Assets:Opt.*': 'SPX_.*'}",
    );
    // Exempt in Assets:Options, so its price is not reported either; not
    // in Assets:Cash, which sorts first and reports it.
    assert_eq!(
        messages(&CheckCommodityPlugin.process(input)),
        [
            "Missing Commodity directive for 'SPX_1P' in 'Assets:Cash'",
            "Missing Commodity directive for 'USD' in 'Price Directive Context'",
        ]
    );
    let input = make_input_with_config(vec![], "['not', 'a', 'dict']");
    assert_eq!(
        messages(&CheckCommodityPlugin.process(input)),
        ["Invalid configuration for check_commodity plugin; skipping."]
    );
}

/// One error per parent account, at its `open`, in tree order; a `pad`
/// posts, a `note` does not (the documented divergence from beancount).
#[test]
fn leafonly_reports_once_per_account_at_its_open() {
    let input = make_input(vec![
        located(make_open("2024-01-01", "Assets:B"), 2),
        located(make_open("2024-01-01", "Assets:B:Sub"), 3),
        located(make_open("2024-01-01", "Assets:A"), 4),
        located(make_open("2024-01-01", "Assets:A:Sub"), 5),
        located(make_open("2024-01-01", "Equity:E"), 6),
        located(make_open("2024-01-01", "Equity:E:Sub"), 7),
        located(make_open("2024-01-01", "Assets:N"), 8),
        located(make_open("2024-01-01", "Assets:N:Sub"), 9),
        make_transaction(
            "2024-01-02",
            "a",
            vec![("Assets:B", "1", "USD"), ("Assets:B:Sub", "-1", "USD")],
        ),
        make_transaction(
            "2024-01-03",
            "b",
            vec![("Assets:B", "1", "USD"), ("Assets:A", "-1", "USD")],
        ),
        wrap(
            "2024-01-04",
            "pad",
            DirectiveData::Pad(PadData {
                account: "Assets:A:Sub".to_string(),
                source_account: "Equity:E".to_string(),
                metadata: vec![],
            }),
        ),
        wrap(
            "2024-01-04",
            "note",
            DirectiveData::Note(NoteData {
                account: "Assets:N".to_string(),
                comment: "hi".to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
            }),
        ),
    ]);
    let output = LeafOnlyPlugin.process(input);
    assert_eq!(
        messages(&output),
        [
            "Non-leaf account 'Assets:A' has postings on it",
            "Non-leaf account 'Assets:B' has postings on it",
            "Non-leaf account 'Equity:E' has postings on it",
        ]
    );
    let lines: Vec<_> = output.errors.iter().map(|e| e.line_number).collect();
    assert_eq!(lines, [Some(4), Some(2), Some(6)]);
}

/// A currency held at cost in one posting and without cost (no price
/// needed) in another, located at the first one without cost.
#[test]
fn coherent_cost_reports_with_and_without_cost() {
    let input = make_input(vec![
        make_transaction_with_cost(
            "2024-01-02",
            "buy",
            "Assets:Stock",
            ("1", "HOOL"),
            ("5", "USD"),
            "Assets:Cash",
        ),
        located(
            make_transaction(
                "2024-01-03",
                "gift",
                vec![("Assets:Stock", "1", "HOOL"), ("Income:Gift", "-1", "HOOL")],
            ),
            8,
        ),
    ]);
    let output = CoherentCostPlugin.process(input);
    assert_eq!(
        messages(&output),
        ["Currency 'HOOL' is used both with and without cost"]
    );
    assert_eq!(output.errors[0].line_number, Some(8));
}

/// The config's account regex, the `onecommodity: FALSE` opt-out, an
/// `open` listing several currencies, cost currencies and balances.
#[test]
fn onecommodity_honors_config_opt_out_costs_and_balances() {
    let mut opted_out = make_open("2024-01-01", "Assets:Free");
    if let DirectiveData::Open(open) = &mut opted_out.data {
        open.metadata
            .push(("onecommodity".to_string(), MetaValueData::Bool(false)));
    }
    let two = |date: &str, account: &'static str| {
        vec![
            make_transaction(
                date,
                "u",
                vec![(account, "1", "USD"), ("Equity:X", "-1", "USD")],
            ),
            make_transaction(
                date,
                "e",
                vec![(account, "1", "EUR"), ("Equity:X", "-1", "EUR")],
            ),
        ]
    };
    let mut directives = vec![
        opted_out,
        make_open_with_currencies("2024-01-01", "Assets:Multi", vec!["USD", "EUR"]),
        make_open("2024-01-01", "Equity:X"),
        make_open("2024-01-01", "Assets:Lots"),
        make_transaction_with_cost(
            "2024-01-02",
            "a",
            "Assets:Lots",
            ("1", "HOOL"),
            ("5", "USD"),
            "Equity:X",
        ),
        make_transaction_with_cost(
            "2024-01-03",
            "b",
            "Assets:Lots",
            ("1", "HOOL"),
            ("5", "EUR"),
            "Equity:X",
        ),
        wrap(
            "2024-01-04",
            "balance",
            DirectiveData::Balance(BalanceData {
                account: "Assets:Bal".to_string(),
                amount: AmountData {
                    number: "0".to_string(),
                    currency: "CAD".to_string(),
                },
                tolerance: None,
                metadata: vec![],
            }),
        ),
        make_transaction(
            "2024-01-05",
            "c",
            vec![("Assets:Bal", "1", "USD"), ("Equity:X", "-1", "USD")],
        ),
    ];
    directives.extend(two("2024-01-02", "Assets:Free"));
    directives.extend(two("2024-01-02", "Assets:Multi"));
    let output = OneCommodityPlugin.process(make_input(directives.clone()));
    assert_eq!(
        messages(&output),
        [
            "More than one currency in account 'Assets:Bal': CAD,USD",
            "More than one currency in account 'Equity:X': EUR,USD",
            "More than one cost currency in account 'Assets:Lots': EUR,USD",
        ]
    );
    // An account whose `open` the regex does not match at the start is
    // skipped; one with no `open` (Assets:Bal) is checked, as in beancount.
    let output = OneCommodityPlugin.process(make_input_with_config(directives, "Assets:B"));
    assert_eq!(
        messages(&output),
        ["More than one currency in account 'Assets:Bal': CAD,USD"]
    );
}

/// beancount's `unique_prices` locates the error at the last entry holding
/// the first number given.
#[test]
fn unique_prices_locates_as_beancount_does() {
    let input = make_input(vec![
        located(make_price("2024-01-15", "HOOL", "10", "USD"), 3),
        located(make_price("2024-01-15", "HOOL", "10.0", "USD"), 4),
        located(make_price("2024-01-15", "HOOL", "11", "USD"), 5),
    ]);
    let output = UniquePricesPlugin.process(input);
    assert_eq!(messages(&output), ["Disagreeing price entries"]);
    assert_eq!(output.errors[0].line_number, Some(4));
}

/// A tuple of allowed values, as beancount's examples write them, is
/// checked; the messages are beancount's, at the `commodity` directive.
#[test]
fn commodity_attr_reads_tuples_and_reports_as_beancount_does() {
    let mut eur = located(make_commodity("2024-01-01", "EUR"), 7);
    if let DirectiveData::Commodity(c) = &mut eur.data {
        c.metadata.push((
            "asset-class".to_string(),
            MetaValueData::String("bogus".to_string()),
        ));
    }
    let input = make_input_with_config(
        vec![located(make_commodity("2024-01-01", "USD"), 6), eur],
        "{'name': None, 'asset-class': ('stock', 'bond')}",
    );
    let output = CommodityAttrPlugin::new().process(input);
    assert_eq!(
        messages(&output),
        [
            "Missing attribute 'name' for Commodity directive USD",
            "Missing attribute 'asset-class' for Commodity directive USD",
            "Missing attribute 'name' for Commodity directive EUR",
            "Invalid value 'bogus' for attribute asset-class, Commodity directive EUR; \
             valid options: stock, bond",
        ]
    );
    let lines: Vec<_> = output.errors.iter().map(|e| e.line_number).collect();
    assert_eq!(lines, [Some(6), Some(6), Some(7), Some(7)]);
    let input = make_input_with_config(vec![], "['name']");
    assert_eq!(
        messages(&CommodityAttrPlugin::new().process(input)),
        ["Invalid configuration for commodity_attr plugin; skipping."]
    );
}

/// The duplicate is reported at the later copy, starting as beancount's
/// message does.
#[test]
fn noduplicates_locates_the_later_copy() {
    let txn = || {
        make_transaction(
            "2024-01-02",
            "Lunch",
            vec![
                ("Assets:Bank", "-10", "USD"),
                ("Expenses:Food", "10", "USD"),
            ],
        )
    };
    let output = NoDuplicatesPlugin.process(make_input(vec![located(txn(), 5), located(txn(), 8)]));
    assert_eq!(messages(&output), ["Duplicate entry: 2024-01-02 \"Lunch\""]);
    assert_eq!(output.errors[0].line_number, Some(8));
}

// ============================================================================
// CheckOptionExpiryPlugin Tests
// ============================================================================

use rustledger_plugin::native::CheckOptionExpiryPlugin;

const OPT_ACCT: &str = "Assets:Broker:Options";
const CASH_ACCT: &str = "Assets:Broker:Cash";

/// One option leg against cash. `units` is signed contracts: `-1` sells to
/// open (or closes a long), `1` buys to open (or closes a short).
fn option_txn(date: &str, account: &str, units: &str, symbol: &str) -> DirectiveWrapper {
    make_transaction(
        date,
        "option leg",
        vec![(account, units, symbol), (CASH_ACCT, "0", "USD")],
    )
}

/// A transaction with no option postings, used to move the ledger's last
/// date forward.
fn later_entry(date: &str) -> DirectiveWrapper {
    make_transaction(
        date,
        "unrelated",
        vec![
            (CASH_ACCT, "-1.00", "USD"),
            ("Expenses:Fees", "1.00", "USD"),
        ],
    )
}

fn option_expiry_errors(directives: Vec<DirectiveWrapper>) -> Vec<PluginError> {
    let plugin = CheckOptionExpiryPlugin;
    let mut all = vec![
        make_open("2026-01-01", OPT_ACCT),
        make_open("2026-01-01", CASH_ACCT),
        make_open("2026-01-01", "Expenses:Fees"),
    ];
    all.extend(directives);
    let input = make_input(all);
    let n = input.directives.len();
    let output = process_and_materialize(&plugin, input);
    // The plugin never inserts, deletes, or modifies directives.
    assert_eq!(output.directives.len(), n);
    output.errors
}

/// T01: a short closed before expiry is not reported.
#[test]
fn test_option_expiry_closed_before_expiry() {
    let errors = option_expiry_errors(vec![
        option_txn("2026-09-02", OPT_ACCT, "-1", "AAPL261016P00230000"),
        option_txn("2026-09-20", OPT_ACCT, "1", "AAPL261016P00230000"),
        later_entry("2026-11-01"),
    ]);
    assert_eq!(errors.len(), 0, "{errors:?}");
}

/// T02: a close dated on the expiry day itself is not reported.
#[test]
fn test_option_expiry_closed_on_expiry_day() {
    let errors = option_expiry_errors(vec![
        option_txn("2026-09-02", OPT_ACCT, "-1", "AAPL261016P00230000"),
        option_txn("2026-10-16", OPT_ACCT, "1", "AAPL261016P00230000"),
        later_entry("2026-11-01"),
    ]);
    assert_eq!(errors.len(), 0, "{errors:?}");
}

/// T03: a short left open past expiry is reported once, at the opening
/// entry, naming the symbol, expiry date, quantity, and account.
#[test]
fn test_option_expiry_short_left_open() {
    let mut open = option_txn("2026-09-02", OPT_ACCT, "-1", "AAPL261016P00230000");
    open.filename = Some("ledger.beancount".to_string());
    open.lineno = Some(42);
    let errors = option_expiry_errors(vec![open, later_entry("2026-10-17")]);
    assert_eq!(errors.len(), 1, "{errors:?}");
    let e = &errors[0];
    assert_eq!(e.severity, PluginErrorSeverity::Error);
    assert_eq!(
        e.message,
        "AAPL261016P00230000 expired 2026-10-16 but -1 contract(s) remain open in Assets:Broker:Options"
    );
    assert_eq!(e.source_file.as_deref(), Some("ledger.beancount"));
    assert_eq!(e.line_number, Some(42));
}

/// T04: a long left open past expiry is reported.
#[test]
fn test_option_expiry_long_left_open() {
    let errors = option_expiry_errors(vec![
        option_txn("2026-09-03", OPT_ACCT, "1", "SPXW261030C06800000"),
        later_entry("2026-11-02"),
    ]);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].message.contains(" but 1 contract(s) "),
        "{errors:?}"
    );
}

/// T05: an open contract is not reported when the ledger ends on or
/// before its expiry date.
#[test]
fn test_option_expiry_ledger_ends_before_expiry() {
    let on_expiry = option_expiry_errors(vec![
        option_txn("2026-09-02", OPT_ACCT, "-1", "AAPL261016P00230000"),
        later_entry("2026-10-16"),
    ]);
    assert_eq!(on_expiry.len(), 0, "{on_expiry:?}");

    let before = option_expiry_errors(vec![option_txn(
        "2026-09-02",
        OPT_ACCT,
        "-1",
        "AAPL261016P00230000",
    )]);
    assert_eq!(before.len(), 0, "{before:?}");
}

/// T06: the same contract in two accounts is tracked per account.
#[test]
fn test_option_expiry_tracked_per_account() {
    let ira = "Assets:IRA:Options";
    let errors = option_expiry_errors(vec![
        make_open("2026-01-01", ira),
        option_txn("2026-09-02", OPT_ACCT, "-1", "AAPL261016P00230000"),
        option_txn("2026-09-02", ira, "-1", "AAPL261016P00230000"),
        option_txn("2026-09-20", OPT_ACCT, "1", "AAPL261016P00230000"),
        later_entry("2026-11-01"),
    ]);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].message.ends_with(ira), "{errors:?}");
}

/// T07: a partial close reports only the remaining quantity.
#[test]
fn test_option_expiry_partial_close() {
    let errors = option_expiry_errors(vec![
        option_txn("2026-09-02", OPT_ACCT, "-3", "AAPL261016P00232500"),
        option_txn("2026-09-20", OPT_ACCT, "2", "AAPL261016P00232500"),
        later_entry("2026-11-01"),
    ]);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].message.contains(" but -1 contract(s) "),
        "{errors:?}"
    );
}

/// T08: commodities that are not valid OCC option symbols are ignored.
#[test]
fn test_option_expiry_ignores_non_option_commodities() {
    let errors = option_expiry_errors(vec![
        option_txn("2026-09-02", OPT_ACCT, "100", "AAPL"),
        option_txn("2026-09-02", OPT_ACCT, "-1", "AAPL261316P00230000"), // month 13
        option_txn("2026-09-02", OPT_ACCT, "-1", "AAPL261032P00230000"), // day 32
        option_txn("2026-09-02", OPT_ACCT, "-1", "AAPL261016X00230000"), // not C/P
        option_txn("2026-09-02", OPT_ACCT, "-1", "AAPL261016P0023000"),  // 7 strike digits
        option_txn("2026-09-02", OPT_ACCT, "-1", "TOOLONGX261016P00230000"), // root > 6
        later_entry("2027-01-01"),
    ]);
    assert_eq!(errors.len(), 0, "{errors:?}");
}

/// T09: a roll closes the old leg and opens a later one; neither is
/// reported while the new leg has not expired.
#[test]
fn test_option_expiry_roll() {
    let roll = make_transaction(
        "2026-09-15",
        "roll",
        vec![
            (OPT_ACCT, "1", "AAPL260918C00270000"),
            (OPT_ACCT, "-1", "AAPL261016C00280000"),
            (CASH_ACCT, "0", "USD"),
        ],
    );
    let errors = option_expiry_errors(vec![
        option_txn("2026-09-05", OPT_ACCT, "-1", "AAPL260918C00270000"),
        roll,
        later_entry("2026-10-01"),
    ]);
    assert_eq!(errors.len(), 0, "{errors:?}");
}

/// T10: each expired open contract is reported separately.
#[test]
fn test_option_expiry_two_contracts() {
    let errors = option_expiry_errors(vec![
        option_txn("2026-09-02", OPT_ACCT, "-1", "AAPL261016P00230000"),
        option_txn("2026-09-03", OPT_ACCT, "1", "SPY261016C00700000"),
        later_entry("2026-11-01"),
    ]);
    assert_eq!(errors.len(), 2, "{errors:?}");
}

/// `w` with a line number, so a test can tell which entry an error names.
fn at_line(mut w: DirectiveWrapper, line: u32) -> DirectiveWrapper {
    w.filename = Some("ledger.beancount".to_string());
    w.lineno = Some(line);
    w
}

/// A short that a single larger buy turns long is a new position: the
/// error names the entry that crossed zero, not the old sell-to-open.
#[test]
fn test_option_expiry_sign_change_reopens() {
    let errors = option_expiry_errors(vec![
        at_line(
            option_txn("2026-09-02", OPT_ACCT, "-1", "AAPL261016P00230000"),
            7,
        ),
        at_line(
            option_txn("2026-09-10", OPT_ACCT, "2", "AAPL261016P00230000"),
            11,
        ),
        later_entry("2026-11-01"),
    ]);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].message.contains(" but 1 contract(s) "),
        "{errors:?}"
    );
    assert_eq!(errors[0].line_number, Some(11));

    let errors = option_expiry_errors(vec![
        at_line(
            option_txn("2026-09-02", OPT_ACCT, "2", "AAPL261016P00230000"),
            7,
        ),
        at_line(
            option_txn("2026-09-10", OPT_ACCT, "-3", "AAPL261016P00230000"),
            11,
        ),
        later_entry("2026-11-01"),
    ]);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].message.contains(" but -1 contract(s) "),
        "{errors:?}"
    );
    assert_eq!(errors[0].line_number, Some(11));
}

/// Each entry's legs are netted first, so posting order inside one entry
/// doesn't move the error, and an entry whose legs cancel changes nothing.
#[test]
fn test_option_expiry_nets_each_entry() {
    for (first, second) in [("1", "-1"), ("-1", "1")] {
        let cancelling = make_transaction(
            "2026-09-10",
            "cancelling legs",
            vec![
                (OPT_ACCT, first, "AAPL261016P00230000"),
                (OPT_ACCT, second, "AAPL261016P00230000"),
            ],
        );
        let errors = option_expiry_errors(vec![
            at_line(
                option_txn("2026-09-02", OPT_ACCT, "-1", "AAPL261016P00230000"),
                7,
            ),
            at_line(cancelling, 11),
            later_entry("2026-11-01"),
        ]);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert_eq!(errors[0].line_number, Some(7), "order {first}, {second}");
    }
}

/// Two openers that stack without going flat: reported at the first.
#[test]
fn test_option_expiry_stacked_openers() {
    let errors = option_expiry_errors(vec![
        at_line(
            option_txn("2026-09-02", OPT_ACCT, "-1", "AAPL261016P00230000"),
            7,
        ),
        at_line(
            option_txn("2026-09-05", OPT_ACCT, "-1", "AAPL261016P00230000"),
            11,
        ),
        later_entry("2026-11-01"),
    ]);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].message.contains(" but -2 contract(s) "),
        "{errors:?}"
    );
    assert_eq!(errors[0].line_number, Some(7));
}

/// Roots with digits and dots (adjusted contracts, share classes), and the
/// shortest and longest root lengths, are all checked.
#[test]
fn test_option_expiry_root_shapes() {
    let roots = ["XYZ1", "BRK.B", "ABCDEF", "F"];
    let mut directives: Vec<DirectiveWrapper> = roots
        .iter()
        .map(|r| option_txn("2026-09-02", OPT_ACCT, "-1", &format!("{r}261016C00050000")))
        .collect();
    directives.push(later_entry("2026-11-01"));
    let errors = option_expiry_errors(directives);
    assert_eq!(errors.len(), 4, "{errors:?}");
}

/// A count of 100 prints as `100`, not `1E+2`.
#[test]
fn test_option_expiry_hundred_contracts_message() {
    let errors = option_expiry_errors(vec![
        option_txn("2026-09-02", OPT_ACCT, "100", "AAPL261016P00230000"),
        later_entry("2026-11-01"),
    ]);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(
        errors[0].message,
        "AAPL261016P00230000 expired 2026-10-16 but 100 contract(s) remain open in Assets:Broker:Options"
    );
}

/// A directive from file `file` at line `line`.
fn located_at(mut w: DirectiveWrapper, file: &str, line: u32) -> DirectiveWrapper {
    w.filename = Some(file.to_string());
    w.lineno = Some(line);
    w
}

/// Same-day entries are walked in beancount's `entry_sortkey` order (date,
/// type, line), not in file order, so a position opened by two same-day
/// buys in two files is reported at the one with the lower line, as
/// `bean-check` reports it. The input lists `main.beancount:16` first, as
/// the loader does when `other.beancount` is included after it.
#[test]
fn test_option_expiry_same_day_entries_sorted_by_line() {
    let errors = option_expiry_errors(vec![
        located_at(
            option_txn("2026-09-02", OPT_ACCT, "1", "AAPL261016P00230000"),
            "main.beancount",
            16,
        ),
        located_at(
            option_txn("2026-09-02", OPT_ACCT, "1", "AAPL261016P00230000"),
            "other.beancount",
            1,
        ),
        later_entry("2026-11-01"),
    ]);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(
        errors[0].message,
        "AAPL261016P00230000 expired 2026-10-16 but 2 contract(s) remain open in Assets:Broker:Options"
    );
    assert_eq!(errors[0].source_file.as_deref(), Some("other.beancount"));
    assert_eq!(errors[0].line_number, Some(1));
}

/// A position whose net leaves `Decimal`'s range is not checked, and the
/// plugin does not panic: across entries, and inside one entry's legs.
#[test]
fn test_option_expiry_overflow_is_skipped() {
    let big = "-50000000000000000000000000000";
    let across = option_expiry_errors(vec![
        option_txn("2026-09-02", OPT_ACCT, big, "AAPL261016P00230000"),
        option_txn("2026-09-03", OPT_ACCT, big, "AAPL261016P00230000"),
        later_entry("2026-11-01"),
    ]);
    assert_eq!(across.len(), 0, "{across:?}");

    let within = option_expiry_errors(vec![
        make_transaction(
            "2026-09-02",
            "two huge legs",
            vec![
                (OPT_ACCT, big, "AAPL261016P00230000"),
                (OPT_ACCT, big, "AAPL261016P00230000"),
                (CASH_ACCT, "0", "USD"),
            ],
        ),
        later_entry("2026-11-01"),
    ]);
    assert_eq!(within.len(), 0, "{within:?}");

    // A position that overflowed stays unchecked even if a later entry
    // brings the arithmetic back into range.
    let after = option_expiry_errors(vec![
        option_txn("2026-09-02", OPT_ACCT, big, "AAPL261016P00230000"),
        option_txn("2026-09-03", OPT_ACCT, big, "AAPL261016P00230000"),
        option_txn("2026-09-04", OPT_ACCT, "1", "AAPL261016P00230000"),
        later_entry("2026-11-01"),
    ]);
    assert_eq!(after.len(), 0, "{after:?}");
}

/// The plugin with `config`, on the shared opens plus `directives`.
fn option_expiry_with_config(
    config: Option<&str>,
    directives: Vec<DirectiveWrapper>,
) -> Vec<PluginError> {
    let mut all = vec![
        make_open("2026-01-01", OPT_ACCT),
        make_open("2026-01-01", CASH_ACCT),
        make_open("2026-01-01", "Expenses:Fees"),
    ];
    all.extend(directives);
    let mut input = make_input(all);
    input.config = config.map(str::to_string);
    let n = input.directives.len();
    let output = process_and_materialize(&CheckOptionExpiryPlugin, input);
    // Whatever the config, every directive is kept and nothing is added.
    assert_eq!(output.directives.len(), n);
    output.errors
}

/// The full message of a config error with `problem`.
fn invalid_expiry_config(problem: &str) -> String {
    format!("Invalid configuration for check_option_expiry plugin: {problem}; skipping.")
}

/// `config` is rejected with exactly one error, located as beancount's
/// `check_commodity` locates its config errors, and the plugin skips: the
/// expired position in the ledger is not reported.
fn assert_expiry_config_problem(config: &str, problem: &str) {
    let errors = option_expiry_with_config(
        Some(config),
        vec![
            option_txn("2026-09-02", OPT_ACCT, "-1", "AAPL261016P00230000"),
            later_entry("2026-11-01"),
        ],
    );
    assert_eq!(errors.len(), 1, "{config:?}: {errors:?}");
    let e = &errors[0];
    assert_eq!(e.message, invalid_expiry_config(problem), "{config:?}");
    assert_eq!(e.severity, PluginErrorSeverity::Error, "{config:?}");
    assert_eq!(
        e.source_file.as_deref(),
        Some("<check_option_expiry>"),
        "{config:?}"
    );
    assert_eq!(e.line_number, Some(0), "{config:?}");
}

const EXPIRED_PUT: &str = "AAPL261016P00230000 expired 2026-10-16 but -1 contract(s) remain open in Assets:Broker:Options";

/// A put expiring `d - 1` and one expiring `d`, both sold before, the
/// first bought back on `d + 1`, and an entry on `d + 30`. With `as_of`
/// = `d` exactly the first is reported (expired before `as_of`, its close
/// ignored); by default (last date `d + 30`) exactly the second.
fn as_of_probe(config: Option<&str>, d: jiff::civil::Date) -> Vec<String> {
    let day = |n: i64| d.checked_add(jiff::Span::new().days(n)).unwrap();
    let symbol = |date: jiff::civil::Date| format!("AAPL{}P00230000", date.strftime("%y%m%d"));
    let iso = |date: jiff::civil::Date| date.strftime("%Y-%m-%d").to_string();
    let errors = option_expiry_with_config(
        config,
        vec![
            option_txn(&iso(day(-30)), OPT_ACCT, "-1", &symbol(day(-1))),
            option_txn(&iso(day(-30)), OPT_ACCT, "-1", &symbol(d)),
            option_txn(&iso(day(1)), OPT_ACCT, "1", &symbol(day(-1))),
            later_entry(&iso(day(30))),
        ],
    );
    errors.into_iter().map(|e| e.message).collect()
}

/// What [`as_of_probe`] reports when the contract expiring `date` is the
/// one left open.
fn probe_error(date: jiff::civil::Date) -> String {
    format!(
        "AAPL{}P00230000 expired {} but -1 contract(s) remain open in Assets:Broker:Options",
        date.strftime("%y%m%d"),
        date.strftime("%Y-%m-%d")
    )
}

/// T40: beancount-options' shared config cases
/// (`tests/cases/expiry_config.json`): each config gives its `as_of` or its
/// `problem` natively, byte for byte. A case marked `native_differs` is
/// skipped here; what native gives for it is pinned in
/// `test_option_expiry_config_native_differs_pinned`. Reads the checkout
/// named by `BEANCOUNT_OPTIONS_DIR`, and prints the same skip marker as
/// `options_plugins_parity` when it is unset; CI fails on that marker.
#[test]
fn test_option_expiry_config_cases() {
    let Some(dir) = std::env::var_os("BEANCOUNT_OPTIONS_DIR") else {
        eprintln!(
            "Skipping: BEANCOUNT_OPTIONS_DIR not set (the beancount-options checkout with tests/cases/)"
        );
        return;
    };
    let path = std::path::PathBuf::from(dir).join("tests/cases/expiry_config.json");
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("reading {}: {e}", path.display()));
    let json: serde_json::Value = serde_json::from_str(&text).unwrap();
    let cases = json["cases"].as_array().expect("a `cases` array");
    let default_date = jiff::civil::date(2026, 10, 16);
    let (mut checked, mut differs) = (0, 0);
    let mut failures = Vec::new();
    for case in cases {
        if case.get("native_differs").is_some() {
            differs += 1;
            continue;
        }
        checked += 1;
        let config = case["config"].as_str().expect("a config string");
        let as_of = case["as_of"].as_str();
        let problem = case["problem"].as_str();
        let (got, want) = match (as_of, problem) {
            (_, Some(problem)) => {
                let errors = option_expiry_with_config(Some(config), vec![]);
                let got: Vec<_> = errors
                    .iter()
                    .map(|e| {
                        (
                            e.message.clone(),
                            e.source_file.clone(),
                            e.line_number,
                            e.severity,
                        )
                    })
                    .collect();
                let want = vec![(
                    invalid_expiry_config(problem),
                    Some("<check_option_expiry>".to_string()),
                    Some(0),
                    PluginErrorSeverity::Error,
                )];
                (format!("{got:?}"), format!("{want:?}"))
            }
            (Some(as_of), None) => {
                let d: jiff::civil::Date = as_of.parse().unwrap();
                let day_before = d.yesterday().unwrap();
                (
                    format!("{:?}", as_of_probe(Some(config), d)),
                    format!("{:?}", [probe_error(day_before)]),
                )
            }
            (None, None) => (
                format!("{:?}", as_of_probe(Some(config), default_date)),
                format!("{:?}", [probe_error(default_date)]),
            ),
        };
        if got != want {
            failures.push(format!("{config:?}\n  got:  {got}\n  want: {want}"));
        }
    }
    eprintln!("expiry_config.json: {checked} cases checked, {differs} native_differs skipped");
    assert_eq!(checked + differs, cases.len());
    assert!(checked > 0, "no cases in {}", path.display());
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// T44: no config, an empty one, one of ASCII whitespace only (stripped
/// as beancount-options strips it), and `{}` all mean the default rules.
/// A non-ASCII space is not stripped, so it is not a dict, as in Python.
#[test]
fn test_option_expiry_blank_configs() {
    let blanks = [
        None,
        Some(""),
        Some(" "),
        Some("\t"),
        Some("\n"),
        Some("\r"),
        Some("\x0c"),
        Some("\x0b"),
        Some(" \t\n\r\x0c\x0b"),
        Some("{}"),
        Some(" {} "),
        Some("\x0b{}\x0c"),
    ];
    for blank in blanks {
        let errors = option_expiry_with_config(
            blank,
            vec![
                option_txn("2026-09-02", OPT_ACCT, "-1", "AAPL261016P00230000"),
                later_entry("2026-11-01"),
            ],
        );
        assert_eq!(errors.len(), 1, "{blank:?}: {errors:?}");
        assert_eq!(errors[0].message, EXPIRED_PUT, "{blank:?}");
        assert_eq!(errors[0].severity, PluginErrorSeverity::Error);
    }
    let not_a_dict = "expected a dict such as {'as_of': '2026-10-16'}";
    for config in ["\u{a0}", "\u{a0}{}", "\u{2003}{}", "\x1c{}", "{}\x1f"] {
        assert_expiry_config_problem(config, not_a_dict);
    }
}

/// T42: `as_of` before, on and after the expiry. A contract expiring on
/// `as_of` is fine, as on the last entry's date by default; one that
/// expired before it is reported even with no entry after the expiry.
#[test]
fn test_option_expiry_as_of_around_expiry() {
    let run = |as_of: &str, later: bool| {
        let mut directives = vec![option_txn(
            "2026-09-02",
            OPT_ACCT,
            "-1",
            "AAPL261016P00230000",
        )];
        if later {
            directives.push(later_entry("2026-11-01"));
        }
        let config = format!("{{'as_of': '{as_of}'}}");
        option_expiry_with_config(Some(&config), directives)
            .into_iter()
            .map(|e| e.message)
            .collect::<Vec<_>>()
    };
    for later in [false, true] {
        assert_eq!(run("2026-10-15", later), Vec::<String>::new(), "{later}");
        assert_eq!(run("2026-10-16", later), Vec::<String>::new(), "{later}");
        assert_eq!(run("2026-10-17", later), [EXPIRED_PUT], "{later}");
    }
    // Without as_of, the same ledger with nothing after the expiry passes.
    let errors = option_expiry_with_config(
        None,
        vec![option_txn(
            "2026-09-02",
            OPT_ACCT,
            "-1",
            "AAPL261016P00230000",
        )],
    );
    assert_eq!(errors.len(), 0, "{errors:?}");
}

/// T43: entries dated after `as_of` are ignored entirely. A later entry
/// does not move "today" past the expiry, and a close dated after `as_of`
/// does not close the position; an entry dated on `as_of` counts, and an
/// opener dated after it is never seen.
#[test]
fn test_option_expiry_as_of_ignores_later_entries() {
    let config = |d: &str| format!("{{'as_of': '{d}'}}");
    let open = || {
        let mut open = option_txn("2026-09-02", OPT_ACCT, "-1", "AAPL261016P00230000");
        open.filename = Some("ledger.beancount".to_string());
        open.lineno = Some(7);
        open
    };

    // "Today": the later entry would report the put by default.
    let errors = option_expiry_with_config(
        Some(&config("2026-10-10")),
        vec![open(), later_entry("2026-11-01")],
    );
    assert_eq!(errors.len(), 0, "{errors:?}");

    // Closing: a forecast close after as_of leaves the put open.
    let close = || option_txn("2026-10-20", OPT_ACCT, "1", "AAPL261016P00230000");
    let errors = option_expiry_with_config(None, vec![open(), close()]);
    assert_eq!(errors.len(), 0, "default: {errors:?}");
    let errors = option_expiry_with_config(Some(&config("2026-10-18")), vec![open(), close()]);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(errors[0].message, EXPIRED_PUT);
    assert_eq!(errors[0].source_file.as_deref(), Some("ledger.beancount"));
    assert_eq!(errors[0].line_number, Some(7));
    // The close dated on as_of itself counts.
    let errors = option_expiry_with_config(Some(&config("2026-10-20")), vec![open(), close()]);
    assert_eq!(errors.len(), 0, "{errors:?}");

    // An opener dated after as_of is not a position.
    let errors = option_expiry_with_config(
        Some(&config("2026-10-25")),
        vec![option_txn(
            "2026-10-26",
            OPT_ACCT,
            "-1",
            "AAPL261016P00230000",
        )],
    );
    assert_eq!(errors.len(), 0, "{errors:?}");

    // A sign change after as_of does not move the opener either: the
    // position open on as_of is the short sold on 09-02.
    let errors = option_expiry_with_config(
        Some(&config("2026-10-18")),
        vec![
            open(),
            option_txn("2026-10-19", OPT_ACCT, "2", "AAPL261016P00230000"),
        ],
    );
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(errors[0].message, EXPIRED_PUT);
    assert_eq!(errors[0].line_number, Some(7));
}

/// An empty ledger with `as_of` reports nothing.
#[test]
fn test_option_expiry_as_of_empty_ledger() {
    let mut input = make_input(vec![]);
    input.config = Some("{'as_of': '2026-10-16'}".to_string());
    let output = CheckOptionExpiryPlugin.process(input);
    assert_eq!(output.errors.len(), 0, "{:?}", output.errors);
    assert_eq!(output.ops.len(), 0);
}

/// Each config problem, checked in beancount-options' order: not a dict,
/// a non-str key, the first unknown key, a non-str `as_of`, a bad date.
#[test]
fn test_option_expiry_config_problems() {
    let not_a_dict = "expected a dict such as {'as_of': '2026-10-16'}";
    for config in [
        "not a literal",
        "['as_of']",
        "('as_of', '2026-10-16')",
        "'2026-10-16'",
        "2026",
        "None",
        "{'as_of': '2026-10-16'",
        "{'as_of': '2026-10-16'} {}",
        "{'as_of': '2026-10-16',,}",
        "{'as_of': f'2026-10-16'}",
        "{'as_of': date(2026, 10, 16)}",
    ] {
        assert_expiry_config_problem(config, not_a_dict);
    }
    for config in [
        "{1: 'x'}",
        "{'as_of': '2026-10-16', 1: 2}",
        "{'zz': 1, 1: 2}",
        "{1: 'x', True: 'y'}",
        "{None: 1}",
        "{(1,): 2}",
        "{b'as_of': '2026-10-16'}",
        "{'as_of': 'bad', 2.5: 1}",
    ] {
        assert_expiry_config_problem(config, "keys must be strings");
    }
    assert_expiry_config_problem("{'asof': '2026-10-16'}", "unknown key 'asof'");
    assert_expiry_config_problem("{'zz': 1, 'aa': 2}", "unknown key 'zz'");
    assert_expiry_config_problem("{'as_of': '2026-10-16', 'zz': 1}", "unknown key 'zz'");
    assert_expiry_config_problem("{'as_of': 1, 'zz': 1}", "unknown key 'zz'");
    assert_expiry_config_problem("{'AS_OF': '2026-10-16'}", "unknown key 'AS_OF'");
    for config in [
        "{'as_of': 20261016}",
        "{'as_of': None}",
        "{'as_of': True}",
        "{'as_of': b'2026-10-16'}",
        "{'as_of': ['2026-10-16']}",
        "{'as_of': {'b', 'a', 'c'}}",
        "{'as_of': {'d': '2026-10-16'}}",
    ] {
        assert_expiry_config_problem(config, "as_of must be a string");
    }
    let bad_date = |v: &str| format!("as_of must be a date written YYYY-MM-DD, not '{v}'");
    for value in [
        "20261016",
        "2026-02-30",
        "2027-02-29",
        "0000-01-01",
        "2026-13-01",
        "2026-00-10",
        "2026-10-00",
        "2026-10-32",
        "2026-1-16",
        "26-10-16",
        "+2026-10-16",
        "2026/10/16",
        "2026-10-16 ",
        " 2026-10-16",
        "2026-10-16T00:00",
        "2026-W42-5",
        " ",
        "bad",
    ] {
        assert_expiry_config_problem(&format!("{{'as_of': '{value}'}}"), &bad_date(value));
    }
}

/// A key or value is quoted back only when it is 1–40 printable ASCII
/// characters other than `'`, `"` and `\`, as in beancount-options;
/// otherwise the message leaves it out.
#[test]
fn test_option_expiry_config_quoting() {
    let forty = "a".repeat(40);
    let forty_one = "a".repeat(41);
    assert_expiry_config_problem(
        &format!("{{'{forty}': 1}}"),
        &format!("unknown key '{forty}'"),
    );
    assert_expiry_config_problem(&format!("{{'{forty_one}': 1}}"), "an unknown key");
    for key in [
        "",
        "it\\'s",
        "say \"hi\"",
        "a\\\\b",
        "clé",
        "a\\x7fb",
        "a\\tb",
    ] {
        assert_expiry_config_problem(&format!("{{'{key}': 1}}"), "an unknown key");
    }
    // The printable edges: space, `!`, `#`, `&`, `(`, `[`, `]`, `~`.
    assert_expiry_config_problem("{' !#&([]~': 1}", "unknown key ' !#&([]~'");

    let date = "as_of must be a date written YYYY-MM-DD";
    let digits = "9".repeat(40);
    assert_expiry_config_problem(
        &format!("{{'as_of': '{digits}'}}"),
        &format!("{date}, not '{digits}'"),
    );
    assert_expiry_config_problem(&format!("{{'as_of': '9{digits}'}}"), date);
    for value in [
        "",
        "\"it's\"",
        "'a\\\\b'",
        "'say \"hi\"'",
        "'２026-10-16'",
        "'2026-10-16\\n'",
        "'\\x7f'",
    ] {
        let config = if value.is_empty() {
            "{'as_of': ''}".to_string()
        } else {
            format!("{{'as_of': {value}}}")
        };
        assert_expiry_config_problem(&config, date);
    }
}

/// Valid dates: leap days, the first and last years Python allows, and
/// the date forms beancount-options accepts (either quote, any spacing
/// `literal_eval` allows, a comment, a trailing comma).
#[test]
fn test_option_expiry_config_valid_dates() {
    let d = jiff::civil::date(2026, 10, 16);
    let expect = [probe_error(d.yesterday().unwrap())];
    for config in [
        "{'as_of': '2026-10-16'}",
        "{\"as_of\": \"2026-10-16\"}",
        "{'as_of': '2026-10-16',}",
        "{ 'as_of' : '2026-10-16' }",
        "{'as_of':\n  '2026-10-16'}",
        "{'as_of': '2026-10-16'}  # comment",
        "{'as_of': '2026' '-10-16'}",
        "{'as_of': r'2026-10-16'}",
        "{'as_of': u'2026-10-16'}",
        "{'as_of': '''2026-10-16'''}",
        "{'as_of': '\\x32026-10-16'}",
        "\t{'as_of': '2026-10-16'}\n",
    ] {
        assert_eq!(as_of_probe(Some(config), d), expect, "{config:?}");
    }
    let leap = jiff::civil::date(2028, 2, 29);
    assert_eq!(
        as_of_probe(Some("{'as_of': '2028-02-29'}"), leap),
        [probe_error(leap.yesterday().unwrap())]
    );

    // Year 1 is Python's first: every entry is after it, so nothing is
    // reported. Year 9999 is its last: the put is long expired.
    let put = || {
        vec![
            option_txn("2026-09-02", OPT_ACCT, "-1", "AAPL261016P00230000"),
            later_entry("2026-10-17"),
        ]
    };
    let errors = option_expiry_with_config(Some("{'as_of': '0001-01-01'}"), put());
    assert_eq!(errors.len(), 0, "{errors:?}");
    let errors = option_expiry_with_config(Some("{'as_of': '9999-12-31'}"), put());
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(errors[0].message, EXPIRED_PUT);
}

/// A repeated key keeps its first position and takes its last value, as
/// in the Python dict beancount-options reads.
#[test]
fn test_option_expiry_config_repeated_keys() {
    let d = jiff::civil::date(2026, 10, 17);
    assert_eq!(
        as_of_probe(Some("{'as_of': 'bad', 'as_of': '2026-10-17'}"), d),
        [probe_error(d.yesterday().unwrap())]
    );
    assert_expiry_config_problem(
        "{'as_of': '2026-10-16', 'as_of': 1}",
        "as_of must be a string",
    );
    assert_expiry_config_problem(
        "{'as_of': '2026-10-16', 'as_of': '2026-10-99'}",
        "as_of must be a date written YYYY-MM-DD, not '2026-10-99'",
    );
    assert_expiry_config_problem("{'yy': 1, 'zz': 2, 'yy': 3}", "unknown key 'yy'");
    assert_expiry_config_problem(
        "{'as_of': '2026-10-16', 'zz': 1, 'as_of': 'x'}",
        "unknown key 'zz'",
    );
}

/// T41: the configs beancount-options' cases mark `native_differs`, and
/// one more of the same kind (a dict as a key). Python rejects them
/// differently because `literal_eval` raises on an unhashable key or set
/// element, or accepts what `py_literal` rejects (`\N{...}` and complex
/// numbers). None is a config anyone would write; what native gives is
/// pinned here so it stays deliberate.
#[test]
fn test_option_expiry_config_native_differs_pinned() {
    let not_a_dict = "expected a dict such as {'as_of': '2026-10-16'}";
    assert_expiry_config_problem("{[1]: 2}", "keys must be strings");
    assert_expiry_config_problem("{{}: 1}", "keys must be strings");
    assert_expiry_config_problem("{'zz': {[]: 1}}", "unknown key 'zz'");
    assert_expiry_config_problem("{'as_of': {[1]}}", "as_of must be a string");
    assert_expiry_config_problem("{'as_of': 1+2j}", not_a_dict);
    assert_expiry_config_problem("{'as_of': '\\N{DIGIT TWO}026-10-16'}", not_a_dict);
}

/// The plugin is reachable by name through the registry.
#[test]
fn test_option_expiry_registered() {
    assert!(NativePluginRegistry::global().has("check_option_expiry"));
}

// ============================================================================
// CheckOptionAssignmentPlugin Tests
// ============================================================================

use rustledger_plugin::native::CheckOptionAssignmentPlugin;
use rustledger_plugin_types::CostNumberData;

const STOCK_ACCT: &str = "Assets:Broker:Stock";
const GAINS_ACCT: &str = "Income:Trading:Gains";

/// A booked posting, built up with cost and price annotations.
fn leg(account: &str, units: &str, currency: &str) -> PostingData {
    PostingData {
        account: account.to_string(),
        units: Some(AmountData {
            number: units.to_string(),
            currency: currency.to_string(),
        }),
        cost: None,
        price: None,
        flag: None,
        metadata: vec![],
        span: None,
    }
}

fn with_cost(mut p: PostingData, number: CostNumberData) -> PostingData {
    p.cost = Some(CostData {
        number: Some(number),
        currency: Some("USD".to_string()),
        date: None,
        label: None,
        merge: false,
    });
    p
}

fn per_unit(p: PostingData, value: &str) -> PostingData {
    with_cost(
        p,
        CostNumberData::PerUnit {
            value: value.to_string(),
        },
    )
}

fn priced(mut p: PostingData, number: &str, is_total: bool) -> PostingData {
    p.price = Some(PriceAnnotationData {
        is_total,
        amount: Some(AmountData {
            number: number.to_string(),
            currency: "USD".to_string(),
        }),
        number: None,
        currency: None,
    });
    p
}

fn cash(number: &str) -> PostingData {
    leg(CASH_ACCT, number, "USD")
}

fn txn_of(date: &str, postings: Vec<PostingData>) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: "transaction".to_string(),
        date: date.to_string(),
        filename: Some("ledger.beancount".to_string()),
        lineno: Some(7),
        data: DirectiveData::Transaction(TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: "test".to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings,
        }),
    }
}

/// Sell to open `n` contracts of `symbol` at `cost` (premium × 100).
fn sto(date: &str, n: &str, symbol: &str, cost: &str) -> DirectiveWrapper {
    txn_of(
        date,
        vec![
            per_unit(leg(OPT_ACCT, &format!("-{n}"), symbol), cost),
            cash("0"),
        ],
    )
}

fn assignment_errors(directives: Vec<DirectiveWrapper>) -> Vec<PluginError> {
    let plugin = CheckOptionAssignmentPlugin;
    let mut all = vec![
        make_open("2026-01-01", OPT_ACCT),
        make_open("2026-01-01", CASH_ACCT),
        make_open("2026-01-01", STOCK_ACCT),
        make_open("2026-01-01", GAINS_ACCT),
    ];
    all.extend(directives);
    let input = make_input(all);
    let n = input.directives.len();
    let output = process_and_materialize(&plugin, input);
    assert_eq!(output.directives.len(), n);
    output.errors
}

const PUT: &str = "AAPL261016P00225000";
const CALL: &str = "AAPL261016C00280000";

/// Short put assigned: close the option at cost, buy stock at `basis`.
fn put_assignment(basis: &str) -> Vec<DirectiveWrapper> {
    vec![
        sto("2026-09-03", "1", PUT, "300.00"),
        txn_of(
            "2026-10-16",
            vec![
                per_unit(leg(OPT_ACCT, "1", PUT), "300.00"),
                per_unit(leg(STOCK_ACCT, "100", "AAPL"), basis),
                cash("-22500.00"),
            ],
        ),
    ]
}

/// Covered call assigned: close the option at cost, sell the stock with
/// `stock_leg` describing its price annotation.
fn call_assignment(stock_leg: PostingData) -> Vec<DirectiveWrapper> {
    vec![
        txn_of(
            "2026-01-02",
            vec![
                per_unit(leg(STOCK_ACCT, "100", "AAPL"), "200.00"),
                cash("0"),
            ],
        ),
        sto("2026-09-04", "1", CALL, "220.00"),
        txn_of(
            "2026-10-16",
            vec![
                per_unit(leg(OPT_ACCT, "1", CALL), "220.00"),
                stock_leg,
                cash("28000.00"),
                leg(GAINS_ACCT, "-8220.00", "USD"),
            ],
        ),
    ]
}

fn sold_aapl() -> PostingData {
    per_unit(leg(STOCK_ACCT, "-100", "AAPL"), "200.00")
}

/// T11: short put assigned with basis = strike − premium.
#[test]
fn test_option_assignment_put_correct() {
    let errors = assignment_errors(put_assignment("222.00"));
    assert_eq!(errors.len(), 0, "{errors:?}");
}

/// T12: short put assigned with stock at the full strike.
#[test]
fn test_option_assignment_put_basis_at_strike() {
    let errors = assignment_errors(put_assignment("225.00"));
    assert_eq!(errors.len(), 1, "{errors:?}");
    let e = &errors[0];
    assert_eq!(e.severity, PluginErrorSeverity::Error);
    assert_eq!(
        e.message,
        "AAPL261016P00225000 assignment: AAPL basis 22500.00 USD, expected 22200.00 USD (strike 225 × 100 − premium 300.00)"
    );
    assert_eq!(e.source_file.as_deref(), Some("ledger.beancount"));
    assert_eq!(e.line_number, Some(7));
}

/// T13: covered call assigned with `@` proceeds = strike + premium.
#[test]
fn test_option_assignment_call_correct_unit_price() {
    let errors = assignment_errors(call_assignment(priced(sold_aapl(), "282.20", false)));
    assert_eq!(errors.len(), 0, "{errors:?}");
}

/// T14: covered call assigned with proceeds at the strike.
#[test]
fn test_option_assignment_call_proceeds_at_strike() {
    let errors = assignment_errors(call_assignment(priced(sold_aapl(), "280.00", false)));
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(
        errors[0].message,
        "AAPL261016C00280000 assignment: AAPL proceeds 28000.00 USD, expected 28220.00 USD (strike 280 × 100 + premium 220.00)"
    );
}

/// T15: covered call assigned with `@@` total proceeds.
#[test]
fn test_option_assignment_call_correct_total_price() {
    let errors = assignment_errors(call_assignment(priced(sold_aapl(), "28220.00", true)));
    assert_eq!(errors.len(), 0, "{errors:?}");
    let wrong = assignment_errors(call_assignment(priced(sold_aapl(), "28000.00", true)));
    assert_eq!(wrong.len(), 1, "{wrong:?}");
}

/// T16: the premium is realized on the option leg and the stock is bought
/// at the full strike. R2 is reported, not R3.
#[test]
fn test_option_assignment_premium_on_option_leg() {
    let errors = assignment_errors(vec![
        sto("2026-09-03", "1", PUT, "300.00"),
        txn_of(
            "2026-10-16",
            vec![
                priced(per_unit(leg(OPT_ACCT, "1", PUT), "300.00"), "0.00", false),
                per_unit(leg(STOCK_ACCT, "100", "AAPL"), "225.00"),
                cash("-22500.00"),
                leg(GAINS_ACCT, "-300.00", "USD"),
            ],
        ),
    ]);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(
        errors[0].message,
        "AAPL261016P00225000 assignment: option leg priced at 0.00 USD, not its cost 300.00 USD; close it at cost and fold the premium into the AAPL leg"
    );
}

/// T16b: an option-leg price equal to its cost realizes no gain.
#[test]
fn test_option_assignment_option_leg_priced_at_cost() {
    let errors = assignment_errors(vec![
        sto("2026-09-03", "1", PUT, "300.00"),
        txn_of(
            "2026-10-16",
            vec![
                priced(per_unit(leg(OPT_ACCT, "1", PUT), "300.00"), "300.00", false),
                per_unit(leg(STOCK_ACCT, "100", "AAPL"), "222.00"),
                cash("-22500.00"),
            ],
        ),
    ]);
    assert_eq!(errors.len(), 0, "{errors:?}");
}

/// T17: share count does not match 100 per contract. R1 is reported first.
#[test]
fn test_option_assignment_wrong_share_count() {
    let errors = assignment_errors(vec![
        sto("2026-09-03", "1", PUT, "300.00"),
        txn_of(
            "2026-10-16",
            vec![
                per_unit(leg(OPT_ACCT, "1", PUT), "300.00"),
                per_unit(leg(STOCK_ACCT, "50", "AAPL"), "225.00"),
                cash("-11250.00"),
            ],
        ),
    ]);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(
        errors[0].message,
        "AAPL261016P00225000 assignment: 1 contract(s) but 50 AAPL; expected 100"
    );
}

/// Two short puts opened at different premiums, both assigned.
fn two_lot_assignment(stock: Vec<PostingData>) -> Vec<DirectiveWrapper> {
    let mut assign = vec![
        per_unit(leg(OPT_ACCT, "1", PUT), "300.00"),
        per_unit(leg(OPT_ACCT, "1", PUT), "250.00"),
    ];
    assign.extend(stock);
    assign.push(cash("-45000.00"));
    vec![
        sto("2026-09-03", "1", PUT, "300.00"),
        sto("2026-09-10", "1", PUT, "250.00"),
        txn_of("2026-10-16", assign),
    ]
}

/// T18: two lots, basis correct as a total across two stock lots.
#[test]
fn test_option_assignment_two_lots_correct() {
    let errors = assignment_errors(two_lot_assignment(vec![
        per_unit(leg(STOCK_ACCT, "100", "AAPL"), "222.00"),
        per_unit(leg(STOCK_ACCT, "100", "AAPL"), "222.50"),
    ]));
    assert_eq!(errors.len(), 0, "{errors:?}");
}

/// T19: two lots, basis wrong.
#[test]
fn test_option_assignment_two_lots_wrong() {
    let errors = assignment_errors(two_lot_assignment(vec![per_unit(
        leg(STOCK_ACCT, "200", "AAPL"),
        "225.00",
    )]));
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(
        errors[0].message,
        "AAPL261016P00225000 assignment: AAPL basis 45000.00 USD, expected 44450.00 USD (strike 225 × 200 − premium 550.00)"
    );
}

/// T20: an ordinary buy-to-close with no stock leg is not an assignment.
#[test]
fn test_option_assignment_ordinary_close() {
    let errors = assignment_errors(vec![
        sto("2026-09-03", "1", PUT, "300.00"),
        txn_of(
            "2026-09-20",
            vec![
                priced(per_unit(leg(OPT_ACCT, "1", PUT), "300.00"), "100.00", false),
                cash("-100.00"),
                leg(GAINS_ACCT, "-200.00", "USD"),
            ],
        ),
    ]);
    assert_eq!(errors.len(), 0, "{errors:?}");
}

/// T21: buying a long put together with stock (protective put) is not an
/// assignment, even though stock units rise.
#[test]
fn test_option_assignment_protective_put() {
    let errors = assignment_errors(vec![txn_of(
        "2026-09-03",
        vec![
            per_unit(leg(OPT_ACCT, "1", PUT), "500.00"),
            per_unit(leg(STOCK_ACCT, "100", "AAPL"), "230.00"),
            cash("-23500.00"),
        ],
    )]);
    assert_eq!(errors.len(), 0, "{errors:?}");
}

/// T22: exercising a long put is out of scope and not checked.
#[test]
fn test_option_assignment_long_put_exercise_ignored() {
    let errors = assignment_errors(vec![
        txn_of(
            "2026-01-02",
            vec![
                per_unit(leg(STOCK_ACCT, "100", "AAPL"), "200.00"),
                cash("0"),
            ],
        ),
        txn_of(
            "2026-09-03",
            vec![per_unit(leg(OPT_ACCT, "1", PUT), "500.00"), cash("-500.00")],
        ),
        txn_of(
            "2026-10-16",
            vec![
                per_unit(leg(OPT_ACCT, "-1", PUT), "500.00"),
                priced(sold_aapl(), "999.00", false),
                cash("22500.00"),
            ],
        ),
    ]);
    assert_eq!(errors.len(), 0, "{errors:?}");
}

/// T23: rounding tolerance is half a cent per share, inclusive.
/// Premium 237.50 → expected basis 22262.50; 222.63 × 100 is 0.50 off
/// (inside), 222.64 × 100 is 1.50 off (outside).
#[test]
fn test_option_assignment_tolerance() {
    let case = |basis: &str| {
        assignment_errors(vec![
            sto("2026-09-03", "1", PUT, "237.50"),
            txn_of(
                "2026-10-16",
                vec![
                    per_unit(leg(OPT_ACCT, "1", PUT), "237.50"),
                    per_unit(leg(STOCK_ACCT, "100", "AAPL"), basis),
                    cash("-22500.00"),
                ],
            ),
        ])
    };
    assert_eq!(case("222.63").len(), 0);
    assert_eq!(case("222.62").len(), 0);
    assert_eq!(case("222.64").len(), 1);
    assert_eq!(case("222.61").len(), 1);
}

/// T23b: the call tolerance is also inclusive at exactly half a cent per
/// share. Expected proceeds 28220.00; 28220.50 is 0.50 off (inside),
/// 28220.51 is just outside.
#[test]
fn test_option_assignment_call_tolerance() {
    let case = |total: &str| assignment_errors(call_assignment(priced(sold_aapl(), total, true)));
    assert_eq!(case("28220.50").len(), 0);
    assert_eq!(case("28219.50").len(), 0);
    assert_eq!(case("28220.51").len(), 1);
    assert_eq!(case("28219.49").len(), 1);
}

/// T24: cash-settled index option, no stock leg.
#[test]
fn test_option_assignment_cash_settled_index() {
    let spxw = "SPXW261030C06800000";
    let errors = assignment_errors(vec![
        sto("2026-09-03", "1", spxw, "1240.00"),
        txn_of(
            "2026-10-30",
            vec![
                priced(
                    per_unit(leg(OPT_ACCT, "1", spxw), "1240.00"),
                    "2000.00",
                    false,
                ),
                cash("-2000.00"),
                leg(GAINS_ACCT, "760.00", "USD"),
            ],
        ),
    ]);
    assert_eq!(errors.len(), 0, "{errors:?}");
}

/// T25: every stock cost form is read as its total.
#[test]
fn test_option_assignment_cost_forms() {
    let case = |cost: CostNumberData| {
        assignment_errors(vec![
            sto("2026-09-03", "1", PUT, "300.00"),
            txn_of(
                "2026-10-16",
                vec![
                    per_unit(leg(OPT_ACCT, "1", PUT), "300.00"),
                    with_cost(leg(STOCK_ACCT, "100", "AAPL"), cost),
                    cash("-22500.00"),
                ],
            ),
        ])
    };
    let total = |v: &str| CostNumberData::Total {
        value: v.to_string(),
    };
    let from_total = |v: &str| CostNumberData::PerUnitFromTotal {
        per_unit: "999".to_string(),
        total: v.to_string(),
    };
    let compound = |per: &str, lump: &str| CostNumberData::Compound {
        per_unit: per.to_string(),
        total: lump.to_string(),
    };
    assert_eq!(case(total("22200.00")).len(), 0);
    assert_eq!(case(total("22500.00")).len(), 1);
    assert_eq!(case(from_total("22200.00")).len(), 0);
    assert_eq!(case(from_total("22500.00")).len(), 1);
    assert_eq!(case(compound("221.00", "100.00")).len(), 0);
    assert_eq!(case(compound("222.00", "100.00")).len(), 1);
}

/// T26: a call assignment whose stock leg has no usable price.
#[test]
fn test_option_assignment_call_without_price() {
    let errors = assignment_errors(call_assignment(sold_aapl()));
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(
        errors[0].message,
        "AAPL261016C00280000 assignment: AAPL sale has no price; expected proceeds 28220.00 USD"
    );

    let mut incomplete = sold_aapl();
    incomplete.price = Some(PriceAnnotationData {
        is_total: false,
        amount: None,
        number: None,
        currency: None,
    });
    let errors = assignment_errors(call_assignment(incomplete));
    assert_eq!(errors.len(), 1, "{errors:?}");
}

/// T27: an option position held without cost has no known premium and is
/// not checked.
#[test]
fn test_option_assignment_without_option_cost() {
    let errors = assignment_errors(vec![
        txn_of("2026-09-03", vec![leg(OPT_ACCT, "-1", PUT), cash("300.00")]),
        txn_of(
            "2026-10-16",
            vec![
                leg(OPT_ACCT, "1", PUT),
                per_unit(leg(STOCK_ACCT, "100", "AAPL"), "225.00"),
                cash("-22500.00"),
            ],
        ),
    ]);
    assert_eq!(errors.len(), 0, "{errors:?}");
}

/// T28: two strikes on the same underlying assigned in one transaction are
/// checked together, and the message lists both contracts.
#[test]
fn test_option_assignment_two_strikes() {
    let put230 = "AAPL261016P00230000";
    let case = |basis: &str| {
        assignment_errors(vec![
            sto("2026-09-03", "1", PUT, "300.00"),
            sto("2026-09-03", "1", put230, "400.00"),
            txn_of(
                "2026-10-16",
                vec![
                    per_unit(leg(OPT_ACCT, "1", PUT), "300.00"),
                    per_unit(leg(OPT_ACCT, "1", put230), "400.00"),
                    per_unit(leg(STOCK_ACCT, "200", "AAPL"), basis),
                    cash("-45500.00"),
                ],
            ),
        ])
    };
    // (225 + 230) × 100 − 700 = 44800 → 224.00 per share.
    assert_eq!(case("224.00").len(), 0);
    let errors = case("227.50");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(
        errors[0].message,
        "AAPL261016P00225000, AAPL261016P00230000 assignment: AAPL basis 45500.00 USD, expected 44800.00 USD (strike value 45500.00 − premium 700.00)"
    );
}

/// T29: the stock leg must move in the assignment's direction; a short
/// put closed alongside a stock sale is not an assignment.
#[test]
fn test_option_assignment_wrong_direction_ignored() {
    let errors = assignment_errors(vec![
        txn_of(
            "2026-01-02",
            vec![
                per_unit(leg(STOCK_ACCT, "100", "AAPL"), "200.00"),
                cash("0"),
            ],
        ),
        sto("2026-09-03", "1", PUT, "300.00"),
        txn_of(
            "2026-10-16",
            vec![
                priced(per_unit(leg(OPT_ACCT, "1", PUT), "300.00"), "100.00", false),
                priced(sold_aapl(), "230.00", false),
                cash("22900.00"),
            ],
        ),
    ]);
    assert_eq!(errors.len(), 0, "{errors:?}");
}

/// T31: an adjusted contract (numeric root suffix after a reverse split,
/// 10-share deliverable) is not checked. Its root `XYZ1` names no stock
/// commodity, so the `XYZ` leg is not read as an assignment, and the
/// 100-share rule is never applied to it.
#[test]
fn test_option_assignment_adjusted_contract_skipped() {
    let adjusted = "XYZ1261016P00005000";
    let errors = assignment_errors(vec![
        sto("2026-09-03", "1", adjusted, "50.00"),
        txn_of(
            "2026-10-16",
            vec![
                per_unit(leg(OPT_ACCT, "1", adjusted), "50.00"),
                per_unit(leg(STOCK_ACCT, "10", "XYZ"), "45.00"),
                cash("-500.00"),
            ],
        ),
    ]);
    assert_eq!(errors.len(), 0, "{errors:?}");
}

/// Same-day entries are walked in beancount's `entry_sortkey` order: a
/// sell-to-open at `other.beancount:1` comes before an assignment the same
/// day at `main.beancount:16`, even though the loader lists `main` first.
#[test]
fn test_option_assignment_same_day_entries_sorted_by_line() {
    let mut directives = put_assignment("225.00");
    let assignment = directives.pop().expect("assignment");
    let mut opening = directives.pop().expect("sell to open");
    opening.date = "2026-10-16".to_string();
    let errors = assignment_errors(vec![
        located_at(assignment, "main.beancount", 16),
        located_at(opening, "other.beancount", 1),
    ]);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(
        errors[0].message,
        "AAPL261016P00225000 assignment: AAPL basis 22500.00 USD, expected 22200.00 USD (strike 225 × 100 − premium 300.00)"
    );
    assert_eq!(errors[0].source_file.as_deref(), Some("main.beancount"));
    assert_eq!(errors[0].line_number, Some(16));
}

/// Numbers whose products leave `Decimal`'s range do not panic, and do not
/// pass silently: each rule whose arithmetic fits still runs, and an
/// assignment whose remaining rules cannot run gets a "not checked" error
/// at the entry. None of them is mistaken for a missing cost or price.
#[test]
fn test_option_assignment_overflow_is_reported() {
    let huge = "1000000000000000000000000";
    let shares = "100000000000000000000000000";
    let big_put = "AAPL261016P99999999";
    let unchecked = |label: &str| {
        format!("{label} assignment not checked: amounts exceed the supported decimal range")
    };
    let messages =
        |errors: Vec<PluginError>| errors.into_iter().map(|e| e.message).collect::<Vec<_>>();
    let assignment = |symbol: &str, option_leg: PostingData, stock_leg: PostingData| {
        assignment_errors(vec![
            sto("2026-09-03", huge, symbol, "1"),
            txn_of("2026-10-16", vec![option_leg, stock_leg, cash("0")]),
        ])
    };

    // Strike × shares (about 10^31) is out of range, but contracts × 100
    // is not: the share count is still checked (#2661 review).
    let share_count = assignment(
        big_put,
        per_unit(leg(OPT_ACCT, huge, big_put), "1"),
        per_unit(leg(STOCK_ACCT, "1", "AAPL"), "1"),
    );
    assert_eq!(
        share_count[0].source_file.as_deref(),
        Some("ledger.beancount")
    );
    assert_eq!(share_count[0].line_number, Some(7));
    assert_eq!(
        messages(share_count),
        [format!(
            "{big_put} assignment: {huge} contract(s) but 1 AAPL; expected {shares}"
        )]
    );

    // Not an assignment (no stock moves): nothing to check, so nothing to
    // report, however large the numbers.
    let ordinary_close = assignment(
        big_put,
        per_unit(leg(OPT_ACCT, huge, big_put), "1"),
        cash("0"),
    );
    assert_eq!(messages(ordinary_close), Vec::<String>::new());

    // The option leg's price is still checked too; it realizes a gain here.
    let realized = assignment(
        big_put,
        priced(per_unit(leg(OPT_ACCT, huge, big_put), "1"), "0", false),
        per_unit(leg(STOCK_ACCT, shares, "AAPL"), "1"),
    );
    assert_eq!(
        messages(realized),
        [format!(
            "{big_put} assignment: option leg priced at 0.00 USD, not its cost {huge}.00 USD; close it at cost and fold the premium into the AAPL leg"
        )]
    );

    // The share count is right, so only the basis is left, and it needs the
    // strike value: not checked.
    let strike_value = assignment(
        big_put,
        per_unit(leg(OPT_ACCT, huge, big_put), "1"),
        per_unit(leg(STOCK_ACCT, shares, "AAPL"), "1"),
    );
    assert_eq!(messages(strike_value), [unchecked(big_put)]);

    // 10^24 contracts of the 1.00 put: strike value 10^26 fits, but 10^26
    // shares at 1000 each (10^29) do not.
    let basis = assignment(
        "AAPL261016P00001000",
        per_unit(leg(OPT_ACCT, huge, "AAPL261016P00001000"), "1"),
        per_unit(leg(STOCK_ACCT, shares, "AAPL"), "1000"),
    );
    assert_eq!(messages(basis), [unchecked("AAPL261016P00001000")]);

    let proceeds = assignment(
        "AAPL261016C00001000",
        per_unit(leg(OPT_ACCT, huge, "AAPL261016C00001000"), "1"),
        priced(
            per_unit(leg(STOCK_ACCT, &format!("-{shares}"), "AAPL"), "1"),
            "1000",
            false,
        ),
    );
    assert_eq!(messages(proceeds), [unchecked("AAPL261016C00001000")]);

    // The option leg's own cost out of range: its contracts still count.
    let premium = assignment(
        PUT,
        per_unit(leg(OPT_ACCT, huge, PUT), "100000000"),
        per_unit(leg(STOCK_ACCT, "1", "AAPL"), "1"),
    );
    assert_eq!(
        messages(premium),
        [format!(
            "{PUT} assignment: {huge} contract(s) but 1 AAPL; expected {shares}"
        )]
    );

    // Contracts, or stock units, summed across accounts out of range: no
    // rule can run, so the assignment is not checked.
    let big = "50000000000000000000000000000";
    let two_accounts = |stock: Vec<PostingData>| {
        let mut postings = vec![
            per_unit(leg(OPT_ACCT, big, PUT), "0"),
            per_unit(leg(GAINS_ACCT, big, PUT), "0"),
        ];
        postings.extend(stock);
        postings.push(cash("0"));
        assignment_errors(vec![
            sto("2026-09-03", big, PUT, "0"),
            txn_of(
                "2026-09-03",
                vec![
                    per_unit(leg(GAINS_ACCT, &format!("-{big}"), PUT), "0"),
                    cash("0"),
                ],
            ),
            txn_of("2026-10-16", postings),
        ])
    };
    let contracts = two_accounts(vec![per_unit(leg(STOCK_ACCT, "100", "AAPL"), "1")]);
    assert_eq!(messages(contracts), [unchecked(PUT)]);
    let stock_units = two_accounts(vec![
        per_unit(leg(STOCK_ACCT, big, "AAPL"), "0"),
        per_unit(leg(CASH_ACCT, big, "AAPL"), "0"),
    ]);
    assert_eq!(messages(stock_units), [unchecked(PUT)]);

    // Running positions that overflow are dropped, not panicked on. Only
    // unbooked input reaches this: booking rejects such an inventory.
    let net = assignment_errors(vec![
        sto("2026-09-03", big, PUT, "0"),
        sto("2026-09-04", big, PUT, "0"),
    ]);
    assert_eq!(net.len(), 0, "{net:?}");
}

/// A put and a call on one root settled in one entry are checked
/// separately: the put assignment is checked, and the call bought back at
/// cost beside it is not an assignment (#2661 review).
#[test]
fn test_option_assignment_put_and_call_in_one_entry() {
    let case = |basis: &str| {
        assignment_errors(vec![
            sto("2026-09-03", "1", PUT, "300.00"),
            sto("2026-09-04", "1", CALL, "220.00"),
            txn_of(
                "2026-10-16",
                vec![
                    per_unit(leg(OPT_ACCT, "1", PUT), "300.00"),
                    per_unit(leg(OPT_ACCT, "1", CALL), "220.00"),
                    per_unit(leg(STOCK_ACCT, "100", "AAPL"), basis),
                    cash("-22500.00"),
                    leg(GAINS_ACCT, "-300.00", "USD"),
                ],
            ),
        ])
    };
    let errors = case("225.00");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(
        errors[0].message,
        "AAPL261016P00225000 assignment: AAPL basis 22500.00 USD, expected 22200.00 USD (strike 225 × 100 − premium 300.00)"
    );
    assert_eq!(case("222.00").len(), 0);
}

/// A put assignment whose stock is bought with a price and no cost is an
/// error, as a call's sale with no price is (#2661 review).
#[test]
fn test_option_assignment_put_without_stock_cost() {
    let errors = assignment_errors(vec![
        sto("2026-09-03", "1", PUT, "300.00"),
        txn_of(
            "2026-10-16",
            vec![
                per_unit(leg(OPT_ACCT, "1", PUT), "300.00"),
                priced(leg(STOCK_ACCT, "100", "AAPL"), "225.00", false),
                cash("-22500.00"),
                leg(GAINS_ACCT, "-300.00", "USD"),
            ],
        ),
    ]);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(
        errors[0].message,
        "AAPL261016P00225000 assignment: AAPL purchase has no cost; expected basis 22200.00 USD"
    );
}

/// A naked call assigned opens a short stock lot. Its cost is the sale's
/// proceeds, so a cost with no price is checked as proceeds instead of
/// reported as a sale with no price. A covered call's sale of a long lot
/// with no price is still an error (T26).
#[test]
fn test_option_assignment_naked_call_opens_short() {
    let case = |cost: &str| {
        assignment_errors(vec![
            sto("2026-09-04", "1", CALL, "220.00"),
            txn_of(
                "2026-10-16",
                vec![
                    per_unit(leg(OPT_ACCT, "1", CALL), "220.00"),
                    per_unit(leg(STOCK_ACCT, "-100", "AAPL"), cost),
                    cash("28000.00"),
                ],
            ),
        ])
    };
    assert_eq!(case("282.20").len(), 0);
    let errors = case("280.00");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(
        errors[0].message,
        "AAPL261016C00280000 assignment: AAPL proceeds 28000.00 USD, expected 28220.00 USD (strike 280 × 100 + premium 220.00)"
    );

    // Long stock held in another account does not make this a sale of it.
    let mut directives = vec![txn_of(
        "2026-01-02",
        vec![
            per_unit(leg("Assets:Other:Stock", "100", "AAPL"), "200.00"),
            cash("0"),
        ],
    )];
    directives.extend([
        sto("2026-09-04", "1", CALL, "220.00"),
        txn_of(
            "2026-10-16",
            vec![
                per_unit(leg(OPT_ACCT, "1", CALL), "220.00"),
                per_unit(leg(STOCK_ACCT, "-100", "AAPL"), "282.20"),
                cash("28000.00"),
            ],
        ),
    ]);
    let errors = assignment_errors(directives);
    assert_eq!(errors.len(), 0, "{errors:?}");
}

/// The plugin has no options, so a config string gives one warning
/// instead of being ignored silently.
#[test]
fn test_option_assignment_config_is_ignored_with_a_warning() {
    let mut all = vec![
        make_open("2026-01-01", OPT_ACCT),
        make_open("2026-01-01", CASH_ACCT),
        make_open("2026-01-01", STOCK_ACCT),
    ];
    all.extend(put_assignment("222.00"));
    let mut input = make_input(all);
    input.config = Some("{'tolerance': 1}".to_string());
    let errors = process_and_materialize(&CheckOptionAssignmentPlugin, input).errors;
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(errors[0].severity, PluginErrorSeverity::Warning);
    assert_eq!(
        errors[0].message,
        "check_option_assignment: the config is ignored; this plugin has no options"
    );

    let mut all = vec![make_open("2026-01-01", OPT_ACCT)];
    all.extend(put_assignment("222.00"));
    let mut input = make_input(all);
    input.config = Some(" \t".to_string());
    let errors = process_and_materialize(&CheckOptionAssignmentPlugin, input).errors;
    assert_eq!(errors.len(), 0, "{errors:?}");
}

/// The plugin is reachable by name through the registry.
#[test]
fn test_option_assignment_registered() {
    assert!(NativePluginRegistry::global().has("check_option_assignment"));
}

// PT1: for any strike, premium, and contract count, a put assignment with
// basis = strike × shares − premium passes, and one whose basis is off by
// more than the half-cent-per-share tolerance fails exactly once. Same for
// calls with proceeds = strike × shares + premium.
proptest::proptest! {
    #![proptest_config(proptest::prelude::ProptestConfig::with_cases(64))]

    #[test]
    fn prop_option_assignment_basis_invariant(
        strike_halves in 2u32..2000,   // $1.00 .. $999.50 in $0.50 steps
        premium_cents in 1u32..20_000, // $1 .. $19,999 per contract
        contracts in 1u32..20,
        is_call in proptest::bool::ANY,
        off_cents in 1u32..500,        // error, in cents per share, beyond tolerance
    ) {
        use rust_decimal::Decimal;

        let strike = Decimal::new(i64::from(strike_halves) * 5, 1);
        let premium_per_contract = Decimal::new(i64::from(premium_cents), 0);
        // A put's premium cannot exceed its strike value; keep inputs realistic.
        proptest::prop_assume!(premium_per_contract < strike * Decimal::from(100));
        let shares = Decimal::from(contracts * 100);
        let premium_total = premium_per_contract * Decimal::from(contracts);
        let strike_tag = format!("{:08}", (strike * Decimal::from(1000)).normalize());
        let symbol = format!("AAPL261016{}{strike_tag}", if is_call { "C" } else { "P" });
        let expected = if is_call {
            strike * shares + premium_total
        } else {
            strike * shares - premium_total
        };

        let run = |total: Decimal| {
            let n = contracts.to_string();
            let mut ds = vec![];
            if is_call {
                ds.push(txn_of(
                    "2026-01-02",
                    vec![per_unit(leg(STOCK_ACCT, &shares.to_string(), "AAPL"), "1.00"), cash("0")],
                ));
            }
            ds.push(sto("2026-09-03", &n, &symbol, &premium_per_contract.to_string()));
            let stock = if is_call {
                priced(
                    per_unit(leg(STOCK_ACCT, &(-shares).to_string(), "AAPL"), "1.00"),
                    &total.to_string(),
                    true,
                )
            } else {
                with_cost(
                    leg(STOCK_ACCT, &shares.to_string(), "AAPL"),
                    CostNumberData::Total { value: total.to_string() },
                )
            };
            ds.push(txn_of(
                "2026-10-16",
                vec![
                    per_unit(leg(OPT_ACCT, &n, &symbol), &premium_per_contract.to_string()),
                    stock,
                    cash("0"),
                ],
            ));
            assignment_errors(ds)
        };

        let ok = run(expected);
        proptest::prop_assert_eq!(ok.len(), 0, "{:?}", ok);

        let off = Decimal::new(i64::from(off_cents), 2) * shares + Decimal::new(5, 3) * shares;
        let bad = run(expected + off);
        proptest::prop_assert_eq!(bad.len(), 1, "{:?}", bad);
    }
}
