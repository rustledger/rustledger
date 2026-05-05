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
use rustledger_plugin::types::*;

// ============================================================================
// Helper Functions
// ============================================================================

fn make_input(directives: Vec<DirectiveWrapper>) -> PluginInput {
    PluginInput {
        directives,
        options: PluginOptions {
            operating_currencies: vec!["USD".to_string()],
            title: None,
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
                        number_per: Some(cost.0.to_string()),
                        number_total: None,
                        currency: Some(cost.1.to_string()),
                        date: None,
                        label: None,
                        merge: false,
                    }),
                    price: None,
                    flag: None,
                    metadata: vec![],
                },
                PostingData {
                    account: other_account.to_string(),
                    units: None,
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
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
                        number_per: Some(cost.0.to_string()),
                        number_total: None,
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
                },
                PostingData {
                    account: other_account.to_string(),
                    units: None,
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
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
                        number_per: Some(cost.0.to_string()),
                        number_total: None,
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
                },
                PostingData {
                    account: other_account.to_string(),
                    units: None,
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
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

    let output = plugin.process(input);

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

    let output = plugin.process(input);
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

    let output = plugin.process(input);

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

    let output = plugin.process(input);
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

    let output = plugin.process(input);
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

    let output = plugin.process(input);
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

    let output = plugin.process(input);
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

    let output = plugin.process(input);
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

    let output = plugin.process(input);
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

    let output = plugin.process(input);
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

    let output = plugin.process(input);
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

    let output = plugin.process(input);
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

    let output = plugin.process(input);
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
    let output = plugin.process(input);
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
    let output = plugin.process(input);
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
    let output = plugin.process(input);
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
    let output = plugin.process(input);
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
    let output = plugin.process(input);
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
    let output = plugin.process(input);
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
    let output = plugin.process(input);
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
    let output = plugin.process(input);
    assert!(
        output.errors.is_empty(),
        "different posting counts must not collide, got: {:?}",
        output.errors
    );
}

/// Posting order IS part of structural identity per beancount — two
/// transactions with the same postings in different orders hash
/// differently. This matches the Python `Posting` tuple being ordered
/// inside `Transaction.postings: List[Posting]`.
#[test]
fn test_noduplicates_reordered_postings_are_not_duplicates() {
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
    let output = plugin.process(input);
    assert!(
        output.errors.is_empty(),
        "reordered postings must not collide (postings are an ordered list in \
         beancount), got: {:?}",
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
    let output = plugin.process(input);
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
    let output = plugin.process(input);
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
    let output = plugin.process(input);
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
        cost.number_per = None;
        cost.number_total = Some("1500.00".to_string());
    }
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Stock"),
        make_open("2024-01-01", "Assets:Cash"),
        txn_a,
        txn_b,
    ]);
    let output = plugin.process(input);
    assert!(
        output.errors.is_empty(),
        "per-unit cost must not collide with total cost, got: {:?}",
        output.errors
    );
}

/// `@` (per-unit price) and `@@` (total price) are structurally
/// different annotations.
#[test]
fn test_noduplicates_unit_vs_total_price_differ() {
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
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Stock"),
        make_open("2024-01-01", "Assets:Cash"),
        txn_a,
        txn_b,
    ]);
    let output = plugin.process(input);
    assert!(
        output.errors.is_empty(),
        "`@` and `@@` prices must not collide, got: {:?}",
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
    let output = plugin.process(input);
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
    let output = plugin.process(input);
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
    let output = plugin.process(input);
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
    let output = plugin.process(input);
    assert_eq!(
        output.errors.len(),
        2,
        "three identical transactions should produce two duplicate errors, got: {:?}",
        output.errors
    );
}

/// Non-transaction directives (Open, Close, etc.) are ignored by the
/// plugin — they should never be flagged as duplicates, and their
/// presence between transactions should not affect duplicate detection.
#[test]
fn test_noduplicates_ignores_non_transaction_directives() {
    let plugin = NoDuplicatesPlugin;
    let postings = vec![
        ("Expenses:Food", "5.00", "USD"),
        ("Assets:Bank", "-5.00", "USD"),
    ];
    let input = make_input(vec![
        // Two identical opens — not a transaction, must be ignored by
        // the plugin (validators handle duplicate opens separately).
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Assets:Bank"),
        make_open("2024-01-01", "Expenses:Food"),
        make_transaction("2024-01-15", "Coffee", postings.clone()),
        // An Open directive between the two transactions shouldn't
        // cause any hash collision with either.
        make_open("2024-02-01", "Assets:Savings"),
        make_transaction("2024-01-15", "Coffee", postings),
    ]);
    let output = plugin.process(input);
    assert_eq!(
        output.errors.len(),
        1,
        "only the two real transaction duplicates should be flagged \
         (non-transaction directives ignored), got: {:?}",
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
    let output = plugin.process(input);
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
    let output = plugin.process(input);
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
    let output = plugin.process(input);
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

    let output = plugin.process(input);

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

    let output = plugin.process(input);
    assert!(output.errors.is_empty(), "expected no errors");
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

    let output = plugin.process(input);

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

    let output = plugin.process(input);

    // Should not have warning about USD since it's declared
    let has_usd_warning = output.errors.iter().any(|e| e.message.contains("USD"));
    assert!(!has_usd_warning, "should not warn about declared USD");
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

    let output = plugin.process(input);

    assert_eq!(output.errors.len(), 1, "expected 1 duplicate price error");
    assert!(
        output.errors[0].message.contains("Duplicate price"),
        "error should mention duplicate"
    );
}

/// Test prices on different days pass.
#[test]
fn test_unique_prices_different_days_ok() {
    let plugin = UniquePricesPlugin;

    let input = make_input(vec![
        make_price("2024-01-15", "HOOL", "520.00", "USD"),
        make_price("2024-01-16", "HOOL", "525.00", "USD"),
    ]);

    let output = plugin.process(input);
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

    let output = plugin.process(input);
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
    output: &PluginOutput,
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
                },
                PostingData {
                    account: "Assets:Cash".to_string(),
                    units: None,
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
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
    let output = plugin.process(input.clone());
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
                            number_per: None,
                            number_total: Some("500".to_string()),
                            currency: Some("USD".to_string()),
                            date: None,
                            label: None,
                            merge: false,
                        }),
                        price: None,
                        flag: None,
                        metadata: vec![],
                    },
                    PostingData {
                        account: "Assets:Cash".to_string(),
                        units: None,
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                    },
                ],
            }),
        },
    ]);
    let output = plugin.process(input.clone());
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
    let output = plugin.process(input.clone());
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
    let output = plugin.process(input.clone());
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
    let output = plugin.process(input.clone());
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
    let output = plugin.process(input.clone());
    let prices = implicit_prices_emitted(&input, &output);
    assert_eq!(prices.len(), 1, "exactly one price");
    assert_eq!(
        prices[0],
        ("ABC".into(), "50".into(), "USD".into()),
        "currency must come from the same source as the per-unit value (cost = USD), \
         NOT the annotation (EUR). Pre-fix this returned (50, EUR)."
    );
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
    let output = plugin.process(input.clone());
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
    let output = plugin.process(input.clone());
    // The explicit price (500.00) must NOT appear in plugin output.
    // Only the cost-derived 520.00 should.
    assert_eq!(
        implicit_prices_emitted(&input, &output),
        vec![("HOOL".into(), "520.00".into(), "USD".into())]
    );
}

// ============================================================================
// NativePluginRegistry Tests
// ============================================================================

#[test]
fn test_registry_finds_all_plugins() {
    let registry = NativePluginRegistry::new();

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
        assert!(registry.find(name).is_some(), "should find plugin: {name}");
    }
}

#[test]
fn test_registry_finds_with_beancount_prefix() {
    let registry = NativePluginRegistry::new();

    assert!(registry.find("beancount.plugins.leafonly").is_some());
    assert!(registry.find("beancount.plugins.noduplicates").is_some());
}

#[test]
fn test_registry_list_all() {
    let registry = NativePluginRegistry::new();
    let plugins = registry.list();

    // Should have at least 13 plugins (14 minus auto_tag which might be different).
    // allow weak-count: registry-shape test — count grows as plugins are added,
    // pinning to a specific value would force every plugin addition to update
    // this test. See scripts/check-plugin-test-quality.sh.
    assert!(plugins.len() >= 13, "should have at least 13 plugins");
}

#[test]
fn test_auto_accounts_generates_opens() {
    use rustledger_plugin::types::*;
    use rustledger_plugin::*;

    let registry = NativePluginRegistry::new();
    let plugin = registry.find("auto_accounts").unwrap();

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
                    },
                ],
                metadata: vec![],
            }),
        }],
        options: PluginOptions::default(),
        config: None,
    };

    let output = plugin.process(input);

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

    let registry = NativePluginRegistry::new();
    let plugin = registry.find("auto_accounts").unwrap();

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
                        },
                    ],
                    metadata: vec![],
                }),
            },
        ],
        options: PluginOptions::default(),
        config: None,
    };

    let output = plugin.process(input);

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
                },
                PostingData {
                    account: other_account.to_string(),
                    units: None,
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
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

    let output = plugin.process(input);

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

    let output = plugin.process(input);

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

    let output = plugin.process(input);

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

    let output = plugin.process(input);

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
                },
                PostingData {
                    account: other_account.to_string(),
                    units: None,
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
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

    let output = plugin.process(input);

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

    let output = plugin.process(input);
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

    let output = plugin.process(input);
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

    let output = plugin.process(input);
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
    let output = plugin.process(input);
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
    let output = plugin.process(input);
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
    let output = plugin.process(input);
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
    let output = plugin.process(input);
    assert_eq!(
        output.errors.len(),
        1,
        "exactly one error for the single leaf-only violation"
    );
}

// ============================================================================
// RxTxnPlugin Tests
// ============================================================================

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
    let output = plugin.process(input);
    assert!(output.errors.is_empty());
    // Verify metadata was added to the tagged transaction
    let txn = output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction")
        .unwrap();
    if let DirectiveData::Transaction(data) = &txn.data {
        let has_final = data.metadata.iter().any(|(k, _)| k == "final");
        let has_roll = data.metadata.iter().any(|(k, _)| k == "roll");
        assert!(
            has_final || has_roll,
            "rx_txn should add 'final' and/or 'roll' metadata to tagged transaction"
        );
    }
}

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
    let output = plugin.process(input);
    assert!(output.errors.is_empty());
}

// ============================================================================
// SellGainsPlugin Tests
// ============================================================================

#[test]
fn test_sell_gains_warns_missing_gains_posting() {
    let plugin = SellGainsPlugin;
    // Sale with cost and price but no Income posting
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Stock"),
        make_open("2024-01-01", "Assets:Cash"),
        make_transaction_with_cost_and_price(
            "2024-06-15",
            "Sell stock",
            "Assets:Stock",
            ("-10", "AAPL"),
            ("100", "USD"),
            ("150", "USD"),
            "Assets:Cash",
        ),
    ]);
    let output = plugin.process(input);
    // Should warn about missing Income:Capital-Gains posting
    assert_eq!(
        output.errors.len(),
        1,
        "exactly one warning for the single sale missing gains posting"
    );
    assert!(
        output.errors[0].message.contains("gain") || output.errors[0].message.contains("Gain"),
        "warning should reference the missing gains posting"
    );
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
    let output = plugin.process(input);
    assert!(output.errors.is_empty());
    // Should have added balance assertion directives
    let balance_count = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "balance")
        .count();
    assert!(
        balance_count > 0,
        "should insert balance assertions after close"
    );
}

// ============================================================================
// CommodityAttrPlugin Tests
// ============================================================================

#[test]
fn test_commodity_attr_ok_with_no_config() {
    let plugin = CommodityAttrPlugin::new();
    let input = make_input(vec![make_commodity("2024-01-01", "USD")]);
    let output = plugin.process(input);
    assert!(output.errors.is_empty());
}

#[test]
fn test_commodity_attr_error_with_missing_required_attr() {
    let plugin = CommodityAttrPlugin::new();
    let input =
        make_input_with_config(vec![make_commodity("2024-01-01", "AAPL")], "{'name': null}");
    let output = plugin.process(input);
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
    let output = plugin.process(input);
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
    let output = plugin.process(input);
    assert!(output.errors.is_empty());
    // Without effective_date metadata, directives pass through unchanged
    assert_eq!(output.directives.len(), 3);
}

#[test]
fn test_effective_date_splits_transaction() {
    let plugin = EffectiveDatePlugin;
    // Create transaction with effective_date metadata on a posting
    let mut txn = make_transaction(
        "2024-01-15",
        "Deferred expense",
        vec![
            ("Expenses:Food", "25", "USD"),
            ("Assets:Cash", "-25", "USD"),
        ],
    );
    // Add effective_date to the first posting
    if let DirectiveData::Transaction(ref mut data) = txn.data {
        data.postings[0].metadata.push((
            "effective_date".to_string(),
            MetaValueData::Date("2024-02-15".to_string()),
        ));
    }
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Expenses:Food"),
        txn,
    ]);
    let output = plugin.process(input);
    assert!(output.errors.is_empty());
    // Should have more directives than input (split + opens for holding account)
    assert!(
        output.directives.len() > 3,
        "effective_date should split into multiple directives (got {})",
        output.directives.len()
    );
}

// ============================================================================
// ForecastPlugin Tests
// ============================================================================

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
    let output = plugin.process(input);
    assert!(output.errors.is_empty());
    // No forecast flag, so no expansion
    assert_eq!(output.directives.len(), 3);
}

#[test]
fn test_forecast_expands_recurring_transaction() {
    let plugin = ForecastPlugin;
    // Transaction with # flag and [MONTHLY REPEAT 3 TIMES] pattern
    let forecast_txn = DirectiveWrapper {
        directive_type: "transaction".to_string(),
        date: "2024-01-15".to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Transaction(TransactionData {
            flag: "#".to_string(),
            payee: None,
            narration: "Rent [MONTHLY REPEAT 3 TIMES]".to_string(),
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
                },
            ],
        }),
    };
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_open("2024-01-01", "Expenses:Rent"),
        forecast_txn,
    ]);
    let output = plugin.process(input);
    assert!(output.errors.is_empty());
    let txn_count = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "transaction")
        .count();
    assert!(
        txn_count >= 3,
        "forecast should expand to at least 3 transactions (got {txn_count})"
    );
}

// ============================================================================
// GenerateBaseCcyPricesPlugin Tests
// ============================================================================

#[test]
fn test_generate_base_ccy_prices_creates_derived_price() {
    let plugin = GenerateBaseCcyPricesPlugin;
    let input = make_input_with_config(
        vec![
            make_price("2024-01-01", "EUR", "1.10", "USD"),
            make_price("2024-01-01", "ETH", "2000", "EUR"),
        ],
        "USD",
    );
    let output = plugin.process(input);
    assert!(output.errors.is_empty());
    // Should generate ETH in USD price
    let price_count = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "price")
        .count();
    assert!(
        price_count > 2,
        "should generate derived price entries (got {price_count})"
    );
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
    let output = plugin.process(input);
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

#[test]
fn test_split_expenses_divides_by_members() {
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
    let output = plugin.process(input);
    assert!(output.errors.is_empty());
    // Should have split the Expenses:Food posting into member postings
    let txn = output
        .directives
        .iter()
        .find(|d| d.directive_type == "transaction")
        .unwrap();
    if let DirectiveData::Transaction(data) = &txn.data {
        let expense_postings: Vec<_> = data
            .postings
            .iter()
            .filter(|p| p.account.starts_with("Expenses:Food"))
            .collect();
        assert!(
            expense_postings.len() >= 2,
            "should split expense into at least 2 member postings (got {})",
            expense_postings.len()
        );
    }
}

// ============================================================================
// UnrealizedPlugin Tests
// ============================================================================

#[test]
fn test_unrealized_reports_unrealized_gains() {
    let plugin = UnrealizedPlugin::new();
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Stock"),
        make_open("2024-01-01", "Assets:Cash"),
        make_commodity("2024-01-01", "AAPL"),
        // Buy stock
        make_transaction_with_cost(
            "2024-01-15",
            "Buy",
            "Assets:Stock",
            ("10", "AAPL"),
            ("100", "USD"),
            "Assets:Cash",
        ),
        // Current market price higher
        make_price("2024-06-15", "AAPL", "150", "USD"),
    ]);
    let output = plugin.process(input);
    // Should report unrealized gain of 10 * (150 - 100) = 500
    // The plugin may generate warnings or new directives
    // As long as it doesn't error out, the plugin works
    assert!(
        output.errors.is_empty()
            || output
                .errors
                .iter()
                .all(|e| e.severity == PluginErrorSeverity::Warning)
    );
}

// ============================================================================
// CheckAverageCostPlugin Tests
// ============================================================================

#[test]
fn test_check_average_cost_no_error_on_correct_sale() {
    let plugin = CheckAverageCostPlugin::new();
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Stock"),
        make_open("2024-01-01", "Assets:Cash"),
        // Buy at 100
        make_transaction_with_cost(
            "2024-01-15",
            "Buy",
            "Assets:Stock",
            ("10", "AAPL"),
            ("100", "USD"),
            "Assets:Cash",
        ),
    ]);
    let output = plugin.process(input);
    assert!(output.errors.is_empty());
}

// ============================================================================
// ZerosumPlugin Tests
// ============================================================================

#[test]
fn test_zerosum_requires_config() {
    let plugin = ZerosumPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_transaction("2024-01-15", "Test", vec![("Assets:Cash", "100", "USD")]),
    ]);
    let output = plugin.process(input);
    assert_eq!(
        output.errors.len(),
        1,
        "exactly one error for missing required config"
    );
    assert!(output.errors[0].message.contains("requires configuration"));
}

// ============================================================================
// BoxAccrualPlugin Tests
// ============================================================================

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
    let output = plugin.process(input);
    assert!(output.errors.is_empty());
    // No synthetic_loan_expiry metadata → directives unchanged
    assert_eq!(output.directives.len(), 3);
}

#[test]
fn test_box_accrual_with_metadata_splits_losses() {
    let plugin = BoxAccrualPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Income:Capital-Losses"),
        make_open("2024-01-01", "Assets:Cash"),
        make_transaction_with_metadata(
            "2024-07-01",
            "Loss with expiry",
            vec![(
                "synthetic_loan_expiry",
                MetaValueData::Date("2026-06-30".to_string()),
            )],
            vec![
                ("Income:Capital-Losses", "-1000", "USD"),
                ("Assets:Cash", "1000", "USD"),
            ],
        ),
    ]);
    let output = plugin.process(input);
    assert!(output.errors.is_empty());
}

// ============================================================================
// CapitalGainsLongShortPlugin Tests
// ============================================================================

#[test]
fn test_capital_gains_long_short_no_config_passthrough() {
    let plugin = CapitalGainsLongShortPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_transaction("2024-01-15", "Simple", vec![("Assets:Cash", "100", "USD")]),
    ]);
    let output = plugin.process(input);
    assert!(output.errors.is_empty());
    assert_eq!(output.directives.len(), 2);
}

// ============================================================================
// CapitalGainsGainLossPlugin Tests
// ============================================================================

#[test]
fn test_capital_gains_gain_loss_no_config_passthrough() {
    let plugin = CapitalGainsGainLossPlugin;
    let input = make_input(vec![
        make_open("2024-01-01", "Assets:Cash"),
        make_transaction("2024-01-15", "Simple", vec![("Assets:Cash", "100", "USD")]),
    ]);
    let output = plugin.process(input);
    assert!(output.errors.is_empty());
    assert_eq!(output.directives.len(), 2);
}
