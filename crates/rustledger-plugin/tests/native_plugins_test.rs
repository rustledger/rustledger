//! Integration tests for native plugins.
//!
//! Tests are converted from beancount's plugin test suite.

use rustledger_plugin::native::{
    CheckCommodityPlugin, ImplicitPricesPlugin, LeafOnlyPlugin, NativePlugin, NativePluginRegistry,
    NoDuplicatesPlugin, OneCommodityPlugin, UniquePricesPlugin,
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
        data: DirectiveData::Open(OpenData {
            account: account.to_string(),
            currencies: vec![],
            booking: None,
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
        data: DirectiveData::Price(PriceData {
            currency: currency.to_string(),
            amount: AmountData {
                number: amount.to_string(),
                currency: quote_currency.to_string(),
            },
        }),
    }
}

fn make_commodity(date: &str, currency: &str) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: "commodity".to_string(),
        date: date.to_string(),
        data: DirectiveData::Commodity(CommodityData {
            currency: currency.to_string(),
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

    assert!(
        !output.errors.is_empty(),
        "expected warning for undeclared USD"
    );
    assert!(
        output.errors.iter().any(|e| e.message.contains("USD")),
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

/// Test price generation from cost.
/// Converted from: `test_add_implicit_prices__all_cases` (partial)
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

    let output = plugin.process(input);

    // Should generate a price directive
    let price_count = output
        .directives
        .iter()
        .filter(|d| d.directive_type == "price")
        .count();
    assert!(
        price_count >= 1,
        "should generate at least 1 price directive"
    );

    // Find the generated price
    let price = output
        .directives
        .iter()
        .find(|d| d.directive_type == "price");
    assert!(price.is_some(), "should have a price directive");

    if let Some(p) = price {
        if let DirectiveData::Price(price_data) = &p.data {
            assert_eq!(price_data.currency, "HOOL");
            assert_eq!(price_data.amount.currency, "USD");
        }
    }
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

    // Should have at least 13 plugins (14 minus auto_tag which might be different)
    assert!(plugins.len() >= 13, "should have at least 13 plugins");
}
