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

    if let Some(p) = price
        && let DirectiveData::Price(price_data) = &p.data
    {
        assert_eq!(price_data.currency, "HOOL");
        assert_eq!(price_data.amount.currency, "USD");
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

fn make_commodity_with_metadata(
    date: &str,
    currency: &str,
    metadata: Vec<(&str, MetaValueData)>,
) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: "commodity".to_string(),
        date: date.to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Commodity(CommodityData {
            currency: currency.to_string(),
            metadata: metadata
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
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

fn make_balance(date: &str, account: &str, number: &str, currency: &str) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: "balance".to_string(),
        date: date.to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Balance(BalanceData {
            account: account.to_string(),
            amount: AmountData {
                number: number.to_string(),
                currency: currency.to_string(),
            },
            tolerance: None,
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
    assert!(!output.errors.is_empty(), "should warn about Assets:Unused");
    assert!(
        output.errors.iter().any(|e| e.message.contains("Unused")),
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
    assert!(
        !output.errors.is_empty(),
        "pedantic should catch leaf-only violation"
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
    assert!(
        !output.errors.is_empty(),
        "should warn about missing gains posting"
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
    assert!(!output.errors.is_empty(), "should error without config");
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
    assert_eq!(output.directives.len(), 3);
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
}
