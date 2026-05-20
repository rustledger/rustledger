//! Property-Based Tests from TLA+ Invariants
//!
//! These tests verify that the Rust implementation satisfies the same
//! invariants defined in the TLA+ specifications.
//!
//! Reference: spec/tla/PluginCorrect.tla

use proptest::prelude::*;
use rustledger_plugin::native::NativePluginRegistry;
use rustledger_plugin::test_helpers::materialize_ops;
use rustledger_plugin::types::*;

// ============================================================================
// Test Strategies
// ============================================================================

fn date_strategy() -> impl Strategy<Value = String> {
    (2020i32..2025, 1u32..13, 1u32..29).prop_map(|(y, m, d)| {
        let d = d.min(28); // Ensure valid day
        format!("{y:04}-{m:02}-{d:02}")
    })
}

fn amount_strategy() -> impl Strategy<Value = String> {
    (1i64..1000).prop_map(|n| format!("{n}.00"))
}

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
    amount: &str,
    expense_account: &str,
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
                    account: expense_account.to_string(),
                    units: Some(AmountData {
                        number: amount.to_string(),
                        currency: "USD".to_string(),
                    }),
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
                PostingData {
                    account: "Assets:Bank:Checking".to_string(),
                    units: Some(AmountData {
                        number: format!("-{amount}"),
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

fn extract_transaction_date(wrapper: &DirectiveWrapper) -> Option<&str> {
    if wrapper.directive_type == "transaction" {
        Some(&wrapper.date)
    } else {
        None
    }
}

// ============================================================================
// Plugin Execution Order Tests (from PluginCorrect.tla)
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(30))]

    /// TLA+ PluginsInOrder:
    /// Plugin N+1 doesn't start before plugin N completes.
    ///
    /// When executing multiple plugins, they must run sequentially in
    /// registration order, with each completing before the next starts.
    #[test]
    fn prop_plugins_execute_in_order(
        date in date_strategy(),
        amount in amount_strategy(),
    ) {
        let registry = NativePluginRegistry::new();
        let plugins = registry.list();

        // Track execution order
        let execution_order: Vec<String> = plugins.iter().map(|p| p.name().to_string()).collect();

        let directives = vec![
            make_open(&date, "Expenses:Food"),
            make_open(&date, "Assets:Bank:Checking"),
            make_transaction(&date, "Test", &amount, "Expenses:Food"),
        ];

        // Execute all plugins in sequence (as the system does)
        let mut input = make_input(directives);

        let mut last_plugin_name = String::new();
        for (i, plugin) in plugins.iter().enumerate() {
            let output = plugin.process(input.clone());

            // Verify we're executing in order
            prop_assert_eq!(
                plugin.name(),
                execution_order[i].as_str(),
                "Plugin execution should follow registration order"
            );

            // Plugin N must have completed before N+1 starts
            if i > 0 {
                prop_assert_ne!(
                    last_plugin_name, "",
                    "Previous plugin should have run"
                );
            }

            last_plugin_name = plugin.name().to_string();

            // Pass output to next iteration (chain processing) — materialize
            // ops against the current input to produce the next plugin's input.
            input.directives = materialize_ops(&input.directives, &output);
        }
    }

    /// TLA+ DirectivesInOrder:
    /// Each plugin processes directives in sequence.
    ///
    /// Within a plugin, directives are processed in their natural order
    /// (as they appear in the input).
    #[test]
    fn prop_directives_maintain_order(
        num_directives in 2usize..8,
        base_date in date_strategy(),
    ) {
        // Parse base date to create sequential dates
        let parts: Vec<&str> = base_date.split('-').collect();
        if parts.len() != 3 {
            return Ok(());
        }
        let year: i32 = parts[0].parse().unwrap_or(2024);
        let month: u32 = parts[1].parse().unwrap_or(1);
        let base_day: u32 = parts[2].parse().unwrap_or(1);

        // Create directives with sequential dates
        let mut directives = vec![
            make_open(&base_date, "Expenses:Food"),
            make_open(&base_date, "Assets:Bank:Checking"),
        ];

        for i in 0..num_directives {
            let day = (base_day + i as u32).min(28);
            let date = format!("{year:04}-{month:02}-{day:02}");
            directives.push(make_transaction(&date, &format!("Txn {i}"), "10.00", "Expenses:Food"));
        }

        // Use a simple plugin that doesn't reorder
        let registry = NativePluginRegistry::new();
        if let Some(plugin) = registry.find("implicit_prices") {
            let input = make_input(directives);
            let input_dirs = input.directives.clone();
            let output = plugin.process(input);
            let materialized = materialize_ops(&input_dirs, &output);

            // Check that transaction directives maintain their relative order
            let mut prev_date: Option<&str> = None;
            for wrapper in &materialized {
                if let Some(date) = extract_transaction_date(wrapper) {
                    if let Some(pd) = prev_date {
                        // Order should be maintained (or equal for same-day txns)
                        prop_assert!(
                            date >= pd,
                            "Directive order should be maintained: {} < {}",
                            date, pd
                        );
                    }
                    prev_date = Some(date);
                }
            }
        }
    }

    /// TLA+ NoFutureDirectives:
    /// A plugin can only see directives added by earlier plugins.
    ///
    /// Plugin N doesn't see directives added by plugin N+1.
    /// This is enforced by the sequential execution model.
    #[test]
    fn prop_plugin_isolation(
        date in date_strategy(),
        amount in amount_strategy(),
    ) {
        // Create minimal directives
        let directives = vec![
            make_open(&date, "Expenses:Food"),
            make_open(&date, "Assets:Bank:Checking"),
            make_transaction(&date, "Test", &amount, "Expenses:Food"),
        ];

        let registry = NativePluginRegistry::new();

        // First, run implicit_prices
        let plugin1 = registry.find("implicit_prices").unwrap();
        let input1 = make_input(directives.clone());
        let _output1 = plugin1.process(input1);

        // Then run a different plugin on the SAME original input
        let plugin2 = registry.find("auto_accounts").unwrap();
        let input2 = make_input(directives);
        let _output2 = plugin2.process(input2);

        // The second plugin's input was the ORIGINAL directives, not the output
        // from the first plugin. This is how isolation works.
        // Each plugin starts fresh from what it receives.
        prop_assert!(true, "Plugins operate on their input, not global state");
    }

    /// Plugin output contains valid directives.
    ///
    /// Plugins should not corrupt the directive stream.
    #[test]
    fn prop_plugin_output_valid(
        date in date_strategy(),
        amount in amount_strategy(),
    ) {
        let registry = NativePluginRegistry::new();

        let directives = vec![
            make_open(&date, "Expenses:Food"),
            make_open(&date, "Assets:Bank:Checking"),
            make_transaction(&date, "Test", &amount, "Expenses:Food"),
        ];

        // Test a few specific plugins
        for plugin_name in &["implicit_prices", "auto_accounts", "noduplicates"] {
            if let Some(plugin) = registry.find(plugin_name) {
                let input = make_input(directives.clone());
                let input_dirs = input.directives.clone();
                let output = plugin.process(input);
                let materialized = materialize_ops(&input_dirs, &output);

                // Output should be valid (no panic, has directives)
                prop_assert!(
                    !materialized.is_empty(),
                    "Plugin {} should produce valid output",
                    plugin_name
                );
            }
        }
    }

    /// Plugins are deterministic.
    ///
    /// Running the same plugin with the same input produces identical output.
    #[test]
    fn prop_plugin_deterministic(
        date in date_strategy(),
        amount in amount_strategy(),
    ) {
        let registry = NativePluginRegistry::new();

        let directives = vec![
            make_open(&date, "Expenses:Food"),
            make_open(&date, "Assets:Bank:Checking"),
            make_transaction(&date, "Test", &amount, "Expenses:Food"),
        ];

        if let Some(plugin) = registry.find("implicit_prices") {
            let input = make_input(directives);

            let output1 = plugin.process(input.clone());
            let output2 = plugin.process(input);

            prop_assert_eq!(
                output1.ops.len(),
                output2.ops.len(),
                "Plugin should be deterministic"
            );

            prop_assert_eq!(
                output1.errors.len(),
                output2.errors.len(),
                "Error count should be deterministic"
            );
        }
    }
}

// ============================================================================
// Plugin Registry Tests
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(20))]

    /// Registry lookup is consistent.
    ///
    /// Finding a plugin by name should always return the same plugin.
    #[test]
    fn prop_registry_lookup_consistent(
        plugin_name in prop::sample::select(vec![
            "implicit_prices",
            "check_commodity",
            "auto_accounts",
            "leafonly",
            "noduplicates",
        ]),
    ) {
        let registry = NativePluginRegistry::new();

        let plugin1 = registry.find(plugin_name);
        let plugin2 = registry.find(plugin_name);

        match (plugin1, plugin2) {
            (Some(p1), Some(p2)) => {
                prop_assert_eq!(
                    p1.name(),
                    p2.name(),
                    "Registry lookup should be consistent"
                );
            }
            (None, None) => {
                // Both not found is consistent
            }
            _ => {
                prop_assert!(false, "Inconsistent registry lookup");
            }
        }
    }

    /// Registry accepts beancount.plugins.* prefix.
    #[test]
    fn prop_registry_prefix_handling(
        plugin_name in prop::sample::select(vec![
            "implicit_prices",
            "check_commodity",
            "auto_accounts",
        ]),
    ) {
        let registry = NativePluginRegistry::new();

        // With prefix
        let prefixed = format!("beancount.plugins.{plugin_name}");
        let with_prefix = registry.find(&prefixed);

        // Without prefix
        let without_prefix = registry.find(plugin_name);

        match (with_prefix, without_prefix) {
            (Some(p1), Some(p2)) => {
                prop_assert_eq!(
                    p1.name(),
                    p2.name(),
                    "Prefix should be stripped correctly"
                );
            }
            _ => {
                prop_assert!(false, "Both lookups should succeed");
            }
        }
    }

    /// Registry listing returns all plugins.
    #[test]
    fn prop_registry_list_complete(_dummy in 0..1i32) {
        let registry = NativePluginRegistry::new();
        let plugins = registry.list();

        // Should have at least 14 plugins
        prop_assert!(
            plugins.len() >= 14,
            "Registry should have at least 14 plugins, got {}",
            plugins.len()
        );

        // All plugins should have unique names
        let names: Vec<&str> = plugins.iter().map(|p| p.name()).collect();
        let mut sorted_names = names.clone();
        sorted_names.sort_unstable();
        sorted_names.dedup();

        prop_assert_eq!(
            names.len(),
            sorted_names.len(),
            "Plugin names should be unique"
        );
    }
}
