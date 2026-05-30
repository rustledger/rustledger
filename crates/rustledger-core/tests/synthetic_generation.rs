//! Synthetic beancount file generation using proptest.
//!
//! This module provides proptest strategies for generating arbitrary directives
//! that can be serialized to valid beancount text and validated with bean-check.
//!
//! Run with: cargo test -p rustledger-core --test `synthetic_generation`

use proptest::prelude::*;
use rust_decimal::Decimal;
use rustledger_core::NaiveDate;
use rustledger_core::{
    Amount, Balance, Close, Commodity, Custom, Directive, Document, Event, FormatConfig, MetaValue,
    Note, Open, Pad, Posting, Price, Query, Transaction, format_directives,
};

// ============================================================================
// Primitive Generators
// ============================================================================

/// Generate dates in a reasonable range
fn arb_date() -> impl Strategy<Value = NaiveDate> {
    (2020i32..2026i32, 1u32..13u32, 1u32..29u32)
        .prop_map(|(y, m, d)| rustledger_core::naive_date(y, m, d).unwrap())
}

/// Generate reasonable decimal values
fn arb_decimal() -> impl Strategy<Value = Decimal> {
    (-1_000_000i64..1_000_000i64).prop_map(|n| Decimal::new(n, 2))
}

/// Generate positive decimal values
fn arb_positive_decimal() -> impl Strategy<Value = Decimal> {
    (1i64..1_000_000i64).prop_map(|n| Decimal::new(n, 2))
}

/// Generate currency codes
fn arb_currency() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("USD".to_string()),
        Just("EUR".to_string()),
        Just("GBP".to_string()),
        Just("CAD".to_string()),
        Just("JPY".to_string()),
        Just("CHF".to_string()),
    ]
}

/// Generate stock/commodity symbols
fn arb_stock() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("AAPL".to_string()),
        Just("GOOGL".to_string()),
        Just("MSFT".to_string()),
        Just("VTI".to_string()),
        Just("BTC".to_string()),
    ]
}

/// Generate amount with currency
fn arb_amount() -> impl Strategy<Value = Amount> {
    (arb_decimal(), arb_currency()).prop_map(|(n, c)| Amount::new(n, c))
}

/// Generate positive amount
fn arb_positive_amount() -> impl Strategy<Value = Amount> {
    (arb_positive_decimal(), arb_currency()).prop_map(|(n, c)| Amount::new(n, c))
}

// ============================================================================
// Account Name Generators
// ============================================================================

/// Account type prefixes
fn arb_account_type() -> impl Strategy<Value = &'static str> {
    prop_oneof![
        Just("Assets"),
        Just("Liabilities"),
        Just("Equity"),
        Just("Income"),
        Just("Expenses"),
    ]
}

/// Account subtype names
fn arb_account_subtype() -> impl Strategy<Value = &'static str> {
    prop_oneof![
        Just("Bank"),
        Just("Cash"),
        Just("Checking"),
        Just("Savings"),
        Just("CreditCard"),
        Just("Investments"),
        Just("Salary"),
        Just("Food"),
        Just("Rent"),
        Just("Utilities"),
        Just("Opening-Balances"),
    ]
}

/// Generate valid beancount account names
fn arb_account() -> impl Strategy<Value = String> {
    (arb_account_type(), arb_account_subtype()).prop_map(|(typ, sub)| format!("{typ}:{sub}"))
}

/// Generate equity accounts for padding
fn arb_equity_account() -> impl Strategy<Value = String> {
    Just("Equity:Opening-Balances".to_string())
}

// ============================================================================
// String Generators (for narrations, payees, etc.)
// ============================================================================

/// Generate safe narration strings (no quotes or special chars)
fn arb_narration() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("Grocery shopping".to_string()),
        Just("Monthly rent payment".to_string()),
        Just("Coffee".to_string()),
        Just("Salary deposit".to_string()),
        Just("Transfer".to_string()),
        Just("Dividend payment".to_string()),
        Just("Gas station".to_string()),
        Just("Restaurant dinner".to_string()),
        Just("Online purchase".to_string()),
        Just("Subscription".to_string()),
    ]
}

/// Generate safe payee strings
fn arb_payee() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("Amazon".to_string()),
        Just("Whole Foods".to_string()),
        Just("Shell".to_string()),
        Just("Netflix".to_string()),
        Just("Employer Inc".to_string()),
        Just("Landlord".to_string()),
        Just("Vanguard".to_string()),
        Just("Bank Transfer".to_string()),
    ]
}

/// Generate tag names (alphanumeric)
fn arb_tag() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("food".to_string()),
        Just("travel".to_string()),
        Just("work".to_string()),
        Just("home".to_string()),
        Just("medical".to_string()),
        Just("entertainment".to_string()),
    ]
}

/// Generate link names
fn arb_link() -> impl Strategy<Value = String> {
    (1u32..1000u32).prop_map(|n| format!("invoice-{n}"))
}

/// Generate event types
fn arb_event_type() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("location".to_string()),
        Just("employer".to_string()),
        Just("address".to_string()),
    ]
}

/// Generate event values
fn arb_event_value() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("New York, NY".to_string()),
        Just("San Francisco, CA".to_string()),
        Just("Remote".to_string()),
        Just("Acme Corp".to_string()),
    ]
}

/// Generate file paths for documents
fn arb_document_path() -> impl Strategy<Value = String> {
    (2020u32..2026u32, 1u32..13u32).prop_map(|(y, m)| format!("/documents/{y}/{m:02}/receipt.pdf"))
}

/// Generate query names
fn arb_query_name() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("monthly-expenses".to_string()),
        Just("income-summary".to_string()),
        Just("balance-sheet".to_string()),
    ]
}

/// Generate BQL queries
fn arb_query_string() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("SELECT account, sum(position) GROUP BY account".to_string()),
        Just("SELECT date, narration, position".to_string()),
        Just("SELECT currency, sum(position) GROUP BY currency".to_string()),
    ]
}

/// Generate custom directive types
fn arb_custom_type() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("budget".to_string()),
        Just("autopay".to_string()),
        Just("goal".to_string()),
    ]
}

// ============================================================================
// Directive Generators
// ============================================================================

/// Generate an Open directive
fn arb_open() -> impl Strategy<Value = Open> {
    (arb_date(), arb_account(), prop::option::of(arb_currency())).prop_map(
        |(date, account, currency)| {
            let mut open = Open::new(date, account);
            if let Some(c) = currency {
                open = open.with_currencies(vec![c.into()]);
            }
            open
        },
    )
}

/// Generate a Close directive
fn arb_close() -> impl Strategy<Value = Close> {
    (arb_date(), arb_account()).prop_map(|(date, account)| Close::new(date, account))
}

/// Generate a Commodity directive
fn arb_commodity() -> impl Strategy<Value = Commodity> {
    (arb_date(), prop_oneof![arb_currency(), arb_stock()])
        .prop_map(|(date, currency)| Commodity::new(date, currency))
}

/// Generate a Balance directive
fn arb_balance() -> impl Strategy<Value = Balance> {
    (arb_date(), arb_account(), arb_amount())
        .prop_map(|(date, account, amount)| Balance::new(date, account, amount))
}

/// Generate a Pad directive
fn arb_pad() -> impl Strategy<Value = Pad> {
    (arb_date(), arb_account(), arb_equity_account())
        .prop_map(|(date, account, source)| Pad::new(date, account, source))
}

/// Generate a balanced Transaction (two postings that sum to zero)
fn arb_transaction() -> impl Strategy<Value = Transaction> {
    (
        arb_date(),
        arb_narration(),
        prop::option::of(arb_payee()),
        arb_account(),
        arb_account(),
        arb_positive_amount(),
        prop::option::of(arb_tag()),
        prop::option::of(arb_link()),
        prop::bool::ANY, // flag: * or !
    )
        .prop_map(
            |(date, narration, payee, from_account, to_account, amount, tag, link, is_complete)| {
                let flag = if is_complete { '*' } else { '!' };
                let mut txn = Transaction::new(date, narration).with_flag(flag);

                if let Some(p) = payee {
                    txn = txn.with_payee(p);
                }
                if let Some(t) = tag {
                    txn = txn.with_tag(t);
                }
                if let Some(l) = link {
                    txn = txn.with_link(l);
                }

                // Create balanced postings
                let debit = Posting::new(&to_account, amount.clone());
                let credit = Posting::new(&from_account, -amount);

                txn.with_synthesized_posting(debit)
                    .with_synthesized_posting(credit)
            },
        )
}

/// Generate an Event directive
fn arb_event() -> impl Strategy<Value = Event> {
    (arb_date(), arb_event_type(), arb_event_value())
        .prop_map(|(date, event_type, value)| Event::new(date, event_type, value))
}

/// Generate a Query directive
fn arb_query() -> impl Strategy<Value = Query> {
    (arb_date(), arb_query_name(), arb_query_string())
        .prop_map(|(date, name, query)| Query::new(date, name, query))
}

/// Generate a Note directive
fn arb_note() -> impl Strategy<Value = Note> {
    (arb_date(), arb_account(), arb_narration())
        .prop_map(|(date, account, comment)| Note::new(date, account, comment))
}

/// Generate a Document directive
fn arb_document() -> impl Strategy<Value = Document> {
    (arb_date(), arb_account(), arb_document_path())
        .prop_map(|(date, account, path)| Document::new(date, account, path))
}

/// Generate a Price directive
fn arb_price() -> impl Strategy<Value = Price> {
    (arb_date(), arb_stock(), arb_positive_amount())
        .prop_map(|(date, currency, amount)| Price::new(date, currency, amount))
}

/// Generate a Custom directive
fn arb_custom() -> impl Strategy<Value = Custom> {
    (arb_date(), arb_custom_type(), arb_narration()).prop_map(|(date, custom_type, value)| {
        Custom::new(date, custom_type).with_value(MetaValue::String(value))
    })
}

/// Generate any directive type
fn arb_directive() -> impl Strategy<Value = Directive> {
    prop_oneof![
        arb_transaction().prop_map(Directive::Transaction),
        arb_balance().prop_map(Directive::Balance),
        arb_open().prop_map(Directive::Open),
        arb_close().prop_map(Directive::Close),
        arb_commodity().prop_map(Directive::Commodity),
        arb_pad().prop_map(Directive::Pad),
        arb_event().prop_map(Directive::Event),
        arb_query().prop_map(Directive::Query),
        arb_note().prop_map(Directive::Note),
        arb_document().prop_map(Directive::Document),
        arb_price().prop_map(Directive::Price),
        arb_custom().prop_map(Directive::Custom),
    ]
}

// ============================================================================
// Complete Ledger Generation
// ============================================================================

/// A complete synthetic ledger with proper account setup
#[derive(Debug)]
pub struct SyntheticLedger {
    /// All directives in the ledger
    pub directives: Vec<Directive>,
}

impl SyntheticLedger {
    /// Convert to beancount text format
    pub fn to_beancount(&self) -> String {
        let config = FormatConfig::default();
        self.directives
            .iter()
            .map(|d| format_directives([d], &config))
            .collect::<Vec<_>>()
            .join("\n\n")
    }
}

/// Generate a valid synthetic ledger with account declarations
fn arb_synthetic_ledger() -> impl Strategy<Value = SyntheticLedger> {
    // Generate a fixed set of accounts first, then transactions using those accounts
    let accounts = vec![
        "Assets:Bank".to_string(),
        "Assets:Cash".to_string(),
        "Expenses:Food".to_string(),
        "Expenses:Rent".to_string(),
        "Income:Salary".to_string(),
        "Liabilities:CreditCard".to_string(),
        "Equity:Opening-Balances".to_string(),
    ];

    let start_date = rustledger_core::naive_date(2020, 1, 1).unwrap();

    // Generate transactions
    (
        prop::collection::vec(
            (
                0usize..7usize,
                0usize..7usize,
                arb_positive_decimal(),
                arb_currency(),
                arb_narration(),
                1u32..365u32,
            ),
            1..20,
        ),
        prop::collection::vec(arb_price(), 0..5),
        prop::collection::vec(arb_event(), 0..3),
    )
        .prop_map(move |(txn_params, prices, events)| {
            let mut directives = Vec::new();

            // Open all accounts on the start date
            for account in &accounts {
                directives.push(Directive::Open(Open::new(start_date, account.clone())));
            }

            // Add some commodities
            directives.push(Directive::Commodity(Commodity::new(start_date, "USD")));
            directives.push(Directive::Commodity(Commodity::new(start_date, "AAPL")));

            // Generate transactions
            for (from_idx, to_idx, amount, currency, narration, day_offset) in txn_params {
                let from_account = &accounts[from_idx % accounts.len()];
                let to_account = &accounts[to_idx % accounts.len()];

                if from_account != to_account {
                    let txn_date = start_date
                        .checked_add(jiff::ToSpan::days(i64::from(day_offset)))
                        .unwrap();
                    let amt = Amount::new(amount, &currency);

                    let txn = Transaction::new(txn_date, &narration)
                        .with_synthesized_posting(Posting::new(to_account, amt.clone()))
                        .with_synthesized_posting(Posting::new(from_account, -amt));

                    directives.push(Directive::Transaction(txn));
                }
            }

            // Add prices and events
            for price in prices {
                directives.push(Directive::Price(price));
            }
            for event in events {
                directives.push(Directive::Event(event));
            }

            // Sort by date
            rustledger_core::sort_directives(&mut directives);

            SyntheticLedger { directives }
        })
}

// ============================================================================
// Property Tests
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// All generated directives should have valid format output
    #[test]
    fn prop_directive_has_format(directive in arb_directive()) {
        let config = FormatConfig::default();
        let display = format_directives([&directive], &config);
        prop_assert!(!display.is_empty(), "Directive format should not be empty");
        prop_assert!(display.contains("20"), "Directive should contain a date (year 20xx)");
    }

    /// Transactions should always have at least 2 postings (balanced)
    #[test]
    fn prop_transaction_has_postings(txn in arb_transaction()) {
        prop_assert!(txn.postings.len() >= 2, "Transaction should have at least 2 postings");
    }

    /// Synthetic ledger should produce non-empty output
    #[test]
    fn prop_synthetic_ledger_not_empty(ledger in arb_synthetic_ledger()) {
        let text = ledger.to_beancount();
        prop_assert!(!text.is_empty(), "Ledger text should not be empty");
        prop_assert!(text.contains("open"), "Ledger should contain open directives");
    }

    /// Synthetic ledger should have accounts opened before use
    #[test]
    fn prop_synthetic_ledger_accounts_opened(ledger in arb_synthetic_ledger()) {
        // Find all open directives
        let opened: std::collections::HashSet<_> = ledger.directives.iter()
            .filter_map(|d| {
                if let Directive::Open(open) = d {
                    Some(open.account.as_str().to_string())
                } else {
                    None
                }
            })
            .collect();

        // Check that all transaction accounts are in opened set
        for directive in &ledger.directives {
            if let Directive::Transaction(txn) = directive {
                for posting in &txn.postings {
                    let account = posting.account.as_str();
                    prop_assert!(
                        opened.contains(account),
                        "Account {} should be opened before use", account
                    );
                }
            }
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_synthetic_ledger_output() {
        // Create a simple test ledger
        let date = rustledger_core::naive_date(2024, 1, 1).unwrap();

        let directives = vec![
            Directive::Open(Open::new(date, "Assets:Bank")),
            Directive::Open(Open::new(date, "Expenses:Food")),
            Directive::Transaction(
                Transaction::new(date, "Test transaction")
                    .with_synthesized_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(Decimal::new(5000, 2), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(Decimal::new(-5000, 2), "USD"),
                    )),
            ),
        ];

        let ledger = SyntheticLedger { directives };
        let text = ledger.to_beancount();

        println!("Generated ledger:\n{text}");

        assert!(
            text.contains("2024-01-01 open Assets:Bank"),
            "Missing open Assets:Bank"
        );
        assert!(
            text.contains("2024-01-01 open Expenses:Food"),
            "Missing open Expenses:Food"
        );
        assert!(text.contains("Test transaction"), "Missing narration");
        assert!(text.contains("50.00 USD"), "Missing amount");
    }

    #[test]
    fn test_all_directive_types_have_format() {
        let date = rustledger_core::naive_date(2024, 1, 1).unwrap();
        let config = FormatConfig::default();

        // Create one of each directive type and verify format works
        let directives: Vec<Directive> = vec![
            Directive::Open(Open::new(date, "Assets:Bank")),
            Directive::Close(Close::new(date, "Assets:Bank")),
            Directive::Commodity(Commodity::new(date, "USD")),
            Directive::Balance(Balance::new(
                date,
                "Assets:Bank",
                Amount::new(Decimal::ZERO, "USD"),
            )),
            Directive::Pad(Pad::new(date, "Assets:Bank", "Equity:Opening-Balances")),
            Directive::Transaction(
                Transaction::new(date, "Test")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(Decimal::new(100, 0), "USD"),
                    ))
                    .with_synthesized_posting(Posting::auto("Expenses:Food")),
            ),
            Directive::Event(Event::new(date, "location", "New York")),
            Directive::Query(Query::new(date, "test", "SELECT *")),
            Directive::Note(Note::new(date, "Assets:Bank", "Test note")),
            Directive::Document(Document::new(date, "Assets:Bank", "/path/to/doc.pdf")),
            Directive::Price(Price::new(
                date,
                "AAPL",
                Amount::new(Decimal::new(15000, 2), "USD"),
            )),
            Directive::Custom(
                Custom::new(date, "budget").with_value(MetaValue::String("Food".to_string())),
            ),
        ];

        for directive in &directives {
            let display = format_directives([directive], &config);
            assert!(
                !display.is_empty(),
                "Format for {:?} should not be empty",
                directive.type_name()
            );
            println!("{}: {}", directive.type_name(), display);
        }
    }

    // ============================================================================
    // Bean-check Validation Tests
    // ============================================================================

    /// Test that generated ledgers can be validated by Python beancount's bean-check.
    ///
    /// Run with: cargo test -p rustledger-core --test `synthetic_generation` -- --ignored
    /// Requires: bean-check to be installed (pip install beancount)
    #[test]
    #[ignore = "requires bean-check to be installed"]
    fn test_beancheck_validates_generated_ledger() {
        use std::io::Write;
        use std::process::Command;

        let date = rustledger_core::naive_date(2024, 1, 1).unwrap();

        // Create a valid ledger
        let directives = vec![
            Directive::Open(Open::new(date, "Assets:Bank:Checking")),
            Directive::Open(Open::new(date, "Assets:Cash")),
            Directive::Open(Open::new(date, "Expenses:Food")),
            Directive::Open(Open::new(date, "Income:Salary")),
            Directive::Transaction(
                Transaction::new(date, "Paycheck")
                    .with_flag('*')
                    .with_payee("Employer Inc")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank:Checking",
                        Amount::new(Decimal::new(100_000, 2), "USD"),
                    ))
                    .with_synthesized_posting(Posting::auto("Income:Salary")),
            ),
            Directive::Transaction(
                Transaction::new(
                    rustledger_core::naive_date(2024, 1, 15).unwrap(),
                    "Groceries",
                )
                .with_flag('*')
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(Decimal::new(5000, 2), "USD"),
                ))
                .with_synthesized_posting(Posting::auto("Assets:Bank:Checking")),
            ),
        ];

        let ledger = SyntheticLedger { directives };
        let text = ledger.to_beancount();

        // Write to temp file
        let mut temp = tempfile::NamedTempFile::new().expect("Failed to create temp file");
        temp.write_all(text.as_bytes())
            .expect("Failed to write temp file");

        // Run bean-check
        let output = Command::new("bean-check").arg(temp.path()).output();

        match output {
            Ok(result) => {
                if !result.status.success() {
                    let stderr = String::from_utf8_lossy(&result.stderr);
                    panic!("bean-check failed on generated file:\n{text}\n\nErrors:\n{stderr}");
                }
                println!("bean-check validated successfully!");
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                eprintln!("bean-check not found, skipping test");
            }
            Err(e) => {
                panic!("Failed to run bean-check: {e}");
            }
        }
    }

    // Property test: generated ledgers should validate with bean-check.
    //
    // Run with: cargo test -p rustledger-core --test synthetic_generation -- --ignored prop_beancheck
    // Requires: bean-check to be installed (pip install beancount)
    proptest! {
        #![proptest_config(ProptestConfig::with_cases(5))]

        #[test]
        #[ignore = "requires bean-check to be installed"]
        fn prop_beancheck_validates_random_ledger(ledger in arb_synthetic_ledger()) {
            use std::io::Write;
            use std::process::Command;

            let text = ledger.to_beancount();

            // Write to temp file
            let mut temp = tempfile::NamedTempFile::new().expect("Failed to create temp file");
            temp.write_all(text.as_bytes())
                .expect("Failed to write temp file");

            // Run bean-check
            let output = Command::new("bean-check")
                .arg(temp.path())
                .output();

            match output {
                Ok(result) => {
                    prop_assert!(
                        result.status.success(),
                        "bean-check failed on generated file:\n{}\n\nErrors:\n{}",
                        text,
                        String::from_utf8_lossy(&result.stderr)
                    );
                }
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                    // bean-check not installed, skip
                    eprintln!("bean-check not found, skipping test");
                }
                Err(e) => {
                    prop_assert!(false, "Failed to run bean-check: {}", e);
                }
            }
        }
    }
}
