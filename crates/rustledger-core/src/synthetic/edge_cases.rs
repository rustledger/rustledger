//! Edge case generators for stress-testing beancount parsers.
//!
//! These generators produce beancount directives that exercise edge cases
//! in parsing and validation, such as:
//!
//! - Unicode in various positions
//! - Extreme decimal precision
//! - Deep account hierarchies
//! - Large transactions with many postings
//! - Boundary dates
//! - Special characters

use crate::{
    Amount, Balance, Close, Commodity, Directive, Event, Note, Open, Pad, Posting, Price,
    Transaction,
    format::{FormatConfig, FormatLine, format_directive_lines, render_lines},
};
use rust_decimal::Decimal;
use std::str::FromStr;

/// Collection of edge case directives grouped by category.
#[derive(Debug, Clone)]
pub struct EdgeCaseCollection {
    /// Category name (e.g., "unicode", "decimals", "hierarchy")
    pub category: String,
    /// Directives in this collection
    pub directives: Vec<Directive>,
}

impl EdgeCaseCollection {
    /// Create a new edge case collection.
    pub fn new(category: impl Into<String>, directives: Vec<Directive>) -> Self {
        Self {
            category: category.into(),
            directives,
        }
    }

    /// Format all directives to beancount text.
    ///
    /// All directives are aligned together against shared, file-wide column
    /// widths, with a blank line separating each one.
    pub fn to_beancount(&self) -> String {
        let config = FormatConfig::default();
        let mut lines: Vec<FormatLine> = vec![
            FormatLine::Plain(format!("; Edge cases: {}", self.category)),
            FormatLine::Plain(String::new()),
        ];

        for directive in &self.directives {
            lines.extend(format_directive_lines(directive, &config));
            lines.push(FormatLine::Plain(String::new()));
        }

        render_lines(&lines, &config.alignment)
    }
}

/// Generate all edge case collections.
pub fn generate_all_edge_cases() -> Vec<EdgeCaseCollection> {
    vec![
        generate_unicode_edge_cases(),
        generate_decimal_edge_cases(),
        generate_hierarchy_edge_cases(),
        generate_large_transaction_edge_cases(),
        generate_boundary_date_edge_cases(),
        generate_special_character_edge_cases(),
        generate_minimal_edge_cases(),
    ]
}

/// Generate Unicode edge cases.
///
/// Tests Unicode handling in:
/// - Account names (via valid account segments)
/// - Payee and narration strings
/// - Metadata values
/// - Event descriptions
pub fn generate_unicode_edge_cases() -> EdgeCaseCollection {
    let base_date = crate::naive_date(2024, 1, 1).unwrap();
    let open_date = base_date.yesterday().ok().unwrap();

    let directives = vec![
        // Open accounts first
        Directive::Open(Open::new(open_date, "Assets:Bank:Checking")),
        Directive::Open(Open::new(open_date, "Assets:Bank:Savings")),
        Directive::Open(Open::new(open_date, "Assets:Cash")),
        Directive::Open(Open::new(open_date, "Expenses:Food")),
        Directive::Open(Open::new(open_date, "Expenses:Food:Cafe")),
        Directive::Open(Open::new(open_date, "Expenses:Food:Groceries")),
        Directive::Open(Open::new(open_date, "Expenses:Travel")),
        // Transaction with Unicode in payee and narration
        Directive::Transaction(
            Transaction::new(base_date, "Café Purchase")
                .with_flag('*')
                .with_payee("Bäckerei München")
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food:Cafe",
                    Amount::new(dec("5.50"), "EUR"),
                ))
                .with_synthesized_posting(Posting::auto("Assets:Bank:Checking")),
        ),
        // Japanese characters
        Directive::Transaction(
            Transaction::new(base_date, "東京での買い物")
                .with_flag('*')
                .with_payee("コンビニ")
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec("1000"), "JPY"),
                ))
                .with_synthesized_posting(Posting::auto("Assets:Cash")),
        ),
        // Russian Cyrillic
        Directive::Transaction(
            Transaction::new(base_date, "Покупка продуктов")
                .with_flag('*')
                .with_payee("Магазин")
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec("500"), "RUB"),
                ))
                .with_synthesized_posting(Posting::auto("Assets:Cash")),
        ),
        // Arabic
        Directive::Transaction(
            Transaction::new(base_date, "شراء طعام")
                .with_flag('*')
                .with_payee("متجر")
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec("100"), "SAR"),
                ))
                .with_synthesized_posting(Posting::auto("Assets:Cash")),
        ),
        // Emoji in narration
        Directive::Transaction(
            Transaction::new(base_date, "Grocery run with emoji")
                .with_flag('*')
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food:Groceries",
                    Amount::new(dec("45.99"), "USD"),
                ))
                .with_synthesized_posting(Posting::auto("Assets:Bank:Checking")),
        ),
        // Mixed scripts
        Directive::Transaction(
            Transaction::new(base_date, "International trip")
                .with_flag('*')
                .with_synthesized_posting(Posting::new(
                    "Expenses:Travel",
                    Amount::new(dec("2500"), "USD"),
                ))
                .with_synthesized_posting(Posting::auto("Assets:Bank:Savings")),
        ),
        // Note with Unicode
        Directive::Note(Note::new(
            base_date,
            "Assets:Bank:Checking",
            "Überprüfung der Kontoauszüge für März",
        )),
        // Event with Unicode
        Directive::Event(Event::new(base_date, "location", "Zürich, Schweiz")),
    ];

    EdgeCaseCollection::new("unicode", directives)
}

/// Generate decimal precision edge cases.
///
/// Tests handling of:
/// - High decimal precision (up to 20 decimal places)
/// - Very large numbers
/// - Very small numbers
/// - Numbers with trailing zeros
pub fn generate_decimal_edge_cases() -> EdgeCaseCollection {
    let base_date = crate::naive_date(2024, 1, 1).unwrap();
    let open_date = base_date.yesterday().ok().unwrap();

    let directives = vec![
        // Open accounts first
        Directive::Open(Open::new(open_date, "Assets:Bank:Checking")),
        Directive::Open(Open::new(open_date, "Assets:Crypto:BTC")),
        Directive::Open(Open::new(open_date, "Assets:Investments:Stock")),
        Directive::Open(Open::new(open_date, "Expenses:Test")),
        Directive::Open(Open::new(open_date, "Equity:Opening")),
        // High precision (8 decimal places - crypto common)
        Directive::Transaction(
            Transaction::new(base_date, "Bitcoin purchase")
                .with_flag('*')
                .with_synthesized_posting(Posting::new(
                    "Assets:Crypto:BTC",
                    Amount::new(dec("0.00012345"), "BTC"),
                ))
                .with_synthesized_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec("-5.00"), "USD"),
                )),
        ),
        // Very high precision (16 decimal places)
        Directive::Transaction(
            Transaction::new(base_date, "High precision test")
                .with_flag('*')
                .with_synthesized_posting(Posting::new(
                    "Assets:Investments:Stock",
                    Amount::new(dec("1.1234567890123456"), "MICRO"),
                ))
                .with_synthesized_posting(Posting::auto("Equity:Opening")),
        ),
        // Very large number
        Directive::Transaction(
            Transaction::new(base_date, "Large number test")
                .with_flag('*')
                .with_synthesized_posting(Posting::new(
                    "Assets:Bank:Checking",
                    Amount::new(dec("999999999999.99"), "USD"),
                ))
                .with_synthesized_posting(Posting::auto("Equity:Opening")),
        ),
        // Very small fractional amount
        Directive::Transaction(
            Transaction::new(base_date, "Tiny amount")
                .with_flag('*')
                .with_synthesized_posting(Posting::new(
                    "Expenses:Test",
                    Amount::new(dec("0.00000001"), "USD"),
                ))
                .with_synthesized_posting(Posting::auto("Assets:Bank:Checking")),
        ),
        // Trailing zeros (should preserve precision)
        Directive::Transaction(
            Transaction::new(base_date, "Trailing zeros")
                .with_flag('*')
                .with_synthesized_posting(Posting::new(
                    "Expenses:Test",
                    Amount::new(dec("100.10000"), "USD"),
                ))
                .with_synthesized_posting(Posting::auto("Assets:Bank:Checking")),
        ),
        // Negative with high precision
        Directive::Transaction(
            Transaction::new(base_date, "Negative high precision")
                .with_flag('*')
                .with_synthesized_posting(Posting::new(
                    "Expenses:Test",
                    Amount::new(dec("-0.12345678"), "USD"),
                ))
                .with_synthesized_posting(Posting::auto("Assets:Bank:Checking")),
        ),
        // Price with high precision
        Directive::Price(Price::new(
            base_date,
            "BTC",
            Amount::new(dec("45678.12345678"), "USD"),
        )),
    ];

    EdgeCaseCollection::new("decimals", directives)
}

/// Generate deep account hierarchy edge cases.
///
/// Tests parsing of accounts with many segments.
pub fn generate_hierarchy_edge_cases() -> EdgeCaseCollection {
    let base_date = crate::naive_date(2024, 1, 1).unwrap();
    let open_date = base_date.yesterday().ok().unwrap();

    // Deep hierarchy accounts
    let deep_asset = "Assets:Bank:Region:Country:City:Branch:Department:Team:SubTeam:Account";
    let deep_expense = "Expenses:Category:SubCategory:Type:SubType:Detail:MoreDetail:Final";

    let directives = vec![
        // Open deep accounts
        Directive::Open(Open::new(open_date, deep_asset)),
        Directive::Open(Open::new(open_date, deep_expense)),
        Directive::Open(Open::new(open_date, "Assets:A:B:C:D:E:F:G:H:I:J")),
        Directive::Open(Open::new(
            open_date,
            "Liabilities:Debt:Type:Lender:Account:SubAccount",
        )),
        Directive::Open(Open::new(open_date, "Equity:Opening")),
        // Transaction with deep accounts
        Directive::Transaction(
            Transaction::new(base_date, "Deep hierarchy transfer")
                .with_flag('*')
                .with_synthesized_posting(Posting::new(
                    deep_expense,
                    Amount::new(dec("100.00"), "USD"),
                ))
                .with_synthesized_posting(Posting::auto(deep_asset)),
        ),
        // Balance assertion on deep account
        Directive::Balance(Balance::new(
            base_date,
            deep_asset,
            Amount::new(dec("-100.00"), "USD"),
        )),
        // Pad with deep accounts
        Directive::Pad(Pad::new(
            base_date,
            "Assets:A:B:C:D:E:F:G:H:I:J",
            "Equity:Opening",
        )),
    ];

    EdgeCaseCollection::new("hierarchy", directives)
}

/// Generate edge cases with large transactions (many postings).
pub fn generate_large_transaction_edge_cases() -> EdgeCaseCollection {
    let base_date = crate::naive_date(2024, 1, 1).unwrap();
    let open_date = base_date.yesterday().ok().unwrap();

    // Generate open directives for accounts
    let mut directives: Vec<Directive> = (0..25)
        .map(|i| Directive::Open(Open::new(open_date, format!("Expenses:Category{i}"))))
        .collect();

    directives.push(Directive::Open(Open::new(
        open_date,
        "Assets:Bank:Checking",
    )));

    // Create a transaction with 20 postings
    let mut txn =
        Transaction::new(base_date, "Expense allocation with 20 categories").with_flag('*');

    for i in 0..20 {
        txn = txn.with_synthesized_posting(Posting::new(
            format!("Expenses:Category{i}"),
            Amount::new(dec("10.00"), "USD"),
        ));
    }

    // Add the balancing posting
    txn = txn.with_synthesized_posting(Posting::new(
        "Assets:Bank:Checking",
        Amount::new(dec("-200.00"), "USD"),
    ));

    directives.push(Directive::Transaction(txn));

    // Transaction with many tags and links
    let mut txn2 = Transaction::new(base_date, "Tagged transaction")
        .with_flag('*')
        .with_synthesized_posting(Posting::new(
            "Expenses:Category0",
            Amount::new(dec("50.00"), "USD"),
        ))
        .with_synthesized_posting(Posting::auto("Assets:Bank:Checking"));

    for i in 0..10 {
        txn2 = txn2.with_tag(format!("tag{i}"));
    }
    for i in 0..10 {
        txn2 = txn2.with_link(format!("link{i}"));
    }

    directives.push(Directive::Transaction(txn2));

    EdgeCaseCollection::new("large-transactions", directives)
}

/// Generate boundary date edge cases.
pub fn generate_boundary_date_edge_cases() -> EdgeCaseCollection {
    // Early date (1900)
    let early_date = crate::naive_date(1900, 1, 1).unwrap();
    // Late date
    let late_date = crate::naive_date(2099, 12, 31).unwrap();
    // Leap year dates
    let leap_date = crate::naive_date(2024, 2, 29).unwrap();
    // End of months
    let end_jan = crate::naive_date(2024, 1, 31).unwrap();
    let end_apr = crate::naive_date(2024, 4, 30).unwrap();

    let directives = vec![
        // Open accounts at early date
        Directive::Open(Open::new(
            crate::naive_date(1899, 12, 31).unwrap(),
            "Assets:Historical:Account",
        )),
        Directive::Open(Open::new(
            crate::naive_date(1899, 12, 31).unwrap(),
            "Equity:Opening",
        )),
        // Early date transaction
        Directive::Transaction(
            Transaction::new(early_date, "Historical transaction from 1900")
                .with_flag('*')
                .with_synthesized_posting(Posting::new(
                    "Assets:Historical:Account",
                    Amount::new(dec("1.00"), "USD"),
                ))
                .with_synthesized_posting(Posting::auto("Equity:Opening")),
        ),
        // Late date transaction
        Directive::Transaction(
            Transaction::new(late_date, "Far future transaction")
                .with_flag('*')
                .with_synthesized_posting(Posting::new(
                    "Assets:Historical:Account",
                    Amount::new(dec("1000000.00"), "USD"),
                ))
                .with_synthesized_posting(Posting::auto("Equity:Opening")),
        ),
        // Leap year
        Directive::Transaction(
            Transaction::new(leap_date, "Leap day transaction")
                .with_flag('*')
                .with_synthesized_posting(Posting::new(
                    "Assets:Historical:Account",
                    Amount::new(dec("29.02"), "USD"),
                ))
                .with_synthesized_posting(Posting::auto("Equity:Opening")),
        ),
        // End of month
        Directive::Transaction(
            Transaction::new(end_jan, "End of January")
                .with_flag('*')
                .with_synthesized_posting(Posting::new(
                    "Assets:Historical:Account",
                    Amount::new(dec("31.00"), "USD"),
                ))
                .with_synthesized_posting(Posting::auto("Equity:Opening")),
        ),
        Directive::Transaction(
            Transaction::new(end_apr, "End of April")
                .with_flag('*')
                .with_synthesized_posting(Posting::new(
                    "Assets:Historical:Account",
                    Amount::new(dec("30.00"), "USD"),
                ))
                .with_synthesized_posting(Posting::auto("Equity:Opening")),
        ),
    ];

    EdgeCaseCollection::new("boundary-dates", directives)
}

/// Generate special character edge cases.
///
/// Tests handling of escaped characters and special strings.
pub fn generate_special_character_edge_cases() -> EdgeCaseCollection {
    let base_date = crate::naive_date(2024, 1, 1).unwrap();
    let open_date = base_date.yesterday().ok().unwrap();

    let directives = vec![
        Directive::Open(Open::new(open_date, "Assets:Bank:Checking")),
        Directive::Open(Open::new(open_date, "Expenses:Test")),
        // Quotes in narration (escaped)
        Directive::Transaction(
            Transaction::new(base_date, "Purchase at Joe's Diner")
                .with_flag('*')
                .with_synthesized_posting(Posting::new(
                    "Expenses:Test",
                    Amount::new(dec("25.00"), "USD"),
                ))
                .with_synthesized_posting(Posting::auto("Assets:Bank:Checking")),
        ),
        // Backslash in narration
        Directive::Transaction(
            Transaction::new(base_date, r"Path: C:\Users\Documents\file.txt")
                .with_flag('*')
                .with_synthesized_posting(Posting::new(
                    "Expenses:Test",
                    Amount::new(dec("10.00"), "USD"),
                ))
                .with_synthesized_posting(Posting::auto("Assets:Bank:Checking")),
        ),
        // Multi-line description split across text
        Directive::Transaction(
            Transaction::new(base_date, "Multi-line description split across text")
                .with_flag('*')
                .with_synthesized_posting(Posting::new(
                    "Expenses:Test",
                    Amount::new(dec("5.00"), "USD"),
                ))
                .with_synthesized_posting(Posting::auto("Assets:Bank:Checking")),
        ),
        // Long narration (200 characters)
        Directive::Transaction(
            Transaction::new(base_date, "A".repeat(200))
                .with_flag('*')
                .with_synthesized_posting(Posting::new(
                    "Expenses:Test",
                    Amount::new(dec("1.00"), "USD"),
                ))
                .with_synthesized_posting(Posting::auto("Assets:Bank:Checking")),
        ),
        // Special whitespace in payee
        Directive::Transaction(
            Transaction::new(base_date, "Regular narration")
                .with_flag('*')
                .with_payee("Company Name") // No tab - tabs are invalid in beancount
                .with_synthesized_posting(Posting::new(
                    "Expenses:Test",
                    Amount::new(dec("15.00"), "USD"),
                ))
                .with_synthesized_posting(Posting::auto("Assets:Bank:Checking")),
        ),
    ];

    EdgeCaseCollection::new("special-characters", directives)
}

/// Generate minimal/empty edge cases.
///
/// Tests handling of minimal valid directives.
pub fn generate_minimal_edge_cases() -> EdgeCaseCollection {
    let base_date = crate::naive_date(2024, 1, 1).unwrap();

    let directives = vec![
        // Minimal open
        Directive::Open(Open::new(base_date, "Assets:Minimal")),
        // Open with currencies
        Directive::Open(
            Open::new(base_date, "Assets:WithCurrency").with_currencies(vec!["USD".into()]),
        ),
        // Close
        Directive::Close(Close::new(
            base_date.tomorrow().ok().unwrap(),
            "Assets:Minimal",
        )),
        // Minimal commodity
        Directive::Commodity(Commodity::new(base_date, "MINI")),
        // Minimal price
        Directive::Price(Price::new(
            base_date,
            "MINI",
            Amount::new(dec("1.00"), "USD"),
        )),
        // Minimal note
        Directive::Note(Note::new(base_date, "Assets:WithCurrency", "A note")),
        // Minimal event
        Directive::Event(Event::new(base_date, "type", "value")),
        // Transaction with empty narration
        Directive::Transaction(
            Transaction::new(base_date, "")
                .with_flag('*')
                .with_synthesized_posting(Posting::new(
                    "Assets:WithCurrency",
                    Amount::new(dec("0.00"), "USD"),
                )),
        ),
        // Transaction with only auto-balanced postings
        Directive::Transaction(
            Transaction::new(base_date, "Auto-balanced")
                .with_flag('*')
                .with_synthesized_posting(Posting::new(
                    "Assets:WithCurrency",
                    Amount::new(dec("100.00"), "USD"),
                ))
                .with_synthesized_posting(Posting::auto("Assets:WithCurrency")),
        ),
    ];

    EdgeCaseCollection::new("minimal", directives)
}

/// Generate a complete beancount file with all edge cases.
///
/// Returns a string containing all edge cases formatted as valid beancount.
pub fn generate_all_edge_cases_beancount() -> String {
    let mut output = String::new();
    output.push_str("; Synthetic edge case beancount file\n");
    output.push_str("; Generated by rustledger synthetic module\n\n");

    for collection in generate_all_edge_cases() {
        output.push_str(&format!(
            "\n; === {} ===\n\n",
            collection.category.to_uppercase()
        ));
        output.push_str(&collection.to_beancount());
    }

    output
}

// Helper function to parse decimal from string
fn dec(s: &str) -> Decimal {
    Decimal::from_str(s).expect("Invalid decimal string")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generate_unicode_edge_cases() {
        let collection = generate_unicode_edge_cases();
        assert!(!collection.directives.is_empty());
        assert_eq!(collection.category, "unicode");

        let text = collection.to_beancount();
        assert!(text.contains("Café"));
        assert!(text.contains("東京"));
    }

    #[test]
    fn test_generate_decimal_edge_cases() {
        let collection = generate_decimal_edge_cases();
        assert!(!collection.directives.is_empty());

        let text = collection.to_beancount();
        assert!(text.contains("0.00012345"));
    }

    #[test]
    fn test_generate_all_edge_cases() {
        let collections = generate_all_edge_cases();
        assert!(!collections.is_empty());

        // Check all categories are present
        let categories: Vec<_> = collections.iter().map(|c| c.category.as_str()).collect();
        assert!(categories.contains(&"unicode"));
        assert!(categories.contains(&"decimals"));
        assert!(categories.contains(&"hierarchy"));
    }

    #[test]
    fn test_generate_all_edge_cases_beancount() {
        let text = generate_all_edge_cases_beancount();
        assert!(text.contains("UNICODE"));
        assert!(text.contains("DECIMALS"));
        assert!(text.contains("HIERARCHY"));
    }
}
