//! Integration tests for the parser crate.
//!
//! Tests cover all directive types, error recovery, edge cases, and real-world scenarios.

use rustledger_core::Directive;
use rustledger_parser::{parse, parse_directives, ParseResult};

// ============================================================================
// Helper Functions
// ============================================================================

fn parse_ok(source: &str) -> ParseResult {
    let result = parse(source);
    assert!(
        result.errors.is_empty(),
        "expected no errors, got: {:?}",
        result.errors
    );
    result
}

fn count_directive_type(result: &ParseResult, type_name: &str) -> usize {
    result
        .directives
        .iter()
        .filter(|d| match &d.value {
            Directive::Open(_) => type_name == "open",
            Directive::Close(_) => type_name == "close",
            Directive::Transaction(_) => type_name == "transaction",
            Directive::Balance(_) => type_name == "balance",
            Directive::Pad(_) => type_name == "pad",
            Directive::Price(_) => type_name == "price",
            Directive::Event(_) => type_name == "event",
            Directive::Note(_) => type_name == "note",
            Directive::Document(_) => type_name == "document",
            Directive::Commodity(_) => type_name == "commodity",
            Directive::Query(_) => type_name == "query",
            Directive::Custom(_) => type_name == "custom",
        })
        .count()
}

// ============================================================================
// Basic Directive Parsing
// ============================================================================

#[test]
fn test_parse_open_directive() {
    let source = r"2024-01-01 open Assets:Bank:Checking USD, EUR";
    let result = parse_ok(source);
    assert_eq!(count_directive_type(&result, "open"), 1);

    if let Directive::Open(open) = &result.directives[0].value {
        assert_eq!(open.account, "Assets:Bank:Checking");
        assert_eq!(open.currencies, vec!["USD", "EUR"]);
    } else {
        panic!("expected open directive");
    }
}

#[test]
fn test_parse_close_directive() {
    let source = r"2024-12-31 close Assets:Bank:OldAccount";
    let result = parse_ok(source);
    assert_eq!(count_directive_type(&result, "close"), 1);

    if let Directive::Close(close) = &result.directives[0].value {
        assert_eq!(close.account, "Assets:Bank:OldAccount");
    } else {
        panic!("expected close directive");
    }
}

#[test]
fn test_parse_simple_transaction() {
    let source = r#"
2024-01-15 * "Coffee Shop" "Morning coffee"
  Expenses:Food:Coffee  5.00 USD
  Assets:Cash
"#;
    let result = parse_ok(source);
    assert_eq!(count_directive_type(&result, "transaction"), 1);

    if let Directive::Transaction(txn) = &result.directives[0].value {
        assert_eq!(txn.payee, Some("Coffee Shop".to_string()));
        assert_eq!(txn.narration, "Morning coffee");
        assert_eq!(txn.postings.len(), 2);
    } else {
        panic!("expected transaction");
    }
}

#[test]
fn test_parse_transaction_with_tags_and_links() {
    let source = r#"
2024-01-15 * "Dinner" #food #restaurant ^receipt-123
  Expenses:Food  45.00 USD
  Assets:Cash
"#;
    let result = parse_ok(source);
    assert_eq!(count_directive_type(&result, "transaction"), 1);

    if let Directive::Transaction(txn) = &result.directives[0].value {
        assert!(txn.tags.contains(&"food".to_string()));
        assert!(txn.tags.contains(&"restaurant".to_string()));
        assert!(txn.links.contains(&"receipt-123".to_string()));
    } else {
        panic!("expected transaction");
    }
}

#[test]
fn test_parse_balance_directive() {
    let source = r"2024-01-31 balance Assets:Bank:Checking 1000.00 USD";
    let result = parse_ok(source);
    assert_eq!(count_directive_type(&result, "balance"), 1);

    if let Directive::Balance(bal) = &result.directives[0].value {
        assert_eq!(bal.account, "Assets:Bank:Checking");
        assert_eq!(bal.amount.number.to_string(), "1000.00");
        assert_eq!(bal.amount.currency, "USD");
    } else {
        panic!("expected balance");
    }
}

#[test]
fn test_parse_pad_directive() {
    let source = r"2024-01-01 pad Assets:Bank:Checking Equity:Opening-Balances";
    let result = parse_ok(source);
    assert_eq!(count_directive_type(&result, "pad"), 1);

    if let Directive::Pad(pad) = &result.directives[0].value {
        assert_eq!(pad.account, "Assets:Bank:Checking");
        assert_eq!(pad.source_account, "Equity:Opening-Balances");
    } else {
        panic!("expected pad");
    }
}

#[test]
fn test_parse_price_directive() {
    let source = r"2024-01-15 price AAPL 185.50 USD";
    let result = parse_ok(source);
    assert_eq!(count_directive_type(&result, "price"), 1);

    if let Directive::Price(price) = &result.directives[0].value {
        assert_eq!(price.currency, "AAPL");
        assert_eq!(price.amount.number.to_string(), "185.50");
        assert_eq!(price.amount.currency, "USD");
    } else {
        panic!("expected price");
    }
}

#[test]
fn test_parse_event_directive() {
    let source = r#"2024-01-01 event "location" "New York""#;
    let result = parse_ok(source);
    assert_eq!(count_directive_type(&result, "event"), 1);

    if let Directive::Event(event) = &result.directives[0].value {
        assert_eq!(event.event_type, "location");
        assert_eq!(event.value, "New York");
    } else {
        panic!("expected event");
    }
}

#[test]
fn test_parse_note_directive() {
    let source = r#"2024-01-15 note Assets:Bank:Checking "Account review completed""#;
    let result = parse_ok(source);
    assert_eq!(count_directive_type(&result, "note"), 1);

    if let Directive::Note(note) = &result.directives[0].value {
        assert_eq!(note.account, "Assets:Bank:Checking");
        assert_eq!(note.comment, "Account review completed");
    } else {
        panic!("expected note");
    }
}

#[test]
fn test_parse_document_directive() {
    let source = r#"2024-01-15 document Assets:Bank:Checking "/path/to/statement.pdf""#;
    let result = parse_ok(source);
    assert_eq!(count_directive_type(&result, "document"), 1);

    if let Directive::Document(doc) = &result.directives[0].value {
        assert_eq!(doc.account, "Assets:Bank:Checking");
        assert_eq!(doc.path, "/path/to/statement.pdf");
    } else {
        panic!("expected document");
    }
}

#[test]
fn test_parse_commodity_directive() {
    let source = r#"2024-01-01 commodity USD
  name: "US Dollar""#;
    let result = parse_ok(source);
    assert_eq!(count_directive_type(&result, "commodity"), 1);

    if let Directive::Commodity(comm) = &result.directives[0].value {
        assert_eq!(comm.currency, "USD");
    } else {
        panic!("expected commodity");
    }
}

#[test]
fn test_parse_query_directive() {
    let source = r#"2024-01-01 query "expenses" "SELECT account, SUM(position)""#;
    let result = parse_ok(source);
    assert_eq!(count_directive_type(&result, "query"), 1);

    if let Directive::Query(q) = &result.directives[0].value {
        assert_eq!(q.name, "expenses");
        assert!(q.query.contains("SELECT"));
    } else {
        panic!("expected query");
    }
}

#[test]
fn test_parse_custom_directive() {
    let source = r#"2024-01-01 custom "budget" Expenses:Food 500.00 USD"#;
    let result = parse_ok(source);
    assert_eq!(count_directive_type(&result, "custom"), 1);
}

// ============================================================================
// Options, Includes, and Plugins
// ============================================================================

#[test]
fn test_parse_options() {
    let source = r#"
option "title" "My Ledger"
option "operating_currency" "USD"
option "operating_currency" "EUR"
"#;
    let result = parse_ok(source);
    assert_eq!(result.options.len(), 3);
    assert_eq!(result.options[0].0, "title");
    assert_eq!(result.options[0].1, "My Ledger");
}

#[test]
fn test_parse_includes() {
    let source = r#"
include "accounts.beancount"
include "transactions/2024.beancount"
"#;
    let result = parse_ok(source);
    assert_eq!(result.includes.len(), 2);
    assert_eq!(result.includes[0].0, "accounts.beancount");
    assert_eq!(result.includes[1].0, "transactions/2024.beancount");
}

#[test]
fn test_parse_plugins() {
    let source = r#"
plugin "beancount.plugins.leafonly"
plugin "beancount.plugins.check_commodity" "config_string"
"#;
    let result = parse_ok(source);
    assert_eq!(result.plugins.len(), 2);
    assert_eq!(result.plugins[0].0, "beancount.plugins.leafonly");
    assert!(result.plugins[0].1.is_none());
    assert_eq!(result.plugins[1].0, "beancount.plugins.check_commodity");
    assert_eq!(result.plugins[1].1, Some("config_string".to_string()));
}

// ============================================================================
// Complex Transactions
// ============================================================================

#[test]
fn test_parse_transaction_with_cost() {
    let source = r#"
2024-01-15 * "Buy stock"
  Assets:Brokerage  10 AAPL {185.50 USD}
  Assets:Cash  -1855.00 USD
"#;
    let result = parse_ok(source);
    assert_eq!(count_directive_type(&result, "transaction"), 1);

    if let Directive::Transaction(txn) = &result.directives[0].value {
        let posting = &txn.postings[0];
        assert!(posting.cost.is_some());
        let cost = posting.cost.as_ref().unwrap();
        assert_eq!(cost.number_per.unwrap().to_string(), "185.50");
        assert_eq!(cost.currency.as_deref(), Some("USD"));
    } else {
        panic!("expected transaction");
    }
}

#[test]
fn test_parse_transaction_with_price() {
    let source = r#"
2024-01-15 * "Currency exchange"
  Assets:USD  100.00 USD @ 0.85 EUR
  Assets:EUR  -85.00 EUR
"#;
    let result = parse_ok(source);
    assert_eq!(count_directive_type(&result, "transaction"), 1);

    if let Directive::Transaction(txn) = &result.directives[0].value {
        let posting = &txn.postings[0];
        assert!(posting.price.is_some());
    } else {
        panic!("expected transaction");
    }
}

#[test]
fn test_parse_transaction_with_total_cost() {
    let source = r#"
2024-01-15 * "Buy stock with fees"
  Assets:Brokerage  10 AAPL {{1860.00 USD}}
  Assets:Cash  -1860.00 USD
"#;
    let result = parse_ok(source);
    assert_eq!(count_directive_type(&result, "transaction"), 1);

    if let Directive::Transaction(txn) = &result.directives[0].value {
        let posting = &txn.postings[0];
        assert!(posting.cost.is_some());
    } else {
        panic!("expected transaction");
    }
}

#[test]
fn test_parse_transaction_with_metadata() {
    let source = r#"
2024-01-15 * "Purchase"
  receipt: "scan-001.pdf"
  category: "office"
  Expenses:Office  100.00 USD
    item: "Printer paper"
  Assets:Cash
"#;
    let result = parse_ok(source);
    assert_eq!(count_directive_type(&result, "transaction"), 1);

    if let Directive::Transaction(txn) = &result.directives[0].value {
        assert!(txn.meta.contains_key("receipt"));
        assert!(txn.meta.contains_key("category"));
        assert!(txn.postings[0].meta.contains_key("item"));
    } else {
        panic!("expected transaction");
    }
}

// ============================================================================
// Error Recovery
// ============================================================================

#[test]
fn test_error_recovery_continues_parsing() {
    let source = r"
2024-01-01 open Assets:Bank

; This line has an error
2024-01-15 invalid directive here

2024-01-31 close Assets:Bank
";
    let result = parse(source);

    // Should have errors
    assert!(!result.errors.is_empty(), "expected parse errors");

    // But should still have parsed valid directives
    assert!(
        count_directive_type(&result, "open") >= 1,
        "should have parsed open directive"
    );
}

#[test]
fn test_error_on_invalid_date() {
    let source = r"2024-13-45 open Assets:Bank";
    let result = parse(source);
    assert!(!result.errors.is_empty(), "expected error for invalid date");
}

#[test]
fn test_error_on_invalid_account() {
    let source = r"2024-01-01 open lowercase:invalid";
    let result = parse(source);
    // Account names must start with a capital letter
    assert!(
        !result.errors.is_empty(),
        "expected error for invalid account"
    );
}

// ============================================================================
// Edge Cases
// ============================================================================

#[test]
fn test_parse_empty_input() {
    let result = parse("");
    assert!(result.errors.is_empty());
    assert!(result.directives.is_empty());
}

#[test]
fn test_parse_only_comments() {
    let source = r"
; This is a comment
; Another comment
";
    let result = parse_ok(source);
    assert!(result.directives.is_empty());
}

#[test]
fn test_parse_unicode_in_narration() {
    let source = r#"2024-01-15 * "Café ☕" "Latte mit Milch"
  Expenses:Food  5.00 EUR
  Assets:Cash"#;
    let result = parse_ok(source);
    assert_eq!(count_directive_type(&result, "transaction"), 1);

    if let Directive::Transaction(txn) = &result.directives[0].value {
        assert_eq!(txn.payee, Some("Café ☕".to_string()));
        assert_eq!(txn.narration, "Latte mit Milch");
    } else {
        panic!("expected transaction");
    }
}

#[test]
fn test_parse_negative_amounts() {
    let source = r#"
2024-01-15 * "Refund"
  Assets:Bank  -50.00 USD
  Expenses:Food
"#;
    let result = parse_ok(source);
    assert_eq!(count_directive_type(&result, "transaction"), 1);
}

#[test]
fn test_parse_large_numbers() {
    let source = r"2024-01-15 price BTC 15000.00 USD";
    let result = parse_ok(source);
    assert_eq!(count_directive_type(&result, "price"), 1);
}

#[test]
fn test_parse_booking_method() {
    let source = r#"2024-01-01 open Assets:Stock "FIFO""#;
    let result = parse_ok(source);
    assert_eq!(count_directive_type(&result, "open"), 1);

    if let Directive::Open(open) = &result.directives[0].value {
        assert_eq!(open.booking, Some("FIFO".to_string()));
    } else {
        panic!("expected open");
    }
}

// ============================================================================
// Real-World Scenarios
// ============================================================================

#[test]
fn test_parse_complete_ledger() {
    let source = r#"
; Main ledger file
option "title" "Personal Finance"
option "operating_currency" "USD"

plugin "beancount.plugins.auto_accounts"

2024-01-01 open Assets:Bank:Checking USD
2024-01-01 open Assets:Bank:Savings USD
2024-01-01 open Expenses:Food
2024-01-01 open Expenses:Transport
2024-01-01 open Income:Salary

2024-01-01 pad Assets:Bank:Checking Equity:Opening-Balances

2024-01-15 * "Employer" "Monthly salary"
  Income:Salary  -5000.00 USD
  Assets:Bank:Checking  5000.00 USD

2024-01-16 * "Grocery Store" "Weekly groceries" #food
  Expenses:Food  150.00 USD
  Assets:Bank:Checking

2024-01-17 * "Gas Station" "Fill up"
  Expenses:Transport  45.00 USD
  Assets:Bank:Checking

2024-01-31 balance Assets:Bank:Checking 4805.00 USD

2024-01-31 note Assets:Bank:Checking "Reconciled with bank statement"
"#;
    let result = parse_ok(source);

    assert_eq!(result.options.len(), 2);
    assert_eq!(result.plugins.len(), 1);
    assert_eq!(count_directive_type(&result, "open"), 5);
    assert_eq!(count_directive_type(&result, "pad"), 1);
    assert_eq!(count_directive_type(&result, "transaction"), 3);
    assert_eq!(count_directive_type(&result, "balance"), 1);
    assert_eq!(count_directive_type(&result, "note"), 1);
}

#[test]
fn test_parse_investment_ledger() {
    let source = r#"
2024-01-01 open Assets:Brokerage AAPL, GOOG, USD
2024-01-01 open Income:Dividends
2024-01-01 open Income:Capital-Gains

2024-01-01 commodity AAPL
  name: "Apple Inc."

2024-01-15 * "Buy Apple stock"
  Assets:Brokerage  10 AAPL {185.00 USD, 2024-01-15}
  Assets:Brokerage  -1850.00 USD

2024-02-15 * "Receive dividend"
  Assets:Brokerage  5.00 USD
  Income:Dividends  -5.00 USD

2024-03-15 price AAPL 190.00 USD

2024-04-15 * "Sell Apple stock"
  Assets:Brokerage  -5 AAPL {185.00 USD, 2024-01-15}
  Assets:Brokerage  950.00 USD
  Income:Capital-Gains  -25.00 USD
"#;
    let result = parse_ok(source);

    assert_eq!(count_directive_type(&result, "open"), 3);
    assert_eq!(count_directive_type(&result, "commodity"), 1);
    assert_eq!(count_directive_type(&result, "transaction"), 3);
    assert_eq!(count_directive_type(&result, "price"), 1);
}

// ============================================================================
// parse_directives API
// ============================================================================

#[test]
fn test_parse_directives_simple() {
    let source = r#"
option "title" "Test"
2024-01-01 open Assets:Bank
"#;
    let (directives, errors) = parse_directives(source);
    assert!(errors.is_empty());
    assert_eq!(directives.len(), 1);
}
