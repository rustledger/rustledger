//! Integration tests for the parser crate.
//!
//! Tests cover all directive types, error recovery, edge cases, and real-world scenarios.

use rustledger_core::Directive;
use rustledger_parser::{ParseError, ParseErrorKind, ParseResult, parse, parse_directives};

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
        assert_eq!(txn.payee.as_deref(), Some("Coffee Shop"));
        assert_eq!(txn.narration.as_str(), "Morning coffee");
        assert_eq!(txn.postings.len(), 2);
    } else {
        panic!("expected transaction");
    }
}

#[test]
fn string_escapes_are_decoded() {
    // The semantic value strips quotes AND decodes escapes (Beancount):
    // \" -> ", \\ -> \, \t -> tab, unknown \x -> x.
    let source = "2024-01-15 * \"q=\\\"hi\\\" bs=\\\\ tab=\\t x=\\x\"\n  \
                  Assets:Cash  -5.00 USD\n  Expenses:X  5.00 USD\n";
    let result = parse_ok(source);
    if let Directive::Transaction(txn) = &result.directives[0].value {
        assert_eq!(txn.narration.as_str(), "q=\"hi\" bs=\\ tab=\t x=x");
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
        assert!(txn.tags.iter().any(|t| t.as_str() == "food"));
        assert!(txn.tags.iter().any(|t| t.as_str() == "restaurant"));
        assert!(txn.links.iter().any(|l| l.as_str() == "receipt-123"));
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
fn test_commodity_precision_metadata_round_trips() {
    // Issue #991: per-commodity `precision: N` metadata must round-trip
    // through parse → format → parse without changing value or type.
    use rust_decimal_macros::dec;
    use rustledger_core::{FormatConfig, MetaValue, format_directives};

    let source = "2024-01-01 commodity USD\n  precision: 2\n";
    let parsed = parse_ok(source);
    let Directive::Commodity(comm) = &parsed.directives[0].value else {
        panic!("expected commodity");
    };
    // First parse: stays a Number(2), not a string or anything else.
    assert_eq!(
        comm.meta.get("precision"),
        Some(&MetaValue::Number(dec!(2))),
        "parser must produce Number(2) for unquoted integer metadata"
    );

    // Format the directive and re-parse — the value must survive unchanged.
    let formatted = format_directives([&parsed.directives[0].value], &FormatConfig::default());
    let reparsed = parse_ok(&formatted);
    let Directive::Commodity(comm2) = &reparsed.directives[0].value else {
        panic!("expected commodity after re-parse");
    };
    assert_eq!(
        comm2.meta.get("precision"),
        Some(&MetaValue::Number(dec!(2))),
        "round-tripped precision must remain Number(2); got formatted: {formatted:?}"
    );
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
        assert_eq!(
            cost.number.unwrap().per_unit().unwrap().to_string(),
            "185.50"
        );
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

#[test]
fn test_parse_boolean_metadata() {
    let source = r#"
2024-01-15 * "Test"
  recurring: TRUE
  active: FALSE
  enabled: True
  disabled: False
  Expenses:Test  100.00 USD
  Assets:Cash
"#;
    let result = parse_ok(source);

    if let Directive::Transaction(txn) = &result.directives[0].value {
        use rustledger_core::MetaValue;
        assert_eq!(txn.meta.get("recurring"), Some(&MetaValue::Bool(true)));
        assert_eq!(txn.meta.get("active"), Some(&MetaValue::Bool(false)));
        assert_eq!(txn.meta.get("enabled"), Some(&MetaValue::Bool(true)));
        assert_eq!(txn.meta.get("disabled"), Some(&MetaValue::Bool(false)));
    } else {
        panic!("expected transaction");
    }
}

#[test]
fn test_parse_extended_transaction_flags() {
    // Test all extended flags parse correctly
    for (flag, expected) in [
        ("P", 'P'), // Pad-generated
        ("S", 'S'), // Summarization
        ("T", 'T'), // Transfer
        ("C", 'C'), // Conversion
        ("U", 'U'), // Unrealized
        ("R", 'R'), // Return
        ("M", 'M'), // Merge
        ("#", '#'), // Bookmarked
        ("?", '?'), // Needs investigation
    ] {
        let source = format!(
            r#"
2024-01-15 {flag} "Test transaction"
  Expenses:Test  100 USD
  Assets:Cash
"#
        );
        let result = parse_ok(&source);
        if let Directive::Transaction(txn) = &result.directives[0].value {
            assert_eq!(
                txn.flag, expected,
                "Flag {flag} should parse as '{expected}'"
            );
        } else {
            panic!("expected transaction for flag {flag}");
        }
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
fn test_parse_single_digit_month() {
    // Beancount accepts YYYY-M-DD (single-digit month)
    let source = "2024-1-15 open Assets:Checking\n";
    let result = parse(source);
    assert!(
        result.errors.is_empty(),
        "unexpected errors for single-digit month: {:?}",
        result.errors
    );
    assert_eq!(count_directive_type(&result, "open"), 1);
    if let Directive::Open(open) = &result.directives[0].value {
        assert_eq!(open.date, rustledger_core::naive_date(2024, 1, 15).unwrap());
    } else {
        panic!("expected open directive");
    }
}

#[test]
fn test_parse_single_digit_day() {
    // Beancount accepts YYYY-MM-D (single-digit day)
    let source = "2024-01-5 open Assets:Cash USD\n";
    let result = parse(source);
    assert!(
        result.errors.is_empty(),
        "unexpected errors for single-digit day: {:?}",
        result.errors
    );
    assert_eq!(count_directive_type(&result, "open"), 1);
}

#[test]
fn test_parse_single_digit_month_and_day() {
    // Beancount accepts YYYY-M-D (single-digit month and day)
    let source = "2024-1-1 open Assets:Cash USD\n";
    let result = parse(source);
    assert!(
        result.errors.is_empty(),
        "unexpected errors for single-digit month/day: {:?}",
        result.errors
    );
    assert_eq!(count_directive_type(&result, "open"), 1);
    if let Directive::Open(open) = &result.directives[0].value {
        assert_eq!(open.date, rustledger_core::naive_date(2024, 1, 1).unwrap());
    } else {
        panic!("expected open directive");
    }
}

#[test]
fn test_error_invalid_leap_year_date() {
    // Feb 29 in a non-leap year should produce a descriptive error
    let source = "2023-02-29 open Assets:Cash USD\n";
    let result = parse(source);
    assert!(
        !result.errors.is_empty(),
        "expected error for invalid leap-year date"
    );
    let err = &result.errors[0];
    assert!(
        matches!(err.kind, ParseErrorKind::InvalidDateValue(_)),
        "expected InvalidDateValue error kind, got: {:?}",
        err.kind
    );
    let msg = err.message();
    assert!(
        msg.contains("day") && msg.contains("out of range"),
        "expected error mentioning 'day' and 'out of range', got: '{msg}'"
    );
    assert!(
        msg.contains("2023-02"),
        "expected error mentioning '2023-02', got: '{msg}'"
    );
}

#[test]
fn test_error_invalid_date_month_out_of_range() {
    // Month 13 should produce a descriptive error
    let source = "2024-13-01 open Assets:Cash USD\n";
    let result = parse(source);
    assert!(
        !result.errors.is_empty(),
        "expected error for month out of range"
    );
    let err = &result.errors[0];
    assert!(
        matches!(err.kind, ParseErrorKind::InvalidDateValue(_)),
        "expected InvalidDateValue error kind, got: {:?}",
        err.kind
    );
    let msg = err.message();
    assert!(
        msg.contains("month") && msg.contains("out of range"),
        "expected error mentioning 'month' and 'out of range', got: '{msg}'"
    );
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
    // Verify comments are captured
    assert_eq!(result.comments.len(), 2);
    assert!(result.comments[0].value.contains("This is a comment"));
    assert!(result.comments[1].value.contains("Another comment"));
}

#[test]
fn test_parse_comments_with_directives() {
    let source = r#"
; Header comment
option "operating_currency" "USD"

; Section comment
2024-01-01 open Assets:Bank USD
  description: "Main account"

; Footer comment
"#;
    let result = parse_ok(source);

    // Should have 1 directive (open)
    assert_eq!(result.directives.len(), 1);

    // Should have 1 option
    assert_eq!(result.options.len(), 1);

    // Should have 3 comments
    assert_eq!(result.comments.len(), 3);
    assert!(result.comments[0].value.contains("Header comment"));
    assert!(result.comments[1].value.contains("Section comment"));
    assert!(result.comments[2].value.contains("Footer comment"));
}

#[test]
fn test_parse_unicode_in_narration() {
    let source = r#"2024-01-15 * "Café ☕" "Latte mit Milch"
  Expenses:Food  5.00 EUR
  Assets:Cash"#;
    let result = parse_ok(source);
    assert_eq!(count_directive_type(&result, "transaction"), 1);

    if let Directive::Transaction(txn) = &result.directives[0].value {
        assert_eq!(txn.payee.as_deref(), Some("Café ☕"));
        assert_eq!(txn.narration.as_str(), "Latte mit Milch");
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

// ============================================================================
// Conformance: invalid inputs that must be rejected (pta-standards suite)
// ============================================================================

/// Case: invalid-leading-decimal
/// Amounts must have an integer part before the decimal point (.50 is invalid).
/// Valid amounts like 0.50 must still be accepted.
#[test]
fn test_reject_leading_decimal() {
    let source = "2024-01-15 * \"Test\"\n  Expenses:Food  .50 USD\n  Assets:Checking\n";
    let result = parse(source);
    assert!(
        !result.errors.is_empty(),
        "expected parse error for leading decimal amount '.50 USD'"
    );
}

/// Positive counterpart: amounts with an integer part must still be accepted.
#[test]
fn test_accept_decimal_with_integer_part() {
    let source = "2024-01-15 * \"Test\"\n  Expenses:Food  0.50 USD\n  Assets:Checking\n";
    let result = parse(source);
    assert!(
        result.errors.is_empty(),
        "valid amount '0.50 USD' should parse without errors, errors: {:?}",
        result.errors
    );
}

/// Case: invalid-booking-method-lowercase / booking-method-case-sensitive
/// Booking methods must be uppercase (FIFO, STRICT, `STRICT_WITH_SIZE`, LIFO, HIFO, NONE, AVERAGE).
/// Lowercase variants like "fifo" must be rejected.
#[test]
fn test_reject_lowercase_booking_method() {
    let source = "2024-01-01 open Assets:Stock AAPL \"fifo\"\n";
    let result = parse(source);
    assert!(
        !result.errors.is_empty(),
        "expected parse error for lowercase booking method 'fifo'"
    );
}

/// Counterpart: uppercase booking method must still be accepted.
#[test]
fn test_accept_uppercase_booking_method() {
    let source = "2024-01-01 open Assets:Stock AAPL \"FIFO\"\n";
    let result = parse(source);
    assert!(
        result.errors.is_empty(),
        "uppercase booking method 'FIFO' should be valid, errors: {:?}",
        result.errors
    );
}

/// `STRICT_WITH_SIZE` booking method must be accepted on open directives.
#[test]
fn test_accept_strict_with_size_booking_method() {
    let source = "2024-01-01 open Assets:Stock AAPL \"STRICT_WITH_SIZE\"\n";
    let result = parse(source);
    assert!(
        result.errors.is_empty(),
        "booking method 'STRICT_WITH_SIZE' should be valid, errors: {:?}",
        result.errors
    );

    if let Directive::Open(open) = &result.directives[0].value {
        assert_eq!(open.booking, Some("STRICT_WITH_SIZE".to_string()));
    } else {
        panic!("expected open directive");
    }
}

/// Invalid booking method error message should include `STRICT_WITH_SIZE` in the valid list.
#[test]
fn test_invalid_booking_method_error_includes_strict_with_size() {
    let source = "2024-01-01 open Assets:Stock AAPL \"invalid_method\"\n";
    let result = parse(source);
    assert!(
        !result.errors.is_empty(),
        "expected parse error for invalid booking method"
    );
    let error_msg = result.errors[0].message();
    assert!(
        error_msg.contains("STRICT_WITH_SIZE"),
        "error message should list STRICT_WITH_SIZE as a valid method, got: {error_msg}"
    );
}

/// Case: invalid-metadata-uppercase-key
/// Metadata keys must start with a lowercase ASCII letter.
/// Keys starting with uppercase (e.g. "Category:") must be rejected.
#[test]
fn test_reject_uppercase_metadata_key() {
    let source =
        "2024-01-15 * \"Test\"\n  Category: \"test\"\n  Expenses:Food  50 USD\n  Assets:Checking\n";
    let result = parse(source);
    assert!(
        !result.errors.is_empty(),
        "expected parse error for metadata key starting with uppercase 'Category:'"
    );
}

/// Case: invalid-balance-no-amount
/// Balance directives require both an account and an amount+currency.
#[test]
fn test_reject_balance_without_amount() {
    let source = "2024-01-15 balance Assets:Checking\n";
    let result = parse(source);
    assert!(
        !result.errors.is_empty(),
        "expected parse error for balance directive without amount"
    );
}

/// Case: invalid-pad-no-source
/// Pad directives require both a target account and a source account.
#[test]
fn test_reject_pad_without_source_account() {
    let source = "2024-01-15 pad Assets:Checking\n";
    let result = parse(source);
    assert!(
        !result.errors.is_empty(),
        "expected parse error for pad directive without source account"
    );
}

/// Case: unicode-account-name
/// Unicode letters (CJK, Cyrillic, etc.) are valid in account names.
/// This extends beyond the beancount v3 spec's ASCII restriction, which
/// was an artifact of the C flex lexer's poor Unicode support.
#[test]
fn test_accept_unicode_account_name() {
    let source = "2024-01-01 open Assets:銀行口座\n";
    let result = parse(source);
    assert!(
        result.errors.is_empty(),
        "Unicode account names should parse successfully, got: {:?}",
        result
            .errors
            .iter()
            .map(rustledger_parser::ParseError::message)
            .collect::<Vec<_>>()
    );
}

/// Case: invalid-cost-unclosed (issue #736)
/// A cost specification must be closed with `}` on the same logical line
/// as the opening `{`. Hitting a newline before the closing brace is a
/// parse error — the parser must not silently consume tokens on following
/// posting lines looking for a close brace.
#[test]
fn test_reject_unclosed_cost_brace() {
    let source = "\
2024-01-01 open Assets:Stock
2024-01-01 open Assets:Cash USD

2024-01-15 *
  Assets:Stock 10 AAPL {150 USD
  Assets:Cash -1500 USD
";
    let result = parse(source);
    assert!(
        result
            .errors
            .iter()
            .any(|e| e.message().contains("unclosed cost")),
        "expected 'unclosed cost' parse error, got: {:?}",
        result
            .errors
            .iter()
            .map(ParseError::message)
            .collect::<Vec<_>>()
    );
}

/// Regression: an incomplete final directive at EOF (no trailing newline
/// and no account name) must produce a parse error, not be silently
/// dropped by the top-level error-recovery loop. Guards against a Copilot
/// review finding from PR #740 where an overly-eager early-break on an
/// empty stream could mask real EOF syntax errors.
#[test]
fn test_reject_incomplete_final_directive_at_eof() {
    let source = "2024-01-01 open";
    let result = parse(source);
    assert!(
        !result.errors.is_empty(),
        "expected parse error for incomplete open directive at EOF, got: {:?}",
        result
            .errors
            .iter()
            .map(ParseError::message)
            .collect::<Vec<_>>()
    );
}

/// Regression: `{ N # T USD }` source carries both a per-unit and a
/// total. The booker derives per-unit as `T / |units|`, so the
/// user-written `N` is informationally redundant — Python beancount
/// treats this form as semantically equivalent to `{{ T USD }}` and
/// we follow suit. Pin the precedence so a future refactor can't
/// silently flip it (e.g. by keeping `N` instead and dropping `T`,
/// which would invert the post-booking value of every cost-basis
/// read of this spec form).
#[test]
fn test_cost_spec_n_hash_t_uses_total() {
    use rust_decimal_macros::dec;
    use rustledger_core::CostNumber;

    let source = "
2024-01-01 open Assets:Stock
2024-01-01 open Assets:Cash USD

2024-01-15 *
  Assets:Stock  10 STK {50 # 1500 USD}
  Assets:Cash  -1500.00 USD
";
    let result = parse_ok(source);
    let txn = result
        .directives
        .iter()
        .find_map(|d| match &d.value {
            Directive::Transaction(t) => Some(t),
            _ => None,
        })
        .expect("transaction present");
    let cost = txn.postings[0]
        .value
        .cost
        .as_ref()
        .expect("cost spec present");
    assert_eq!(
        cost.number,
        Some(CostNumber::Total { value: dec!(1500) }),
        "the `#` form must store the post-`#` total, not the pre-`#` per-unit"
    );
    assert_eq!(
        cost.currency
            .as_ref()
            .map(rustledger_core::Currency::as_str),
        Some("USD"),
        "currency must still be captured after the `# T` clause"
    );
}

/// Regression: an unclosed cost brace followed by EOF (no trailing newline)
/// should also produce a parse error, not silently drop the cost.
#[test]
fn test_reject_unclosed_cost_brace_at_eof() {
    let source = "\
2024-01-01 open Assets:Stock
2024-01-01 open Assets:Cash USD

2024-01-15 *
  Assets:Stock 10 AAPL {150 USD";
    let result = parse(source);
    assert!(
        result
            .errors
            .iter()
            .any(|e| e.message().contains("unclosed cost")),
        "expected 'unclosed cost' parse error at EOF, got: {:?}",
        result
            .errors
            .iter()
            .map(ParseError::message)
            .collect::<Vec<_>>()
    );
}
