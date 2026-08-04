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
    use rustledger_core::{FormatConfig, MetaValue, format_directives};

    let source = "2024-01-01 commodity USD\n  precision: 2\n";
    let parsed = parse_ok(source);
    let Directive::Commodity(comm) = &parsed.directives[0].value else {
        panic!("expected commodity");
    };
    // First parse: an unquoted integer literal is `Int(2)`, not a Number/string.
    assert_eq!(
        comm.meta.get("precision"),
        Some(&MetaValue::Int(2)),
        "parser must produce Int(2) for unquoted integer metadata"
    );

    // Format the directive and re-parse — the value must survive unchanged.
    let formatted = format_directives([&parsed.directives[0].value], &FormatConfig::default());
    let reparsed = parse_ok(&formatted);
    let Directive::Commodity(comm2) = &reparsed.directives[0].value else {
        panic!("expected commodity after re-parse");
    };
    assert_eq!(
        comm2.meta.get("precision"),
        Some(&MetaValue::Int(2)),
        "round-tripped precision must remain Int(2); got formatted: {formatted:?}"
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

/// Regression: custom directive values must preserve a leading `MINUS` sign and
/// carry `Tag`/`Link` values. `extract_custom_values` previously had no `MINUS`
/// arm (so `-50.00` emitted `+50.00`) and dropped tags/links entirely. All three
/// value-token extractors now share `value_tokens_to_meta`.
#[test]
fn test_custom_directive_preserves_sign_and_tag_link() {
    use rust_decimal_macros::dec;
    use rustledger_core::{Amount, Currency, MetaValue};

    let source = r#"2024-01-01 custom "budget" -50.00 USD #quarterly ^plan-2024 TRUE"#;
    let result = parse_ok(source);
    let spanned = result
        .directives
        .iter()
        .find(|d| matches!(d.value, Directive::Custom(_)))
        .expect("expected a custom directive");
    let Directive::Custom(custom) = &spanned.value else {
        unreachable!()
    };

    assert_eq!(
        custom.values,
        vec![
            // Signed amount keeps its sign (was emitted as +50.00).
            MetaValue::Amount(Amount::new(dec!(-50.00), Currency::new("USD"))),
            // Tag and Link are no longer dropped.
            MetaValue::Tag("quarterly".into()),
            MetaValue::Link("plan-2024".into()),
            MetaValue::Bool(true),
        ],
        "custom values: {:?}",
        custom.values
    );
}

/// Regression: a `pushmeta` value of `NUMBER CURRENCY` must parse as an
/// `Amount`. Before the three value-token walks were unified through
/// `value_tokens_to_meta`, `pushmeta_value` returned on the `NUMBER` token and
/// dropped the currency (`5 USD` became `Number(5)`).
#[test]
fn test_pushmeta_value_with_currency_is_amount() {
    use rust_decimal_macros::dec;
    use rustledger_core::{Amount, Currency, MetaValue};

    let source = r"
pushmeta budget: 5 USD
2024-01-01 open Assets:Cash USD
popmeta budget:
";
    let result = parse_ok(source);
    let open = result
        .directives
        .iter()
        .find_map(|d| match &d.value {
            Directive::Open(o) => Some(o),
            _ => None,
        })
        .expect("expected an open directive");
    assert_eq!(
        open.meta.get("budget"),
        Some(&MetaValue::Amount(Amount::new(
            dec!(5),
            Currency::new("USD")
        ))),
        "pushmeta budget should be Amount(5 USD); meta: {:?}",
        open.meta
    );
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

/// `{N # T CCY}` is beancount's `compound_amount`: per-unit `N` AND lump
/// total `T`; the cost totals `units*N + T`. An earlier version of this
/// test pinned the form to `Total{T}` — itself a partial fix (the parser
/// once dropped `T` entirely) that baked in dropping `N` instead; #1700
/// corrected the parse to carry both components as written.
#[test]
fn test_cost_spec_n_hash_t_parses_compound() {
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
        Some(CostNumber::Compound {
            per_unit: dec!(50),
            total: dec!(1500)
        }),
        "the `#` form must carry BOTH components as written (#1700): \
         beancount's compound_amount weighs N*per_unit + total"
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

/// `parse_without_occurrences` skips the LSP-only occurrence indices but is
/// otherwise identical to `parse` (the processing path's view). Pins the
/// optimization that drops ~40k per-token allocations on the load path.
#[test]
fn parse_without_occurrences_skips_indices_but_matches_directives() {
    let src = "2020-01-01 open Assets:Cash USD\n\
               2020-02-01 * \"p\" \"m\"\n  Assets:Cash 5.00 USD\n  Income:Salary\n";
    let full = rustledger_parser::parse(src);
    let lean = rustledger_parser::parse_without_occurrences(src);
    // Full parse collects occurrences; lean parse does not.
    assert!(
        !full.account_occurrences.is_empty() && !full.currency_occurrences.is_empty(),
        "full parse should collect occurrences"
    );
    assert!(
        lean.account_occurrences.is_empty() && lean.currency_occurrences.is_empty(),
        "lean parse must skip occurrence collection"
    );
    // Everything the processing pipeline consumes must be byte-for-byte
    // identical — only the occurrence indices differ. Compare full contents
    // (via Debug), not just counts, so a content regression that preserves
    // lengths can't slip through.
    assert_eq!(
        format!("{:?}", full.directives),
        format!("{:?}", lean.directives),
        "directives must be identical"
    );
    assert_eq!(
        format!("{:?}", full.errors),
        format!("{:?}", lean.errors),
        "errors must be identical"
    );
    assert_eq!(
        format!("{:?}", full.options),
        format!("{:?}", lean.options),
        "options must be identical"
    );
}

/// #1930: any NON-ASCII character is valid inside an account-name component.
///
/// Found by the beancount oracle's error axis: `Assets:CORP✨` is a committed
/// fixture in fava-portfolio-returns that beancount loads and rledger rejected
/// with P0012. Probing beancount showed its real rule is broader than "Unicode
/// letters" — symbols (`So`), arrows, and `No` digits all pass — so restricting
/// to `\p{L}` meant refusing files that exist.
///
/// The ASCII cases are the point of the test, not padding: they pin the
/// boundary that makes the widening safe. Every character with syntactic
/// meaning in beancount is ASCII, so an account name still cannot swallow a
/// price annotation or a cost brace.
#[test]
fn account_names_accept_any_non_ascii_but_no_ascii_punctuation() {
    for name in [
        "Assets:CORP✨", // So — the reported case
        "Assets:CORP½",  // No
        "Assets:CORP→",  // Sm
        "Assets:CORPé",  // L, already worked
        "Assets:CORP、", // ideographic punctuation
    ] {
        assert!(
            rustledger_parser::is_valid_account_name(name),
            "{name} must be accepted (beancount accepts it)",
        );
    }
    // Unicode whitespace and separators ARE accepted, by both tools. Pinned
    // so the sharp edge is visible in the suite and not only in a doc
    // comment: `Assets:A\u{a0}B` is ONE account, visually identical to
    // `Assets:A B`. Verified against beancount individually — excluding them
    // would reject files beancount loads, which is the bug #1930 fixes.
    for name in ["Assets:A\u{a0}B", "Assets:A\u{2028}B", "Assets:A\u{200b}B"] {
        assert!(
            rustledger_parser::is_valid_account_name(name),
            "{name:?} must be accepted (beancount accepts it)",
        );
    }
    for name in [
        "Assets:CORP_x", // ASCII punctuation
        "Assets:CORP.x",
        "Assets:CORP@x", // would collide with the price sigil
        "Assets:CORP{x", // would collide with a cost spec
        "Assets:corp✨", // component must start ASCII-uppercase
        "Assets:✨x",    // ...and a symbol is not a valid start
    ] {
        assert!(
            !rustledger_parser::is_valid_account_name(name),
            "{name} must be rejected (beancount rejects it)",
        );
    }
}

/// #1949: a `#tag` or `^link` is a parse error on directives that do not take
/// one — and is still fine where beancount allows it.
///
/// The accept half is not padding. beancount v3 DOES take tags and links on
/// `note` and `document`, and we already agreed with it there, so a blanket
/// "reject trailing tokens on non-transaction directives" would have broken
/// the two cases that were already right. That is why the check is a
/// per-directive call rather than one rule in the dispatcher.
#[test]
fn tags_and_links_are_rejected_only_where_beancount_rejects_them() {
    let pre = "2018-01-01 open Assets:CORP\n2018-01-01 open Equity:Opening\n";
    for (body, what) in [
        ("2018-06-01 open Assets:New #tag\n", "open/tag"),
        ("2018-06-01 open Assets:New ^lnk\n", "open/link"),
        ("2018-06-01 close Assets:CORP #tag\n", "close/tag"),
        (
            "2018-06-01 balance Assets:CORP 0.00 USD #tag\n",
            "balance/tag",
        ),
        ("2018-06-01 commodity EUR #tag\n", "commodity/tag"),
        ("2018-06-01 event \"loc\" \"here\" #tag\n", "event/tag"),
        ("2018-06-01 price EUR 1.10 USD #tag\n", "price/tag"),
        (
            "2018-06-01 pad Assets:CORP Equity:Opening #tag\n",
            "pad/tag",
        ),
    ] {
        let parsed = rustledger_parser::parse(&format!("{pre}{body}"));
        assert!(
            !parsed.errors.is_empty(),
            "{what}: must be a parse error (beancount rejects it)",
        );
    }
    for (body, what) in [
        ("2018-06-01 note Assets:CORP \"n\" #tag\n", "note/tag"),
        ("2018-06-01 note Assets:CORP \"n\" ^lnk\n", "note/link"),
        (
            "2018-06-01 document Assets:CORP \"/tmp/x.pdf\" #tag\n",
            "document/tag",
        ),
    ] {
        let parsed = rustledger_parser::parse(&format!("{pre}{body}"));
        assert!(
            parsed.errors.is_empty(),
            "{what}: must parse cleanly (beancount accepts it), got {:?}",
            parsed.errors,
        );
    }
    // A metadata VALUE may be a tag. The check scans DIRECT child tokens only,
    // and metadata lives in child NODES — this is the input a descendant walk
    // would wrongly reject, which is the worse mistake of the two.
    let parsed = rustledger_parser::parse("2018-01-01 open Assets:A\n  category: #groceries\n");
    assert!(
        parsed.errors.is_empty(),
        "a tag-valued metadata entry must still parse, got {:?}",
        parsed.errors,
    );
}

/// #1955: a metadata key needs at least two characters, as in beancount.
///
/// The reject case is the fix; the accept cases are the point of the test.
/// Only the LENGTH diverged — every other part of the key rule already matched
/// beancount — so this pins the boundary rather than the one bug, and would
/// catch a fix that over-tightened the character classes while it was at it.
#[test]
fn metadata_keys_need_at_least_two_characters() {
    let parse =
        |key: &str| rustledger_parser::parse(&format!("2018-01-01 open Assets:A\n  {key}: 42\n"));
    assert!(
        !parse("k").errors.is_empty(),
        "a single-character key must be rejected (beancount: LexerError)",
    );
    for key in ["kk", "k1", "k-", "k_", "abc"] {
        let parsed = parse(key);
        assert!(
            parsed.errors.is_empty(),
            "{key}: must still be accepted (beancount accepts it), got {:?}",
            parsed.errors,
        );
    }
    // Already agreed before this change, kept so a future edit to the rule
    // cannot quietly relax it.
    assert!(
        !parse("A").errors.is_empty(),
        "an uppercase start must stay rejected",
    );
}
