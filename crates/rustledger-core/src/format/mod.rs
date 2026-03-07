//! Beancount file formatter.
//!
//! Provides pretty-printing for beancount directives with configurable
//! amount alignment.

mod amount;
mod directives;
mod helpers;
mod transaction;

pub(crate) use amount::{format_amount, format_cost_spec, format_price_annotation};
pub(crate) use directives::{
    format_balance, format_close, format_commodity, format_custom, format_document, format_event,
    format_note, format_open, format_pad, format_price, format_query,
};
pub use helpers::escape_string;
pub(crate) use helpers::format_meta_value;
pub(crate) use transaction::{format_incomplete_amount, format_transaction};

use crate::Directive;

/// Formatter configuration.
#[derive(Debug, Clone)]
pub struct FormatConfig {
    /// Column to align amounts to (default: 60).
    pub amount_column: usize,
    /// Indentation for postings and metadata (default: 2 spaces).
    pub indent: String,
}

impl Default for FormatConfig {
    fn default() -> Self {
        Self {
            amount_column: 60,
            indent: "  ".to_string(),
        }
    }
}

impl FormatConfig {
    /// Create a new config with the specified amount column.
    #[must_use]
    pub fn with_column(column: usize) -> Self {
        Self {
            amount_column: column,
            ..Default::default()
        }
    }

    /// Create a new config with the specified indent width.
    #[must_use]
    pub fn with_indent(indent_width: usize) -> Self {
        let indent = " ".repeat(indent_width);
        Self {
            indent,
            ..Default::default()
        }
    }

    /// Create a new config with both column and indent settings.
    #[must_use]
    pub fn new(column: usize, indent_width: usize) -> Self {
        let indent = " ".repeat(indent_width);
        Self {
            amount_column: column,
            indent,
        }
    }
}

/// Format a directive to a string.
pub fn format_directive(directive: &Directive, config: &FormatConfig) -> String {
    match directive {
        Directive::Transaction(txn) => format_transaction(txn, config),
        Directive::Balance(bal) => format_balance(bal, config),
        Directive::Open(open) => format_open(open, config),
        Directive::Close(close) => format_close(close, config),
        Directive::Commodity(comm) => format_commodity(comm, config),
        Directive::Pad(pad) => format_pad(pad, config),
        Directive::Event(event) => format_event(event, config),
        Directive::Query(query) => format_query(query, config),
        Directive::Note(note) => format_note(note, config),
        Directive::Document(doc) => format_document(doc, config),
        Directive::Price(price) => format_price(price, config),
        Directive::Custom(custom) => format_custom(custom, config),
    }
}

#[cfg(test)]
mod tests {
    use super::transaction::format_posting;
    use super::*;
    use crate::{
        Amount, Balance, Close, Commodity, CostSpec, Custom, Directive, Document, Event,
        IncompleteAmount, MetaValue, Metadata, NaiveDate, Note, Open, Pad, Posting, Price,
        PriceAnnotation, Query, Transaction,
    };
    use rust_decimal_macros::dec;

    fn date(year: i32, month: u32, day: u32) -> NaiveDate {
        NaiveDate::from_ymd_opt(year, month, day).unwrap()
    }

    #[test]
    fn test_format_simple_transaction() {
        let txn = Transaction::new(date(2024, 1, 15), "Morning coffee")
            .with_flag('*')
            .with_payee("Coffee Shop")
            .with_posting(Posting::new(
                "Expenses:Food:Coffee",
                Amount::new(dec!(5.00), "USD"),
            ))
            .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-5.00), "USD")));

        let config = FormatConfig::with_column(50);
        let formatted = format_transaction(&txn, &config);

        assert!(formatted.contains("2024-01-15 * \"Coffee Shop\" \"Morning coffee\""));
        assert!(formatted.contains("Expenses:Food:Coffee"));
        assert!(formatted.contains("5.00 USD"));
    }

    #[test]
    fn test_format_balance() {
        let bal = Balance::new(
            date(2024, 1, 1),
            "Assets:Bank",
            Amount::new(dec!(1000.00), "USD"),
        );
        let config = FormatConfig::default();
        let formatted = format_balance(&bal, &config);
        assert_eq!(formatted, "2024-01-01 balance Assets:Bank 1000.00 USD\n");
    }

    #[test]
    fn test_format_open() {
        let open = Open {
            date: date(2024, 1, 1),
            account: "Assets:Bank:Checking".into(),
            currencies: vec!["USD".into(), "EUR".into()],
            booking: None,
            meta: Default::default(),
        };
        let config = FormatConfig::default();
        let formatted = format_open(&open, &config);
        assert_eq!(formatted, "2024-01-01 open Assets:Bank:Checking USD,EUR\n");
    }

    #[test]
    fn test_escape_string() {
        assert_eq!(escape_string("hello"), "hello");
        assert_eq!(escape_string("say \"hi\""), "say \\\"hi\\\"");
        assert_eq!(escape_string("line1\nline2"), "line1\\nline2");
    }

    // ====================================================================
    // Phase 2: Additional Coverage Tests for Format Functions
    // ====================================================================

    #[test]
    fn test_escape_string_combined() {
        // Test escaping with quotes + backslash + newline combined
        assert_eq!(
            escape_string("path\\to\\file\n\"quoted\""),
            "path\\\\to\\\\file\\n\\\"quoted\\\""
        );
    }

    #[test]
    fn test_escape_string_backslash_quote() {
        // Backslash followed by quote
        assert_eq!(escape_string("\\\""), "\\\\\\\"");
    }

    #[test]
    fn test_escape_string_empty() {
        assert_eq!(escape_string(""), "");
    }

    #[test]
    fn test_escape_string_unicode() {
        assert_eq!(escape_string("café résumé"), "café résumé");
        assert_eq!(escape_string("日本語"), "日本語");
        assert_eq!(escape_string("emoji 🎉"), "emoji 🎉");
    }

    #[test]
    fn test_format_meta_value_string() {
        let val = MetaValue::String("hello world".to_string());
        assert_eq!(format_meta_value(&val), "\"hello world\"");
    }

    #[test]
    fn test_format_meta_value_string_with_quotes() {
        let val = MetaValue::String("say \"hello\"".to_string());
        assert_eq!(format_meta_value(&val), "\"say \\\"hello\\\"\"");
    }

    #[test]
    fn test_format_meta_value_account() {
        let val = MetaValue::Account("Assets:Bank:Checking".to_string());
        assert_eq!(format_meta_value(&val), "Assets:Bank:Checking");
    }

    #[test]
    fn test_format_meta_value_currency() {
        let val = MetaValue::Currency("USD".to_string());
        assert_eq!(format_meta_value(&val), "USD");
    }

    #[test]
    fn test_format_meta_value_tag() {
        let val = MetaValue::Tag("trip-2024".to_string());
        assert_eq!(format_meta_value(&val), "#trip-2024");
    }

    #[test]
    fn test_format_meta_value_link() {
        let val = MetaValue::Link("invoice-123".to_string());
        assert_eq!(format_meta_value(&val), "^invoice-123");
    }

    #[test]
    fn test_format_meta_value_date() {
        let val = MetaValue::Date(date(2024, 6, 15));
        assert_eq!(format_meta_value(&val), "2024-06-15");
    }

    #[test]
    fn test_format_meta_value_number() {
        let val = MetaValue::Number(dec!(123.456));
        assert_eq!(format_meta_value(&val), "123.456");
    }

    #[test]
    fn test_format_meta_value_amount() {
        let val = MetaValue::Amount(Amount::new(dec!(99.99), "USD"));
        assert_eq!(format_meta_value(&val), "99.99 USD");
    }

    #[test]
    fn test_format_meta_value_bool_true() {
        let val = MetaValue::Bool(true);
        assert_eq!(format_meta_value(&val), "TRUE");
    }

    #[test]
    fn test_format_meta_value_bool_false() {
        let val = MetaValue::Bool(false);
        assert_eq!(format_meta_value(&val), "FALSE");
    }

    #[test]
    fn test_format_meta_value_none() {
        let val = MetaValue::None;
        assert_eq!(format_meta_value(&val), "");
    }

    #[test]
    fn test_format_cost_spec_per_unit() {
        let spec = CostSpec {
            number_per: Some(dec!(150.00)),
            number_total: None,
            currency: Some("USD".into()),
            date: None,
            label: None,
            merge: false,
        };
        assert_eq!(format_cost_spec(&spec), "{150.00 USD}");
    }

    #[test]
    fn test_format_cost_spec_total() {
        let spec = CostSpec {
            number_per: None,
            number_total: Some(dec!(1500.00)),
            currency: Some("USD".into()),
            date: None,
            label: None,
            merge: false,
        };
        assert_eq!(format_cost_spec(&spec), "{{1500.00 USD}}");
    }

    #[test]
    fn test_format_cost_spec_with_date() {
        let spec = CostSpec {
            number_per: Some(dec!(150.00)),
            number_total: None,
            currency: Some("USD".into()),
            date: Some(date(2024, 1, 15)),
            label: None,
            merge: false,
        };
        assert_eq!(format_cost_spec(&spec), "{150.00 USD, 2024-01-15}");
    }

    #[test]
    fn test_format_cost_spec_with_label() {
        let spec = CostSpec {
            number_per: Some(dec!(150.00)),
            number_total: None,
            currency: Some("USD".into()),
            date: None,
            label: Some("lot-a".to_string()),
            merge: false,
        };
        assert_eq!(format_cost_spec(&spec), "{150.00 USD, \"lot-a\"}");
    }

    #[test]
    fn test_format_cost_spec_with_merge() {
        let spec = CostSpec {
            number_per: Some(dec!(150.00)),
            number_total: None,
            currency: Some("USD".into()),
            date: None,
            label: None,
            merge: true,
        };
        assert_eq!(format_cost_spec(&spec), "{150.00 USD, *}");
    }

    #[test]
    fn test_format_cost_spec_all_fields() {
        let spec = CostSpec {
            number_per: Some(dec!(150.00)),
            number_total: None,
            currency: Some("USD".into()),
            date: Some(date(2024, 1, 15)),
            label: Some("lot-a".to_string()),
            merge: true,
        };
        assert_eq!(
            format_cost_spec(&spec),
            "{150.00 USD, 2024-01-15, \"lot-a\", *}"
        );
    }

    #[test]
    fn test_format_cost_spec_empty() {
        let spec = CostSpec {
            number_per: None,
            number_total: None,
            currency: None,
            date: None,
            label: None,
            merge: false,
        };
        assert_eq!(format_cost_spec(&spec), "{}");
    }

    #[test]
    fn test_format_price_annotation_unit() {
        let price = PriceAnnotation::Unit(Amount::new(dec!(150.00), "USD"));
        assert_eq!(format_price_annotation(&price), "@ 150.00 USD");
    }

    #[test]
    fn test_format_price_annotation_total() {
        let price = PriceAnnotation::Total(Amount::new(dec!(1500.00), "USD"));
        assert_eq!(format_price_annotation(&price), "@@ 1500.00 USD");
    }

    #[test]
    fn test_format_price_annotation_unit_incomplete() {
        let price = PriceAnnotation::UnitIncomplete(IncompleteAmount::NumberOnly(dec!(150.00)));
        assert_eq!(format_price_annotation(&price), "@ 150.00");
    }

    #[test]
    fn test_format_price_annotation_total_incomplete() {
        let price = PriceAnnotation::TotalIncomplete(IncompleteAmount::CurrencyOnly("USD".into()));
        assert_eq!(format_price_annotation(&price), "@@ USD");
    }

    #[test]
    fn test_format_price_annotation_unit_empty() {
        let price = PriceAnnotation::UnitEmpty;
        assert_eq!(format_price_annotation(&price), "@");
    }

    #[test]
    fn test_format_price_annotation_total_empty() {
        let price = PriceAnnotation::TotalEmpty;
        assert_eq!(format_price_annotation(&price), "@@");
    }

    #[test]
    fn test_format_incomplete_amount_complete() {
        let amount = IncompleteAmount::Complete(Amount::new(dec!(100.50), "EUR"));
        assert_eq!(format_incomplete_amount(&amount), "100.50 EUR");
    }

    #[test]
    fn test_format_incomplete_amount_number_only() {
        let amount = IncompleteAmount::NumberOnly(dec!(42.00));
        assert_eq!(format_incomplete_amount(&amount), "42.00");
    }

    #[test]
    fn test_format_incomplete_amount_currency_only() {
        let amount = IncompleteAmount::CurrencyOnly("BTC".into());
        assert_eq!(format_incomplete_amount(&amount), "BTC");
    }

    #[test]
    fn test_format_close() {
        let close = Close {
            date: date(2024, 12, 31),
            account: "Assets:OldAccount".into(),
            meta: Default::default(),
        };
        let config = FormatConfig::default();
        let formatted = format_close(&close, &config);
        assert_eq!(formatted, "2024-12-31 close Assets:OldAccount\n");
    }

    #[test]
    fn test_format_commodity() {
        let comm = Commodity {
            date: date(2024, 1, 1),
            currency: "BTC".into(),
            meta: Default::default(),
        };
        let config = FormatConfig::default();
        let formatted = format_commodity(&comm, &config);
        assert_eq!(formatted, "2024-01-01 commodity BTC\n");
    }

    #[test]
    fn test_format_pad() {
        let pad = Pad {
            date: date(2024, 1, 15),
            account: "Assets:Checking".into(),
            source_account: "Equity:Opening-Balances".into(),
            meta: Default::default(),
        };
        let config = FormatConfig::default();
        let formatted = format_pad(&pad, &config);
        assert_eq!(
            formatted,
            "2024-01-15 pad Assets:Checking Equity:Opening-Balances\n"
        );
    }

    #[test]
    fn test_format_event() {
        let event = Event {
            date: date(2024, 6, 1),
            event_type: "location".to_string(),
            value: "New York".to_string(),
            meta: Default::default(),
        };
        let config = FormatConfig::default();
        let formatted = format_event(&event, &config);
        assert_eq!(formatted, "2024-06-01 event \"location\" \"New York\"\n");
    }

    #[test]
    fn test_format_event_with_quotes() {
        let event = Event {
            date: date(2024, 6, 1),
            event_type: "quote".to_string(),
            value: "He said \"hello\"".to_string(),
            meta: Default::default(),
        };
        let config = FormatConfig::default();
        let formatted = format_event(&event, &config);
        assert_eq!(
            formatted,
            "2024-06-01 event \"quote\" \"He said \\\"hello\\\"\"\n"
        );
    }

    #[test]
    fn test_format_query() {
        let query = Query {
            date: date(2024, 1, 1),
            name: "monthly_expenses".to_string(),
            query: "SELECT account, sum(position) WHERE account ~ 'Expenses'".to_string(),
            meta: Default::default(),
        };
        let config = FormatConfig::default();
        let formatted = format_query(&query, &config);
        assert!(formatted.contains("query \"monthly_expenses\""));
        assert!(formatted.contains("SELECT account"));
    }

    #[test]
    fn test_format_note() {
        let note = Note {
            date: date(2024, 3, 15),
            account: "Assets:Bank".into(),
            comment: "Called the bank about fee".to_string(),
            meta: Default::default(),
        };
        let config = FormatConfig::default();
        let formatted = format_note(&note, &config);
        assert_eq!(
            formatted,
            "2024-03-15 note Assets:Bank \"Called the bank about fee\"\n"
        );
    }

    #[test]
    fn test_format_document() {
        let doc = Document {
            date: date(2024, 2, 10),
            account: "Assets:Bank".into(),
            path: "/docs/statement-2024-02.pdf".to_string(),
            tags: vec![],
            links: vec![],
            meta: Default::default(),
        };
        let config = FormatConfig::default();
        let formatted = format_document(&doc, &config);
        assert_eq!(
            formatted,
            "2024-02-10 document Assets:Bank \"/docs/statement-2024-02.pdf\"\n"
        );
    }

    #[test]
    fn test_format_price() {
        let price = Price {
            date: date(2024, 1, 15),
            currency: "AAPL".into(),
            amount: Amount::new(dec!(185.50), "USD"),
            meta: Default::default(),
        };
        let config = FormatConfig::default();
        let formatted = format_price(&price, &config);
        assert_eq!(formatted, "2024-01-15 price AAPL 185.50 USD\n");
    }

    #[test]
    fn test_format_custom() {
        let custom = Custom {
            date: date(2024, 1, 1),
            custom_type: "budget".to_string(),
            values: vec![],
            meta: Default::default(),
        };
        let config = FormatConfig::default();
        let formatted = format_custom(&custom, &config);
        assert_eq!(formatted, "2024-01-01 custom \"budget\"\n");
    }

    #[test]
    fn test_format_open_with_booking() {
        let open = Open {
            date: date(2024, 1, 1),
            account: "Assets:Brokerage".into(),
            currencies: vec!["USD".into()],
            booking: Some("FIFO".to_string()),
            meta: Default::default(),
        };
        let config = FormatConfig::default();
        let formatted = format_open(&open, &config);
        assert_eq!(formatted, "2024-01-01 open Assets:Brokerage USD \"FIFO\"\n");
    }

    #[test]
    fn test_format_open_no_currencies() {
        let open = Open {
            date: date(2024, 1, 1),
            account: "Assets:Misc".into(),
            currencies: vec![],
            booking: None,
            meta: Default::default(),
        };
        let config = FormatConfig::default();
        let formatted = format_open(&open, &config);
        assert_eq!(formatted, "2024-01-01 open Assets:Misc\n");
    }

    #[test]
    fn test_format_balance_with_tolerance() {
        let bal = Balance {
            date: date(2024, 1, 1),
            account: "Assets:Bank".into(),
            amount: Amount::new(dec!(1000.00), "USD"),
            tolerance: Some(dec!(0.01)),
            meta: Default::default(),
        };
        let config = FormatConfig::default();
        let formatted = format_balance(&bal, &config);
        assert_eq!(
            formatted,
            "2024-01-01 balance Assets:Bank 1000.00 USD ~ 0.01\n"
        );
    }

    #[test]
    fn test_format_transaction_with_tags() {
        let txn = Transaction::new(date(2024, 1, 15), "Dinner")
            .with_flag('*')
            .with_tag("trip-2024")
            .with_tag("food")
            .with_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-50.00), "USD"),
            ));

        let config = FormatConfig::default();
        let formatted = format_transaction(&txn, &config);

        assert!(formatted.contains("#trip-2024"));
        assert!(formatted.contains("#food"));
    }

    #[test]
    fn test_format_transaction_with_links() {
        let txn = Transaction::new(date(2024, 1, 15), "Invoice payment")
            .with_flag('*')
            .with_link("invoice-123")
            .with_posting(Posting::new(
                "Income:Freelance",
                Amount::new(dec!(-1000.00), "USD"),
            ))
            .with_posting(Posting::new(
                "Assets:Bank",
                Amount::new(dec!(1000.00), "USD"),
            ));

        let config = FormatConfig::default();
        let formatted = format_transaction(&txn, &config);

        assert!(formatted.contains("^invoice-123"));
    }

    #[test]
    fn test_format_transaction_with_metadata() {
        let mut meta = Metadata::default();
        meta.insert(
            "filename".to_string(),
            MetaValue::String("receipt.pdf".to_string()),
        );
        meta.insert("verified".to_string(), MetaValue::Bool(true));

        let txn = Transaction {
            date: date(2024, 1, 15),
            flag: '*',
            payee: None,
            narration: "Purchase".into(),
            tags: vec![],
            links: vec![],
            postings: vec![],
            meta,
            trailing_comments: Vec::new(),
        };

        let config = FormatConfig::default();
        let formatted = format_transaction(&txn, &config);

        assert!(formatted.contains("filename: \"receipt.pdf\""));
        assert!(formatted.contains("verified: TRUE"));
    }

    #[test]
    fn test_format_posting_with_flag() {
        let mut posting = Posting::new("Expenses:Unknown", Amount::new(dec!(100.00), "USD"));
        posting.flag = Some('!');

        let config = FormatConfig::default();
        let formatted = format_posting(&posting, &config);

        assert!(formatted.contains("! Expenses:Unknown"));
    }

    #[test]
    fn test_format_posting_no_units() {
        let posting = Posting {
            flag: None,
            account: "Assets:Bank".into(),
            units: None,
            cost: None,
            price: None,
            meta: Default::default(),
            comments: Vec::new(),
            trailing_comments: Vec::new(),
        };

        let config = FormatConfig::default();
        let formatted = format_posting(&posting, &config);

        assert!(formatted.contains("Assets:Bank"));
        // No amount should appear
        assert!(!formatted.contains("USD"));
    }

    #[test]
    fn test_format_config_with_column() {
        let config = FormatConfig::with_column(80);
        assert_eq!(config.amount_column, 80);
        assert_eq!(config.indent, "  ");
    }

    #[test]
    fn test_format_config_with_indent() {
        let config = FormatConfig::with_indent(4);
        assert_eq!(config.indent, "    ");
    }

    #[test]
    fn test_format_config_new() {
        let config = FormatConfig::new(70, 3);
        assert_eq!(config.amount_column, 70);
        assert_eq!(config.indent, "   ");
    }

    #[test]
    fn test_format_posting_long_account_name() {
        let posting = Posting::new(
            "Assets:Bank:Checking:Primary:Joint:Savings:Emergency:Fund:Extra:Long",
            Amount::new(dec!(100.00), "USD"),
        );

        let config = FormatConfig::with_column(50);
        let formatted = format_posting(&posting, &config);

        // Should have at least 2 spaces between account and amount
        assert!(formatted.contains("  100.00 USD"));
    }

    #[test]
    fn test_format_posting_with_cost_and_price() {
        let posting = Posting {
            flag: None,
            account: "Assets:Brokerage".into(),
            units: Some(IncompleteAmount::Complete(Amount::new(dec!(10), "AAPL"))),
            cost: Some(CostSpec {
                number_per: Some(dec!(150.00)),
                number_total: None,
                currency: Some("USD".into()),
                date: Some(date(2024, 1, 15)),
                label: None,
                merge: false,
            }),
            price: Some(PriceAnnotation::Unit(Amount::new(dec!(155.00), "USD"))),
            meta: Default::default(),
            comments: Vec::new(),
            trailing_comments: Vec::new(),
        };

        let config = FormatConfig::default();
        let formatted = format_posting(&posting, &config);

        assert!(formatted.contains("10 AAPL"));
        assert!(formatted.contains("{150.00 USD, 2024-01-15}"));
        assert!(formatted.contains("@ 155.00 USD"));
    }

    #[test]
    fn test_format_directive_all_types() {
        let config = FormatConfig::default();

        // Transaction
        let txn = Transaction::new(date(2024, 1, 1), "Test")
            .with_flag('*')
            .with_posting(Posting::new("Expenses:Test", Amount::new(dec!(1), "USD")))
            .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-1), "USD")));
        let formatted = format_directive(&Directive::Transaction(txn), &config);
        assert!(formatted.contains("2024-01-01"));

        // Balance
        let bal = Balance::new(
            date(2024, 1, 1),
            "Assets:Bank",
            Amount::new(dec!(100), "USD"),
        );
        let formatted = format_directive(&Directive::Balance(bal), &config);
        assert!(formatted.contains("balance"));

        // Open
        let open = Open {
            date: date(2024, 1, 1),
            account: "Assets:Test".into(),
            currencies: vec![],
            booking: None,
            meta: Default::default(),
        };
        let formatted = format_directive(&Directive::Open(open), &config);
        assert!(formatted.contains("open"));

        // Close
        let close = Close {
            date: date(2024, 1, 1),
            account: "Assets:Test".into(),
            meta: Default::default(),
        };
        let formatted = format_directive(&Directive::Close(close), &config);
        assert!(formatted.contains("close"));

        // Commodity
        let comm = Commodity {
            date: date(2024, 1, 1),
            currency: "BTC".into(),
            meta: Default::default(),
        };
        let formatted = format_directive(&Directive::Commodity(comm), &config);
        assert!(formatted.contains("commodity"));

        // Pad
        let pad = Pad {
            date: date(2024, 1, 1),
            account: "Assets:A".into(),
            source_account: "Equity:B".into(),
            meta: Default::default(),
        };
        let formatted = format_directive(&Directive::Pad(pad), &config);
        assert!(formatted.contains("pad"));

        // Event
        let event = Event {
            date: date(2024, 1, 1),
            event_type: "test".to_string(),
            value: "value".to_string(),
            meta: Default::default(),
        };
        let formatted = format_directive(&Directive::Event(event), &config);
        assert!(formatted.contains("event"));

        // Query
        let query = Query {
            date: date(2024, 1, 1),
            name: "test".to_string(),
            query: "SELECT *".to_string(),
            meta: Default::default(),
        };
        let formatted = format_directive(&Directive::Query(query), &config);
        assert!(formatted.contains("query"));

        // Note
        let note = Note {
            date: date(2024, 1, 1),
            account: "Assets:Bank".into(),
            comment: "test".to_string(),
            meta: Default::default(),
        };
        let formatted = format_directive(&Directive::Note(note), &config);
        assert!(formatted.contains("note"));

        // Document
        let doc = Document {
            date: date(2024, 1, 1),
            account: "Assets:Bank".into(),
            path: "/path".to_string(),
            tags: vec![],
            links: vec![],
            meta: Default::default(),
        };
        let formatted = format_directive(&Directive::Document(doc), &config);
        assert!(formatted.contains("document"));

        // Price
        let price = Price {
            date: date(2024, 1, 1),
            currency: "AAPL".into(),
            amount: Amount::new(dec!(150), "USD"),
            meta: Default::default(),
        };
        let formatted = format_directive(&Directive::Price(price), &config);
        assert!(formatted.contains("price"));

        // Custom
        let custom = Custom {
            date: date(2024, 1, 1),
            custom_type: "test".to_string(),
            values: vec![],
            meta: Default::default(),
        };
        let formatted = format_directive(&Directive::Custom(custom), &config);
        assert!(formatted.contains("custom"));
    }

    #[test]
    fn test_format_amount_negative() {
        let amount = Amount::new(dec!(-100.50), "USD");
        assert_eq!(format_amount(&amount), "-100.50 USD");
    }

    #[test]
    fn test_format_amount_zero() {
        let amount = Amount::new(dec!(0), "EUR");
        assert_eq!(format_amount(&amount), "0 EUR");
    }

    #[test]
    fn test_format_amount_large_number() {
        let amount = Amount::new(dec!(1234567890.12), "USD");
        assert_eq!(format_amount(&amount), "1234567890.12 USD");
    }

    #[test]
    fn test_format_amount_small_decimal() {
        let amount = Amount::new(dec!(0.00001), "BTC");
        assert_eq!(format_amount(&amount), "0.00001 BTC");
    }

    #[test]
    fn test_format_transaction_with_inline_comment() {
        let config = FormatConfig::default();

        // Create a posting with an inline comment
        let mut posting = Posting::new("Expenses:Food", Amount::new(dec!(50), "USD"));
        posting.comments = vec!["; This is an inline comment".to_string()];

        let txn = Transaction::new(date(2024, 1, 15), "Test transaction")
            .with_flag('*')
            .with_posting(posting)
            .with_posting(Posting::new("Assets:Bank", Amount::new(dec!(-50), "USD")));

        let formatted = format_transaction(&txn, &config);

        // The inline comment should appear before the first posting
        assert!(
            formatted.contains("; This is an inline comment"),
            "Formatted transaction should contain inline comment: {formatted}"
        );
        // Comment should appear before Expenses:Food
        let comment_pos = formatted.find("; This is an inline comment").unwrap();
        let expenses_pos = formatted.find("Expenses:Food").unwrap();
        assert!(
            comment_pos < expenses_pos,
            "Comment should appear before the posting"
        );
    }

    // Issue #364: Comprehensive test for all comment positions in transactions
    #[test]
    fn test_issue_364_format_all_comment_types() {
        let config = FormatConfig::default();

        // Create first posting with pre-comments and trailing comment
        let mut posting1 = Posting::new("Expenses:Food", Amount::new(dec!(50), "USD"));
        posting1.comments = vec!["; Pre-comment 1".to_string(), "; Pre-comment 2".to_string()];
        posting1.trailing_comments = vec!["; trailing on posting".to_string()];

        // Create second posting with pre-comment
        let mut posting2 = Posting::new("Assets:Bank", Amount::new(dec!(-50), "USD"));
        posting2.comments = vec!["; Comment before second posting".to_string()];

        // Create transaction with trailing comments
        let mut txn = Transaction::new(date(2024, 1, 15), "Test transaction")
            .with_flag('*')
            .with_posting(posting1)
            .with_posting(posting2);
        txn.trailing_comments = vec![
            "; Transaction trailing 1".to_string(),
            "; Transaction trailing 2".to_string(),
        ];

        let formatted = format_transaction(&txn, &config);

        // Verify all comments are present in correct order
        let lines: Vec<&str> = formatted.lines().collect();

        // Line 0: transaction header
        assert!(lines[0].contains("2024-01-15 * \"Test transaction\""));

        // Lines 1-2: pre-comments for first posting
        assert_eq!(lines[1].trim(), "; Pre-comment 1");
        assert_eq!(lines[2].trim(), "; Pre-comment 2");

        // Line 3: first posting with trailing comment
        assert!(lines[3].contains("Expenses:Food"));
        assert!(lines[3].contains("; trailing on posting"));

        // Line 4: pre-comment for second posting
        assert_eq!(lines[4].trim(), "; Comment before second posting");

        // Line 5: second posting
        assert!(lines[5].contains("Assets:Bank"));

        // Lines 6-7: transaction trailing comments
        assert_eq!(lines[6].trim(), "; Transaction trailing 1");
        assert_eq!(lines[7].trim(), "; Transaction trailing 2");
    }

    // Issue #364: Verify trailing comments on posting line are formatted correctly
    #[test]
    fn test_issue_364_trailing_comment_on_posting_line() {
        let config = FormatConfig::default();

        let mut posting = Posting::new("Expenses:Food", Amount::new(dec!(50), "USD"));
        posting.trailing_comments = vec!["; This goes on same line".to_string()];

        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_flag('*')
            .with_posting(posting)
            .with_posting(Posting::auto("Assets:Bank"));

        let formatted = format_transaction(&txn, &config);

        // The trailing comment should be on the same line as the posting
        for line in formatted.lines() {
            if line.contains("Expenses:Food") {
                assert!(
                    line.contains("; This goes on same line"),
                    "Trailing comment should be on same line as posting: {line}"
                );
                break;
            }
        }
    }
}
