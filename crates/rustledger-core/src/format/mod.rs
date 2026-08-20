//! Beancount file formatter.
//!
//! Provides pretty-printing for beancount directives with configurable
//! amount alignment.

mod align;
mod amount;
mod directives;
mod helpers;
mod transaction;

pub use align::{Alignment, FormatLine, render_lines, resolve_alignment};
pub(crate) use amount::{format_amount_with, format_cost_spec, format_price_annotation};
use directives::{
    format_balance_lines, format_close_lines, format_commodity_lines, format_custom_lines,
    format_document_lines, format_event_lines, format_note_lines, format_open_lines,
    format_pad_lines, format_price_lines, format_query_lines,
};
pub(crate) use helpers::format_meta_value;
pub use helpers::{escape_csv, escape_json, escape_string};
pub(crate) use transaction::{format_incomplete_amount, format_transaction_lines};
pub use transaction::{format_posting_line, posting_format_line};

use crate::Directive;

/// Formatter configuration.
#[derive(Debug, Clone)]
pub struct FormatConfig {
    /// How to align amounts (default: [`Alignment::Auto`], matching
    /// `bean-format`).
    pub alignment: Alignment,
    /// Indentation for postings and metadata (default: 2 spaces).
    pub indent: String,
    /// Optional number rendering context (#1766): when set, amount,
    /// cost, price, tolerance, and amount-typed metadata numbers render
    /// through [`crate::DisplayContext::format_plain`] — per-currency
    /// PRECISION padding (`option "display_precision"`, observed
    /// distributions) that never rounds an over-precise value away
    /// (quantizing a balance amount would change its meaning), and
    /// leaves currencies the context does not track byte-faithful to
    /// their own scale. Thousands separators are deliberately never
    /// emitted even when the context has `render_commas` set: canonical
    /// ledger text carries no separators (the CST canonicalizer strips
    /// them by definition, matching `bean-format`) — commas remain a
    /// report/query display concern, honored where they always were.
    /// `None` preserves each value's own scale byte-for-byte (the
    /// historical behavior, and what source-preserving formatters
    /// want).
    pub number_display: Option<crate::DisplayContext>,
}

impl Default for FormatConfig {
    fn default() -> Self {
        Self {
            alignment: Alignment::default(),
            indent: "  ".to_string(),
            number_display: None,
        }
    }
}

impl FormatConfig {
    /// Create a config that aligns currencies to a fixed column
    /// (`bean-format`'s `-c` mode).
    #[must_use]
    pub fn with_column(column: usize) -> Self {
        Self {
            alignment: Alignment::CurrencyColumn(column),
            ..Self::default()
        }
    }

    /// Create a config with the specified indent width (auto alignment).
    #[must_use]
    pub fn with_indent(indent_width: usize) -> Self {
        Self {
            indent: " ".repeat(indent_width),
            ..Self::default()
        }
    }

    /// Create a config with a fixed currency column and indent width.
    #[must_use]
    pub fn new(column: usize, indent_width: usize) -> Self {
        Self {
            alignment: Alignment::CurrencyColumn(column),
            indent: " ".repeat(indent_width),
            ..Self::default()
        }
    }
}

/// Render a directive into format lines (the *render* phase).
///
/// Callers that need file-wide alignment collect these across the whole file
/// and align once with [`render_lines`]. Callers formatting a list of
/// directives without surrounding source can use [`format_directives`], which
/// aligns the whole list together.
#[must_use]
pub fn format_directive_lines(directive: &Directive, config: &FormatConfig) -> Vec<FormatLine> {
    match directive {
        Directive::Transaction(txn) => format_transaction_lines(txn, config),
        Directive::Balance(bal) => format_balance_lines(bal, config),
        Directive::Open(open) => format_open_lines(open, config),
        Directive::Close(close) => format_close_lines(close, config),
        Directive::Commodity(comm) => format_commodity_lines(comm, config),
        Directive::Pad(pad) => format_pad_lines(pad, config),
        Directive::Event(event) => format_event_lines(event, config),
        Directive::Query(query) => format_query_lines(query, config),
        Directive::Note(note) => format_note_lines(note, config),
        Directive::Document(doc) => format_document_lines(doc, config),
        Directive::Price(price) => format_price_lines(price, config),
        Directive::Custom(custom) => format_custom_lines(custom, config),
    }
}

/// Render one number for ledger text.
///
/// Through the config's [`crate::DisplayContext`] when present, or the
/// value's own scale otherwise. The single chokepoint every formatter
/// amount/cost/price number emission goes through — keep it that way
/// so the two behaviors cannot drift per call site (#1766).
///
/// Context semantics come from [`crate::DisplayContext::format_plain`]:
/// a TRACKED currency pads to the tracked precision (never rounding an
/// over-precise value away); an UNTRACKED currency stays byte-faithful
/// to its own scale; thousands separators are never emitted (canonical
/// ledger text carries none — `render_commas` stays a report/query
/// display concern).
#[must_use]
pub fn render_number(
    number: rust_decimal::Decimal,
    currency: &str,
    config: &FormatConfig,
) -> String {
    match &config.number_display {
        Some(ctx) => ctx.format_plain(number, currency),
        None => number.to_string(),
    }
}

/// Format a list of directives to a string, aligning all of them together
/// against shared, file-wide column widths in a single pass.
///
/// This is the canonical entry point for callers that have a list of
/// [`Directive`]s but no surrounding source text (e.g. synthesized output,
/// `extract`, plugin round-trips). Callers that also need to preserve
/// comments, blank lines, and non-directive elements from original source
/// should use `rustledger_parser::format::format_source` instead.
///
/// Passing a single directive (`[&directive]`) formats it on its own, which is
/// the natural degenerate case of whole-list alignment.
///
/// # Separator policy
///
/// **No blank line is inserted between adjacent directives** — `format_directives`
/// concatenates each rendered directive directly so it's safe to use as a
/// building block in larger compositions. Callers that need a blank line
/// between directives should drop down to [`format_directive_lines`] +
/// [`render_lines`] and push a `FormatLine::Plain(String::new())` between
/// each directive's lines (see `crates/rustledger/src/cmd/extract_cmd` for
/// an example).
///
/// Numbers render through [`render_number`] — the config's optional
/// display context applies per-currency precision padding (#1766).
/// an example).
#[must_use]
pub fn format_directives<'a, I>(directives: I, config: &FormatConfig) -> String
where
    I: IntoIterator<Item = &'a Directive>,
{
    let mut lines: Vec<FormatLine> = Vec::new();
    for directive in directives {
        lines.extend(format_directive_lines(directive, config));
    }
    render_lines(&lines, &config.alignment)
}

#[cfg(test)]
mod tests {
    use super::directives::{
        format_balance, format_close, format_commodity, format_custom, format_document,
        format_event, format_note, format_open, format_pad, format_price, format_query,
    };
    use super::transaction::{format_posting, format_transaction};
    use super::*;
    use crate::{
        Amount, Balance, Close, Commodity, CostSpec, Custom, Directive, Document, Event,
        IncompleteAmount, MetaValue, Metadata, NaiveDate, Note, Open, Pad, Posting, Price,
        PriceAnnotation, Query, Transaction,
    };
    use rust_decimal_macros::dec;

    fn date(year: i32, month: u32, day: u32) -> NaiveDate {
        crate::naive_date(year, month, day).unwrap()
    }

    #[test]
    fn test_format_simple_transaction() {
        let txn = Transaction::new(date(2024, 1, 15), "Morning coffee")
            .with_flag('*')
            .with_payee("Coffee Shop")
            .with_synthesized_posting(Posting::new(
                "Expenses:Food:Coffee",
                Amount::new(dec!(5.00), "USD"),
            ))
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-5.00), "USD")));

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
        // Auto alignment puts a two-space gap before the (self-aligned)
        // number — balances now align like postings.
        assert_eq!(formatted, "2024-01-01 balance Assets:Bank  1000.00 USD\n");
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
    fn test_escape_csv() {
        assert_eq!(escape_csv("plain"), "plain");
        assert_eq!(escape_csv("a,b"), "\"a,b\"");
        assert_eq!(escape_csv("say \"hi\""), "\"say \"\"hi\"\"\"");
        assert_eq!(escape_csv("line1\nline2"), "\"line1\nline2\"");
        assert_eq!(escape_csv(""), "");
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
        assert_eq!(
            format_meta_value(&val, &FormatConfig::default()),
            "\"hello world\""
        );
    }

    #[test]
    fn test_format_meta_value_string_with_quotes() {
        let val = MetaValue::String("say \"hello\"".to_string());
        assert_eq!(
            format_meta_value(&val, &FormatConfig::default()),
            "\"say \\\"hello\\\"\""
        );
    }

    #[test]
    fn test_format_meta_value_account() {
        let val = MetaValue::Account("Assets:Bank:Checking".into());
        assert_eq!(
            format_meta_value(&val, &FormatConfig::default()),
            "Assets:Bank:Checking"
        );
    }

    #[test]
    fn test_format_meta_value_currency() {
        let val = MetaValue::Currency("USD".into());
        assert_eq!(format_meta_value(&val, &FormatConfig::default()), "USD");
    }

    #[test]
    fn test_format_meta_value_tag() {
        let val = MetaValue::Tag("trip-2024".into());
        assert_eq!(
            format_meta_value(&val, &FormatConfig::default()),
            "#trip-2024"
        );
    }

    #[test]
    fn test_format_meta_value_link() {
        let val = MetaValue::Link("invoice-123".into());
        assert_eq!(
            format_meta_value(&val, &FormatConfig::default()),
            "^invoice-123"
        );
    }

    #[test]
    fn test_format_meta_value_date() {
        let val = MetaValue::Date(date(2024, 6, 15));
        assert_eq!(
            format_meta_value(&val, &FormatConfig::default()),
            "2024-06-15"
        );
    }

    #[test]
    fn test_format_meta_value_number() {
        let val = MetaValue::Number(dec!(123.456));
        assert_eq!(format_meta_value(&val, &FormatConfig::default()), "123.456");
    }

    #[test]
    fn test_format_meta_value_amount() {
        let val = MetaValue::Amount(Amount::new(dec!(99.99), "USD"));
        assert_eq!(
            format_meta_value(&val, &FormatConfig::default()),
            "99.99 USD"
        );
    }

    #[test]
    fn test_format_meta_value_bool_true() {
        let val = MetaValue::Bool(true);
        assert_eq!(format_meta_value(&val, &FormatConfig::default()), "TRUE");
    }

    #[test]
    fn test_format_meta_value_bool_false() {
        let val = MetaValue::Bool(false);
        assert_eq!(format_meta_value(&val, &FormatConfig::default()), "FALSE");
    }

    #[test]
    fn test_format_meta_value_none() {
        let val = MetaValue::None;
        assert_eq!(format_meta_value(&val, &FormatConfig::default()), "");
    }

    #[test]
    fn test_format_cost_spec_per_unit() {
        let spec = CostSpec {
            number: Some(crate::CostNumber::PerUnit {
                value: dec!(150.00),
            }),
            currency: Some("USD".into()),
            date: None,
            label: None,
            merge: false,
        };
        assert_eq!(
            format_cost_spec(&spec, &FormatConfig::default()),
            "{150.00 USD}"
        );
    }

    #[test]
    fn test_format_cost_spec_total() {
        let spec = CostSpec {
            number: Some(crate::CostNumber::Total {
                value: dec!(1500.00),
            }),
            currency: Some("USD".into()),
            date: None,
            label: None,
            merge: false,
        };
        assert_eq!(
            format_cost_spec(&spec, &FormatConfig::default()),
            "{{1500.00 USD}}"
        );
    }

    #[test]
    fn test_format_cost_spec_with_date() {
        let spec = CostSpec {
            number: Some(crate::CostNumber::PerUnit {
                value: dec!(150.00),
            }),
            currency: Some("USD".into()),
            date: Some(date(2024, 1, 15)),
            label: None,
            merge: false,
        };
        assert_eq!(
            format_cost_spec(&spec, &FormatConfig::default()),
            "{150.00 USD, 2024-01-15}"
        );
    }

    #[test]
    fn test_format_cost_spec_with_label() {
        let spec = CostSpec {
            number: Some(crate::CostNumber::PerUnit {
                value: dec!(150.00),
            }),
            currency: Some("USD".into()),
            date: None,
            label: Some("lot-a".to_string()),
            merge: false,
        };
        assert_eq!(
            format_cost_spec(&spec, &FormatConfig::default()),
            "{150.00 USD, \"lot-a\"}"
        );
    }

    #[test]
    fn test_format_cost_spec_with_merge() {
        let spec = CostSpec {
            number: Some(crate::CostNumber::PerUnit {
                value: dec!(150.00),
            }),
            currency: Some("USD".into()),
            date: None,
            label: None,
            merge: true,
        };
        assert_eq!(
            format_cost_spec(&spec, &FormatConfig::default()),
            "{150.00 USD, *}"
        );
    }

    #[test]
    fn test_format_cost_spec_all_fields() {
        let spec = CostSpec {
            number: Some(crate::CostNumber::PerUnit {
                value: dec!(150.00),
            }),
            currency: Some("USD".into()),
            date: Some(date(2024, 1, 15)),
            label: Some("lot-a".to_string()),
            merge: true,
        };
        assert_eq!(
            format_cost_spec(&spec, &FormatConfig::default()),
            "{150.00 USD, 2024-01-15, \"lot-a\", *}"
        );
    }

    #[test]
    fn test_format_cost_spec_empty() {
        let spec = CostSpec {
            number: None,
            currency: None,
            date: None,
            label: None,
            merge: false,
        };
        assert_eq!(format_cost_spec(&spec, &FormatConfig::default()), "{}");
    }

    #[test]
    fn test_format_price_annotation_unit() {
        let price = PriceAnnotation::unit(Amount::new(dec!(150.00), "USD"));
        assert_eq!(
            format_price_annotation(&price, &FormatConfig::default()),
            "@ 150.00 USD"
        );
    }

    #[test]
    fn test_format_price_annotation_total() {
        let price = PriceAnnotation::total(Amount::new(dec!(1500.00), "USD"));
        assert_eq!(
            format_price_annotation(&price, &FormatConfig::default()),
            "@@ 1500.00 USD"
        );
    }

    #[test]
    fn test_format_price_annotation_unit_incomplete() {
        let price = PriceAnnotation::unit_incomplete(IncompleteAmount::NumberOnly(dec!(150.00)));
        assert_eq!(
            format_price_annotation(&price, &FormatConfig::default()),
            "@ 150.00"
        );
    }

    #[test]
    fn test_format_price_annotation_total_incomplete() {
        let price = PriceAnnotation::total_incomplete(IncompleteAmount::CurrencyOnly("USD".into()));
        assert_eq!(
            format_price_annotation(&price, &FormatConfig::default()),
            "@@ USD"
        );
    }

    #[test]
    fn test_format_price_annotation_unit_empty() {
        let price = PriceAnnotation::unit_empty();
        assert_eq!(
            format_price_annotation(&price, &FormatConfig::default()),
            "@"
        );
    }

    #[test]
    fn test_format_price_annotation_total_empty() {
        let price = PriceAnnotation::total_empty();
        assert_eq!(
            format_price_annotation(&price, &FormatConfig::default()),
            "@@"
        );
    }

    #[test]
    fn test_format_incomplete_amount_complete() {
        let amount = IncompleteAmount::Complete(Amount::new(dec!(100.50), "EUR"));
        assert_eq!(
            format_incomplete_amount(&amount, &FormatConfig::default()),
            "100.50 EUR"
        );
    }

    #[test]
    fn test_format_incomplete_amount_number_only() {
        let amount = IncompleteAmount::NumberOnly(dec!(42.00));
        assert_eq!(
            format_incomplete_amount(&amount, &FormatConfig::default()),
            "42.00"
        );
    }

    #[test]
    fn test_format_incomplete_amount_currency_only() {
        let amount = IncompleteAmount::CurrencyOnly("BTC".into());
        assert_eq!(
            format_incomplete_amount(&amount, &FormatConfig::default()),
            "BTC"
        );
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
        assert_eq!(formatted, "2024-01-15 price AAPL  185.50 USD\n");
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

    /// Regression test for issue #573: custom directive values were not formatted
    /// <https://github.com/rustledger/rustledger/issues/573>
    #[test]
    fn test_issue_573_format_custom_with_values() {
        // Test case from issue: fava-option with multiple string values
        let custom = Custom {
            date: date(2024, 1, 1),
            custom_type: "fava-option".to_string(),
            values: vec![
                MetaValue::String("language".to_string()),
                MetaValue::String("en".to_string()),
            ],
            meta: Default::default(),
        };
        let config = FormatConfig::default();
        let formatted = format_custom(&custom, &config);
        assert_eq!(
            formatted,
            "2024-01-01 custom \"fava-option\" \"language\" \"en\"\n"
        );
    }

    #[test]
    fn test_format_custom_with_mixed_values() {
        // Test custom directive with various value types
        let custom = Custom {
            date: date(2024, 3, 15),
            custom_type: "budget".to_string(),
            values: vec![
                MetaValue::Account("Expenses:Food".into()),
                MetaValue::Amount(Amount::new(dec!(500), "USD")),
                MetaValue::String("monthly".to_string()),
            ],
            meta: Default::default(),
        };
        let config = FormatConfig::default();
        let formatted = format_custom(&custom, &config);
        assert_eq!(
            formatted,
            "2024-03-15 custom \"budget\" Expenses:Food 500 USD \"monthly\"\n"
        );
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
            "2024-01-01 balance Assets:Bank  1000.00 USD ~ 0.01\n"
        );
    }

    #[test]
    fn test_format_transaction_with_tags() {
        let txn = Transaction::new(date(2024, 1, 15), "Dinner")
            .with_flag('*')
            .with_tag("trip-2024")
            .with_tag("food")
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
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
            .with_synthesized_posting(Posting::new(
                "Income:Freelance",
                Amount::new(dec!(-1000.00), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
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

    /// The optional number-display context (#1766): fixed precision
    /// pads; thousands separators are NOT emitted in ledger text even
    /// when the context requests them (canonical form has none); and
    /// the default config stays byte-identical to the historical
    /// own-scale rendering.
    #[test]
    fn number_display_context_pads_without_separators() {
        use crate::DisplayContext;
        let mut ctx = DisplayContext::new();
        ctx.set_fixed_precision("USD", 2);
        ctx.set_render_commas(true);
        let config = FormatConfig {
            number_display: Some(ctx),
            ..FormatConfig::default()
        };

        assert_eq!(
            render_number(rust_decimal_macros::dec!(1234.5), "USD", &config),
            "1234.50",
            "fixed precision pads; separators stay a display concern"
        );
        assert_eq!(
            render_number(rust_decimal_macros::dec!(7), "JPY", &config),
            "7",
            "untracked currencies keep natural rendering"
        );
        assert_eq!(
            render_number(rust_decimal_macros::dec!(100.50), "EUR", &config),
            "100.50",
            "untracked currencies stay byte-faithful — no trailing-zero \
             stripping, which would widen a balance assertion's implicit \
             tolerance (deep review of #1807)"
        );
        assert_eq!(
            render_number(
                rust_decimal_macros::dec!(1234.5),
                "USD",
                &FormatConfig::default()
            ),
            "1234.5",
            "no context = historical own-scale rendering"
        );
    }

    /// The context threads through every directive number emission:
    /// balance, price, and posting units/cost/price annotations.
    #[test]
    fn number_display_context_threads_through_directives() {
        use crate::DisplayContext;
        let mut ctx = DisplayContext::new();
        ctx.set_fixed_precision("USD", 2);
        ctx.set_render_commas(true);
        let config = FormatConfig {
            number_display: Some(ctx),
            ..FormatConfig::default()
        };

        let bal = Balance::new(
            crate::naive_date(2024, 1, 15).unwrap(),
            "Assets:Bank",
            Amount::new(rust_decimal_macros::dec!(1234.5), "USD"),
        );
        let out = format_directives(std::iter::once(&Directive::Balance(bal)), &config);
        assert_eq!(
            out, "2024-01-15 balance Assets:Bank  1234.50 USD\n",
            "balance renders through the context (padded, no separators)"
        );
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
        assert!(matches!(config.alignment, Alignment::CurrencyColumn(80)));
        assert_eq!(config.indent, "  ");
    }

    #[test]
    fn test_format_config_with_indent() {
        let config = FormatConfig::with_indent(4);
        assert!(matches!(config.alignment, Alignment::Auto { .. }));
        assert_eq!(config.indent, "    ");
    }

    #[test]
    fn test_format_config_new() {
        let config = FormatConfig::new(70, 3);
        assert!(matches!(config.alignment, Alignment::CurrencyColumn(70)));
        assert_eq!(config.indent, "   ");
    }

    #[test]
    fn test_format_config_default_is_auto() {
        let config = FormatConfig::default();
        assert!(matches!(
            config.alignment,
            Alignment::Auto {
                prefix_width: None,
                num_width: None
            }
        ));
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
            cost: Some(Box::new(CostSpec {
                number: Some(crate::CostNumber::PerUnit {
                    value: dec!(150.00),
                }),
                currency: Some("USD".into()),
                date: Some(date(2024, 1, 15)),
                label: None,
                merge: false,
            })),
            price: Some(Box::new(PriceAnnotation::unit(Amount::new(
                dec!(155.00),
                "USD",
            )))),
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
    fn test_format_directives_all_types() {
        let config = FormatConfig::default();

        // Transaction
        let txn = Transaction::new(date(2024, 1, 1), "Test")
            .with_flag('*')
            .with_synthesized_posting(Posting::new("Expenses:Test", Amount::new(dec!(1), "USD")))
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-1), "USD")));
        let formatted = format_directives([&Directive::Transaction(txn)], &config);
        assert!(formatted.contains("2024-01-01"));

        // Balance
        let bal = Balance::new(
            date(2024, 1, 1),
            "Assets:Bank",
            Amount::new(dec!(100), "USD"),
        );
        let formatted = format_directives([&Directive::Balance(bal)], &config);
        assert!(formatted.contains("balance"));

        // Open
        let open = Open {
            date: date(2024, 1, 1),
            account: "Assets:Test".into(),
            currencies: vec![],
            booking: None,
            meta: Default::default(),
        };
        let formatted = format_directives([&Directive::Open(open)], &config);
        assert!(formatted.contains("open"));

        // Close
        let close = Close {
            date: date(2024, 1, 1),
            account: "Assets:Test".into(),
            meta: Default::default(),
        };
        let formatted = format_directives([&Directive::Close(close)], &config);
        assert!(formatted.contains("close"));

        // Commodity
        let comm = Commodity {
            date: date(2024, 1, 1),
            currency: "BTC".into(),
            meta: Default::default(),
        };
        let formatted = format_directives([&Directive::Commodity(comm)], &config);
        assert!(formatted.contains("commodity"));

        // Pad
        let pad = Pad {
            date: date(2024, 1, 1),
            account: "Assets:A".into(),
            source_account: "Equity:B".into(),
            meta: Default::default(),
        };
        let formatted = format_directives([&Directive::Pad(pad)], &config);
        assert!(formatted.contains("pad"));

        // Event
        let event = Event {
            date: date(2024, 1, 1),
            event_type: "test".to_string(),
            value: "value".to_string(),
            meta: Default::default(),
        };
        let formatted = format_directives([&Directive::Event(event)], &config);
        assert!(formatted.contains("event"));

        // Query
        let query = Query {
            date: date(2024, 1, 1),
            name: "test".to_string(),
            query: "SELECT *".to_string(),
            meta: Default::default(),
        };
        let formatted = format_directives([&Directive::Query(query)], &config);
        assert!(formatted.contains("query"));

        // Note
        let note = Note {
            date: date(2024, 1, 1),
            account: "Assets:Bank".into(),
            comment: "test".to_string(),
            meta: Default::default(),
        };
        let formatted = format_directives([&Directive::Note(note)], &config);
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
        let formatted = format_directives([&Directive::Document(doc)], &config);
        assert!(formatted.contains("document"));

        // Price
        let price = Price {
            date: date(2024, 1, 1),
            currency: "AAPL".into(),
            amount: Amount::new(dec!(150), "USD"),
            meta: Default::default(),
        };
        let formatted = format_directives([&Directive::Price(price)], &config);
        assert!(formatted.contains("price"));

        // Custom
        let custom = Custom {
            date: date(2024, 1, 1),
            custom_type: "test".to_string(),
            values: vec![],
            meta: Default::default(),
        };
        let formatted = format_directives([&Directive::Custom(custom)], &config);
        assert!(formatted.contains("custom"));
    }

    #[test]
    fn test_format_amount_negative() {
        let amount = Amount::new(dec!(-100.50), "USD");
        assert_eq!(
            format_amount_with(&amount, &FormatConfig::default()),
            "-100.50 USD"
        );
    }

    #[test]
    fn test_format_amount_zero() {
        let amount = Amount::new(dec!(0), "EUR");
        assert_eq!(
            format_amount_with(&amount, &FormatConfig::default()),
            "0 EUR"
        );
    }

    #[test]
    fn test_format_amount_large_number() {
        let amount = Amount::new(dec!(1234567890.12), "USD");
        assert_eq!(
            format_amount_with(&amount, &FormatConfig::default()),
            "1234567890.12 USD"
        );
    }

    #[test]
    fn test_format_amount_small_decimal() {
        let amount = Amount::new(dec!(0.00001), "BTC");
        assert_eq!(
            format_amount_with(&amount, &FormatConfig::default()),
            "0.00001 BTC"
        );
    }

    #[test]
    fn test_format_transaction_with_inline_comment() {
        let config = FormatConfig::default();

        // Create a posting with an inline comment
        let mut posting = Posting::new("Expenses:Food", Amount::new(dec!(50), "USD"));
        posting.comments = vec!["; This is an inline comment".to_string()];

        let txn = Transaction::new(date(2024, 1, 15), "Test transaction")
            .with_flag('*')
            .with_synthesized_posting(posting)
            .with_synthesized_posting(Posting::new("Assets:Bank", Amount::new(dec!(-50), "USD")));

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
            .with_synthesized_posting(posting1)
            .with_synthesized_posting(posting2);
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
            .with_synthesized_posting(posting)
            .with_synthesized_posting(Posting::auto("Assets:Bank"));

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

    #[test]
    fn test_format_posting_metadata_issue_701() {
        // Issue #701: posting-level metadata should not be lost on format
        let mut posting_meta = Metadata::default();
        posting_meta.insert(
            "note".to_string(),
            MetaValue::String("this note is lost".to_string()),
        );

        let mut posting = Posting::new("Expenses:Expense", Amount::new(dec!(10), "USD"));
        posting.meta = posting_meta;

        let txn = Transaction {
            date: date(2026, 4, 7),
            flag: '*',
            payee: None,
            narration: "my expense".into(),
            tags: vec![],
            links: vec![],
            postings: vec![
                crate::Spanned::synthesized(posting),
                crate::Spanned::synthesized(Posting::auto("Assets:Wallet")),
            ],
            meta: Metadata::default(),
            trailing_comments: Vec::new(),
        };

        let config = FormatConfig::default();
        let formatted = format_transaction(&txn, &config);

        assert!(
            formatted.contains("note: \"this note is lost\""),
            "posting metadata should be preserved in formatted output, got:\n{formatted}"
        );
        // Metadata should be indented deeper than the posting
        assert!(
            formatted.contains("    note:"),
            "posting metadata should have double indent (4 spaces), got:\n{formatted}"
        );
    }
}
