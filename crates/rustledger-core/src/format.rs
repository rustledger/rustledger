//! Beancount file formatter.
//!
//! Provides pretty-printing for beancount directives with configurable
//! amount alignment.

use crate::{
    Amount, Balance, Close, Commodity, CostSpec, Custom, Directive, Document, Event,
    IncompleteAmount, MetaValue, Note, Open, Pad, Posting, Price, PriceAnnotation, Query,
    Transaction,
};
use std::fmt::Write;

/// Formatter configuration.
#[derive(Debug, Clone)]
pub struct FormatConfig {
    /// Column to align amounts to (default: 60).
    pub amount_column: usize,
    /// Indentation for postings.
    pub indent: String,
    /// Indentation for metadata.
    pub meta_indent: String,
}

impl Default for FormatConfig {
    fn default() -> Self {
        Self {
            amount_column: 60,
            indent: "  ".to_string(),
            meta_indent: "    ".to_string(),
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
        let meta_indent = " ".repeat(indent_width * 2);
        Self {
            indent,
            meta_indent,
            ..Default::default()
        }
    }

    /// Create a new config with both column and indent settings.
    #[must_use]
    pub fn new(column: usize, indent_width: usize) -> Self {
        let indent = " ".repeat(indent_width);
        let meta_indent = " ".repeat(indent_width * 2);
        Self {
            amount_column: column,
            indent,
            meta_indent,
        }
    }
}

/// Format a directive to a string.
pub fn format_directive(directive: &Directive, config: &FormatConfig) -> String {
    match directive {
        Directive::Transaction(txn) => format_transaction(txn, config),
        Directive::Balance(bal) => format_balance(bal),
        Directive::Open(open) => format_open(open),
        Directive::Close(close) => format_close(close),
        Directive::Commodity(comm) => format_commodity(comm),
        Directive::Pad(pad) => format_pad(pad),
        Directive::Event(event) => format_event(event),
        Directive::Query(query) => format_query(query),
        Directive::Note(note) => format_note(note),
        Directive::Document(doc) => format_document(doc),
        Directive::Price(price) => format_price(price),
        Directive::Custom(custom) => format_custom(custom),
    }
}

/// Format a transaction.
fn format_transaction(txn: &Transaction, config: &FormatConfig) -> String {
    let mut out = String::new();

    // Date and flag
    write!(out, "{} {}", txn.date, txn.flag).unwrap();

    // Payee and narration
    if let Some(payee) = &txn.payee {
        write!(out, " \"{}\"", escape_string(payee)).unwrap();
    }
    write!(out, " \"{}\"", escape_string(&txn.narration)).unwrap();

    // Tags
    for tag in &txn.tags {
        write!(out, " #{tag}").unwrap();
    }

    // Links
    for link in &txn.links {
        write!(out, " ^{link}").unwrap();
    }

    out.push('\n');

    // Transaction-level metadata
    for (key, value) in &txn.meta {
        writeln!(
            out,
            "{}{}: {}",
            &config.indent,
            key,
            format_meta_value(value)
        )
        .unwrap();
    }

    // Postings
    for posting in &txn.postings {
        out.push_str(&format_posting(posting, config));
        out.push('\n');
    }

    out
}

/// Format a posting with amount alignment.
fn format_posting(posting: &Posting, config: &FormatConfig) -> String {
    let mut line = String::new();
    line.push_str(&config.indent);

    // Flag (if present)
    if let Some(flag) = posting.flag {
        write!(line, "{flag} ").unwrap();
    }

    // Account
    line.push_str(&posting.account);

    // Units, cost, price
    if let Some(incomplete_amount) = &posting.units {
        // Calculate padding to align amount
        let current_len = line.len();
        let amount_str = format_incomplete_amount(incomplete_amount);
        let amount_with_extras =
            format_posting_incomplete_amount(incomplete_amount, &posting.cost, &posting.price);

        // Pad to align the number at the configured column
        let target_col = config.amount_column.saturating_sub(amount_str.len());
        if current_len < target_col {
            let padding = target_col - current_len;
            for _ in 0..padding {
                line.push(' ');
            }
        } else {
            line.push_str("  "); // Minimum 2 spaces
        }

        line.push_str(&amount_with_extras);
    }

    line
}

/// Format an incomplete amount.
fn format_incomplete_amount(amount: &IncompleteAmount) -> String {
    match amount {
        IncompleteAmount::Complete(a) => format!("{} {}", a.number, a.currency),
        IncompleteAmount::NumberOnly(n) => n.to_string(),
        IncompleteAmount::CurrencyOnly(c) => c.clone(),
    }
}

/// Format the amount part of a posting with incomplete amount support.
fn format_posting_incomplete_amount(
    units: &IncompleteAmount,
    cost: &Option<CostSpec>,
    price: &Option<PriceAnnotation>,
) -> String {
    let mut out = format_incomplete_amount(units);

    // Cost spec
    if let Some(cost_spec) = cost {
        out.push(' ');
        out.push_str(&format_cost_spec(cost_spec));
    }

    // Price annotation
    if let Some(price_ann) = price {
        out.push(' ');
        out.push_str(&format_price_annotation(price_ann));
    }

    out
}

/// Format the amount part of a posting (units + cost + price).
#[allow(dead_code)]
fn format_posting_amount(
    units: &Amount,
    cost: &Option<CostSpec>,
    price: &Option<PriceAnnotation>,
) -> String {
    let mut out = format_amount(units);

    // Cost spec
    if let Some(cost_spec) = cost {
        out.push(' ');
        out.push_str(&format_cost_spec(cost_spec));
    }

    // Price annotation
    if let Some(price_ann) = price {
        out.push(' ');
        out.push_str(&format_price_annotation(price_ann));
    }

    out
}

/// Format an amount.
fn format_amount(amount: &Amount) -> String {
    format!("{} {}", amount.number, amount.currency)
}

/// Format a cost specification.
fn format_cost_spec(spec: &CostSpec) -> String {
    let mut parts = Vec::new();

    // Amount (per-unit or total)
    if let (Some(num), Some(curr)) = (&spec.number_per, &spec.currency) {
        parts.push(format!("{num} {curr}"));
    } else if let (Some(num), Some(curr)) = (&spec.number_total, &spec.currency) {
        // Total cost uses double braces
        return format!("{{{{{num} {curr}}}}}");
    }

    // Date
    if let Some(date) = spec.date {
        parts.push(date.to_string());
    }

    // Label
    if let Some(label) = &spec.label {
        parts.push(format!("\"{}\"", escape_string(label)));
    }

    // Merge marker
    if spec.merge {
        parts.push("*".to_string());
    }

    format!("{{{}}}", parts.join(", "))
}

/// Format a price annotation.
fn format_price_annotation(price: &PriceAnnotation) -> String {
    match price {
        PriceAnnotation::Unit(amount) => format!("@ {}", format_amount(amount)),
        PriceAnnotation::Total(amount) => format!("@@ {}", format_amount(amount)),
        PriceAnnotation::UnitIncomplete(inc) => format!("@ {}", format_incomplete_amount(inc)),
        PriceAnnotation::TotalIncomplete(inc) => format!("@@ {}", format_incomplete_amount(inc)),
        PriceAnnotation::UnitEmpty => "@".to_string(),
        PriceAnnotation::TotalEmpty => "@@".to_string(),
    }
}

/// Format a metadata value.
fn format_meta_value(value: &MetaValue) -> String {
    match value {
        MetaValue::String(s) => format!("\"{}\"", escape_string(s)),
        MetaValue::Account(a) => a.clone(),
        MetaValue::Currency(c) => c.clone(),
        MetaValue::Tag(t) => format!("#{t}"),
        MetaValue::Link(l) => format!("^{l}"),
        MetaValue::Date(d) => d.to_string(),
        MetaValue::Number(n) => n.to_string(),
        MetaValue::Amount(a) => format_amount(a),
        MetaValue::Bool(b) => if *b { "TRUE" } else { "FALSE" }.to_string(),
        MetaValue::None => String::new(),
    }
}

/// Format a balance directive.
fn format_balance(bal: &Balance) -> String {
    let mut out = format!(
        "{} balance {} {}",
        bal.date,
        bal.account,
        format_amount(&bal.amount)
    );
    if let Some(tol) = &bal.tolerance {
        write!(out, " ~ {tol}").unwrap();
    }
    out.push('\n');
    out
}

/// Format an open directive.
fn format_open(open: &Open) -> String {
    let mut out = format!("{} open {}", open.date, open.account);
    if !open.currencies.is_empty() {
        write!(out, " {}", open.currencies.join(",")).unwrap();
    }
    if let Some(booking) = &open.booking {
        write!(out, " \"{booking}\"").unwrap();
    }
    out.push('\n');
    out
}

/// Format a close directive.
fn format_close(close: &Close) -> String {
    format!("{} close {}\n", close.date, close.account)
}

/// Format a commodity directive.
fn format_commodity(comm: &Commodity) -> String {
    format!("{} commodity {}\n", comm.date, comm.currency)
}

/// Format a pad directive.
fn format_pad(pad: &Pad) -> String {
    format!("{} pad {} {}\n", pad.date, pad.account, pad.source_account)
}

/// Format an event directive.
fn format_event(event: &Event) -> String {
    format!(
        "{} event \"{}\" \"{}\"\n",
        event.date,
        escape_string(&event.event_type),
        escape_string(&event.value)
    )
}

/// Format a query directive.
fn format_query(query: &Query) -> String {
    format!(
        "{} query \"{}\" \"{}\"\n",
        query.date,
        escape_string(&query.name),
        escape_string(&query.query)
    )
}

/// Format a note directive.
fn format_note(note: &Note) -> String {
    format!(
        "{} note {} \"{}\"\n",
        note.date,
        note.account,
        escape_string(&note.comment)
    )
}

/// Format a document directive.
fn format_document(doc: &Document) -> String {
    format!(
        "{} document {} \"{}\"\n",
        doc.date,
        doc.account,
        escape_string(&doc.path)
    )
}

/// Format a price directive.
fn format_price(price: &Price) -> String {
    format!(
        "{} price {} {}\n",
        price.date,
        price.currency,
        format_amount(&price.amount)
    )
}

/// Format a custom directive.
fn format_custom(custom: &Custom) -> String {
    format!(
        "{} custom \"{}\"\n",
        custom.date,
        escape_string(&custom.custom_type)
    )
}

/// Escape a string for output (handle quotes and backslashes).
fn escape_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            _ => out.push(c),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;
    use crate::NaiveDate;

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
        let formatted = format_balance(&bal);
        assert_eq!(formatted, "2024-01-01 balance Assets:Bank 1000.00 USD\n");
    }

    #[test]
    fn test_format_open() {
        let open = Open {
            date: date(2024, 1, 1),
            account: "Assets:Bank:Checking".to_string(),
            currencies: vec!["USD".to_string(), "EUR".to_string()],
            booking: None,
            meta: Default::default(),
        };
        let formatted = format_open(&open);
        assert_eq!(formatted, "2024-01-01 open Assets:Bank:Checking USD,EUR\n");
    }

    #[test]
    fn test_escape_string() {
        assert_eq!(escape_string("hello"), "hello");
        assert_eq!(escape_string("say \"hi\""), "say \\\"hi\\\"");
        assert_eq!(escape_string("line1\nline2"), "line1\\nline2");
    }
}
