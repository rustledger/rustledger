//! Directive formatting for balance, open, close, etc.

use super::{FormatConfig, escape_string, format_amount, format_meta_value};
use crate::{
    Balance, Close, Commodity, Custom, Document, Event, Metadata, Note, Open, Pad, Price, Query,
};
use std::fmt::Write;

/// Format metadata entries in deterministic (sorted) order.
fn format_metadata(meta: &Metadata, meta_indent: &str, out: &mut String) {
    // Sort keys for deterministic output order
    let mut keys: Vec<_> = meta.keys().collect();
    keys.sort();

    for key in keys {
        let value = &meta[key];
        writeln!(out, "{meta_indent}{}: {}", key, format_meta_value(value)).unwrap();
    }
}

/// Format a balance directive.
pub fn format_balance(bal: &Balance, config: &FormatConfig) -> String {
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
    format_metadata(&bal.meta, &config.meta_indent, &mut out);
    out
}

/// Format an open directive.
pub fn format_open(open: &Open, config: &FormatConfig) -> String {
    let mut out = format!("{} open {}", open.date, open.account);
    if !open.currencies.is_empty() {
        write!(out, " {}", open.currencies.join(",")).unwrap();
    }
    if let Some(booking) = &open.booking {
        write!(out, " \"{booking}\"").unwrap();
    }
    out.push('\n');
    format_metadata(&open.meta, &config.meta_indent, &mut out);
    out
}

/// Format a close directive.
pub fn format_close(close: &Close, config: &FormatConfig) -> String {
    let mut out = format!("{} close {}\n", close.date, close.account);
    format_metadata(&close.meta, &config.meta_indent, &mut out);
    out
}

/// Format a commodity directive.
pub fn format_commodity(comm: &Commodity, config: &FormatConfig) -> String {
    let mut out = format!("{} commodity {}\n", comm.date, comm.currency);
    format_metadata(&comm.meta, &config.meta_indent, &mut out);
    out
}

/// Format a pad directive.
pub fn format_pad(pad: &Pad, config: &FormatConfig) -> String {
    let mut out = format!("{} pad {} {}\n", pad.date, pad.account, pad.source_account);
    format_metadata(&pad.meta, &config.meta_indent, &mut out);
    out
}

/// Format an event directive.
pub fn format_event(event: &Event, config: &FormatConfig) -> String {
    let mut out = format!(
        "{} event \"{}\" \"{}\"\n",
        event.date,
        escape_string(&event.event_type),
        escape_string(&event.value)
    );
    format_metadata(&event.meta, &config.meta_indent, &mut out);
    out
}

/// Format a query directive.
pub fn format_query(query: &Query, config: &FormatConfig) -> String {
    let mut out = format!(
        "{} query \"{}\" \"{}\"\n",
        query.date,
        escape_string(&query.name),
        escape_string(&query.query)
    );
    format_metadata(&query.meta, &config.meta_indent, &mut out);
    out
}

/// Format a note directive.
pub fn format_note(note: &Note, config: &FormatConfig) -> String {
    let mut out = format!(
        "{} note {} \"{}\"\n",
        note.date,
        note.account,
        escape_string(&note.comment)
    );
    format_metadata(&note.meta, &config.meta_indent, &mut out);
    out
}

/// Format a document directive.
pub fn format_document(doc: &Document, config: &FormatConfig) -> String {
    let mut out = format!(
        "{} document {} \"{}\"\n",
        doc.date,
        doc.account,
        escape_string(&doc.path)
    );
    format_metadata(&doc.meta, &config.meta_indent, &mut out);
    out
}

/// Format a price directive.
pub fn format_price(price: &Price, config: &FormatConfig) -> String {
    let mut out = format!(
        "{} price {} {}\n",
        price.date,
        price.currency,
        format_amount(&price.amount)
    );
    format_metadata(&price.meta, &config.meta_indent, &mut out);
    out
}

/// Format a custom directive.
pub fn format_custom(custom: &Custom, config: &FormatConfig) -> String {
    let mut out = format!(
        "{} custom \"{}\"\n",
        custom.date,
        escape_string(&custom.custom_type)
    );
    format_metadata(&custom.meta, &config.meta_indent, &mut out);
    out
}
