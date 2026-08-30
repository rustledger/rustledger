//! Directive formatting for balance, open, close, etc.
//!
//! Each directive has a `format_X_lines` function that renders it into a
//! [`FormatLine`] sequence (the *render* phase) and a thin `format_X`
//! wrapper that aligns that sequence on its own (the *align* phase, scoped
//! to a single directive). The file-wide formatter calls the `_lines`
//! variants and aligns the whole file at once; single-directive callers
//! (and the unit tests) use the `String` wrappers.

use super::align::FormatLine;
#[cfg(test)]
use super::align::render_lines;
use super::{FormatConfig, escape_string, format_meta_value};
use crate::{
    Amount, Balance, Close, Commodity, Custom, Document, Event, Metadata, Note, Open, Pad, Price,
    Query,
};
use std::fmt::Write;

/// Append metadata entries (deterministic sorted order) as `Plain` lines.
pub(super) fn metadata_lines(
    meta: &Metadata,
    indent: &str,
    config: &FormatConfig,
    out: &mut Vec<FormatLine>,
) {
    let mut keys: Vec<_> = meta.keys().collect();
    keys.sort();
    for key in keys {
        out.push(FormatLine::Plain(format!(
            "{indent}{}: {}",
            key,
            format_meta_value(&meta[key], config)
        )));
    }
}

/// Split an [`Amount`] into its number token and currency, so the aligner
/// can move the number independently (matching `bean-format`, which aligns
/// the bare number and treats the currency as part of the suffix).
fn amount_split(amount: &Amount, config: &FormatConfig) -> (String, String) {
    (
        super::render_number(amount.number, amount.currency.as_str(), config),
        amount.currency.to_string(),
    )
}

/// Render a balance directive into format lines.
pub fn format_balance_lines(bal: &Balance, config: &FormatConfig) -> Vec<FormatLine> {
    let (number, mut suffix) = amount_split(&bal.amount, config);
    if let Some(tol) = &bal.tolerance {
        // The tolerance shares the amount's currency and its display
        // precision — mixed precision on one line reads as a typo
        // (deep review of #1807).
        write!(
            suffix,
            " ~ {}",
            super::render_number(*tol, bal.amount.currency.as_str(), config)
        )
        .expect("write to String is infallible");
    }
    let mut lines = vec![FormatLine::Aligned {
        prefix: format!("{} balance {}", bal.date, bal.account),
        number,
        suffix,
    }];
    metadata_lines(&bal.meta, &config.indent, config, &mut lines);
    lines
}

/// Render a price directive into format lines.
pub fn format_price_lines(price: &Price, config: &FormatConfig) -> Vec<FormatLine> {
    let (number, suffix) = amount_split(&price.amount, config);
    let mut lines = vec![FormatLine::Aligned {
        prefix: format!("{} price {}", price.date, price.currency),
        number,
        suffix,
    }];
    metadata_lines(&price.meta, &config.indent, config, &mut lines);
    lines
}

/// Render an open directive into format lines.
pub fn format_open_lines(open: &Open, config: &FormatConfig) -> Vec<FormatLine> {
    let mut header = format!("{} open {}", open.date, open.account);
    if !open.currencies.is_empty() {
        write!(header, " {}", open.currencies.join(",")).expect("write to String is infallible");
    }
    if let Some(booking) = &open.booking {
        write!(header, " \"{booking}\"").expect("write to String is infallible");
    }
    let mut lines = vec![FormatLine::Plain(header)];
    metadata_lines(&open.meta, &config.indent, config, &mut lines);
    lines
}

/// Render a close directive into format lines.
pub fn format_close_lines(close: &Close, config: &FormatConfig) -> Vec<FormatLine> {
    let mut lines = vec![FormatLine::Plain(format!(
        "{} close {}",
        close.date, close.account
    ))];
    metadata_lines(&close.meta, &config.indent, config, &mut lines);
    lines
}

/// Render a commodity directive into format lines.
pub fn format_commodity_lines(comm: &Commodity, config: &FormatConfig) -> Vec<FormatLine> {
    let mut lines = vec![FormatLine::Plain(format!(
        "{} commodity {}",
        comm.date, comm.currency
    ))];
    metadata_lines(&comm.meta, &config.indent, config, &mut lines);
    lines
}

/// Render a pad directive into format lines.
pub fn format_pad_lines(pad: &Pad, config: &FormatConfig) -> Vec<FormatLine> {
    let mut lines = vec![FormatLine::Plain(format!(
        "{} pad {} {}",
        pad.date, pad.account, pad.source_account
    ))];
    metadata_lines(&pad.meta, &config.indent, config, &mut lines);
    lines
}

/// Render an event directive into format lines.
pub fn format_event_lines(event: &Event, config: &FormatConfig) -> Vec<FormatLine> {
    let mut lines = vec![FormatLine::Plain(format!(
        "{} event \"{}\" \"{}\"",
        event.date,
        escape_string(&event.event_type),
        escape_string(&event.value)
    ))];
    metadata_lines(&event.meta, &config.indent, config, &mut lines);
    lines
}

/// Render a query directive into format lines.
pub fn format_query_lines(query: &Query, config: &FormatConfig) -> Vec<FormatLine> {
    let mut lines = vec![FormatLine::Plain(format!(
        "{} query \"{}\" \"{}\"",
        query.date,
        escape_string(&query.name),
        escape_string(&query.query)
    ))];
    metadata_lines(&query.meta, &config.indent, config, &mut lines);
    lines
}

/// Append a header's `#tag` / `^link` list, in the order the transaction
/// emitter uses.
///
/// `note` and `document` take these exactly as a transaction does. Both
/// emitters here omitted them, so any consumer of the typed-directive
/// emitter -- `rledger add`, `rledger extract`, the FFI `format.entry`
/// endpoints, all of which reach it through
/// `rustledger_parser::format::canonicalize_directives` -- deleted them
/// from the text it produced (#2184).
fn write_tags_and_links(header: &mut String, tags: &[crate::Tag], links: &[crate::Link]) {
    for tag in tags {
        write!(header, " #{tag}").expect("write to String is infallible");
    }
    for link in links {
        write!(header, " ^{link}").expect("write to String is infallible");
    }
}

/// Render a note directive into format lines.
pub fn format_note_lines(note: &Note, config: &FormatConfig) -> Vec<FormatLine> {
    let mut header = format!(
        "{} note {} \"{}\"",
        note.date,
        note.account,
        escape_string(&note.comment)
    );
    write_tags_and_links(&mut header, &note.tags, &note.links);
    let mut lines = vec![FormatLine::Plain(header)];
    metadata_lines(&note.meta, &config.indent, config, &mut lines);
    lines
}

/// Render a document directive into format lines.
pub fn format_document_lines(doc: &Document, config: &FormatConfig) -> Vec<FormatLine> {
    let mut header = format!(
        "{} document {} \"{}\"",
        doc.date,
        doc.account,
        escape_string(&doc.path)
    );
    write_tags_and_links(&mut header, &doc.tags, &doc.links);
    let mut lines = vec![FormatLine::Plain(header)];
    metadata_lines(&doc.meta, &config.indent, config, &mut lines);
    lines
}

/// Render a custom directive into format lines.
pub fn format_custom_lines(custom: &Custom, config: &FormatConfig) -> Vec<FormatLine> {
    let mut header = format!(
        "{} custom \"{}\"",
        custom.date,
        escape_string(&custom.custom_type)
    );
    for value in &custom.values {
        write!(header, " {}", format_meta_value(value, config))
            .expect("write to String is infallible");
    }
    let mut lines = vec![FormatLine::Plain(header)];
    metadata_lines(&custom.meta, &config.indent, config, &mut lines);
    lines
}

/// Thin `String` wrappers used by the unit tests to format one directive
/// in isolation (self-aligned). Production code formats whole files via
/// [`super::format_directive_lines`] + [`render_lines`], so these are
/// gated to test builds to avoid dead-code warnings.
macro_rules! string_wrapper {
    ($(#[$m:meta])* $name:ident, $lines:ident, $ty:ty) => {
        #[cfg(test)]
        $(#[$m])*
        pub(super) fn $name(value: &$ty, config: &FormatConfig) -> String {
            render_lines(&$lines(value, config), &config.alignment)
        }
    };
}

string_wrapper!(
    /// Format a balance directive to a string (self-aligned).
    format_balance, format_balance_lines, Balance);
string_wrapper!(
    /// Format a price directive to a string (self-aligned).
    format_price, format_price_lines, Price);
string_wrapper!(
    /// Format an open directive to a string.
    format_open, format_open_lines, Open);
string_wrapper!(
    /// Format a close directive to a string.
    format_close, format_close_lines, Close);
string_wrapper!(
    /// Format a commodity directive to a string.
    format_commodity, format_commodity_lines, Commodity);
string_wrapper!(
    /// Format a pad directive to a string.
    format_pad, format_pad_lines, Pad);
string_wrapper!(
    /// Format an event directive to a string.
    format_event, format_event_lines, Event);
string_wrapper!(
    /// Format a query directive to a string.
    format_query, format_query_lines, Query);
string_wrapper!(
    /// Format a note directive to a string.
    format_note, format_note_lines, Note);
string_wrapper!(
    /// Format a document directive to a string.
    format_document, format_document_lines, Document);
string_wrapper!(
    /// Format a custom directive to a string.
    format_custom, format_custom_lines, Custom);
