//! Transaction and posting formatting.

use super::align::{FormatLine, render_lines};
use super::directives::metadata_lines;
use super::{FormatConfig, format_cost_spec, format_price_annotation};
use crate::{IncompleteAmount, Posting, Transaction};
use std::fmt::Write;

/// Render a transaction into format lines.
///
/// The header, metadata, comments, and amount-free posting lines are
/// `Plain`; posting lines that carry a number are `Aligned` so the
/// file-wide aligner can line up the numbers across the whole file.
pub fn format_transaction_lines(txn: &Transaction, config: &FormatConfig) -> Vec<FormatLine> {
    let mut lines = Vec::new();

    // Header: date, flag, payee, narration, tags, links.
    let mut header = format!("{} {}", txn.date, txn.flag);
    if let Some(payee) = &txn.payee {
        write!(header, " \"{}\"", super::escape_string(payee))
            .expect("write to String is infallible");
    }
    write!(header, " \"{}\"", super::escape_string(&txn.narration))
        .expect("write to String is infallible");
    for tag in &txn.tags {
        write!(header, " #{tag}").expect("write to String is infallible");
    }
    for link in &txn.links {
        write!(header, " ^{link}").expect("write to String is infallible");
    }
    lines.push(FormatLine::Plain(header));

    // Transaction-level metadata (deterministic sorted order).
    metadata_lines(&txn.meta, &config.indent, &mut lines);

    // Posting-level metadata is indented one level deeper than the posting.
    let meta_indent = format!("{}{}", &config.indent, &config.indent);

    for posting in &txn.postings {
        // Comments that appear before this posting.
        for comment in &posting.comments {
            lines.push(FormatLine::Plain(format!("{}{}", &config.indent, comment)));
        }
        // The posting line itself (account + amount + first trailing comment).
        lines.push(posting_format_line(posting, config));
        // Any additional trailing comments on their own lines.
        for trailing in posting.trailing_comments.iter().skip(1) {
            lines.push(FormatLine::Plain(format!("{}{}", &config.indent, trailing)));
        }
        // Posting-level metadata.
        if !posting.meta.is_empty() {
            metadata_lines(&posting.meta, &meta_indent, &mut lines);
        }
    }

    // Transaction trailing comments (after all postings).
    for comment in &txn.trailing_comments {
        lines.push(FormatLine::Plain(format!("{}{}", &config.indent, comment)));
    }

    lines
}

/// Format a transaction to a string (self-aligned). Test-only convenience;
/// production code aligns whole files via [`format_transaction_lines`].
#[cfg(test)]
pub(super) fn format_transaction(txn: &Transaction, config: &FormatConfig) -> String {
    render_lines(&format_transaction_lines(txn, config), &config.alignment)
}

/// Build the indented account prefix for a posting (indent + optional
/// flag + account name), with no trailing whitespace.
fn posting_prefix(posting: &Posting, config: &FormatConfig) -> String {
    let mut prefix = String::new();
    prefix.push_str(&config.indent);
    if let Some(flag) = posting.flag {
        write!(prefix, "{flag} ").expect("write to String is infallible");
    }
    prefix.push_str(&posting.account);
    prefix
}

/// Split a posting's amount into the alignable number token and the
/// "rest" (currency, cost, price). Returns `None` for the number when the
/// posting has no number to align (currency-only or amount-free postings),
/// in which case the `rest` still holds any currency/cost/price text.
fn posting_amount_split(posting: &Posting) -> (Option<String>, String) {
    let (number, mut rest) = match &posting.units {
        None => (None, String::new()),
        Some(IncompleteAmount::Complete(amount)) => {
            (Some(amount.number.to_string()), amount.currency.to_string())
        }
        Some(IncompleteAmount::NumberOnly(n)) => (Some(n.to_string()), String::new()),
        Some(IncompleteAmount::CurrencyOnly(c)) => (None, c.to_string()),
    };

    if let Some(cost) = &posting.cost {
        if !rest.is_empty() {
            rest.push(' ');
        }
        rest.push_str(&format_cost_spec(cost));
    }
    if let Some(price) = &posting.price {
        if !rest.is_empty() {
            rest.push(' ');
        }
        rest.push_str(&format_price_annotation(price));
    }
    (number, rest)
}

/// Build the [`FormatLine`] for a single posting line.
///
/// This is the unit both the on-disk formatter (`format_transaction`) and
/// the LSP per-line formatter emit, so they stay in lockstep. The first
/// same-line trailing comment is included; subsequent trailing comments,
/// pre-line comments, and posting metadata live on their own lines and are
/// emitted by `format_transaction_lines`.
#[must_use]
pub fn posting_format_line(posting: &Posting, config: &FormatConfig) -> FormatLine {
    build_posting_line(posting, config, true)
}

/// Build a posting line, optionally including the first same-line trailing
/// comment. `include_trailing_comment` is `false` for [`format_posting`],
/// which historically emits only the account + amount.
fn build_posting_line(
    posting: &Posting,
    config: &FormatConfig,
    include_trailing_comment: bool,
) -> FormatLine {
    let prefix = posting_prefix(posting, config);
    let (number, rest) = posting_amount_split(posting);
    let comment = if include_trailing_comment {
        posting.trailing_comments.first()
    } else {
        None
    };

    if let Some(number) = number {
        let mut suffix = rest;
        if let Some(c) = comment {
            if !suffix.is_empty() {
                suffix.push(' ');
            }
            suffix.push_str(c);
        }
        FormatLine::Aligned {
            prefix,
            number,
            suffix,
        }
    } else {
        // No number to align — emit verbatim. A currency-only amount
        // keeps a two-space gap from the account (beancount leaves
        // such lines untouched; we still canonicalize the gap).
        let mut line = prefix;
        if !rest.is_empty() {
            line.push_str("  ");
            line.push_str(&rest);
        }
        if let Some(c) = comment {
            line.push(' ');
            line.push_str(c);
        }
        FormatLine::Plain(line)
    }
}

/// Format the single-line representation of a posting, including the first
/// same-line trailing comment.
///
/// **Self-aligned against `config` only.** This function picks column widths
/// from the single posting it's given — it has no view of the surrounding
/// document. The result is therefore NOT guaranteed to align with the same
/// posting as rendered by [`super::format_directives`] or
/// `rustledger_parser::format::format_source`, both of which resolve widths across
/// every amount-bearing line in the file.
///
/// Use this only when you genuinely want a self-aligned single-posting
/// render (e.g., a hover preview or a doctest fixture). For "format this
/// posting like the CLI would" use the whole-file path
/// `format_directives([&Directive::Transaction(t)], cfg)` or
/// `rustledger_parser::format::format_source`.
#[must_use]
pub fn format_posting_line(posting: &Posting, config: &FormatConfig) -> String {
    render_lines(
        &[build_posting_line(posting, config, true)],
        &config.alignment,
    )
    .trim_end_matches('\n')
    .to_string()
}

/// Format a posting with amount alignment, without any trailing comment.
/// Test-only convenience.
#[cfg(test)]
pub(super) fn format_posting(posting: &Posting, config: &FormatConfig) -> String {
    render_lines(
        &[build_posting_line(posting, config, false)],
        &config.alignment,
    )
    .trim_end_matches('\n')
    .to_string()
}

/// Format an incomplete amount.
pub fn format_incomplete_amount(amount: &IncompleteAmount) -> String {
    match amount {
        IncompleteAmount::Complete(a) => format!("{} {}", a.number, a.currency),
        IncompleteAmount::NumberOnly(n) => n.to_string(),
        IncompleteAmount::CurrencyOnly(c) => c.to_string(),
    }
}
