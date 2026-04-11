//! Transaction and posting formatting.

use super::directives::format_metadata;
use super::{FormatConfig, format_amount, format_cost_spec, format_price_annotation};
use crate::{Amount, CostSpec, IncompleteAmount, Posting, PriceAnnotation, Transaction};
use std::fmt::Write;

/// Format a transaction.
pub fn format_transaction(txn: &Transaction, config: &FormatConfig) -> String {
    // Estimate: date(10) + flag(2) + payee(50) + narration(100) + postings(200) ≈ 362 bytes
    let mut out = String::with_capacity(400);

    // Date and flag
    write!(out, "{} {}", txn.date, txn.flag).unwrap();

    // Payee and narration
    if let Some(payee) = &txn.payee {
        write!(out, " \"{}\"", super::escape_string(payee)).unwrap();
    }
    write!(out, " \"{}\"", super::escape_string(&txn.narration)).unwrap();

    // Tags
    for tag in &txn.tags {
        write!(out, " #{tag}").unwrap();
    }

    // Links
    for link in &txn.links {
        write!(out, " ^{link}").unwrap();
    }

    out.push('\n');

    // Transaction-level metadata (deterministic sorted order)
    format_metadata(&txn.meta, &config.indent, &mut out);

    // Double indent for posting-level metadata
    let meta_indent = format!("{}{}", &config.indent, &config.indent);

    // Postings
    for posting in &txn.postings {
        // Output comments that appear before this posting
        for comment in &posting.comments {
            writeln!(out, "{}{}", &config.indent, comment).unwrap();
        }
        // Output the posting line
        let posting_line = format_posting(posting, config);
        // Append trailing comment on same line if present (only first one)
        if let Some(trailing) = posting.trailing_comments.first() {
            writeln!(out, "{posting_line} {trailing}").unwrap();
        } else {
            out.push_str(&posting_line);
            out.push('\n');
        }
        // Output any additional trailing comments on their own lines
        for trailing in posting.trailing_comments.iter().skip(1) {
            writeln!(out, "{}{}", &config.indent, trailing).unwrap();
        }
        // Posting-level metadata (indented one level deeper than the posting)
        if !posting.meta.is_empty() {
            format_metadata(&posting.meta, &meta_indent, &mut out);
        }
    }

    // Output transaction trailing comments (comments after all postings)
    for comment in &txn.trailing_comments {
        writeln!(out, "{}{}", &config.indent, comment).unwrap();
    }

    out
}

/// Format a posting with amount alignment.
pub fn format_posting(posting: &Posting, config: &FormatConfig) -> String {
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
pub fn format_incomplete_amount(amount: &IncompleteAmount) -> String {
    match amount {
        IncompleteAmount::Complete(a) => format!("{} {}", a.number, a.currency),
        IncompleteAmount::NumberOnly(n) => n.to_string(),
        IncompleteAmount::CurrencyOnly(c) => c.to_string(),
    }
}

/// Format the amount part of a posting with incomplete amount support.
pub fn format_posting_incomplete_amount(
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
pub fn format_posting_amount(
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
