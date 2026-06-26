//! Date, amount, and balance parsing for the add command.

use anyhow::{Context, Result, bail};
use rustledger_core::Decimal;
use rustledger_core::{Amount, NaiveDate};
use std::str::FromStr;

/// Parse a flexible date string.
///
/// Supports:
/// - "today" or empty → current date
/// - "yesterday" → previous day
/// - "+N" / "-N" → relative days from today
/// - "YYYY-MM-DD" → explicit date
pub fn parse_date(input: &str) -> Result<NaiveDate> {
    let trimmed = input.trim().to_lowercase();
    let today = jiff::Zoned::now().date();

    if trimmed.is_empty() || trimmed == "today" {
        return Ok(today);
    }

    if trimmed == "yesterday" {
        return today
            .yesterday()
            .ok()
            .context("Cannot compute yesterday's date");
    }

    // Relative days: +N or -N
    if let Some(stripped) = trimmed.strip_prefix('+') {
        let days: i64 = stripped
            .parse()
            .with_context(|| format!("Invalid relative date: {input}"))?;
        return today
            .checked_add(jiff::ToSpan::days(days))
            .ok()
            .context("Date out of range");
    }

    if let Some(stripped) = trimmed.strip_prefix('-') {
        let days: i64 = stripped
            .parse()
            .with_context(|| format!("Invalid relative date: {input}"))?;
        return today
            .checked_add(jiff::ToSpan::days(-(days)))
            .ok()
            .context("Date out of range");
    }

    // Explicit date: YYYY-MM-DD
    trimmed
        .parse::<NaiveDate>()
        .with_context(|| format!("Invalid date format: {input}. Use YYYY-MM-DD."))
}

/// Check if a character is valid in a beancount currency.
const fn is_currency_char(c: char) -> bool {
    c.is_ascii_uppercase() || c.is_ascii_digit() || matches!(c, '\'' | '.' | '_' | '-')
}

/// Parse an amount string like "123.45 USD" or "123.45USD" or "10 BRK.B".
pub fn parse_amount(input: &str) -> Result<Amount> {
    let trimmed = input.trim();

    // First try splitting by whitespace (most common case)
    let parts: Vec<&str> = trimmed.split_whitespace().collect();
    if parts.len() == 2 {
        let number = Decimal::from_str(parts[0])
            .with_context(|| format!("Invalid number in amount: {}", parts[0]))?;
        return Ok(Amount::new(number, parts[1]));
    }

    // Handle no-space format like "123.45USD" or "10BRK.B"
    let mut split_pos = trimmed.len();
    let chars: Vec<char> = trimmed.chars().collect();

    for i in (0..chars.len()).rev() {
        let c = chars[i];
        if is_currency_char(c) || c == '/' {
            if c.is_ascii_uppercase() || c == '/' {
                split_pos = chars[..i].iter().collect::<String>().len();
            }
        } else {
            break;
        }
    }

    if split_pos == 0 || split_pos == trimmed.len() {
        bail!("Invalid amount format: {input}. Expected '123.45 USD' or '123.45USD'.");
    }

    let number_part = trimmed[..split_pos].trim();
    let currency_part = trimmed[split_pos..].trim();

    let number = Decimal::from_str(number_part)
        .with_context(|| format!("Invalid number in amount: {number_part}"))?;

    if currency_part.is_empty() {
        bail!("Missing currency in amount: {input}");
    }

    Ok(Amount::new(number, currency_part))
}

/// Calculate the balancing amount for a transaction.
///
/// Returns the negative sum of all provided amounts.
/// Only works when all amounts have the same currency.
pub fn calculate_balance(amounts: &[Amount]) -> Result<Amount> {
    if amounts.is_empty() {
        bail!("Cannot calculate balance with no amounts");
    }

    let currency = &amounts[0].currency;

    for amt in amounts.iter().skip(1) {
        if amt.currency != *currency {
            bail!(
                "Cannot auto-balance: mixed currencies ({} and {})",
                currency,
                amt.currency
            );
        }
    }

    let sum: Decimal = amounts.iter().map(|a| a.number).sum();
    Ok(Amount::new(-sum, currency.as_str()))
}
