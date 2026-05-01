//! Display context for formatting numbers with consistent precision.
//!
//! This module provides the [`DisplayContext`] type which tracks the precision
//! (number of decimal places) seen for each currency during parsing. This allows
//! numbers to be formatted consistently - for example, if a file contains both
//! `100 USD` and `50.25 USD`, both should display with 2 decimal places.
//!
//! This matches Python beancount's `display_context` behavior.
//!
//! # Example
//!
//! ```
//! use rustledger_core::DisplayContext;
//! use rust_decimal_macros::dec;
//!
//! let mut ctx = DisplayContext::new();
//!
//! // Track precision from parsed numbers
//! ctx.update(dec!(100), "USD");      // 0 decimal places
//! ctx.update(dec!(50.25), "USD");    // 2 decimal places
//! ctx.update(dec!(1.5), "EUR");      // 1 decimal place
//!
//! // Get the precision to use (maximum seen)
//! assert_eq!(ctx.get_precision("USD"), Some(2));
//! assert_eq!(ctx.get_precision("EUR"), Some(1));
//! assert_eq!(ctx.get_precision("GBP"), None);  // Never seen
//!
//! // Format a number with the tracked precision
//! assert_eq!(ctx.format(dec!(100), "USD"), "100.00");
//! assert_eq!(ctx.format(dec!(50.25), "USD"), "50.25");
//! assert_eq!(ctx.format(dec!(1.5), "EUR"), "1.5");
//! ```

use rust_decimal::Decimal;
use std::collections::{HashMap, HashSet};

/// Display context for formatting numbers with consistent precision per currency.
///
/// Tracks the maximum number of decimal places seen for each currency during parsing,
/// and provides methods to format numbers with that precision.
#[derive(Debug, Clone, Default)]
pub struct DisplayContext {
    /// Maximum decimal places seen per currency.
    precisions: HashMap<String, u32>,

    /// Whether to render commas in numbers (from `option "render_commas"`).
    render_commas: bool,

    /// Fixed precision overrides (from `option "display_precision"`).
    /// These take precedence over inferred precision.
    fixed_precisions: HashMap<String, u32>,
}

impl DisplayContext {
    /// Create a new empty display context.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Update the display context with a number for a currency.
    ///
    /// This records the decimal precision of the number (number of digits after
    /// the decimal point) and updates the maximum precision seen for that currency.
    /// Update the display context with a number for a currency.
    ///
    /// This records the decimal precision of the number (number of digits after
    /// the decimal point) and updates the maximum precision seen for that currency.
    pub fn update(&mut self, number: Decimal, currency: &str) {
        let precision = Self::decimal_precision(number);
        let entry = self.precisions.entry(currency.to_string()).or_insert(0);
        *entry = (*entry).max(precision);
    }

    /// Update the display context from another display context.
    ///
    /// - Inferred per-currency precisions: take the max of self and other.
    /// - Fixed per-currency overrides (`option "display_precision"`):
    ///   propagated from `other` only when `self` has no fixed override for
    ///   that currency (so a per-context override stays authoritative).
    /// - `render_commas`: enabled if either side has it on (treated as a
    ///   one-way "sticky on" merge — same rationale as the inferred-max).
    ///
    /// The fixed-precision and `render_commas` merging matters when a column
    /// context inherits from a ledger context for `Value::Number` rendering:
    /// without it, the ledger's display options would silently fail to apply
    /// to naked-decimal columns. See PR #961 follow-up.
    pub fn update_from(&mut self, other: &Self) {
        for (currency, precision) in &other.precisions {
            let entry = self.precisions.entry(currency.clone()).or_insert(0);
            *entry = (*entry).max(*precision);
        }
        for (currency, precision) in &other.fixed_precisions {
            self.fixed_precisions
                .entry(currency.clone())
                .or_insert(*precision);
        }
        if other.render_commas {
            self.render_commas = true;
        }
    }

    /// Set the `render_commas` flag.
    pub const fn set_render_commas(&mut self, render_commas: bool) {
        self.render_commas = render_commas;
    }

    /// Get the `render_commas` flag.
    #[must_use]
    pub const fn render_commas(&self) -> bool {
        self.render_commas
    }

    /// Set a fixed precision for a currency (from `option "display_precision"`).
    ///
    /// Fixed precision takes precedence over inferred precision.
    pub fn set_fixed_precision(&mut self, currency: &str, precision: u32) {
        self.fixed_precisions
            .insert(currency.to_string(), precision);
    }

    /// Get the precision for a currency.
    ///
    /// Returns the fixed precision if set, otherwise the maximum precision seen,
    /// or None if the currency has never been seen.
    #[must_use]
    pub fn get_precision(&self, currency: &str) -> Option<u32> {
        // Fixed precision takes precedence
        if let Some(&precision) = self.fixed_precisions.get(currency) {
            return Some(precision);
        }
        self.precisions.get(currency).copied()
    }

    /// Get the default precision used when formatting a Decimal that has no
    /// associated currency (e.g. the result of `SUM(number)` in BQL).
    ///
    /// Matches Python `bean-query`'s `format_decimal` behavior: pick the
    /// max effective precision across every currency known to the context.
    /// "Effective" means per-currency `fixed` overrides `inferred` (same rule
    /// as [`get_precision`](Self::get_precision)) — so a fixed `display_precision`
    /// of 2 for USD won't be overridden by an inferred 4-digit value seen
    /// somewhere in the file. Returns 0 if no currencies have been recorded.
    #[must_use]
    pub fn default_precision(&self) -> u32 {
        // Union of all currency keys, then look up effective precision per
        // currency. `get_precision` handles the fixed-vs-inferred priority.
        let mut max_dp: u32 = 0;
        let mut seen: HashSet<&str> = HashSet::new();
        for currency in self
            .fixed_precisions
            .keys()
            .chain(self.precisions.keys())
            .map(String::as_str)
        {
            if seen.insert(currency)
                && let Some(dp) = self.get_precision(currency)
            {
                max_dp = max_dp.max(dp);
            }
        }
        max_dp
    }

    /// Quantize a number to the tracked precision for a currency.
    ///
    /// Rounds the number to the maximum decimal places seen for the currency.
    /// If the currency has no tracked precision, returns the number unchanged.
    #[must_use]
    pub fn quantize(&self, number: Decimal, currency: &str) -> Decimal {
        if let Some(dp) = self.get_precision(currency) {
            number.round_dp(dp)
        } else {
            number
        }
    }

    /// Format a decimal number for a currency using the tracked precision.
    ///
    /// If the currency has been seen, formats with the maximum precision.
    /// Otherwise, formats with the number's natural precision (no trailing zeros).
    /// Uses half-up rounding to match Python beancount behavior.
    #[must_use]
    pub fn format(&self, number: Decimal, currency: &str) -> String {
        let precision = self.get_precision(currency);

        if let Some(dp) = precision {
            // Round with half-up (MidpointAwayFromZero) to match Python behavior
            // Note: format!("{:.N}", decimal) uses truncation which gives wrong results
            // for values like -1202.00896 (would give -1202.00 instead of -1202.01)
            let rounded = number.round_dp(dp);
            let formatted = format!("{rounded}");
            // Ensure we have the right number of decimal places (add trailing zeros if needed)
            let formatted = Self::ensure_decimal_places(&formatted, dp);
            if self.render_commas {
                Self::add_commas(&formatted)
            } else {
                formatted
            }
        } else {
            // No tracked precision - use natural formatting
            let formatted = number.normalize().to_string();
            if self.render_commas {
                Self::add_commas(&formatted)
            } else {
                formatted
            }
        }
    }

    /// Format an amount (number + currency) using the tracked precision.
    #[must_use]
    pub fn format_amount(&self, number: Decimal, currency: &str) -> String {
        format!("{} {}", self.format(number, currency), currency)
    }

    /// Format a Decimal that has no associated currency, using the
    /// [`default_precision`](Self::default_precision).
    ///
    /// Used by the BQL query renderer for `Value::Number` results — bare
    /// Decimals produced by aggregates like `SUM(number)`. Matches
    /// `bean-query`'s rendering for unspecified-currency Decimal columns.
    #[must_use]
    pub fn format_default(&self, number: Decimal) -> String {
        let dp = self.default_precision();
        let rounded = number.round_dp(dp);
        let formatted = format!("{rounded}");
        let formatted = Self::ensure_decimal_places(&formatted, dp);
        if self.render_commas {
            Self::add_commas(&formatted)
        } else {
            formatted
        }
    }

    /// Get the decimal precision (number of digits after decimal point) of a number.
    const fn decimal_precision(number: Decimal) -> u32 {
        // scale() returns the number of decimal digits
        number.scale()
    }

    /// Ensure a formatted number has exactly `dp` decimal places.
    /// Adds trailing zeros if needed, or adds ".00..." if no decimal point.
    fn ensure_decimal_places(s: &str, dp: u32) -> String {
        if dp == 0 {
            // No decimal places needed - remove any decimal point
            return s.split('.').next().unwrap_or(s).to_string();
        }

        let dp = dp as usize;
        if let Some(dot_pos) = s.find('.') {
            let current_decimals = s.len() - dot_pos - 1;
            if current_decimals >= dp {
                // Already has enough or more decimals
                s.to_string()
            } else {
                // Need to add trailing zeros
                let zeros_needed = dp - current_decimals;
                format!("{s}{}", "0".repeat(zeros_needed))
            }
        } else {
            // No decimal point - add one with zeros
            format!("{s}.{}", "0".repeat(dp))
        }
    }

    /// Add thousand separators (commas) to a formatted number string.
    fn add_commas(s: &str) -> String {
        // Split on decimal point
        let (integer_part, decimal_part) = match s.find('.') {
            Some(pos) => (&s[..pos], Some(&s[pos..])),
            None => (s, None),
        };

        // Handle negative sign
        let (sign, digits) = if let Some(stripped) = integer_part.strip_prefix('-') {
            ("-", stripped)
        } else {
            ("", integer_part)
        };

        // Add commas to integer part (from right to left)
        let mut result = String::with_capacity(digits.len() + digits.len() / 3);
        for (i, c) in digits.chars().rev().enumerate() {
            if i > 0 && i % 3 == 0 {
                result.push(',');
            }
            result.push(c);
        }
        let integer_with_commas: String = result.chars().rev().collect();

        // Combine parts
        match decimal_part {
            Some(dec) => format!("{sign}{integer_with_commas}{dec}"),
            None => format!("{sign}{integer_with_commas}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;

    #[test]
    fn test_update_and_get_precision() {
        let mut ctx = DisplayContext::new();

        ctx.update(dec!(100), "USD");
        assert_eq!(ctx.get_precision("USD"), Some(0));

        ctx.update(dec!(50.25), "USD");
        assert_eq!(ctx.get_precision("USD"), Some(2));

        // Maximum is kept
        ctx.update(dec!(1), "USD");
        assert_eq!(ctx.get_precision("USD"), Some(2));

        // Unknown currency
        assert_eq!(ctx.get_precision("EUR"), None);
    }

    #[test]
    fn test_format_with_precision() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(100), "USD");
        ctx.update(dec!(50.25), "USD");

        // Formats to max precision (2)
        assert_eq!(ctx.format(dec!(100), "USD"), "100.00");
        assert_eq!(ctx.format(dec!(50.25), "USD"), "50.25");
        assert_eq!(ctx.format(dec!(7.5), "USD"), "7.50");
    }

    #[test]
    fn test_format_unknown_currency() {
        let ctx = DisplayContext::new();

        // Unknown currency uses natural formatting
        assert_eq!(ctx.format(dec!(100), "EUR"), "100");
        assert_eq!(ctx.format(dec!(50.25), "EUR"), "50.25");
    }

    #[test]
    fn test_fixed_precision_override() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(100), "USD");
        ctx.update(dec!(50.25), "USD");

        // Inferred precision is 2
        assert_eq!(ctx.get_precision("USD"), Some(2));

        // Set fixed precision to 4
        ctx.set_fixed_precision("USD", 4);
        assert_eq!(ctx.get_precision("USD"), Some(4));

        // Formatting uses fixed precision
        assert_eq!(ctx.format(dec!(100), "USD"), "100.0000");
    }

    #[test]
    fn test_render_commas() {
        let mut ctx = DisplayContext::new();
        ctx.set_render_commas(true);
        ctx.update(dec!(1234567.89), "USD");

        assert_eq!(ctx.format(dec!(1234567.89), "USD"), "1,234,567.89");
        assert_eq!(ctx.format(dec!(1000), "USD"), "1,000.00");
    }

    #[test]
    fn test_add_commas() {
        assert_eq!(DisplayContext::add_commas("1234567"), "1,234,567");
        assert_eq!(DisplayContext::add_commas("1234567.89"), "1,234,567.89");
        assert_eq!(DisplayContext::add_commas("-1234567.89"), "-1,234,567.89");
        assert_eq!(DisplayContext::add_commas("123"), "123");
        assert_eq!(DisplayContext::add_commas("1"), "1");
    }

    #[test]
    fn test_update_from() {
        let mut ctx1 = DisplayContext::new();
        ctx1.update(dec!(100), "USD");

        let mut ctx2 = DisplayContext::new();
        ctx2.update(dec!(50.25), "USD");
        ctx2.update(dec!(1.5), "EUR");

        ctx1.update_from(&ctx2);

        assert_eq!(ctx1.get_precision("USD"), Some(2));
        assert_eq!(ctx1.get_precision("EUR"), Some(1));
    }

    #[test]
    fn test_update_from_propagates_fixed_precisions_and_render_commas() {
        // Copilot review on PR #961: previously update_from only merged
        // inferred precisions, so naked-decimal columns inheriting from a
        // ledger context with `option "display_precision"` would miss the
        // fixed overrides.
        let mut ledger = DisplayContext::new();
        ledger.update(dec!(1.234), "USD"); // inferred precision 3
        ledger.set_fixed_precision("USD", 2); // fixed override
        ledger.set_fixed_precision("BTC", 8);
        ledger.set_render_commas(true);

        let mut col = DisplayContext::new();
        col.update_from(&ledger);

        // Inferred precision merged.
        assert_eq!(col.precisions.get("USD"), Some(&3));
        // Fixed overrides also propagated.
        assert_eq!(col.fixed_precisions.get("USD"), Some(&2));
        assert_eq!(col.fixed_precisions.get("BTC"), Some(&8));
        // get_precision still respects the fixed override.
        assert_eq!(col.get_precision("USD"), Some(2));
        assert_eq!(col.get_precision("BTC"), Some(8));
        // render_commas propagated.
        assert!(col.render_commas);
    }

    #[test]
    fn test_update_from_preserves_self_fixed_overrides() {
        // If self already has a fixed override for a currency, update_from
        // shouldn't clobber it with the other's value. Self wins.
        let mut ledger = DisplayContext::new();
        ledger.set_fixed_precision("USD", 2);

        let mut col = DisplayContext::new();
        col.set_fixed_precision("USD", 4); // self's override
        col.update_from(&ledger);

        assert_eq!(col.fixed_precisions.get("USD"), Some(&4));
    }

    #[test]
    fn test_default_precision_respects_fixed_override_lower_than_inferred() {
        // Copilot review on PR #961: if USD has inferred=4 but fixed=2,
        // the user said "render USD with 2 decimals" — default_precision
        // for naked Decimals must respect that, not fall back to the
        // inferred max (4).
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.2345), "USD"); // inferred 4
        ctx.set_fixed_precision("USD", 2); // fixed override

        // get_precision returns the effective precision (fixed wins).
        assert_eq!(ctx.get_precision("USD"), Some(2));
        // default_precision must use the same effective view, not raw max.
        assert_eq!(ctx.default_precision(), 2);
    }

    #[test]
    fn test_default_precision_takes_max_across_currencies_with_overrides() {
        // EUR fixed=4 wins over USD fixed=2 → default = 4.
        let mut ctx = DisplayContext::new();
        ctx.set_fixed_precision("USD", 2);
        ctx.set_fixed_precision("EUR", 4);

        assert_eq!(ctx.default_precision(), 4);
    }

    #[test]
    fn test_format_amount() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(50.25), "USD");

        assert_eq!(ctx.format_amount(dec!(100), "USD"), "100.00 USD");
    }

    #[test]
    fn test_default_precision_picks_max_across_currencies() {
        // Issue #954: bare Decimals (e.g. SUM(number) result) need a default
        // precision matching what bean-query uses — the max precision across
        // every known currency.
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.23), "USD"); // precision 2
        ctx.update(dec!(1.2345), "EUR"); // precision 4
        ctx.update(dec!(0.5), "GBP"); // precision 1

        assert_eq!(ctx.default_precision(), 4);
    }

    #[test]
    fn test_default_precision_includes_fixed_overrides() {
        // Fixed precision (from `option "display_precision"`) should also
        // contribute to the max.
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.23), "USD");
        ctx.set_fixed_precision("BTC", 8);

        assert_eq!(ctx.default_precision(), 8);
    }

    #[test]
    fn test_default_precision_empty_context_is_zero() {
        let ctx = DisplayContext::new();
        assert_eq!(ctx.default_precision(), 0);
    }

    #[test]
    fn test_format_default_pads_to_max_precision() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.23), "USD");
        ctx.update(dec!(1.2345), "EUR");

        // Default precision = 4 (EUR's), so even an integer-shaped value
        // gets four trailing zeros.
        assert_eq!(ctx.format_default(dec!(0)), "0.0000");
        assert_eq!(ctx.format_default(dec!(100)), "100.0000");
    }

    #[test]
    fn test_format_default_rounds_overprecise_values() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.23), "USD");

        // Default precision = 2, so 1.235 rounds half-away-from-zero to 1.24.
        assert_eq!(ctx.format_default(dec!(1.235)), "1.24");
    }

    #[test]
    fn test_format_default_empty_context_natural() {
        let ctx = DisplayContext::new();
        // No tracked precision → 0 → integer-like rendering.
        assert_eq!(ctx.format_default(dec!(42)), "42");
        // Fractional values with default precision 0 round to integer.
        assert_eq!(ctx.format_default(dec!(1.5)), "2");
    }

    #[test]
    fn test_format_default_renders_commas() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.23), "USD");
        ctx.set_render_commas(true);

        assert_eq!(ctx.format_default(dec!(1234567.89)), "1,234,567.89");
    }
}
