//! Display context for formatting numbers with consistent precision.
//!
//! This module provides the [`DisplayContext`] type which tracks a frequency
//! distribution of decimal places per currency, observed during parsing. The
//! configured [`Precision`] policy then determines how that distribution is
//! collapsed to a single per-currency precision for display.
//!
//! Default policy is [`Precision::MostCommon`] — the *mode* of the dp
//! distribution. This matches Python `bean-query`'s default rendering and
//! ensures that outliers (e.g. a single 28-decimal computed price annotation)
//! don't inflate the display precision for an otherwise 2dp-dominant currency.
//!
//! [`Precision::Maximum`] selects the highest dp ever observed, which is what
//! Python uses when rendering price tables. Callers opt in via
//! [`DisplayContext::set_precision`].
//!
//! # Example
//!
//! ```
//! use rustledger_core::DisplayContext;
//! use rust_decimal_macros::dec;
//!
//! let mut ctx = DisplayContext::new();
//!
//! // Track samples for USD: tied 1×0dp + 1×2dp → tie-break favors larger.
//! ctx.update(dec!(100), "USD");       // 0 dp
//! ctx.update(dec!(50.25), "USD");     // 2 dp
//! ctx.update(dec!(1.5), "EUR");       // 1 dp
//!
//! // Default policy (MostCommon) returns the mode of the per-currency dist.
//! assert_eq!(ctx.get_precision("USD"), Some(2));
//! assert_eq!(ctx.get_precision("EUR"), Some(1));
//! assert_eq!(ctx.get_precision("GBP"), None); // Never seen
//!
//! // format() uses the policy's effective precision.
//! assert_eq!(ctx.format(dec!(100), "USD"), "100.00");
//! assert_eq!(ctx.format(dec!(50.25), "USD"), "50.25");
//! assert_eq!(ctx.format(dec!(1.5), "EUR"), "1.5");
//! ```

use rust_decimal::Decimal;
use std::collections::{BTreeMap, HashMap, HashSet};

/// Sentinel currency key for "naked-decimal" observations.
///
/// Used for values with no associated currency, e.g. BQL `Value::Number`
/// results from `SUM(number)` or `cost_number` columns. Matches Python's
/// `__default__` convention in `beancount.core.display_context`.
pub const DEFAULT_CURRENCY: &str = "__default__";

/// Per-currency frequency distribution of decimal-place counts.
///
/// Replaces the old "max-only" `u32` storage so that [`Precision::MostCommon`]
/// can pick the *mode* of observed precisions (matching Python `bean-query`'s
/// default), while [`Precision::Maximum`] still picks the historical max.
///
/// Uses `BTreeMap` so iteration order is deterministic and `mode()`'s
/// tie-breaking matches Python's "largest dp wins on ties" rule (Python
/// iterates sorted ascending with `>=`, which keeps the *last* equal-count
/// entry — i.e. the largest dp).
#[derive(Debug, Clone, Default)]
struct Distribution {
    hist: BTreeMap<u32, u32>,
}

impl Distribution {
    fn update(&mut self, dp: u32) {
        *self.hist.entry(dp).or_insert(0) += 1;
    }

    fn merge(&mut self, other: &Self) {
        for (&dp, &count) in &other.hist {
            *self.hist.entry(dp).or_insert(0) += count;
        }
    }

    fn max(&self) -> Option<u32> {
        self.hist.keys().next_back().copied()
    }

    /// Most-common dp. On ties, prefer the larger dp (matches
    /// `beancount.core.distribution.Distribution.mode`, which iterates
    /// sorted-ascending with `count >= max_count`).
    fn mode(&self) -> Option<u32> {
        let mut best: Option<(u32, u32)> = None; // (count, dp)
        for (&dp, &count) in &self.hist {
            // `>=` keeps the larger dp on ties because BTreeMap iterates ascending
            if best.is_none_or(|(c, _)| count >= c) {
                best = Some((count, dp));
            }
        }
        best.map(|(_, dp)| dp)
    }
}

/// Policy for resolving the per-currency display precision from the
/// observed distribution.
///
/// Matches Python `beancount.core.display_context.Precision`:
/// - [`MostCommon`](Self::MostCommon) returns the mode of the dp histogram.
///   Used by `bean-query` for its result tables. Outliers (a single 28-decimal
///   price annotation, a single integer-valued cost amid mostly 2dp postings)
///   don't dominate.
/// - [`Maximum`](Self::Maximum) returns the highest dp ever observed for the
///   currency. Used by Python `display_context` when rendering prices, where
///   preserving the highest-precision sample is the explicit goal.
///
/// Default is `MostCommon` to match `bean-query`'s default rendering of
/// position/amount columns. See PR #985 follow-up and beanquery#275 for
/// the upstream conversation.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum Precision {
    /// Mode of the per-currency distribution (Python `MOST_COMMON`).
    #[default]
    MostCommon,
    /// Maximum dp ever observed (Python `MAXIMUM`).
    Maximum,
}

/// Display context for formatting numbers with consistent precision per currency.
///
/// Tracks a frequency distribution of decimal places per currency and exposes
/// it via [`get_precision`](Self::get_precision) under the configured
/// [`Precision`] policy. Default policy is [`Precision::MostCommon`] to match
/// Python `bean-query`.
///
/// Fixed per-currency overrides (from `option "display_precision"`) always
/// win over inferred precision regardless of the policy.
#[derive(Debug, Clone, Default)]
pub struct DisplayContext {
    /// Per-currency observed decimal-place distributions.
    distributions: HashMap<String, Distribution>,

    /// Whether to render commas in numbers (from `option "render_commas"`).
    render_commas: bool,

    /// Fixed precision overrides (from `option "display_precision"`).
    /// These take precedence over inferred precision under any policy.
    fixed_precisions: HashMap<String, u32>,

    /// Inference policy for [`DisplayContext::get_precision`]. Defaults
    /// to [`Precision::MostCommon`] to match Python `bean-query`.
    precision: Precision,
}

impl DisplayContext {
    /// Create a new empty display context.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Update the display context with a number for a currency.
    ///
    /// Records the decimal precision (number of digits after the decimal
    /// point) of `number` against `currency`'s histogram, so subsequent
    /// `get_precision` calls reflect the new sample under the active
    /// [`Precision`] policy.
    pub fn update(&mut self, number: Decimal, currency: &str) {
        let dp = Self::decimal_precision(number);
        self.distributions
            .entry(currency.to_string())
            .or_default()
            .update(dp);
    }

    /// Update the display context from another display context.
    ///
    /// - Inferred per-currency distributions: merge histograms (sum counts
    ///   across both sides). This preserves frequency information so the
    ///   merged context's mode reflects the union of samples — strictly more
    ///   correct than the old "max of maxes" merge, and matches Python
    ///   `display_context.DisplayContext.update_from`.
    /// - Fixed per-currency overrides (`option "display_precision"`):
    ///   propagated from `other` only when `self` has no fixed override for
    ///   that currency (so a per-context override stays authoritative).
    /// - `render_commas`: enabled if either side has it on (one-way
    ///   "sticky on" merge — same rationale as before).
    /// - `precision` policy: NOT propagated. The policy is a property of
    ///   the consumer (e.g. BQL renderer vs price-display formatter), not
    ///   the data, so it stays as set on `self`.
    ///
    /// The fixed-precision and `render_commas` merging matters when a column
    /// context inherits from a ledger context for `Value::Number` rendering:
    /// without it, the ledger's display options would silently fail to apply
    /// to naked-decimal columns. See PR #961 follow-up.
    pub fn update_from(&mut self, other: &Self) {
        for (currency, dist) in &other.distributions {
            self.distributions
                .entry(currency.clone())
                .or_default()
                .merge(dist);
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

    /// Set the inference policy for [`Self::get_precision`].
    ///
    /// Default is [`Precision::MostCommon`] to match Python `bean-query`.
    /// Callers that need to preserve the highest-precision sample (e.g.
    /// price-display formatters) can opt into [`Precision::Maximum`].
    pub const fn set_precision(&mut self, precision: Precision) {
        self.precision = precision;
    }

    /// Get the active inference policy.
    #[must_use]
    pub const fn precision(&self) -> Precision {
        self.precision
    }

    /// Iterate the currencies that have observed dp samples or fixed
    /// overrides, in deterministic-but-unspecified order.
    ///
    /// Skips the `__default__` sentinel — that bucket is for naked-decimal
    /// columns (BQL `Value::Number`) and isn't a "real" currency from the
    /// user's perspective.
    pub fn currencies(&self) -> impl Iterator<Item = &str> {
        let mut seen: HashSet<&str> = HashSet::new();
        let mut out: Vec<&str> = Vec::new();
        for currency in self
            .distributions
            .keys()
            .chain(self.fixed_precisions.keys())
            .map(String::as_str)
        {
            if currency != DEFAULT_CURRENCY && seen.insert(currency) {
                out.push(currency);
            }
        }
        out.sort_unstable();
        out.into_iter()
    }

    /// Return the dp histogram for `currency` as ascending `(dp, count)`
    /// pairs. Empty if the currency has no observed samples.
    ///
    /// Useful for diagnostic / debugging tooling
    /// (e.g. `rledger doctor display-context`) that wants to show *why*
    /// a particular precision was chosen.
    #[must_use]
    pub fn histogram(&self, currency: &str) -> Vec<(u32, u32)> {
        self.distributions.get(currency).map_or_else(Vec::new, |d| {
            d.hist.iter().map(|(&dp, &c)| (dp, c)).collect()
        })
    }

    /// Look up the precision that *would* be returned under a specific
    /// policy, without mutating `self`. Same semantics as
    /// [`Self::get_precision`] but lets a single context be queried
    /// under both policies (e.g. for diagnostic output that compares
    /// `MostCommon` vs `Maximum`).
    #[must_use]
    pub fn precision_under(&self, currency: &str, policy: Precision) -> Option<u32> {
        if let Some(&fixed) = self.fixed_precisions.get(currency) {
            return Some(fixed);
        }
        let dist = self.distributions.get(currency)?;
        match policy {
            Precision::MostCommon => dist.mode(),
            Precision::Maximum => dist.max(),
        }
    }

    /// True if `currency` has a fixed-precision override
    /// (from `option "display_precision"` or
    /// [`Self::set_fixed_precision`]).
    #[must_use]
    pub fn has_fixed_precision(&self, currency: &str) -> bool {
        self.fixed_precisions.contains_key(currency)
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
    /// Returns the fixed precision if set; otherwise looks up the inferred
    /// precision under the active [`Precision`] policy
    /// ([`MostCommon`](Precision::MostCommon) by default — the mode of the
    /// observed distribution; or [`Maximum`](Precision::Maximum) — the highest
    /// observed dp). Returns `None` if the currency has never been seen.
    #[must_use]
    pub fn get_precision(&self, currency: &str) -> Option<u32> {
        if let Some(&precision) = self.fixed_precisions.get(currency) {
            return Some(precision);
        }
        let dist = self.distributions.get(currency)?;
        match self.precision {
            Precision::MostCommon => dist.mode(),
            Precision::Maximum => dist.max(),
        }
    }

    /// Get the default precision used when formatting a Decimal that has no
    /// associated currency (e.g. the result of `SUM(number)` in BQL).
    ///
    /// Resolution order (matches the BQL renderer's expectations after
    /// PR #986):
    ///
    /// 1. **`__default__` bucket** — if any naked-decimal observations have
    ///    been recorded via `update(n, DEFAULT_CURRENCY)`, the bucket's
    ///    effective precision wins. This is what BQL populates for
    ///    `Value::Number` columns (matches Python `bean-query`'s per-column
    ///    `DecimalRenderer`).
    /// 2. **Max effective precision across every other currency** — fallback
    ///    when no naked-decimal observations exist. Covers issue #954: a
    ///    column of `Value::Number(0)` that came from an aggregate
    ///    collapsing to literal zero still renders with the column's
    ///    expected dp (e.g. `0.00` for a USD-only file).
    /// 3. **Returns 0** if no currencies have been recorded at all.
    ///
    /// "Effective" precision means per-currency `fixed` overrides `inferred`
    /// (same rule as [`Self::get_precision`]) and respects the active
    /// [`Precision`] policy, so a fixed `display_precision` of 2 for USD
    /// won't be overridden by an inferred 4-digit value.
    #[must_use]
    pub fn default_precision(&self) -> u32 {
        // Prefer the `__default__` bucket if it has samples — this is what
        // BQL renderers populate for naked-Decimal columns (`Value::Number`
        // results from `SUM(number)`, `cost_number`, etc.). Matches Python
        // `bean-query`'s `DecimalRenderer`, which tracks per-column dp
        // independently of the per-currency dctx.
        if let Some(dp) = self.get_precision(DEFAULT_CURRENCY) {
            return dp;
        }

        // Fall back to max-of-effective-precisions across all known
        // currencies. Used when no explicit naked-decimal observations
        // were made (e.g. a query that returns aggregates with implicit
        // 0 results — issue #954). `get_precision` handles fixed-vs-
        // inferred priority and respects the active `Precision` policy.
        let mut max_dp: u32 = 0;
        let mut seen: HashSet<&str> = HashSet::new();
        for currency in self
            .fixed_precisions
            .keys()
            .chain(self.distributions.keys())
            .map(String::as_str)
        {
            if seen.insert(currency)
                && currency != DEFAULT_CURRENCY
                && let Some(dp) = self.get_precision(currency)
            {
                max_dp = max_dp.max(dp);
            }
        }
        max_dp
    }

    /// Quantize a number to the tracked precision for a currency.
    ///
    /// Mirrors Python's `Decimal.quantize`: the result has *exactly* the
    /// target scale — rounding when the input has more dp, padding with
    /// trailing zeros when the input has fewer. This matches what
    /// `bean-query`'s `AmountRenderer` does: it quantizes via the ledger
    /// dctx before populating the column dctx, so the column dctx sees
    /// uniformly-padded values.
    ///
    /// If the currency has no tracked precision, returns the number
    /// unchanged.
    ///
    /// Pre-fix this used `round_dp(dp)`, which only ROUNDS down — it
    /// never PADS up. That meant a 2dp input under a 4dp target stayed
    /// 2dp, the column dctx saw dp=2, and the output rendered 2dp instead
    /// of bean-query's 4dp.
    #[must_use]
    pub fn quantize(&self, number: Decimal, currency: &str) -> Decimal {
        if let Some(dp) = self.get_precision(currency) {
            let mut rounded = number.round_dp(dp);
            // round_dp can leave a smaller scale than `dp` (it only rounds
            // *down* the dp count). rescale pads up to exactly `dp`.
            rounded.rescale(dp);
            rounded
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

    /// Format a Decimal that has no associated currency.
    ///
    /// Used by the BQL query renderer for `Value::Number` results —
    /// bare Decimals produced by aggregates like `SUM(number)` or
    /// columns like `cost_number`.
    ///
    /// Matches Python `bean-query`'s `DecimalRenderer.format`, which
    /// uses the value's *natural* string representation (preserving the
    /// scale baked into the Decimal) without imposing uniform precision
    /// across rows. So `Value::Number(Decimal('0.00'))` renders `0.00`
    /// (scale survives — covers issue #954) while `Value::Number(0)`
    /// renders `0` (no artificial padding).
    ///
    /// When the value has scale 0 (no fractional part) but the context
    /// has a `__default__`-bucket precision, we DO pad up to that
    /// precision — this is the issue #954 path: an aggregate that
    /// collapsed to literal zero (scale lost) still gets rendered with
    /// the column's expected dp.
    #[must_use]
    pub fn format_default(&self, number: Decimal) -> String {
        let dp = self.default_precision();
        let formatted = if number.scale() == 0 && dp > 0 {
            // Bare integer-scale value (typical of an aggregate that
            // collapsed to literal zero, or any unscaled `Value::Number`):
            // pad to the column's default precision. Without this, a
            // `SUM` that returns 0 would render `0` where bean-query
            // renders `0.00` (issue #954).
            let mut padded = number;
            padded.rescale(dp);
            padded.to_string()
        } else {
            // Natural per-value rendering — matches Python
            // DecimalRenderer's `f'{value:<width}'`, which preserves the
            // value's intrinsic scale and does NOT impose uniform
            // precision across rows. This is the common path: each
            // aggregate result keeps the scale produced by the aggregate
            // (rust_decimal's `+` returns max-scale-of-operands).
            number.to_string()
        };
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
    fn test_update_and_get_precision_most_common_default() {
        // Default policy is MostCommon (matches Python bean-query). With
        // 2 integer-valued samples and 1 fractional, the mode is 0dp.
        let mut ctx = DisplayContext::new();

        ctx.update(dec!(100), "USD");
        assert_eq!(ctx.get_precision("USD"), Some(0));

        // Tied at 1×0dp + 1×2dp → tie-break favors larger dp = 2.
        ctx.update(dec!(50.25), "USD");
        assert_eq!(ctx.get_precision("USD"), Some(2));

        // Now 2×0dp + 1×2dp → mode is 0dp (most common).
        ctx.update(dec!(1), "USD");
        assert_eq!(ctx.get_precision("USD"), Some(0));

        // Unknown currency
        assert_eq!(ctx.get_precision("EUR"), None);
    }

    #[test]
    fn test_update_and_get_precision_maximum_policy() {
        // Same samples as the MostCommon test, but with Maximum policy:
        // the highest dp ever observed wins — preserves the historical
        // behavior for callers that opt in.
        let mut ctx = DisplayContext::new();
        ctx.set_precision(Precision::Maximum);

        ctx.update(dec!(100), "USD");
        assert_eq!(ctx.get_precision("USD"), Some(0));

        ctx.update(dec!(50.25), "USD");
        assert_eq!(ctx.get_precision("USD"), Some(2));

        // Adding more 0dp samples doesn't lower the max.
        ctx.update(dec!(1), "USD");
        assert_eq!(ctx.get_precision("USD"), Some(2));
    }

    #[test]
    fn test_default_precision_prefers_default_bucket_over_max_of_modes() {
        // When BQL renders a naked-Decimal column, it observes the column's
        // actual values into the `__default__` bucket (matching Python
        // bean-query's per-column DecimalRenderer). default_precision must
        // prefer that bucket over the max-of-modes across other currencies
        // — otherwise an unrelated currency with a higher mode (e.g. VBMPX
        // at 3dp from `3.149 VBMPX` postings) would inflate the precision
        // of a USD `cost_number` column.
        let mut ctx = DisplayContext::new();
        // Ledger context: USD has mode 2, VBMPX has mode 3.
        for _ in 0..5 {
            ctx.update(dec!(1.23), "USD");
        }
        for _ in 0..5 {
            ctx.update(dec!(1.234), "VBMPX");
        }
        // Without naked-decimal observations, default_precision falls
        // back to max-of-modes = 3 (VBMPX wins).
        assert_eq!(ctx.default_precision(), 3);
        // After observing two 2dp values into __default__, that bucket's
        // mode (2) takes precedence regardless of VBMPX.
        ctx.update(dec!(128.99), DEFAULT_CURRENCY);
        ctx.update(dec!(131.73), DEFAULT_CURRENCY);
        assert_eq!(ctx.default_precision(), 2);
    }

    #[test]
    fn test_format_default_integer_column_stays_integer() {
        // A naked-decimal column where every observed value has scale 0
        // (e.g. an integer count column from a query like
        // `SELECT account, SUM(units) WHERE units > 0`) should render
        // each value as an integer, NOT pad to some fractional precision
        // borrowed from an unrelated currency.
        //
        // Even though USD has 2dp inferred, the __default__ bucket's
        // mode is 0, so format_default returns the value's natural
        // string ("100", "5", etc.) — the scale==0 padding branch only
        // fires when the resolved default_precision > 0. Here dp = 0
        // so no padding.
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.23), "USD"); // ledger USD has 2dp
        // Column observes integer values into __default__:
        for n in [dec!(100), dec!(5), dec!(42)] {
            ctx.update(n, DEFAULT_CURRENCY);
        }
        // __default__ mode is 0 → no padding, natural rendering.
        assert_eq!(ctx.format_default(dec!(100)), "100");
        assert_eq!(ctx.format_default(dec!(5)), "5");
        // A fractional value still prints at its natural scale (matches
        // Python `DecimalRenderer` per-row formatting).
        assert_eq!(ctx.format_default(dec!(7.5)), "7.5");
    }

    #[test]
    fn test_default_precision_falls_back_when_default_bucket_empty() {
        // Issue #954: a column of `Value::Number(0)` (e.g. SUM that
        // collapsed to zero) has no naked-decimal observations to
        // populate __default__. default_precision falls back to the
        // max-of-modes so we still render `0.00` instead of `0`.
        let mut ctx = DisplayContext::new();
        for _ in 0..5 {
            ctx.update(dec!(1.23), "USD");
        }
        // No __default__ observations.
        assert_eq!(ctx.default_precision(), 2);
    }

    // ===== Diagnostic-API tests (currencies / histogram / precision_under) =====

    #[test]
    fn test_currencies_skips_default_sentinel() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.23), "USD");
        ctx.update(dec!(0.5), "EUR");
        ctx.update(dec!(100), DEFAULT_CURRENCY); // sentinel — must be hidden
        let cs: Vec<&str> = ctx.currencies().collect();
        assert_eq!(cs, vec!["EUR", "USD"]); // sorted, no __default__
    }

    #[test]
    fn test_currencies_includes_fixed_only_currencies() {
        let mut ctx = DisplayContext::new();
        // Only a fixed override, no observed samples.
        ctx.set_fixed_precision("BTC", 8);
        let cs: Vec<&str> = ctx.currencies().collect();
        assert_eq!(cs, vec!["BTC"]);
    }

    #[test]
    fn test_histogram_returns_ascending_pairs() {
        let mut ctx = DisplayContext::new();
        for _ in 0..5 {
            ctx.update(dec!(1.23), "USD"); // 2dp × 5
        }
        for _ in 0..2 {
            ctx.update(dec!(1.234), "USD"); // 3dp × 2
        }
        ctx.update(dec!(100), "USD"); // 0dp × 1
        let h = ctx.histogram("USD");
        // Ascending dp order, full counts preserved.
        assert_eq!(h, vec![(0, 1), (2, 5), (3, 2)]);
    }

    #[test]
    fn test_histogram_empty_for_unknown_currency() {
        let ctx = DisplayContext::new();
        assert!(ctx.histogram("XYZ").is_empty());
    }

    #[test]
    fn test_precision_under_does_not_mutate_active_policy() {
        let mut ctx = DisplayContext::new();
        for _ in 0..5 {
            ctx.update(dec!(100), "USD");
        }
        ctx.update(dec!(1.234), "USD");
        // Active policy is MostCommon; mode = 0.
        assert_eq!(ctx.get_precision("USD"), Some(0));
        // Querying under Maximum returns 3 — without changing active.
        assert_eq!(ctx.precision_under("USD", Precision::Maximum), Some(3));
        // Active policy unchanged after the introspection call.
        assert_eq!(ctx.precision(), Precision::MostCommon);
        assert_eq!(ctx.get_precision("USD"), Some(0));
    }

    #[test]
    fn test_precision_under_returns_zero_when_fixed_is_zero() {
        // `set_fixed_precision(c, 0)` is a legitimate setting (forces a
        // currency to render as integer). Both policies must return Some(0)
        // — not None, not the inferred precision.
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.234), "JPY"); // inferred mode = 3
        ctx.set_fixed_precision("JPY", 0); // user wants integer JPY
        assert_eq!(ctx.precision_under("JPY", Precision::MostCommon), Some(0));
        assert_eq!(ctx.precision_under("JPY", Precision::Maximum), Some(0));
        assert_eq!(ctx.get_precision("JPY"), Some(0));
    }

    #[test]
    fn test_precision_under_respects_fixed_override() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.234), "USD");
        ctx.set_fixed_precision("USD", 2);
        // Both policies see the fixed override, regardless.
        assert_eq!(ctx.precision_under("USD", Precision::MostCommon), Some(2));
        assert_eq!(ctx.precision_under("USD", Precision::Maximum), Some(2));
    }

    #[test]
    fn test_has_fixed_precision() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.23), "USD");
        assert!(!ctx.has_fixed_precision("USD"));
        ctx.set_fixed_precision("USD", 2);
        assert!(ctx.has_fixed_precision("USD"));
    }

    #[test]
    fn test_quantize_pads_scale_upward() {
        // Pinned because `Decimal::round_dp(dp)` only rounds *down* — it
        // doesn't pad scale upward. Pre-fix, quantize(150.67, "USD") with
        // USD precision=4 returned 150.67 (scale 2), which broke the
        // bean-query parity for column-level dist tracking.
        let mut ctx = DisplayContext::new();
        for _ in 0..10 {
            ctx.update(dec!(0.0400), "USD"); // 10×4dp samples → mode=4
        }
        for _ in 0..3 {
            ctx.update(dec!(150.67), "USD"); // 3×2dp samples
        }
        // Mode is 4 (ten 4dp samples win).
        assert_eq!(ctx.get_precision("USD"), Some(4));
        // Quantize must produce a Decimal with scale exactly 4, not 2.
        let q = ctx.quantize(dec!(150.67), "USD");
        assert_eq!(q.scale(), 4);
        assert_eq!(q.to_string(), "150.6700");
    }

    #[test]
    fn test_format_with_precision() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(100), "USD");
        ctx.update(dec!(50.25), "USD");

        // 1×0dp + 1×2dp → mode tie-breaks to the larger (2dp), so format
        // uses 2 fractional digits. (See test_mode_tie_break_favors_larger_dp.)
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

    // ===== Precision policy tests =====

    #[test]
    fn test_mode_picks_most_common_dp() {
        let mut ctx = DisplayContext::new();
        for _ in 0..5 {
            ctx.update(dec!(1.23), "USD"); // 2dp × 5
        }
        for _ in 0..2 {
            ctx.update(dec!(1.234), "USD"); // 3dp × 2
        }
        assert_eq!(ctx.get_precision("USD"), Some(2));
    }

    #[test]
    fn test_mode_tie_break_favors_larger_dp() {
        // Pins Python's `Distribution.mode()` tie-break: when counts tie,
        // the LARGEST dp wins. Python iterates sorted-ascending with `>=`
        // (in beancount/core/distribution.py), keeping the last equal
        // entry. We match by iterating the BTreeMap ascending with `>=`.
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.23), "USD"); // 2dp × 1
        ctx.update(dec!(1.234), "USD"); // 3dp × 1
        ctx.update(dec!(1.2345), "USD"); // 4dp × 1
        assert_eq!(ctx.get_precision("USD"), Some(4));
    }

    #[test]
    fn test_mode_outlier_does_not_dominate() {
        // The bean-query parity case: 5x integer + 1x 28dp price annotation
        // → mode = 0dp, NOT 28. Pre-fix rledger returned 28 (the max);
        // post-fix returns 0 to match bean-query's MOST_COMMON default.
        let mut ctx = DisplayContext::new();
        for _ in 0..5 {
            ctx.update(dec!(100), "USD");
        }
        ctx.update(dec!(0.0000000000000000000000000001), "USD");
        assert_eq!(ctx.get_precision("USD"), Some(0));
    }

    #[test]
    fn test_switching_to_maximum_returns_max() {
        let mut ctx = DisplayContext::new();
        for _ in 0..5 {
            ctx.update(dec!(100), "USD");
        }
        ctx.update(dec!(1.234567), "USD");
        // Default MostCommon: integer mode wins
        assert_eq!(ctx.get_precision("USD"), Some(0));
        // Switch policy to Maximum: the single 6dp sample wins
        ctx.set_precision(Precision::Maximum);
        assert_eq!(ctx.get_precision("USD"), Some(6));
        // Switch back: mode again
        ctx.set_precision(Precision::MostCommon);
        assert_eq!(ctx.get_precision("USD"), Some(0));
    }

    #[test]
    fn test_fixed_precision_overrides_both_policies() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.234), "USD");
        ctx.set_fixed_precision("USD", 2);
        assert_eq!(ctx.get_precision("USD"), Some(2));
        // Maximum policy still respects the fixed override
        ctx.set_precision(Precision::Maximum);
        assert_eq!(ctx.get_precision("USD"), Some(2));
    }

    #[test]
    fn test_update_from_merges_distributions_not_just_max() {
        // Pre-fix: update_from took max(self.max, other.max) per currency,
        // collapsing distributions. Post-fix: merges histograms so the mode
        // reflects the union of frequencies. Without this, a column ctx
        // inheriting from a ledger ctx would only see the ledger's MAX
        // value, defeating the whole MostCommon design.
        let mut a = DisplayContext::new();
        for _ in 0..5 {
            a.update(dec!(1.23), "USD"); // 2dp × 5
        }

        let mut b = DisplayContext::new();
        for _ in 0..10 {
            b.update(dec!(1.234), "USD"); // 3dp × 10
        }

        a.update_from(&b);
        // After merge: 5×2dp + 10×3dp → mode = 3dp
        assert_eq!(a.get_precision("USD"), Some(3));
    }

    #[test]
    fn test_update_from_is_not_idempotent_under_add_merge() {
        // Pin the semantics that triggered Copilot's review on PR #986:
        // since update_from now ADDS counts (not max-merges), calling it
        // multiple times multiplies the source's contribution. This is
        // why the BQL renderer must guard against repeated inheritance
        // per row (see crates/rustledger/src/cmd/query/output.rs).
        let mut src = DisplayContext::new();
        for _ in 0..10 {
            src.update(dec!(1.23), "USD"); // 2dp × 10
        }

        let mut dst1 = DisplayContext::new();
        dst1.update_from(&src);
        // After 1 merge: 10×2dp.
        assert_eq!(dst1.histogram("USD"), vec![(2, 10)]);

        let mut dst2 = DisplayContext::new();
        dst2.update_from(&src);
        dst2.update_from(&src);
        // After 2 merges: 20×2dp — counts compounded.
        assert_eq!(dst2.histogram("USD"), vec![(2, 20)]);
    }

    #[test]
    fn test_update_from_does_not_propagate_precision_policy() {
        // Policy is a property of the consumer, not the data. A column ctx
        // that opted into Maximum shouldn't have its policy clobbered by
        // a ledger ctx that uses the MostCommon default.
        let mut ledger = DisplayContext::new();
        // ledger uses default MostCommon
        ledger.update(dec!(1.23), "USD");

        let mut col = DisplayContext::new();
        col.set_precision(Precision::Maximum);
        col.update_from(&ledger);

        assert_eq!(col.precision(), Precision::Maximum);
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

        // Inferred precision distribution merged — under default
        // MostCommon policy, USD has only the single 3dp sample so
        // mode = 3.
        assert_eq!(
            col.distributions.get("USD").and_then(Distribution::mode),
            Some(3)
        );
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
    fn test_format_default_preserves_natural_scale_for_overprecise_values() {
        // Updated post-#985-follow-up: format_default no longer ROUNDS to
        // a uniform precision. Instead it preserves each value's natural
        // scale (matches Python `bean-query`'s DecimalRenderer, which
        // formats with `{value:<width}` — no precision specifier). That
        // means 1.235 prints as "1.235", NOT rounded to "1.24".
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.23), "USD");
        assert_eq!(ctx.format_default(dec!(1.235)), "1.235");
    }

    #[test]
    fn test_format_default_empty_context_natural() {
        let ctx = DisplayContext::new();
        // No tracked precision → integer-like rendering (no padding,
        // no rounding, value's natural scale).
        assert_eq!(ctx.format_default(dec!(42)), "42");
        // Fractional values keep their natural scale.
        assert_eq!(ctx.format_default(dec!(1.5)), "1.5");
    }

    #[test]
    fn test_format_default_renders_commas() {
        let mut ctx = DisplayContext::new();
        ctx.update(dec!(1.23), "USD");
        ctx.set_render_commas(true);

        assert_eq!(ctx.format_default(dec!(1234567.89)), "1,234,567.89");
    }
}
