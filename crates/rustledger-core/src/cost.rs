//! Cost and cost specification types.
//!
//! A [`Cost`] represents the acquisition cost of a position (lot). It includes
//! the per-unit cost, currency, optional acquisition date, and optional label.
//!
//! A [`CostSpec`] is used for matching against existing costs or specifying
//! new costs when all fields may not be known.

use crate::NaiveDate;
use rust_decimal::Decimal;
use serde::{Deserialize, Serialize};
use std::fmt;

use crate::Amount;

// Note: We no longer auto-quantize calculated values during cost storage.
// Python beancount preserves full precision during booking and only rounds
// at display time. Premature rounding of per-unit costs (e.g., from
// total cost / units) causes cost basis errors when selling.
// For example: 300.00 / 1.763 = 170.16505... should NOT be rounded to 170.17,
// because 1.763 * 170.17 = 300.00971 ≠ 300.00.
#[cfg(feature = "rkyv")]
use crate::intern::{AsDecimal, AsNaiveDate};

/// A cost represents the acquisition cost of a position (lot).
///
/// When you buy 10 shares of AAPL at $150 on 2024-01-15, the cost is:
/// - number: 150
/// - currency: "USD"
/// - date: Some(2024-01-15)
/// - label: None (or Some("lot1") if labeled)
///
/// # Examples
///
/// ```
/// use rustledger_core::Cost;
/// use rust_decimal_macros::dec;
///
/// let cost = Cost::new(dec!(150.00), "USD")
///     .with_date(rustledger_core::naive_date(2024, 1, 15).unwrap());
///
/// assert_eq!(cost.number, dec!(150.00));
/// assert_eq!(cost.currency, "USD");
/// assert!(cost.date.is_some());
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)
)]
pub struct Cost {
    /// Cost per unit
    #[cfg_attr(feature = "rkyv", rkyv(with = AsDecimal))]
    pub number: Decimal,
    /// Currency of the cost
    pub currency: crate::Currency,
    /// Acquisition date (optional, for lot identification)
    #[cfg_attr(feature = "rkyv", rkyv(with = rkyv::with::Map<AsNaiveDate>))]
    pub date: Option<NaiveDate>,
    /// Lot label (optional, for explicit lot identification)
    pub label: Option<String>,
}

impl Cost {
    /// Create a new cost with the given number and currency.
    ///
    /// Create a new cost with exact precision.
    /// Use this for user-specified values that should preserve their precision.
    #[must_use]
    pub fn new(number: Decimal, currency: impl Into<crate::Currency>) -> Self {
        Self {
            number,
            currency: currency.into(),
            date: None,
            label: None,
        }
    }

    /// Create a new cost for calculated values.
    ///
    /// Previously this auto-quantized, but we now preserve full precision
    /// to avoid cost basis errors. Rounding should only happen at display time.
    #[must_use]
    pub fn new_calculated(number: Decimal, currency: impl Into<crate::Currency>) -> Self {
        Self::new(number, currency)
    }

    /// Add a date to this cost.
    #[must_use]
    pub const fn with_date(mut self, date: NaiveDate) -> Self {
        self.date = Some(date);
        self
    }

    /// Add an optional date to this cost.
    #[must_use]
    pub const fn with_date_opt(mut self, date: Option<NaiveDate>) -> Self {
        self.date = date;
        self
    }

    /// Add a label to this cost.
    #[must_use]
    pub fn with_label(mut self, label: impl Into<String>) -> Self {
        self.label = Some(label.into());
        self
    }

    /// Add an optional label to this cost.
    #[must_use]
    pub fn with_label_opt(mut self, label: Option<String>) -> Self {
        self.label = label;
        self
    }

    /// Get the cost as an amount.
    #[must_use]
    pub fn as_amount(&self) -> Amount {
        Amount::new(self.number, self.currency.clone())
    }

    /// Calculate the total cost for a given number of units.
    #[must_use]
    pub fn total_cost(&self, units: Decimal) -> Amount {
        Amount::new(units * self.number, self.currency.clone())
    }
}

impl fmt::Display for Cost {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Match Beancount's `Position.__str__` format: `{ 520 USD}` —
        // single space after the opening brace, no space before the
        // closing brace. The space matters for BQL-output compat: the
        // compat harness diffs row-by-row against bean-query, and the
        // pre-fix `{520 USD}` form accounted for ~137 of 510 file ×
        // query mismatches. Verified against beanquery 0.2.0 + beancount
        // 3.2.3 (matches what CI installs and what the dev shell now
        // ships via the compat container — see PR #1047). Source-level
        // `format_cost_spec` (used by `rledger format` to round-trip
        // ledger files) keeps the no-space `{N CCY}` form because that
        // matches Beancount's `print` command output, not its
        // `Position.__str__`.
        write!(f, "{{ {} {}", self.number, self.currency)?;
        if let Some(date) = self.date {
            write!(f, ", {date}")?;
        }
        if let Some(label) = &self.label {
            // Escape via `format::escape_string` so labels containing
            // `"`, `\`, or `\n` round-trip safely. Without this a label
            // like `say "hi"` would render as `"say "hi""` — a parse
            // error if anyone tried to feed it back to a Beancount-
            // compatible reader.
            write!(f, ", \"{}\"", crate::format::escape_string(label))?;
        }
        write!(f, "}}")
    }
}

/// A cost specification for matching or creating costs.
///
/// Unlike [`Cost`], all fields are optional to allow partial matching.
/// This is used in postings where the user may specify only some
/// cost components (e.g., just the date to match a specific lot).
///
/// # Matching Rules
///
/// A `CostSpec` matches a `Cost` if all specified fields match:
/// - If `number` is `Some`, it must equal the cost's number
/// - If `currency` is `Some`, it must equal the cost's currency
/// - If `date` is `Some`, it must equal the cost's date
/// - If `label` is `Some`, it must equal the cost's label
///
/// # Examples
///
/// ```
/// use rustledger_core::{Cost, CostSpec};
/// use rust_decimal_macros::dec;
///
/// let cost = Cost::new(dec!(150.00), "USD")
///     .with_date(rustledger_core::naive_date(2024, 1, 15).unwrap());
///
/// // Match by date only
/// let spec = CostSpec::default().with_date(rustledger_core::naive_date(2024, 1, 15).unwrap());
/// assert!(spec.matches(&cost));
///
/// // Match by wrong date
/// let spec2 = CostSpec::default().with_date(rustledger_core::naive_date(2024, 1, 16).unwrap());
/// assert!(!spec2.matches(&cost));
/// ```
/// The numeric component of a [`CostSpec`].
///
/// Beancount cost specs name a number in one of two source-level
/// shapes:
///
/// - `{150.00 USD}` — per-unit cost ([`Self::PerUnit`])
/// - `{{ 1500.00 USD }}` — total cost for the posting's units
///   ([`Self::Total`])
///
/// During booking the engine converts `Total(t)` into a third state,
/// [`Self::PerUnitFromTotal`], carrying both the derived per-unit
/// value (for display, lot tracking) and the original total (for
/// precision-preserving residual math — division-then-multiplication
/// loses precision at the `rust_decimal` 28-digit ceiling).
///
/// A cost spec without a number at all (e.g. `{}` for a booking-
/// deferred lot match) is represented by `CostSpec.number: None`.
///
/// Pre-#1164 the per-unit and total numbers were two independent
/// `Option<Decimal>` fields on `CostSpec`. The invalid both-set state
/// was prevented only by parser discipline and downstream defensive
/// branches; the "booked from total" state was modeled accidentally
/// by setting both fields, with the meaning encoded only in code
/// comments. Folding the axes into one enum makes both the
/// pre-booking invalid state unrepresentable AND the post-booking
/// derived state explicit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)
)]
pub enum CostNumber {
    /// Per-unit cost as written: `{150.00 USD}`. Booking leaves this
    /// shape unchanged.
    PerUnit(#[cfg_attr(feature = "rkyv", rkyv(with = AsDecimal))] Decimal),
    /// Total cost as written: `{{ 1500.00 USD }}`. Booking rewrites
    /// this to [`Self::PerUnitFromTotal`] once units are known.
    Total(#[cfg_attr(feature = "rkyv", rkyv(with = AsDecimal))] Decimal),
    /// Post-booking state: a per-unit value derived from a
    /// `{{ total USD }}` spec at booking time, with the source total
    /// preserved for exact residual math. Pre-#1164 this was modeled
    /// implicitly by setting both `number_per` and `number_total` on
    /// `CostSpec`. The payload is a separate [`BookedCost`] struct
    /// rather than an inline struct variant so rkyv's per-variant
    /// archived struct keeps `missing_docs` quiet — the wrapped
    /// struct's fields carry the docs.
    PerUnitFromTotal(BookedCost),
}

/// Payload of [`CostNumber::PerUnitFromTotal`].
///
/// Carries both the per-unit value derived at booking time and the
/// original `{{ total }}` cost so residual math can use the exact
/// total (avoiding the division-then-multiplication precision loss
/// that hits the `rust_decimal` 28-digit ceiling on long ledgers).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)
)]
pub struct BookedCost {
    /// Per-unit cost, derived as `total / |units|` during booking.
    /// Used by lot tracking, display (Python-compat post-booking
    /// per-unit form), and validation reads that want a per-unit
    /// value.
    #[cfg_attr(feature = "rkyv", rkyv(with = AsDecimal))]
    pub per_unit: Decimal,
    /// Original total as written. Used by residual calculation to
    /// avoid the division-then-multiplication precision loss that
    /// would otherwise leak into balance checks.
    #[cfg_attr(feature = "rkyv", rkyv(with = AsDecimal))]
    pub total: Decimal,
}

impl CostNumber {
    /// Return the per-unit value if this number carries one.
    ///
    /// - [`Self::PerUnit`] → `Some(its Decimal)`
    /// - [`Self::PerUnitFromTotal`] → `Some(per_unit)`
    /// - [`Self::Total`] → `None` (booking hasn't computed per-unit yet)
    #[must_use]
    pub const fn per_unit(&self) -> Option<Decimal> {
        match self {
            Self::PerUnit(n) => Some(*n),
            Self::PerUnitFromTotal(b) => Some(b.per_unit),
            Self::Total(_) => None,
        }
    }

    /// Return the total value if this number carries one.
    ///
    /// - [`Self::Total`] → `Some(its Decimal)`
    /// - [`Self::PerUnitFromTotal`] → `Some(total)`
    /// - [`Self::PerUnit`] → `None`
    #[must_use]
    pub const fn total(&self) -> Option<Decimal> {
        match self {
            Self::Total(n) => Some(*n),
            Self::PerUnitFromTotal(b) => Some(b.total),
            Self::PerUnit(_) => None,
        }
    }
}

/// A cost specification on a posting (`{...}` or `{{...}}`).
///
/// Carries the parsed cost-spec axes: the numeric component (per-unit
/// vs total, modeled as the mutually-exclusive [`CostNumber`] enum),
/// currency, lot date, label, and merge flag. Any subset may be
/// missing — `{}` corresponds to all-fields-`None` plus `merge: false`,
/// which lets the booker do lot matching deferred to inventory.
///
/// Pre-#1164 this struct had two independent `Option<Decimal>` fields
/// (`number_per`, `number_total`). The mutual-exclusion invariant was
/// enforced only by parser discipline; the post-booking "derived per-
/// unit from total" state was modeled accidentally by setting both
/// fields at once. The new shape (`number: Option<CostNumber>`) makes
/// the invalid state unrepresentable and the derived state explicit.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)
)]
pub struct CostSpec {
    /// The numeric component: per-unit, total, or absent.
    ///
    /// Replaces the pre-#1164 `number_per` / `number_total` pair, which
    /// allowed the invalid both-set state at the type level. See
    /// [`CostNumber`] for the per-unit vs total distinction.
    pub number: Option<CostNumber>,
    /// Currency of the cost (if specified)
    pub currency: Option<crate::Currency>,
    /// Acquisition date (if specified)
    #[cfg_attr(feature = "rkyv", rkyv(with = rkyv::with::Map<AsNaiveDate>))]
    pub date: Option<NaiveDate>,
    /// Lot label (if specified)
    pub label: Option<String>,
    /// Whether to merge with existing lot (average cost)
    pub merge: bool,
}

impl CostSpec {
    /// Create an empty cost spec.
    #[must_use]
    pub fn empty() -> Self {
        Self::default()
    }

    /// Set the per-unit cost.
    ///
    /// Overwrites any previously-set number (per-unit or total) — the
    /// shapes are mutually exclusive by construction.
    #[must_use]
    pub const fn with_number_per(mut self, number: Decimal) -> Self {
        self.number = Some(CostNumber::PerUnit(number));
        self
    }

    /// Set the total cost.
    ///
    /// Overwrites any previously-set number (per-unit or total) — the
    /// shapes are mutually exclusive by construction.
    #[must_use]
    pub const fn with_number_total(mut self, number: Decimal) -> Self {
        self.number = Some(CostNumber::Total(number));
        self
    }

    /// Set the currency.
    #[must_use]
    pub fn with_currency(mut self, currency: impl Into<crate::Currency>) -> Self {
        self.currency = Some(currency.into());
        self
    }

    /// Set the date.
    #[must_use]
    pub const fn with_date(mut self, date: NaiveDate) -> Self {
        self.date = Some(date);
        self
    }

    /// Set the label.
    #[must_use]
    pub fn with_label(mut self, label: impl Into<String>) -> Self {
        self.label = Some(label.into());
        self
    }

    /// Set the merge flag (for average cost booking).
    #[must_use]
    pub const fn with_merge(mut self) -> Self {
        self.merge = true;
        self
    }

    /// Check if this is an empty cost spec (all fields None).
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.number.is_none()
            && self.currency.is_none()
            && self.date.is_none()
            && self.label.is_none()
            && !self.merge
    }

    /// Check if this cost spec matches a cost.
    ///
    /// All specified fields must match the corresponding cost fields.
    /// Per-unit matching uses `CostNumber::per_unit()` — a `Total`-only
    /// spec doesn't constrain the per-unit lot value (booking hasn't
    /// resolved it yet), but a `PerUnitFromTotal` post-booking spec
    /// does.
    #[must_use]
    pub fn matches(&self, cost: &Cost) -> bool {
        // Check per-unit cost — constrains the lot whenever the spec
        // carries a per-unit value (PerUnit or PerUnitFromTotal).
        if let Some(n) = self.number.and_then(|cn| cn.per_unit())
            && n != cost.number
        {
            return false;
        }
        // Check currency
        if let Some(c) = &self.currency
            && c != &cost.currency
        {
            return false;
        }
        // Check date
        if let Some(d) = &self.date
            && cost.date.as_ref() != Some(d)
        {
            return false;
        }
        // Check label
        if let Some(l) = &self.label
            && cost.label.as_ref() != Some(l)
        {
            return false;
        }
        true
    }

    /// Resolve this cost spec to a concrete cost, given the number of units.
    ///
    /// If the number is `CostNumber::Total`, the per-unit cost is
    /// calculated as `total / |units|`. Full precision is preserved to
    /// avoid cost basis errors when the position is later sold.
    /// `PerUnitFromTotal` already carries the derived per-unit value
    /// from a prior booking pass — use it directly.
    ///
    /// Returns `None` if required fields (currency, number) are missing.
    #[must_use]
    pub fn resolve(&self, units: Decimal, date: NaiveDate) -> Option<Cost> {
        let currency = self.currency.clone()?;
        let number = match self.number? {
            // User-specified per-unit cost.
            CostNumber::PerUnit(per) => per,
            // Calculated from total — preserve full precision.
            CostNumber::Total(total) => total / units.abs(),
            // Already booked from a total.
            CostNumber::PerUnitFromTotal(b) => b.per_unit,
        };

        Some(Cost {
            number,
            currency,
            date: self.date.or(Some(date)),
            label: self.label.clone(),
        })
    }
}

impl fmt::Display for CostSpec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        // Max 5 elements: number, currency, date, label, merge
        let mut parts = Vec::with_capacity(5);

        match self.number {
            Some(CostNumber::PerUnit(n)) => parts.push(format!("{n}")),
            Some(CostNumber::PerUnitFromTotal(b)) => parts.push(format!("{}", b.per_unit)),
            Some(CostNumber::Total(n)) => parts.push(format!("# {n}")),
            None => {}
        }
        if let Some(c) = &self.currency {
            parts.push(c.to_string());
        }
        if let Some(d) = self.date {
            parts.push(d.to_string());
        }
        if let Some(l) = &self.label {
            parts.push(format!("\"{l}\""));
        }
        if self.merge {
            parts.push("*".to_string());
        }

        write!(f, "{}", parts.join(", "))?;
        write!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;

    fn date(year: i32, month: u32, day: u32) -> NaiveDate {
        crate::naive_date(year, month, day).unwrap()
    }

    #[test]
    fn test_cost_new() {
        let cost = Cost::new(dec!(150.00), "USD");
        assert_eq!(cost.number, dec!(150.00));
        assert_eq!(cost.currency, "USD");
        assert!(cost.date.is_none());
        assert!(cost.label.is_none());
    }

    #[test]
    fn test_cost_builder() {
        let cost = Cost::new(dec!(150.00), "USD")
            .with_date(date(2024, 1, 15))
            .with_label("lot1");

        assert_eq!(cost.date, Some(date(2024, 1, 15)));
        assert_eq!(cost.label, Some("lot1".to_string()));
    }

    #[test]
    fn test_cost_total() {
        let cost = Cost::new(dec!(150.00), "USD");
        let total = cost.total_cost(dec!(10));
        assert_eq!(total.number, dec!(1500.00));
        assert_eq!(total.currency, "USD");
    }

    #[test]
    fn test_cost_display() {
        let cost = Cost::new(dec!(150.00), "USD")
            .with_date(date(2024, 1, 15))
            .with_label("lot1");
        let s = format!("{cost}");
        assert!(s.contains("150.00"));
        assert!(s.contains("USD"));
        assert!(s.contains("2024-01-15"));
        assert!(s.contains("lot1"));
    }

    /// Exact-format regression covering both fixes in this PR:
    /// - leading space inside `{` (matches Beancount Position.__str__)
    /// - special-character escaping in labels via `format::escape_string`
    #[test]
    fn test_cost_display_escapes_special_characters_in_label() {
        // Bare per-unit cost — pin the leading-space form.
        let bare = Cost::new(dec!(520), "USD");
        assert_eq!(format!("{bare}"), "{ 520 USD}");

        // With date.
        let dated = Cost::new(dec!(520.00), "USD").with_date(date(2024, 1, 15));
        assert_eq!(format!("{dated}"), "{ 520.00 USD, 2024-01-15}");

        // Embedded double-quote.
        let quoted = Cost::new(dec!(100.00), "USD")
            .with_date(date(2024, 1, 15))
            .with_label("say \"hi\"");
        assert_eq!(
            format!("{quoted}"),
            "{ 100.00 USD, 2024-01-15, \"say \\\"hi\\\"\"}"
        );

        // Embedded backslash.
        let backslash = Cost::new(dec!(50.00), "USD").with_label("path\\to\\lot");
        assert_eq!(
            format!("{backslash}"),
            "{ 50.00 USD, \"path\\\\to\\\\lot\"}"
        );

        // Embedded newline.
        let newline = Cost::new(dec!(75.00), "USD").with_label("line1\nline2");
        assert_eq!(format!("{newline}"), "{ 75.00 USD, \"line1\\nline2\"}");

        // Plain label still works (no escaping changes for safe chars).
        let plain = Cost::new(dec!(540.00), "USD")
            .with_date(date(2024, 2, 15))
            .with_label("lot-A");
        assert_eq!(format!("{plain}"), "{ 540.00 USD, 2024-02-15, \"lot-A\"}");
    }

    #[test]
    fn test_cost_spec_empty() {
        let spec = CostSpec::empty();
        assert!(spec.is_empty());
    }

    #[test]
    fn test_cost_spec_matches() {
        let cost = Cost::new(dec!(150.00), "USD")
            .with_date(date(2024, 1, 15))
            .with_label("lot1");

        // Empty spec matches everything
        assert!(CostSpec::empty().matches(&cost));

        // Match by number
        let spec = CostSpec::empty().with_number_per(dec!(150.00));
        assert!(spec.matches(&cost));

        // Wrong number
        let spec = CostSpec::empty().with_number_per(dec!(160.00));
        assert!(!spec.matches(&cost));

        // Match by currency
        let spec = CostSpec::empty().with_currency("USD");
        assert!(spec.matches(&cost));

        // Match by date
        let spec = CostSpec::empty().with_date(date(2024, 1, 15));
        assert!(spec.matches(&cost));

        // Match by label
        let spec = CostSpec::empty().with_label("lot1");
        assert!(spec.matches(&cost));

        // Match by all
        let spec = CostSpec::empty()
            .with_number_per(dec!(150.00))
            .with_currency("USD")
            .with_date(date(2024, 1, 15))
            .with_label("lot1");
        assert!(spec.matches(&cost));
    }

    #[test]
    fn test_cost_spec_resolve() {
        let spec = CostSpec::empty()
            .with_number_per(dec!(150.00))
            .with_currency("USD");

        let cost = spec.resolve(dec!(10), date(2024, 1, 15)).unwrap();
        assert_eq!(cost.number, dec!(150.00));
        assert_eq!(cost.currency, "USD");
        assert_eq!(cost.date, Some(date(2024, 1, 15)));
    }

    #[test]
    fn test_cost_spec_resolve_total() {
        let spec = CostSpec::empty()
            .with_number_total(dec!(1500.00))
            .with_currency("USD");

        let cost = spec.resolve(dec!(10), date(2024, 1, 15)).unwrap();
        assert_eq!(cost.number, dec!(150.00)); // 1500 / 10
        assert_eq!(cost.currency, "USD");
    }
}
