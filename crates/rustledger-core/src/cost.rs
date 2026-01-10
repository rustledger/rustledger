//! Cost and cost specification types.
//!
//! A [`Cost`] represents the acquisition cost of a position (lot). It includes
//! the per-unit cost, currency, optional acquisition date, and optional label.
//!
//! A [`CostSpec`] is used for matching against existing costs or specifying
//! new costs when all fields may not be known.

use chrono::NaiveDate;
use rust_decimal::Decimal;
use serde::{Deserialize, Serialize};
use std::fmt;

use crate::Amount;
use crate::intern::InternedStr;

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
/// use chrono::NaiveDate;
///
/// let cost = Cost::new(dec!(150.00), "USD")
///     .with_date(NaiveDate::from_ymd_opt(2024, 1, 15).unwrap());
///
/// assert_eq!(cost.number, dec!(150.00));
/// assert_eq!(cost.currency, "USD");
/// assert!(cost.date.is_some());
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Cost {
    /// Cost per unit
    pub number: Decimal,
    /// Currency of the cost
    pub currency: InternedStr,
    /// Acquisition date (optional, for lot identification)
    pub date: Option<NaiveDate>,
    /// Lot label (optional, for explicit lot identification)
    pub label: Option<String>,
}

impl Cost {
    /// Create a new cost with the given number and currency.
    #[must_use]
    pub fn new(number: Decimal, currency: impl Into<InternedStr>) -> Self {
        Self {
            number,
            currency: currency.into(),
            date: None,
            label: None,
        }
    }

    /// Add a date to this cost.
    #[must_use]
    pub const fn with_date(mut self, date: NaiveDate) -> Self {
        self.date = Some(date);
        self
    }

    /// Add a label to this cost.
    #[must_use]
    pub fn with_label(mut self, label: impl Into<String>) -> Self {
        self.label = Some(label.into());
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
        write!(f, "{{{} {}", self.number, self.currency)?;
        if let Some(date) = self.date {
            write!(f, ", {date}")?;
        }
        if let Some(label) = &self.label {
            write!(f, ", \"{label}\"")?;
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
/// use chrono::NaiveDate;
///
/// let cost = Cost::new(dec!(150.00), "USD")
///     .with_date(NaiveDate::from_ymd_opt(2024, 1, 15).unwrap());
///
/// // Match by date only
/// let spec = CostSpec::default().with_date(NaiveDate::from_ymd_opt(2024, 1, 15).unwrap());
/// assert!(spec.matches(&cost));
///
/// // Match by wrong date
/// let spec2 = CostSpec::default().with_date(NaiveDate::from_ymd_opt(2024, 1, 16).unwrap());
/// assert!(!spec2.matches(&cost));
/// ```
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct CostSpec {
    /// Cost per unit (if specified)
    pub number_per: Option<Decimal>,
    /// Total cost (if specified) - alternative to `number_per`
    pub number_total: Option<Decimal>,
    /// Currency of the cost (if specified)
    pub currency: Option<InternedStr>,
    /// Acquisition date (if specified)
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
    #[must_use]
    pub const fn with_number_per(mut self, number: Decimal) -> Self {
        self.number_per = Some(number);
        self
    }

    /// Set the total cost.
    #[must_use]
    pub const fn with_number_total(mut self, number: Decimal) -> Self {
        self.number_total = Some(number);
        self
    }

    /// Set the currency.
    #[must_use]
    pub fn with_currency(mut self, currency: impl Into<InternedStr>) -> Self {
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
        self.number_per.is_none()
            && self.number_total.is_none()
            && self.currency.is_none()
            && self.date.is_none()
            && self.label.is_none()
            && !self.merge
    }

    /// Check if this cost spec matches a cost.
    ///
    /// All specified fields must match the corresponding cost fields.
    #[must_use]
    pub fn matches(&self, cost: &Cost) -> bool {
        // Check per-unit cost
        if let Some(n) = &self.number_per {
            if n != &cost.number {
                return false;
            }
        }
        // Check currency
        if let Some(c) = &self.currency {
            if c != &cost.currency {
                return false;
            }
        }
        // Check date
        if let Some(d) = &self.date {
            if cost.date.as_ref() != Some(d) {
                return false;
            }
        }
        // Check label
        if let Some(l) = &self.label {
            if cost.label.as_ref() != Some(l) {
                return false;
            }
        }
        true
    }

    /// Resolve this cost spec to a concrete cost, given the number of units.
    ///
    /// If `number_total` is specified, the per-unit cost is calculated as
    /// `number_total / units`.
    ///
    /// Returns `None` if required fields (currency) are missing.
    #[must_use]
    pub fn resolve(&self, units: Decimal, date: NaiveDate) -> Option<Cost> {
        let currency = self.currency.clone()?;

        let number = if let Some(per) = self.number_per {
            per
        } else if let Some(total) = self.number_total {
            total / units.abs()
        } else {
            return None;
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
        let mut parts = Vec::new();

        if let Some(n) = self.number_per {
            parts.push(format!("{n}"));
        }
        if let Some(n) = self.number_total {
            parts.push(format!("# {n}"));
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
        NaiveDate::from_ymd_opt(year, month, day).unwrap()
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
