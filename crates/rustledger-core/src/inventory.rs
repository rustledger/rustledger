//! Inventory type representing a collection of positions.
//!
//! An [`Inventory`] tracks the holdings of an account as a collection of
//! [`Position`]s. It provides methods for adding and reducing positions
//! using different booking methods (FIFO, LIFO, STRICT, NONE).

use rust_decimal::prelude::Signed;
use rust_decimal::Decimal;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;
use std::str::FromStr;

use crate::intern::InternedStr;
use crate::{Amount, CostSpec, Position};

/// Booking method determines how lots are matched when reducing positions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub enum BookingMethod {
    /// Lots must match exactly (unambiguous).
    /// If multiple lots match the cost spec, an error is raised.
    #[default]
    Strict,
    /// Like STRICT, but exact-size matches accept oldest lot.
    /// If reduction amount equals total inventory, it's considered unambiguous.
    StrictWithSize,
    /// First In, First Out. Oldest lots are reduced first.
    Fifo,
    /// Last In, First Out. Newest lots are reduced first.
    Lifo,
    /// Highest In, First Out. Highest-cost lots are reduced first.
    Hifo,
    /// Average cost booking. All lots of a currency are merged.
    Average,
    /// No cost tracking. Units are reduced without matching lots.
    None,
}

impl FromStr for BookingMethod {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_uppercase().as_str() {
            "STRICT" => Ok(Self::Strict),
            "STRICT_WITH_SIZE" => Ok(Self::StrictWithSize),
            "FIFO" => Ok(Self::Fifo),
            "LIFO" => Ok(Self::Lifo),
            "HIFO" => Ok(Self::Hifo),
            "AVERAGE" => Ok(Self::Average),
            "NONE" => Ok(Self::None),
            _ => Err(format!("unknown booking method: {s}")),
        }
    }
}

impl fmt::Display for BookingMethod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Strict => write!(f, "STRICT"),
            Self::StrictWithSize => write!(f, "STRICT_WITH_SIZE"),
            Self::Fifo => write!(f, "FIFO"),
            Self::Lifo => write!(f, "LIFO"),
            Self::Hifo => write!(f, "HIFO"),
            Self::Average => write!(f, "AVERAGE"),
            Self::None => write!(f, "NONE"),
        }
    }
}

/// Result of a booking operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BookingResult {
    /// Positions that were matched/reduced.
    pub matched: Vec<Position>,
    /// The cost basis of the matched positions (for capital gains).
    pub cost_basis: Option<Amount>,
}

/// Error that can occur during booking.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BookingError {
    /// Multiple lots match but booking method requires unambiguous match.
    AmbiguousMatch {
        /// Number of lots that matched.
        num_matches: usize,
        /// The currency being reduced.
        currency: InternedStr,
    },
    /// No lots match the cost specification.
    NoMatchingLot {
        /// The currency being reduced.
        currency: InternedStr,
        /// The cost spec that didn't match.
        cost_spec: CostSpec,
    },
    /// Not enough units in matching lots.
    InsufficientUnits {
        /// The currency being reduced.
        currency: InternedStr,
        /// Units requested.
        requested: Decimal,
        /// Units available.
        available: Decimal,
    },
    /// Currency mismatch between reduction and inventory.
    CurrencyMismatch {
        /// Expected currency.
        expected: InternedStr,
        /// Got currency.
        got: InternedStr,
    },
}

impl fmt::Display for BookingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AmbiguousMatch {
                num_matches,
                currency,
            } => write!(
                f,
                "Ambiguous match: {num_matches} lots match for {currency}"
            ),
            Self::NoMatchingLot {
                currency,
                cost_spec,
            } => {
                write!(f, "No matching lot for {currency} with cost {cost_spec}")
            }
            Self::InsufficientUnits {
                currency,
                requested,
                available,
            } => write!(
                f,
                "Insufficient units of {currency}: requested {requested}, available {available}"
            ),
            Self::CurrencyMismatch { expected, got } => {
                write!(f, "Currency mismatch: expected {expected}, got {got}")
            }
        }
    }
}

impl std::error::Error for BookingError {}

/// An inventory is a collection of positions.
///
/// It tracks all positions for an account and supports booking operations
/// for adding and reducing positions.
///
/// # Examples
///
/// ```
/// use rustledger_core::{Inventory, Position, Amount, Cost, BookingMethod};
/// use rust_decimal_macros::dec;
///
/// let mut inv = Inventory::new();
///
/// // Add a simple position
/// inv.add(Position::simple(Amount::new(dec!(100), "USD")));
/// assert_eq!(inv.units("USD"), dec!(100));
///
/// // Add a position with cost
/// let cost = Cost::new(dec!(150.00), "USD");
/// inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost));
/// assert_eq!(inv.units("AAPL"), dec!(10));
/// ```
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Inventory {
    positions: Vec<Position>,
}

impl Inventory {
    /// Create an empty inventory.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Get all positions.
    #[must_use]
    pub fn positions(&self) -> &[Position] {
        &self.positions
    }

    /// Get mutable access to all positions.
    pub fn positions_mut(&mut self) -> &mut Vec<Position> {
        &mut self.positions
    }

    /// Check if inventory is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.positions.is_empty()
            || self
                .positions
                .iter()
                .all(super::position::Position::is_empty)
    }

    /// Get the number of positions (including empty ones).
    #[must_use]
    pub fn len(&self) -> usize {
        self.positions.len()
    }

    /// Get total units of a currency (ignoring cost lots).
    ///
    /// This sums all positions of the given currency regardless of cost basis.
    #[must_use]
    pub fn units(&self, currency: &str) -> Decimal {
        self.positions
            .iter()
            .filter(|p| p.units.currency == currency)
            .map(|p| p.units.number)
            .sum()
    }

    /// Get all currencies in this inventory.
    #[must_use]
    pub fn currencies(&self) -> Vec<&str> {
        let mut currencies: Vec<&str> = self
            .positions
            .iter()
            .filter(|p| !p.is_empty())
            .map(|p| p.units.currency.as_str())
            .collect();
        currencies.sort_unstable();
        currencies.dedup();
        currencies
    }

    /// Get the total book value (cost basis) for a currency.
    ///
    /// Returns the sum of all cost bases for positions of the given currency.
    #[must_use]
    pub fn book_value(&self, units_currency: &str) -> HashMap<InternedStr, Decimal> {
        let mut totals: HashMap<InternedStr, Decimal> = HashMap::new();

        for pos in &self.positions {
            if pos.units.currency == units_currency {
                if let Some(book) = pos.book_value() {
                    *totals.entry(book.currency.clone()).or_default() += book.number;
                }
            }
        }

        totals
    }

    /// Add a position to the inventory.
    ///
    /// For positions with cost, this creates a new lot.
    /// For positions without cost, this merges with existing positions
    /// of the same currency.
    pub fn add(&mut self, position: Position) {
        if position.is_empty() {
            return;
        }

        // For positions without cost, try to merge
        if position.cost.is_none() {
            for existing in &mut self.positions {
                if existing.cost.is_none() && existing.units.currency == position.units.currency {
                    existing.units += &position.units;
                    return;
                }
            }
        }

        // Otherwise, add as new lot
        self.positions.push(position);
    }

    /// Reduce positions from the inventory using the specified booking method.
    ///
    /// # Arguments
    ///
    /// * `units` - The units to reduce (negative for selling)
    /// * `cost_spec` - Optional cost specification for matching lots
    /// * `method` - The booking method to use
    ///
    /// # Returns
    ///
    /// Returns a `BookingResult` with the matched positions and cost basis,
    /// or a `BookingError` if the reduction cannot be performed.
    pub fn reduce(
        &mut self,
        units: &Amount,
        cost_spec: Option<&CostSpec>,
        method: BookingMethod,
    ) -> Result<BookingResult, BookingError> {
        let spec = cost_spec.cloned().unwrap_or_default();

        match method {
            BookingMethod::Strict => self.reduce_strict(units, &spec),
            BookingMethod::StrictWithSize => self.reduce_strict_with_size(units, &spec),
            BookingMethod::Fifo => self.reduce_fifo(units, &spec),
            BookingMethod::Lifo => self.reduce_lifo(units, &spec),
            BookingMethod::Hifo => self.reduce_hifo(units, &spec),
            BookingMethod::Average => self.reduce_average(units),
            BookingMethod::None => self.reduce_none(units),
        }
    }

    /// STRICT booking: require exactly one matching lot.
    /// Also allows "total match exception": if reduction equals total inventory, accept.
    fn reduce_strict(
        &mut self,
        units: &Amount,
        spec: &CostSpec,
    ) -> Result<BookingResult, BookingError> {
        let matching_indices: Vec<usize> = self
            .positions
            .iter()
            .enumerate()
            .filter(|(_, p)| {
                p.units.currency == units.currency
                    && !p.is_empty()
                    && p.can_reduce(units)
                    && p.matches_cost_spec(spec)
            })
            .map(|(i, _)| i)
            .collect();

        match matching_indices.len() {
            0 => Err(BookingError::NoMatchingLot {
                currency: units.currency.clone(),
                cost_spec: spec.clone(),
            }),
            1 => {
                let idx = matching_indices[0];
                self.reduce_from_lot(idx, units)
            }
            n => {
                // Total match exception: if reduction equals total inventory, it's unambiguous
                let total_units: Decimal = matching_indices
                    .iter()
                    .map(|&i| self.positions[i].units.number.abs())
                    .sum();
                if total_units == units.number.abs() {
                    // Reduce from all matching lots (use FIFO order)
                    self.reduce_ordered(units, spec, false)
                } else {
                    Err(BookingError::AmbiguousMatch {
                        num_matches: n,
                        currency: units.currency.clone(),
                    })
                }
            }
        }
    }

    /// `STRICT_WITH_SIZE` booking: like STRICT, but exact-size matches accept oldest lot.
    fn reduce_strict_with_size(
        &mut self,
        units: &Amount,
        spec: &CostSpec,
    ) -> Result<BookingResult, BookingError> {
        let matching_indices: Vec<usize> = self
            .positions
            .iter()
            .enumerate()
            .filter(|(_, p)| {
                p.units.currency == units.currency
                    && !p.is_empty()
                    && p.can_reduce(units)
                    && p.matches_cost_spec(spec)
            })
            .map(|(i, _)| i)
            .collect();

        match matching_indices.len() {
            0 => Err(BookingError::NoMatchingLot {
                currency: units.currency.clone(),
                cost_spec: spec.clone(),
            }),
            1 => {
                let idx = matching_indices[0];
                self.reduce_from_lot(idx, units)
            }
            n => {
                // Check for exact-size match with any lot
                let exact_matches: Vec<usize> = matching_indices
                    .iter()
                    .filter(|&&i| self.positions[i].units.number.abs() == units.number.abs())
                    .copied()
                    .collect();

                if exact_matches.is_empty() {
                    // Total match exception
                    let total_units: Decimal = matching_indices
                        .iter()
                        .map(|&i| self.positions[i].units.number.abs())
                        .sum();
                    if total_units == units.number.abs() {
                        self.reduce_ordered(units, spec, false)
                    } else {
                        Err(BookingError::AmbiguousMatch {
                            num_matches: n,
                            currency: units.currency.clone(),
                        })
                    }
                } else {
                    // Use oldest (first) exact-size match
                    let idx = exact_matches[0];
                    self.reduce_from_lot(idx, units)
                }
            }
        }
    }

    /// FIFO booking: reduce from oldest lots first.
    fn reduce_fifo(
        &mut self,
        units: &Amount,
        spec: &CostSpec,
    ) -> Result<BookingResult, BookingError> {
        self.reduce_ordered(units, spec, false)
    }

    /// LIFO booking: reduce from newest lots first.
    fn reduce_lifo(
        &mut self,
        units: &Amount,
        spec: &CostSpec,
    ) -> Result<BookingResult, BookingError> {
        self.reduce_ordered(units, spec, true)
    }

    /// HIFO booking: reduce from highest-cost lots first.
    fn reduce_hifo(
        &mut self,
        units: &Amount,
        spec: &CostSpec,
    ) -> Result<BookingResult, BookingError> {
        let mut remaining = units.number.abs();
        let mut matched = Vec::new();
        let mut cost_basis = Decimal::ZERO;
        let mut cost_currency = None;

        // Get matching positions with their costs
        let mut matching: Vec<(usize, Decimal)> = self
            .positions
            .iter()
            .enumerate()
            .filter(|(_, p)| {
                p.units.currency == units.currency
                    && !p.is_empty()
                    && p.units.number.signum() != units.number.signum()
                    && p.matches_cost_spec(spec)
            })
            .map(|(i, p)| {
                let cost = p.cost.as_ref().map_or(Decimal::ZERO, |c| c.number);
                (i, cost)
            })
            .collect();

        if matching.is_empty() {
            return Err(BookingError::NoMatchingLot {
                currency: units.currency.clone(),
                cost_spec: spec.clone(),
            });
        }

        // Sort by cost descending (highest first)
        matching.sort_by(|a, b| b.1.cmp(&a.1));

        let indices: Vec<usize> = matching.into_iter().map(|(i, _)| i).collect();

        for idx in indices {
            if remaining.is_zero() {
                break;
            }

            let pos = &self.positions[idx];
            let available = pos.units.number.abs();
            let take = remaining.min(available);

            // Calculate cost basis for this portion
            if let Some(cost) = &pos.cost {
                cost_basis += take * cost.number;
                cost_currency = Some(cost.currency.clone());
            }

            // Record what we matched
            let (taken, _) = pos.split(take * pos.units.number.signum());
            matched.push(taken);

            // Reduce the lot
            let reduction = if units.number.is_sign_negative() {
                -take
            } else {
                take
            };

            let new_pos = Position {
                units: Amount::new(pos.units.number + reduction, pos.units.currency.clone()),
                cost: pos.cost.clone(),
            };
            self.positions[idx] = new_pos;

            remaining -= take;
        }

        if !remaining.is_zero() {
            let available = units.number.abs() - remaining;
            return Err(BookingError::InsufficientUnits {
                currency: units.currency.clone(),
                requested: units.number.abs(),
                available,
            });
        }

        // Clean up empty positions
        self.positions.retain(|p| !p.is_empty());

        Ok(BookingResult {
            matched,
            cost_basis: cost_currency.map(|c| Amount::new(cost_basis, c)),
        })
    }

    /// Reduce in order (FIFO or LIFO).
    fn reduce_ordered(
        &mut self,
        units: &Amount,
        spec: &CostSpec,
        reverse: bool,
    ) -> Result<BookingResult, BookingError> {
        let mut remaining = units.number.abs();
        let mut matched = Vec::new();
        let mut cost_basis = Decimal::ZERO;
        let mut cost_currency = None;

        // Get indices of matching positions
        let mut indices: Vec<usize> = self
            .positions
            .iter()
            .enumerate()
            .filter(|(_, p)| {
                p.units.currency == units.currency
                    && !p.is_empty()
                    && p.units.number.signum() != units.number.signum()
                    && p.matches_cost_spec(spec)
            })
            .map(|(i, _)| i)
            .collect();

        // Sort by date for correct FIFO/LIFO ordering (oldest first)
        // This ensures we select by acquisition date, not insertion order
        indices.sort_by_key(|&i| self.positions[i].cost.as_ref().and_then(|c| c.date));

        if reverse {
            indices.reverse();
        }

        if indices.is_empty() {
            return Err(BookingError::NoMatchingLot {
                currency: units.currency.clone(),
                cost_spec: spec.clone(),
            });
        }

        for idx in indices {
            if remaining.is_zero() {
                break;
            }

            let pos = &self.positions[idx];
            let available = pos.units.number.abs();
            let take = remaining.min(available);

            // Calculate cost basis for this portion
            if let Some(cost) = &pos.cost {
                cost_basis += take * cost.number;
                cost_currency = Some(cost.currency.clone());
            }

            // Record what we matched
            let (taken, _) = pos.split(take * pos.units.number.signum());
            matched.push(taken);

            // Reduce the lot
            let reduction = if units.number.is_sign_negative() {
                -take
            } else {
                take
            };

            let new_pos = Position {
                units: Amount::new(pos.units.number + reduction, pos.units.currency.clone()),
                cost: pos.cost.clone(),
            };
            self.positions[idx] = new_pos;

            remaining -= take;
        }

        if !remaining.is_zero() {
            let available = units.number.abs() - remaining;
            return Err(BookingError::InsufficientUnits {
                currency: units.currency.clone(),
                requested: units.number.abs(),
                available,
            });
        }

        // Clean up empty positions
        self.positions.retain(|p| !p.is_empty());

        Ok(BookingResult {
            matched,
            cost_basis: cost_currency.map(|c| Amount::new(cost_basis, c)),
        })
    }

    /// AVERAGE booking: merge all lots of the currency.
    fn reduce_average(&mut self, units: &Amount) -> Result<BookingResult, BookingError> {
        // Calculate average cost
        let total_units: Decimal = self
            .positions
            .iter()
            .filter(|p| p.units.currency == units.currency && !p.is_empty())
            .map(|p| p.units.number)
            .sum();

        if total_units.is_zero() {
            return Err(BookingError::InsufficientUnits {
                currency: units.currency.clone(),
                requested: units.number.abs(),
                available: Decimal::ZERO,
            });
        }

        // Check sufficient units
        let reduction = units.number.abs();
        if reduction > total_units.abs() {
            return Err(BookingError::InsufficientUnits {
                currency: units.currency.clone(),
                requested: reduction,
                available: total_units.abs(),
            });
        }

        // Calculate total cost basis
        let book_values = self.book_value(&units.currency);
        let cost_basis = if let Some((curr, &total)) = book_values.iter().next() {
            let per_unit_cost = total / total_units;
            Some(Amount::new(reduction * per_unit_cost, curr.clone()))
        } else {
            None
        };

        // Create merged position
        let new_units = total_units + units.number;

        // Remove all positions of this currency
        let matched: Vec<Position> = self
            .positions
            .iter()
            .filter(|p| p.units.currency == units.currency && !p.is_empty())
            .cloned()
            .collect();

        self.positions
            .retain(|p| p.units.currency != units.currency);

        // Add back the remainder if non-zero
        if !new_units.is_zero() {
            self.positions.push(Position::simple(Amount::new(
                new_units,
                units.currency.clone(),
            )));
        }

        Ok(BookingResult {
            matched,
            cost_basis,
        })
    }

    /// NONE booking: reduce without matching lots.
    fn reduce_none(&mut self, units: &Amount) -> Result<BookingResult, BookingError> {
        // For NONE booking, we just reduce the total without caring about lots
        let total_units = self.units(&units.currency);

        // Check we have enough in the right direction
        if total_units.signum() == units.number.signum() || total_units.is_zero() {
            // This is an augmentation, not a reduction - just add it
            self.add(Position::simple(units.clone()));
            return Ok(BookingResult {
                matched: vec![],
                cost_basis: None,
            });
        }

        let available = total_units.abs();
        let requested = units.number.abs();

        if requested > available {
            return Err(BookingError::InsufficientUnits {
                currency: units.currency.clone(),
                requested,
                available,
            });
        }

        // Reduce positions proportionally (simplified: just reduce first matching)
        self.reduce_ordered(units, &CostSpec::default(), false)
    }

    /// Reduce from a specific lot.
    fn reduce_from_lot(
        &mut self,
        idx: usize,
        units: &Amount,
    ) -> Result<BookingResult, BookingError> {
        let pos = &self.positions[idx];
        let available = pos.units.number.abs();
        let requested = units.number.abs();

        if requested > available {
            return Err(BookingError::InsufficientUnits {
                currency: units.currency.clone(),
                requested,
                available,
            });
        }

        // Calculate cost basis
        let cost_basis = pos.cost.as_ref().map(|c| c.total_cost(requested));

        // Record matched
        let (matched, _) = pos.split(requested * pos.units.number.signum());

        // Update the position
        let new_units = pos.units.number + units.number;
        let new_pos = Position {
            units: Amount::new(new_units, pos.units.currency.clone()),
            cost: pos.cost.clone(),
        };
        self.positions[idx] = new_pos;

        // Remove if empty
        if self.positions[idx].is_empty() {
            self.positions.remove(idx);
        }

        Ok(BookingResult {
            matched: vec![matched],
            cost_basis,
        })
    }

    /// Remove all empty positions.
    pub fn compact(&mut self) {
        self.positions.retain(|p| !p.is_empty());
    }

    /// Merge this inventory with another.
    pub fn merge(&mut self, other: &Self) {
        for pos in &other.positions {
            self.add(pos.clone());
        }
    }

    /// Convert inventory to cost basis.
    ///
    /// Returns a new inventory where all positions are converted to their
    /// cost basis. Positions without cost are returned as-is.
    #[must_use]
    pub fn at_cost(&self) -> Self {
        let mut result = Self::new();

        for pos in &self.positions {
            if pos.is_empty() {
                continue;
            }

            if let Some(cost) = &pos.cost {
                // Convert to cost basis
                let total = pos.units.number * cost.number;
                result.add(Position::simple(Amount::new(total, &cost.currency)));
            } else {
                // No cost, keep as-is
                result.add(pos.clone());
            }
        }

        result
    }

    /// Convert inventory to units only.
    ///
    /// Returns a new inventory where all positions have their cost removed,
    /// effectively aggregating by currency only.
    #[must_use]
    pub fn at_units(&self) -> Self {
        let mut result = Self::new();

        for pos in &self.positions {
            if pos.is_empty() {
                continue;
            }

            // Strip cost, keep only units
            result.add(Position::simple(pos.units.clone()));
        }

        result
    }
}

impl fmt::Display for Inventory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty() {
            return write!(f, "(empty)");
        }

        let non_empty: Vec<_> = self.positions.iter().filter(|p| !p.is_empty()).collect();
        for (i, pos) in non_empty.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{pos}")?;
        }
        Ok(())
    }
}

impl FromIterator<Position> for Inventory {
    fn from_iter<I: IntoIterator<Item = Position>>(iter: I) -> Self {
        let mut inv = Self::new();
        for pos in iter {
            inv.add(pos);
        }
        inv
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Cost;
    use chrono::NaiveDate;
    use rust_decimal_macros::dec;

    fn date(year: i32, month: u32, day: u32) -> NaiveDate {
        NaiveDate::from_ymd_opt(year, month, day).unwrap()
    }

    #[test]
    fn test_empty_inventory() {
        let inv = Inventory::new();
        assert!(inv.is_empty());
        assert_eq!(inv.len(), 0);
    }

    #[test]
    fn test_add_simple() {
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(100), "USD")));

        assert!(!inv.is_empty());
        assert_eq!(inv.units("USD"), dec!(100));
    }

    #[test]
    fn test_add_merge_simple() {
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(100), "USD")));
        inv.add(Position::simple(Amount::new(dec!(50), "USD")));

        // Should merge into one position
        assert_eq!(inv.len(), 1);
        assert_eq!(inv.units("USD"), dec!(150));
    }

    #[test]
    fn test_add_with_cost_no_merge() {
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(160.00), "USD").with_date(date(2024, 1, 15));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost2));

        // Should NOT merge - different costs
        assert_eq!(inv.len(), 2);
        assert_eq!(inv.units("AAPL"), dec!(15));
    }

    #[test]
    fn test_currencies() {
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(100), "USD")));
        inv.add(Position::simple(Amount::new(dec!(50), "EUR")));
        inv.add(Position::simple(Amount::new(dec!(10), "AAPL")));

        let currencies = inv.currencies();
        assert_eq!(currencies.len(), 3);
        assert!(currencies.contains(&"USD"));
        assert!(currencies.contains(&"EUR"));
        assert!(currencies.contains(&"AAPL"));
    }

    #[test]
    fn test_reduce_strict_unique() {
        let mut inv = Inventory::new();
        let cost = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost));

        let result = inv
            .reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Strict)
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(5));
        assert!(result.cost_basis.is_some());
        assert_eq!(result.cost_basis.unwrap().number, dec!(750.00)); // 5 * 150
    }

    #[test]
    fn test_reduce_strict_ambiguous() {
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(160.00), "USD").with_date(date(2024, 1, 15));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost2));

        // Reducing without cost spec should fail (ambiguous)
        let result = inv.reduce(&Amount::new(dec!(-3), "AAPL"), None, BookingMethod::Strict);

        assert!(matches!(result, Err(BookingError::AmbiguousMatch { .. })));
    }

    #[test]
    fn test_reduce_strict_with_spec() {
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(160.00), "USD").with_date(date(2024, 1, 15));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost2));

        // Reducing with cost spec should work
        let spec = CostSpec::empty().with_date(date(2024, 1, 1));
        let result = inv
            .reduce(
                &Amount::new(dec!(-3), "AAPL"),
                Some(&spec),
                BookingMethod::Strict,
            )
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(12)); // 7 + 5
        assert_eq!(result.cost_basis.unwrap().number, dec!(450.00)); // 3 * 150
    }

    #[test]
    fn test_reduce_fifo() {
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 2, 1));
        let cost3 = Cost::new(dec!(200.00), "USD").with_date(date(2024, 3, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost3));

        // FIFO should reduce from oldest (cost 100) first
        let result = inv
            .reduce(&Amount::new(dec!(-15), "AAPL"), None, BookingMethod::Fifo)
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(15));
        // Cost basis: 10 * 100 + 5 * 150 = 1000 + 750 = 1750
        assert_eq!(result.cost_basis.unwrap().number, dec!(1750.00));
    }

    #[test]
    fn test_reduce_lifo() {
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 2, 1));
        let cost3 = Cost::new(dec!(200.00), "USD").with_date(date(2024, 3, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost3));

        // LIFO should reduce from newest (cost 200) first
        let result = inv
            .reduce(&Amount::new(dec!(-15), "AAPL"), None, BookingMethod::Lifo)
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(15));
        // Cost basis: 10 * 200 + 5 * 150 = 2000 + 750 = 2750
        assert_eq!(result.cost_basis.unwrap().number, dec!(2750.00));
    }

    #[test]
    fn test_reduce_insufficient() {
        let mut inv = Inventory::new();
        let cost = Cost::new(dec!(150.00), "USD");
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost));

        let result = inv.reduce(&Amount::new(dec!(-15), "AAPL"), None, BookingMethod::Fifo);

        assert!(matches!(
            result,
            Err(BookingError::InsufficientUnits { .. })
        ));
    }

    #[test]
    fn test_book_value() {
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(100.00), "USD");
        let cost2 = Cost::new(dec!(150.00), "USD");

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost2));

        let book = inv.book_value("AAPL");
        assert_eq!(book.get("USD"), Some(&dec!(1750.00))); // 10*100 + 5*150
    }

    #[test]
    fn test_display() {
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(100), "USD")));

        let s = format!("{inv}");
        assert!(s.contains("100 USD"));
    }

    #[test]
    fn test_display_empty() {
        let inv = Inventory::new();
        assert_eq!(format!("{inv}"), "(empty)");
    }

    #[test]
    fn test_from_iterator() {
        let positions = vec![
            Position::simple(Amount::new(dec!(100), "USD")),
            Position::simple(Amount::new(dec!(50), "USD")),
        ];

        let inv: Inventory = positions.into_iter().collect();
        assert_eq!(inv.units("USD"), dec!(150));
    }
}
