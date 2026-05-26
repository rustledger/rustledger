//! Inventory type representing a collection of positions.
//!
//! An [`Inventory`] tracks the holdings of an account as a collection of
//! [`Position`]s. It provides methods for adding and reducing positions
//! using different booking methods (FIFO, LIFO, STRICT, NONE).

use imbl::Vector;
use rust_decimal::Decimal;
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;
use std::fmt;
use std::str::FromStr;

use crate::{Amount, CostSpec, Position};

/// Inline storage for `BookingResult::matched`.
///
/// STRICT booking (the default) always produces exactly one matched lot
/// per posting; FIFO / LIFO frequently match a single lot too. Inline
/// cap of 1 covers the hot case with zero heap allocation while still
/// spilling to the heap for multi-lot matches.
///
/// **API surface note**: this is `pub(crate)` deliberately — we don't
/// want to commit downstream consumers to `smallvec` as part of our
/// public API contract. External code reads `BookingResult.matched` via
/// the slice deref (`.iter()`, `.len()`, indexing) which works
/// transparently. The concrete `SmallVec<[Position; 1]>` type is still
/// reachable via the field type but isn't promoted into the crate root.
pub(crate) type MatchedLots = SmallVec<[Position; 1]>;

mod booking;

/// Booking method determines how lots are matched when reducing positions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)
)]
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

/// Controls which positions are considered when checking whether incoming
/// units reduce (i.e. have the opposite sign of) an existing inventory.
///
/// - [`AllPositions`](ReductionScope::AllPositions): every position is
///   considered, regardless of whether it carries a cost.
/// - [`CostBearingOnly`](ReductionScope::CostBearingOnly): only positions
///   with a cost are considered.  This prevents a negative simple (no-cost)
///   position — left behind by a sell-without-cost-spec — from causing a
///   subsequent cost-bearing augmentation to be misclassified as a reduction.
///   See: issue #875, beancount#889.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ReductionScope {
    /// Consider all positions (cost-bearing and simple).
    AllPositions,
    /// Consider only positions that carry a cost.
    CostBearingOnly,
}

/// Result of a booking operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BookingResult {
    /// Positions that were matched/reduced.
    ///
    /// Backed by [`SmallVec<[Position; 1]>`](smallvec::SmallVec) so the
    /// single-match common case (always true under STRICT, common under
    /// FIFO/LIFO) doesn't touch the heap. The concrete type derefs to
    /// `[Position]`, so read-side patterns like `.iter()`,
    /// `.len()`, `.is_empty()`, and indexing work unchanged.
    ///
    /// **Breaking API change in 0.15.0**: prior versions used
    /// `Vec<Position>`. Downstream code that named the type explicitly
    /// (`let v: Vec<Position> = result.matched`) or called Vec-specific
    /// methods (`.capacity()`, `.reserve()`) needs to adapt; reading
    /// the field through the slice deref keeps working.
    pub matched: MatchedLots,
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
        currency: crate::Currency,
    },
    /// No lots match the cost specification.
    NoMatchingLot {
        /// The currency being reduced.
        currency: crate::Currency,
        /// The cost spec that didn't match.
        cost_spec: CostSpec,
    },
    /// Not enough units in matching lots.
    InsufficientUnits {
        /// The currency being reduced.
        currency: crate::Currency,
        /// Units requested.
        requested: Decimal,
        /// Units available.
        available: Decimal,
    },
    /// Currency mismatch between reduction and inventory.
    CurrencyMismatch {
        /// Expected currency.
        expected: crate::Currency,
        /// Got currency.
        got: crate::Currency,
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

impl BookingError {
    /// Wrap this booking error with the account context that produced it.
    ///
    /// `Inventory` itself doesn't know which account it belongs to, so the
    /// raw `BookingError` carries no `account` field. The caller (booking
    /// engine, validator) knows the account and uses this constructor to
    /// produce the user-facing error.
    ///
    /// The resulting [`AccountedBookingError`] is the **single canonical
    /// rendering** of an inventory failure for user-facing output. Both the
    /// booking layer and the validator format errors via this type so the
    /// wording cannot drift between them — the failure mode that produced
    /// #748.
    #[must_use]
    pub const fn with_account(self, account: crate::Account) -> AccountedBookingError {
        AccountedBookingError {
            error: self,
            account,
        }
    }
}

/// A [`BookingError`] paired with the account that produced it.
///
/// This is the canonical user-facing inventory error type. Its `Display`
/// impl is the **single source of truth** for booking-error wording across
/// `rustledger-booking` and `rustledger-validate`. Conformance assertions
/// (e.g. pta-standards `reduction-exceeds-inventory` requires the literal
/// substring `"not enough"`) are pinned by this Display.
///
/// Construct via [`BookingError::with_account`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AccountedBookingError {
    /// The underlying inventory-level error.
    pub error: BookingError,
    /// The account whose inventory produced the error.
    pub account: crate::Account,
}

impl fmt::Display for AccountedBookingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.error {
            BookingError::InsufficientUnits {
                requested,
                available,
                ..
            } => write!(
                f,
                "Not enough units in {}: requested {}, available {}; not enough to reduce",
                self.account, requested, available
            ),
            BookingError::NoMatchingLot { currency, .. } => {
                write!(f, "No matching lot for {} in {}", currency, self.account)
            }
            BookingError::AmbiguousMatch {
                num_matches,
                currency,
            } => write!(
                f,
                "Ambiguous lot match for {}: {} lots match in {}",
                currency, num_matches, self.account
            ),
            // Currency mismatch is semantically a specialization of
            // NoMatchingLot (there is no lot for the given currency in this
            // inventory), so we render and classify it the same way. Consumers
            // filtering on E4001 don't need to special-case CurrencyMismatch.
            //
            // This variant is defensive: no `Inventory::reduce` path in
            // `rustledger-core` currently emits it, but we still render it
            // consistently in case a future emission site is added.
            BookingError::CurrencyMismatch { got, .. } => {
                write!(f, "No matching lot for {} in {}", got, self.account)
            }
        }
    }
}

impl std::error::Error for AccountedBookingError {}

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
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Inventory {
    /// Persistent (structurally-shared) RRB-tree-backed vector. Cloning
    /// is O(1) (Arc bump on the tree root); `push_back` / indexed mutation
    /// are O(log N) per op but share structure with previous versions.
    /// This is the critical property for JOURNAL-style row-per-snapshot
    /// patterns in BQL (issue #1086): N nested snapshots cost O(base + Σ
    /// deltas) memory instead of O(N · base), and the per-row clone cost
    /// drops from O(positions) to O(1).
    ///
    /// The trade is real: booking and BQL aggregator mutations pay an
    /// O(log N) tree walk vs `Vec`'s amortized O(1) push. Measured impact
    /// scales with inventory size M: +85 ns/op at M=10, +1.6 µs/op at
    /// M=100, +19 µs/op at M=500 (criterion `reduce_fifo/*`). For typical
    /// small-M ledgers the overhead is sub-millisecond per `rledger
    /// check`; the users who feel it are users with very large inventories,
    /// the same users who hit the JOURNAL OOM today.
    ///
    /// `rkyv` derives were dropped because (a) `imbl::Vector` has no `rkyv`
    /// impl and (b) no code path currently archives an `Inventory`
    /// (confirmed in the `SmallVec` experiment for #1069). Pre-1.0 break;
    /// downstream callers archiving `Inventory` directly will need to
    /// archive `Vec<Position>` themselves. Serde wire format is unchanged
    /// (sequence-typed, identical for both backings).
    positions: Vector<Position>,
    /// Index for O(1) lookup of simple positions (no cost) by currency.
    /// Maps currency to position index in the `positions` vector.
    /// Not serialized - rebuilt on demand.
    #[serde(skip)]
    simple_index: FxHashMap<crate::Currency, usize>,
    /// Cache of total units per currency for O(1) `units()` lookups.
    /// Updated incrementally on `add()` and `reduce()`.
    /// Not serialized - rebuilt on demand.
    #[serde(skip)]
    units_cache: FxHashMap<crate::Currency, Decimal>,
}

impl PartialEq for Inventory {
    fn eq(&self, other: &Self) -> bool {
        // Only compare positions, not the index (which is derived data)
        self.positions == other.positions
    }
}

impl Eq for Inventory {}

impl Inventory {
    /// Create an empty inventory.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Iterate over all positions.
    ///
    /// Previously returned `&[Position]`; now returns an iterator
    /// because the underlying storage is a tree-based persistent
    /// vector (`imbl::Vector`) that doesn't expose a contiguous slice.
    /// Most callers already iterate — for callers that need
    /// random-access / indexed / `.len()` slice semantics, see
    /// [`Self::position_list`].
    pub fn positions(&self) -> impl Iterator<Item = &Position> + '_ {
        self.positions.iter()
    }

    /// Materialize all positions as a `Vec<&Position>` for slice-style
    /// access (indexing, `.len()`, `.first()`, `.is_empty()`).
    ///
    /// Allocates `O(N)` pointers per call. Callers that only iterate
    /// once should use [`Self::positions`] instead — this is for code
    /// paths that need slice semantics.
    #[must_use]
    pub fn position_list(&self) -> Vec<&Position> {
        self.positions.iter().collect()
    }

    /// Get mutable access to the underlying positions vector.
    ///
    /// Returns `&mut imbl::Vector<Position>` (was `&mut Vec<Position>`
    /// before issue #1086). `imbl::Vector` supports the same surface
    /// for `push_back`, `pop_back`, `retain`, indexed access, and
    /// iteration — but mutations are O(log N) with structural sharing
    /// instead of O(1) amortized.
    pub const fn positions_mut(&mut self) -> &mut Vector<Position> {
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
    /// Uses an internal cache for O(1) lookups.
    #[must_use]
    pub fn units(&self, currency: &str) -> Decimal {
        // Use cache if available, otherwise compute and the caller should
        // ensure cache is built via rebuild_caches() after deserialization
        self.units_cache.get(currency).copied().unwrap_or_else(|| {
            // Fallback to computation if cache miss (e.g., after deserialization)
            self.positions
                .iter()
                .filter(|p| p.units.currency == currency)
                .map(|p| p.units.number)
                .sum()
        })
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

    /// Check if the given units would reduce (not augment) this inventory.
    ///
    /// Returns `true` if there's a position with the same currency but opposite
    /// sign, meaning these units would reduce the inventory rather than add to it.
    ///
    /// When `has_cost_spec` is `true`, only positions **with** a cost basis are
    /// considered for reduction matching.  Simple (no-cost) positions are ignored
    /// because they live in a different "cost layer" — a sell-without-cost-spec
    /// that left a negative simple position should not cause a subsequent
    /// cost-bearing augmentation to be misclassified as a reduction.
    /// See: issue #875, beancount#889.
    ///
    /// This is used to determine whether a posting is a sale/reduction or a
    /// purchase/augmentation.
    #[must_use]
    pub fn is_reduced_by(&self, units: &Amount, scope: ReductionScope) -> bool {
        self.positions.iter().any(|pos| {
            pos.units.currency == units.currency
                && pos.units.number.is_sign_positive() != units.number.is_sign_positive()
                && match scope {
                    ReductionScope::AllPositions => true,
                    ReductionScope::CostBearingOnly => pos.cost.is_some(),
                }
        })
    }

    /// Get the total book value (cost basis) for a currency.
    ///
    /// Returns the sum of all cost bases for positions of the given currency.
    #[must_use]
    pub fn book_value(&self, units_currency: &str) -> FxHashMap<crate::Currency, Decimal> {
        let mut totals: FxHashMap<crate::Currency, Decimal> = FxHashMap::default();

        for pos in &self.positions {
            if pos.units.currency == units_currency
                && let Some(book) = pos.book_value()
            {
                *totals.entry(book.currency.clone()).or_default() += book.number;
            }
        }

        totals
    }

    /// Add a position to the inventory.
    ///
    /// For positions without cost, this merges with existing positions
    /// of the same currency using O(1) `HashMap` lookup.
    ///
    /// For positions with cost, this adds as a new lot (O(1)).
    /// Lot aggregation for display purposes is handled separately at output time
    /// (e.g., in the query result formatter).
    ///
    /// # TLA+ Specification
    ///
    /// Implements `AddAmount` action from `Conservation.tla`:
    /// - Invariant: `inventory + totalReduced = totalAdded`
    /// - After add: `totalAdded' = totalAdded + amount`
    ///
    /// See: `spec/tla/Conservation.tla`
    pub fn add(&mut self, position: Position) {
        if position.is_empty() {
            return;
        }

        // Update units cache
        *self
            .units_cache
            .entry(position.units.currency.clone())
            .or_default() += position.units.number;

        // For positions without cost, use index for O(1) lookup
        if position.cost.is_none() {
            if let Some(&idx) = self.simple_index.get(&position.units.currency) {
                // Merge with existing position
                debug_assert!(self.positions[idx].cost.is_none());
                self.positions[idx].units += &position.units;
                return;
            }
            // No existing position - add new one and index it
            let idx = self.positions.len();
            self.simple_index
                .insert(position.units.currency.clone(), idx);
            self.positions.push_back(position);
            return;
        }

        // For positions with cost, just add as a new lot.
        // This is O(1) and keeps all lots separate, matching Python beancount behavior.
        // Lot aggregation for display purposes is handled separately in query output.
        self.positions.push_back(position);
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
    ///
    /// # TLA+ Specification
    ///
    /// Implements `ReduceAmount` action from `Conservation.tla`:
    /// - Invariant: `inventory + totalReduced = totalAdded`
    /// - After reduce: `totalReduced' = totalReduced + amount`
    /// - Precondition: `amount <= inventory` (else `InsufficientUnits` error)
    ///
    /// Lot selection follows these TLA+ specs based on `method`:
    /// - `Fifo`: `FIFOCorrect.tla` - Oldest lots first (`selected_date <= all other dates`)
    /// - `Lifo`: `LIFOCorrect.tla` - Newest lots first (`selected_date >= all other dates`)
    /// - `Hifo`: `HIFOCorrect.tla` - Highest cost first (`selected_cost >= all other costs`)
    ///
    /// See: `spec/tla/Conservation.tla`, `spec/tla/FIFOCorrect.tla`, etc.
    pub fn reduce(
        &mut self,
        units: &Amount,
        cost_spec: Option<&CostSpec>,
        method: BookingMethod,
    ) -> Result<BookingResult, BookingError> {
        let spec = cost_spec.cloned().unwrap_or_default();

        // {*} merge operator: merge all lots into a single weighted-average-cost
        // lot before reducing, regardless of the account's booking method.
        if spec.merge {
            return self.reduce_merge(units);
        }

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

    /// Remove all empty positions.
    pub fn compact(&mut self) {
        self.positions.retain(|p| !p.is_empty());
        self.rebuild_index();
    }

    /// Rebuild all caches (`simple_index` and `units_cache`) from positions.
    /// Called after operations that may invalidate caches (like retain or deserialization).
    fn rebuild_index(&mut self) {
        self.simple_index.clear();
        self.units_cache.clear();

        for (idx, pos) in self.positions.iter().enumerate() {
            // Update units cache for all positions
            *self
                .units_cache
                .entry(pos.units.currency.clone())
                .or_default() += pos.units.number;

            // Update simple_index only for positions without cost
            if pos.cost.is_none() {
                debug_assert!(
                    !self.simple_index.contains_key(&pos.units.currency),
                    "Invariant violated: multiple simple positions for currency {}",
                    pos.units.currency
                );
                self.simple_index.insert(pos.units.currency.clone(), idx);
            }
        }
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

        // Sort positions alphabetically by currency, then by cost for consistency
        let mut non_empty: Vec<_> = self.positions.iter().filter(|p| !p.is_empty()).collect();
        non_empty.sort_by(|a, b| {
            // First by currency
            let cmp = a.units.currency.cmp(&b.units.currency);
            if cmp != std::cmp::Ordering::Equal {
                return cmp;
            }
            // Then by cost (if present)
            match (&a.cost, &b.cost) {
                (Some(ca), Some(cb)) => ca.number.cmp(&cb.number),
                (Some(_), None) => std::cmp::Ordering::Greater,
                (None, Some(_)) => std::cmp::Ordering::Less,
                (None, None) => std::cmp::Ordering::Equal,
            }
        });

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
    use crate::NaiveDate;
    use rust_decimal_macros::dec;

    fn date(year: i32, month: u32, day: u32) -> NaiveDate {
        crate::naive_date(year, month, day).unwrap()
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
    fn test_reduce_strict_multiple_match_with_different_costs_is_ambiguous() {
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(160.00), "USD").with_date(date(2024, 1, 15));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost2));

        // Per Python beancount: a wildcard reduction (`-3 AAPL` with no cost
        // spec) against an inventory with lots at different costs is
        // genuinely ambiguous and must error. Issue #737.
        let result = inv.reduce(&Amount::new(dec!(-3), "AAPL"), None, BookingMethod::Strict);

        assert!(
            matches!(result, Err(BookingError::AmbiguousMatch { .. })),
            "expected AmbiguousMatch, got {result:?}"
        );
        // Inventory unchanged after a failed reduction
        assert_eq!(inv.units("AAPL"), dec!(15));
    }

    #[test]
    fn test_reduce_strict_multiple_match_with_identical_costs_uses_fifo() {
        let mut inv = Inventory::new();

        // Two lots with identical cost — interchangeable, so FIFO is fine.
        let cost = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 1));

        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            cost.clone(),
        ));
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost));

        let result = inv
            .reduce(&Amount::new(dec!(-3), "AAPL"), None, BookingMethod::Strict)
            .expect("identical lots should fall back to FIFO without error");

        assert_eq!(inv.units("AAPL"), dec!(12));
        assert_eq!(result.cost_basis.unwrap().number, dec!(450.00));
    }

    #[test]
    fn test_reduce_strict_multiple_match_different_dates_same_cost_uses_fifo() {
        let mut inv = Inventory::new();

        // Two lots at the same cost number but different acquisition dates.
        // The user's cost spec could not have constrained the date without
        // naming it, so the lots are interchangeable for the spec — FIFO.
        let cost1 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 15));
        let cost2 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 2, 15));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2));

        let result = inv
            .reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Strict)
            .expect("same cost number, different dates should fall back to FIFO");

        assert_eq!(inv.units("AAPL"), dec!(15));
        // Reduced from the first (oldest) lot at 150.00 USD: 5 * 150 = 750.
        assert_eq!(result.cost_basis.unwrap().number, dec!(750.00));
    }

    #[test]
    fn test_reduce_strict_multiple_match_total_match_exception() {
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(160.00), "USD").with_date(date(2024, 1, 15));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost2));

        // Selling exactly the entire inventory (10 + 5 = 15) is unambiguous
        // even with mixed costs — the user is liquidating the position.
        let result = inv
            .reduce(&Amount::new(dec!(-15), "AAPL"), None, BookingMethod::Strict)
            .expect("total-match exception should accept a full liquidation");

        assert_eq!(inv.units("AAPL"), dec!(0));
        // Cost basis = 10*150 + 5*160 = 1500 + 800 = 2300
        assert_eq!(result.cost_basis.unwrap().number, dec!(2300.00));
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

    #[test]
    fn test_add_costed_positions_kept_separate() {
        // Costed positions are kept as separate lots for O(1) add performance.
        // Aggregation happens at display time (in query output).
        let mut inv = Inventory::new();

        let cost = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 1));

        // Buy 10 shares
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            cost.clone(),
        ));
        assert_eq!(inv.len(), 1);
        assert_eq!(inv.units("AAPL"), dec!(10));

        // Sell 10 shares - kept as separate lot for tracking
        inv.add(Position::with_cost(Amount::new(dec!(-10), "AAPL"), cost));
        assert_eq!(inv.len(), 2); // Both lots kept
        assert_eq!(inv.units("AAPL"), dec!(0)); // Net units still zero
    }

    #[test]
    fn test_add_costed_positions_net_units() {
        // Verify that units() correctly sums across all lots
        let mut inv = Inventory::new();

        let cost = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 1));

        // Buy 10 shares
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            cost.clone(),
        ));

        // Sell 3 shares - kept as separate lot
        inv.add(Position::with_cost(Amount::new(dec!(-3), "AAPL"), cost));
        assert_eq!(inv.len(), 2); // Both lots kept
        assert_eq!(inv.units("AAPL"), dec!(7)); // Net units correct
    }

    #[test]
    fn test_add_no_cancel_different_cost() {
        // Test that different costs don't cancel
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(160.00), "USD").with_date(date(2024, 1, 15));

        // Buy 10 shares at 150
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));

        // Sell 5 shares at 160 - should NOT cancel (different cost)
        inv.add(Position::with_cost(Amount::new(dec!(-5), "AAPL"), cost2));

        // Should have two separate lots
        assert_eq!(inv.len(), 2);
        assert_eq!(inv.units("AAPL"), dec!(5)); // 10 - 5 = 5 total
    }

    #[test]
    fn test_add_no_cancel_same_sign() {
        // Test that same-sign positions don't merge even with same cost
        let mut inv = Inventory::new();

        let cost = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 1));

        // Buy 10 shares
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            cost.clone(),
        ));

        // Buy 5 more shares with same cost - should NOT merge
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost));

        // Should have two separate lots (different acquisitions)
        assert_eq!(inv.len(), 2);
        assert_eq!(inv.units("AAPL"), dec!(15));
    }

    #[test]
    fn test_merge_keeps_lots_separate() {
        // Test that merge keeps costed lots separate (aggregation at display time)
        let mut inv1 = Inventory::new();
        let mut inv2 = Inventory::new();

        let cost = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 1));

        // inv1: buy 10 shares
        inv1.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            cost.clone(),
        ));

        // inv2: sell 10 shares
        inv2.add(Position::with_cost(Amount::new(dec!(-10), "AAPL"), cost));

        // Merge keeps both lots, net units is zero
        inv1.merge(&inv2);
        assert_eq!(inv1.len(), 2); // Both lots preserved
        assert_eq!(inv1.units("AAPL"), dec!(0)); // Net units correct
    }

    // ====================================================================
    // Phase 2: Additional Coverage Tests for Booking Methods
    // ====================================================================

    #[test]
    fn test_hifo_with_tie_breaking() {
        // When multiple lots have the same cost, HIFO should use insertion order
        let mut inv = Inventory::new();

        // Three lots with same cost but different dates
        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 2, 1));
        let cost3 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 3, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost3));

        // HIFO with tied costs should reduce in some deterministic order
        let result = inv
            .reduce(&Amount::new(dec!(-15), "AAPL"), None, BookingMethod::Hifo)
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(15));
        // All at same cost, so 15 * 100 = 1500
        assert_eq!(result.cost_basis.unwrap().number, dec!(1500.00));
    }

    #[test]
    fn test_hifo_with_different_costs() {
        // HIFO should reduce highest cost lots first
        let mut inv = Inventory::new();

        let cost_low = Cost::new(dec!(50.00), "USD").with_date(date(2024, 1, 1));
        let cost_mid = Cost::new(dec!(100.00), "USD").with_date(date(2024, 2, 1));
        let cost_high = Cost::new(dec!(200.00), "USD").with_date(date(2024, 3, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost_low));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost_mid));
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            cost_high,
        ));

        // Reduce 15 shares - should take from highest cost (200) first
        let result = inv
            .reduce(&Amount::new(dec!(-15), "AAPL"), None, BookingMethod::Hifo)
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(15));
        // 10 * 200 + 5 * 100 = 2000 + 500 = 2500
        assert_eq!(result.cost_basis.unwrap().number, dec!(2500.00));
    }

    #[test]
    fn test_average_booking_with_pre_existing_positions() {
        let mut inv = Inventory::new();

        // Add two lots with different costs
        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(200.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2));

        // Total: 20 shares, total cost = 10*100 + 10*200 = 3000, avg = 150/share
        // Reduce 5 shares using AVERAGE
        let result = inv
            .reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Average)
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(15));
        // Cost basis for 5 shares at average 150 = 750
        assert_eq!(result.cost_basis.unwrap().number, dec!(750.00));
    }

    #[test]
    fn test_average_booking_reduces_all() {
        let mut inv = Inventory::new();

        let cost = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost));

        // Reduce all shares
        let result = inv
            .reduce(
                &Amount::new(dec!(-10), "AAPL"),
                None,
                BookingMethod::Average,
            )
            .unwrap();

        assert!(inv.is_empty() || inv.units("AAPL").is_zero());
        assert_eq!(result.cost_basis.unwrap().number, dec!(1000.00));
    }

    #[test]
    fn test_none_booking_augmentation() {
        // NONE booking with same-sign amounts should augment, not reduce
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(100), "USD")));

        // Adding more (same sign) - this is an augmentation
        let result = inv
            .reduce(&Amount::new(dec!(50), "USD"), None, BookingMethod::None)
            .unwrap();

        assert_eq!(inv.units("USD"), dec!(150));
        assert!(result.matched.is_empty()); // No lots matched for augmentation
        assert!(result.cost_basis.is_none());
    }

    #[test]
    fn test_none_booking_reduction() {
        // NONE booking with opposite-sign should reduce
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(100), "USD")));

        let result = inv
            .reduce(&Amount::new(dec!(-30), "USD"), None, BookingMethod::None)
            .unwrap();

        assert_eq!(inv.units("USD"), dec!(70));
        assert!(!result.matched.is_empty());
    }

    #[test]
    fn test_none_booking_insufficient() {
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(100), "USD")));

        let result = inv.reduce(&Amount::new(dec!(-150), "USD"), None, BookingMethod::None);

        assert!(matches!(
            result,
            Err(BookingError::InsufficientUnits { .. })
        ));
    }

    #[test]
    fn test_booking_error_no_matching_lot() {
        let mut inv = Inventory::new();

        // Add a lot with specific cost
        let cost = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost));

        // Try to reduce with a cost spec that doesn't match
        let wrong_spec = CostSpec::empty().with_date(date(2024, 12, 31));
        let result = inv.reduce(
            &Amount::new(dec!(-5), "AAPL"),
            Some(&wrong_spec),
            BookingMethod::Strict,
        );

        assert!(matches!(result, Err(BookingError::NoMatchingLot { .. })));
    }

    #[test]
    fn test_booking_error_insufficient_units() {
        let mut inv = Inventory::new();

        let cost = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost));

        // Try to reduce more than available
        let result = inv.reduce(&Amount::new(dec!(-20), "AAPL"), None, BookingMethod::Fifo);

        match result {
            Err(BookingError::InsufficientUnits {
                requested,
                available,
                ..
            }) => {
                assert_eq!(requested, dec!(20));
                assert_eq!(available, dec!(10));
            }
            _ => panic!("Expected InsufficientUnits error"),
        }
    }

    #[test]
    fn test_strict_with_size_exact_match() {
        let mut inv = Inventory::new();

        // Add two lots with same cost but different sizes
        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost2));

        // Reduce exactly 5 - should match the 5-share lot
        let result = inv
            .reduce(
                &Amount::new(dec!(-5), "AAPL"),
                None,
                BookingMethod::StrictWithSize,
            )
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(10));
        assert_eq!(result.cost_basis.unwrap().number, dec!(500.00));
    }

    #[test]
    fn test_strict_with_size_total_match() {
        let mut inv = Inventory::new();

        // Add two lots
        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost2));

        // Reduce exactly 15 (total) - should succeed via total match exception
        let result = inv
            .reduce(
                &Amount::new(dec!(-15), "AAPL"),
                None,
                BookingMethod::StrictWithSize,
            )
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(0));
        assert_eq!(result.cost_basis.unwrap().number, dec!(1500.00));
    }

    #[test]
    fn test_strict_with_size_ambiguous() {
        let mut inv = Inventory::new();

        // Add two lots of same size and cost
        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2));

        // Reduce 7 shares - doesn't match either lot exactly, not total
        let result = inv.reduce(
            &Amount::new(dec!(-7), "AAPL"),
            None,
            BookingMethod::StrictWithSize,
        );

        assert!(matches!(result, Err(BookingError::AmbiguousMatch { .. })));
    }

    #[test]
    fn test_short_position() {
        // Test short selling (negative positions)
        let mut inv = Inventory::new();

        // Short 10 shares
        let cost = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        inv.add(Position::with_cost(Amount::new(dec!(-10), "AAPL"), cost));

        assert_eq!(inv.units("AAPL"), dec!(-10));
        assert!(!inv.is_empty());
    }

    #[test]
    fn test_at_cost() {
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost2));
        inv.add(Position::simple(Amount::new(dec!(100), "USD")));

        let at_cost = inv.at_cost();

        // AAPL converted: 10*100 + 5*150 = 1000 + 750 = 1750 USD
        // Plus 100 USD simple position = 1850 USD total
        assert_eq!(at_cost.units("USD"), dec!(1850));
        assert_eq!(at_cost.units("AAPL"), dec!(0)); // No AAPL in cost view
    }

    #[test]
    fn test_at_units() {
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost2));

        let at_units = inv.at_units();

        // All AAPL lots merged
        assert_eq!(at_units.units("AAPL"), dec!(15));
        // Should only have one position after aggregation
        assert_eq!(at_units.len(), 1);
    }

    #[test]
    fn test_add_empty_position() {
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(0), "USD")));

        assert!(inv.is_empty());
        assert_eq!(inv.len(), 0);
    }

    #[test]
    fn test_compact() {
        let mut inv = Inventory::new();

        let cost = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost));

        // Reduce all
        inv.reduce(&Amount::new(dec!(-10), "AAPL"), None, BookingMethod::Fifo)
            .unwrap();

        // Compact to remove empty positions
        inv.compact();
        assert!(inv.is_empty());
        assert_eq!(inv.len(), 0);
    }

    #[test]
    fn test_booking_method_from_str() {
        assert_eq!(
            BookingMethod::from_str("STRICT").unwrap(),
            BookingMethod::Strict
        );
        assert_eq!(
            BookingMethod::from_str("fifo").unwrap(),
            BookingMethod::Fifo
        );
        assert_eq!(
            BookingMethod::from_str("LIFO").unwrap(),
            BookingMethod::Lifo
        );
        assert_eq!(
            BookingMethod::from_str("Hifo").unwrap(),
            BookingMethod::Hifo
        );
        assert_eq!(
            BookingMethod::from_str("AVERAGE").unwrap(),
            BookingMethod::Average
        );
        assert_eq!(
            BookingMethod::from_str("NONE").unwrap(),
            BookingMethod::None
        );
        assert_eq!(
            BookingMethod::from_str("strict_with_size").unwrap(),
            BookingMethod::StrictWithSize
        );
        assert!(BookingMethod::from_str("INVALID").is_err());
    }

    #[test]
    fn test_booking_method_display() {
        assert_eq!(format!("{}", BookingMethod::Strict), "STRICT");
        assert_eq!(format!("{}", BookingMethod::Fifo), "FIFO");
        assert_eq!(format!("{}", BookingMethod::Lifo), "LIFO");
        assert_eq!(format!("{}", BookingMethod::Hifo), "HIFO");
        assert_eq!(format!("{}", BookingMethod::Average), "AVERAGE");
        assert_eq!(format!("{}", BookingMethod::None), "NONE");
        assert_eq!(
            format!("{}", BookingMethod::StrictWithSize),
            "STRICT_WITH_SIZE"
        );
    }

    #[test]
    fn test_booking_error_display() {
        let err = BookingError::AmbiguousMatch {
            num_matches: 3,
            currency: "AAPL".into(),
        };
        assert!(format!("{err}").contains("3 lots match"));

        let err = BookingError::NoMatchingLot {
            currency: "AAPL".into(),
            cost_spec: CostSpec::empty(),
        };
        assert!(format!("{err}").contains("No matching lot"));

        let err = BookingError::InsufficientUnits {
            currency: "AAPL".into(),
            requested: dec!(100),
            available: dec!(50),
        };
        assert!(format!("{err}").contains("requested 100"));
        assert!(format!("{err}").contains("available 50"));

        let err = BookingError::CurrencyMismatch {
            expected: "USD".into(),
            got: "EUR".into(),
        };
        assert!(format!("{err}").contains("expected USD"));
        assert!(format!("{err}").contains("got EUR"));
    }

    #[test]
    fn test_book_value_multiple_currencies() {
        let mut inv = Inventory::new();

        // Cost in USD
        let cost_usd = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost_usd));

        // Cost in EUR
        let cost_eur = Cost::new(dec!(90.00), "EUR").with_date(date(2024, 2, 1));
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost_eur));

        let book = inv.book_value("AAPL");
        assert_eq!(book.get("USD"), Some(&dec!(1000.00)));
        assert_eq!(book.get("EUR"), Some(&dec!(450.00)));
    }

    #[test]
    fn test_reduce_hifo_insufficient_units() {
        let mut inv = Inventory::new();

        let cost = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost));

        let result = inv.reduce(&Amount::new(dec!(-20), "AAPL"), None, BookingMethod::Hifo);

        assert!(matches!(
            result,
            Err(BookingError::InsufficientUnits { .. })
        ));
    }

    #[test]
    fn test_reduce_average_insufficient_units() {
        let mut inv = Inventory::new();

        let cost = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost));

        let result = inv.reduce(
            &Amount::new(dec!(-20), "AAPL"),
            None,
            BookingMethod::Average,
        );

        assert!(matches!(
            result,
            Err(BookingError::InsufficientUnits { .. })
        ));
    }

    #[test]
    fn test_reduce_average_empty_inventory() {
        let mut inv = Inventory::new();

        let result = inv.reduce(
            &Amount::new(dec!(-10), "AAPL"),
            None,
            BookingMethod::Average,
        );

        assert!(matches!(
            result,
            Err(BookingError::InsufficientUnits { .. })
        ));
    }

    #[test]
    fn test_reduce_merge_operator() {
        // {*} merge: two lots merged into weighted-average, then reduced
        let mut inv = Inventory::new();
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(150), "USD"),
        ));
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(160), "USD"),
        ));

        let merge_spec = CostSpec::empty().with_merge();
        let result = inv
            .reduce(
                &Amount::new(dec!(-5), "AAPL"),
                Some(&merge_spec),
                BookingMethod::Strict,
            )
            .expect("merge reduction should succeed");

        // Cost basis: 5 units * 155 USD average = 775 USD
        assert_eq!(result.cost_basis, Some(Amount::new(dec!(775), "USD")));

        // Inventory should have a single merged lot with 15 remaining @ 155
        assert_eq!(inv.positions.len(), 1);
        assert_eq!(inv.positions[0].units.number, dec!(15));
        let cost = inv.positions[0].cost.as_ref().expect("should have cost");
        assert_eq!(cost.number, dec!(155));
    }

    #[test]
    fn test_reduce_merge_insufficient_units() {
        let mut inv = Inventory::new();
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(150), "USD"),
        ));

        let merge_spec = CostSpec::empty().with_merge();
        let result = inv.reduce(
            &Amount::new(dec!(-20), "AAPL"),
            Some(&merge_spec),
            BookingMethod::Strict,
        );

        assert!(matches!(
            result,
            Err(BookingError::InsufficientUnits { .. })
        ));
    }

    #[test]
    fn test_reduce_merge_sells_all() {
        // Merge and sell entire position
        let mut inv = Inventory::new();
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(150), "USD"),
        ));
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(160), "USD"),
        ));

        let merge_spec = CostSpec::empty().with_merge();
        let result = inv
            .reduce(
                &Amount::new(dec!(-20), "AAPL"),
                Some(&merge_spec),
                BookingMethod::Strict,
            )
            .expect("merge reduction should succeed");

        // Cost basis: 20 * 155 = 3100 USD
        assert_eq!(result.cost_basis, Some(Amount::new(dec!(3100), "USD")));

        // Inventory should be empty
        assert!(inv.positions.is_empty() || inv.positions.iter().all(Position::is_empty));
    }

    #[test]
    fn test_reduce_merge_single_lot() {
        // {*} with a single lot should work trivially
        let mut inv = Inventory::new();
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(150), "USD"),
        ));

        let merge_spec = CostSpec::empty().with_merge();
        let result = inv
            .reduce(
                &Amount::new(dec!(-3), "AAPL"),
                Some(&merge_spec),
                BookingMethod::Strict,
            )
            .expect("single-lot merge should succeed");

        assert_eq!(result.cost_basis, Some(Amount::new(dec!(450), "USD")));
        assert_eq!(inv.positions.len(), 1);
        assert_eq!(inv.positions[0].units.number, dec!(7));
    }

    #[test]
    fn test_reduce_merge_three_lots() {
        // {*} with three lots at different costs
        let mut inv = Inventory::new();
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(100), "USD"),
        ));
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(150), "USD"),
        ));
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(200), "USD"),
        ));

        // Average cost: (1000 + 1500 + 2000) / 30 = 150 USD
        let merge_spec = CostSpec::empty().with_merge();
        let result = inv
            .reduce(
                &Amount::new(dec!(-6), "AAPL"),
                Some(&merge_spec),
                BookingMethod::Strict,
            )
            .expect("three-lot merge should succeed");

        assert_eq!(result.cost_basis, Some(Amount::new(dec!(900), "USD")));
        assert_eq!(inv.positions.len(), 1);
        assert_eq!(inv.positions[0].units.number, dec!(24));
        let cost = inv.positions[0].cost.as_ref().expect("should have cost");
        assert_eq!(cost.number, dec!(150));
    }

    #[test]
    fn test_reduce_merge_mixed_cost_currencies_errors() {
        // Lots with different cost currencies cannot be merged
        let mut inv = Inventory::new();
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(150), "USD"),
        ));
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(130), "EUR"),
        ));

        let merge_spec = CostSpec::empty().with_merge();
        let result = inv.reduce(
            &Amount::new(dec!(-5), "AAPL"),
            Some(&merge_spec),
            BookingMethod::Strict,
        );

        assert!(
            matches!(result, Err(BookingError::CurrencyMismatch { .. })),
            "expected CurrencyMismatch, got {result:?}"
        );
    }

    #[test]
    fn test_reduce_merge_empty_inventory() {
        let mut inv = Inventory::new();

        let merge_spec = CostSpec::empty().with_merge();
        let result = inv.reduce(
            &Amount::new(dec!(-5), "AAPL"),
            Some(&merge_spec),
            BookingMethod::Strict,
        );

        assert!(matches!(
            result,
            Err(BookingError::InsufficientUnits { .. })
        ));
    }

    #[test]
    fn test_inventory_display_sorted() {
        let mut inv = Inventory::new();

        // Add in non-alphabetical order
        inv.add(Position::simple(Amount::new(dec!(100), "USD")));
        inv.add(Position::simple(Amount::new(dec!(50), "EUR")));
        inv.add(Position::simple(Amount::new(dec!(10), "AAPL")));

        let display = format!("{inv}");

        // Should be sorted alphabetically: AAPL, EUR, USD
        let aapl_pos = display.find("AAPL").unwrap();
        let eur_pos = display.find("EUR").unwrap();
        let usd_pos = display.find("USD").unwrap();

        assert!(aapl_pos < eur_pos);
        assert!(eur_pos < usd_pos);
    }

    #[test]
    fn test_inventory_with_cost_display_sorted() {
        let mut inv = Inventory::new();

        // Add same currency with different costs
        let cost_high = Cost::new(dec!(200.00), "USD").with_date(date(2024, 1, 1));
        let cost_low = Cost::new(dec!(100.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            cost_high,
        ));
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost_low));

        let display = format!("{inv}");

        // Both positions should be in the output
        assert!(display.contains("AAPL"));
        assert!(display.contains("100"));
        assert!(display.contains("200"));
    }

    #[test]
    fn test_reduce_hifo_no_matching_lot() {
        let mut inv = Inventory::new();

        // No AAPL positions
        inv.add(Position::simple(Amount::new(dec!(100), "USD")));

        let result = inv.reduce(&Amount::new(dec!(-10), "AAPL"), None, BookingMethod::Hifo);

        assert!(matches!(result, Err(BookingError::NoMatchingLot { .. })));
    }

    #[test]
    fn test_fifo_respects_dates() {
        // Ensure FIFO uses acquisition date, not insertion order
        let mut inv = Inventory::new();

        // Add newer lot first (out of order)
        let cost_new = Cost::new(dec!(200.00), "USD").with_date(date(2024, 3, 1));
        let cost_old = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost_new));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost_old));

        // FIFO should reduce from oldest (cost 100) first
        let result = inv
            .reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Fifo)
            .unwrap();

        // Should use cost from oldest lot (100)
        assert_eq!(result.cost_basis.unwrap().number, dec!(500.00));
    }

    #[test]
    fn test_lifo_respects_dates() {
        // Ensure LIFO uses acquisition date, not insertion order
        let mut inv = Inventory::new();

        // Add older lot first
        let cost_old = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost_new = Cost::new(dec!(200.00), "USD").with_date(date(2024, 3, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost_old));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost_new));

        // LIFO should reduce from newest (cost 200) first
        let result = inv
            .reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Lifo)
            .unwrap();

        // Should use cost from newest lot (200)
        assert_eq!(result.cost_basis.unwrap().number, dec!(1000.00));
    }

    // =========================================================================
    // Booking method coverage tests
    //
    // These tests cover gaps identified during the spring 2026 audit:
    // - STRICT_WITH_SIZE: cost spec + exact-size, multiple exact-size matches
    // - HIFO: multi-lot ordering, partial reduction, cost spec filtering
    // - AVERAGE: weighted average with different costs, partial reduction preserves cost
    // - NONE: with cost positions, short position reduction
    // =========================================================================

    // --- STRICT_WITH_SIZE ---

    #[test]
    fn test_strict_with_size_different_costs_exact_match() {
        // When lots have different costs but one matches the reduction size exactly,
        // STRICT_WITH_SIZE should pick that lot instead of raising AmbiguousMatch
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(200.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
        inv.add(Position::with_cost(Amount::new(dec!(7), "AAPL"), cost2));

        // Reduce exactly 7 - should match the 7-share lot at cost 200
        let result = inv
            .reduce(
                &Amount::new(dec!(-7), "AAPL"),
                None,
                BookingMethod::StrictWithSize,
            )
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(10));
        assert_eq!(result.cost_basis.unwrap().number, dec!(1400.00)); // 7 * 200
    }

    #[test]
    fn test_strict_with_size_multiple_exact_matches_picks_oldest() {
        // When multiple lots have the exact same size, STRICT_WITH_SIZE should
        // pick the oldest one (first in index order)
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(200.00), "USD").with_date(date(2024, 6, 1));

        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost1));
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost2));

        // Both lots are size 5 — should pick the first (oldest) one
        let result = inv
            .reduce(
                &Amount::new(dec!(-5), "AAPL"),
                None,
                BookingMethod::StrictWithSize,
            )
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(5));
        // Should use cost from the oldest lot (100)
        assert_eq!(result.cost_basis.unwrap().number, dec!(500.00));
    }

    #[test]
    fn test_strict_with_size_with_cost_spec() {
        // Cost spec should filter lots before exact-size matching
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(200.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2));

        // With cost spec filtering to the 200 USD lot, should find unique match
        let spec = CostSpec::empty().with_number(crate::CostNumber::PerUnit {
            value: dec!(200.00),
        });
        let result = inv
            .reduce(
                &Amount::new(dec!(-5), "AAPL"),
                Some(&spec),
                BookingMethod::StrictWithSize,
            )
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(15));
        assert_eq!(result.cost_basis.unwrap().number, dec!(1000.00)); // 5 * 200
    }

    // --- HIFO ---

    #[test]
    fn test_hifo_reduces_highest_cost_first() {
        // HIFO should reduce the highest-cost lot first, regardless of date
        let mut inv = Inventory::new();

        let cost_low = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost_mid = Cost::new(dec!(150.00), "USD").with_date(date(2024, 2, 1));
        let cost_high = Cost::new(dec!(200.00), "USD").with_date(date(2024, 3, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost_low));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost_mid));
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            cost_high,
        ));

        // Reduce 5 — should come from highest cost lot (200)
        let result = inv
            .reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Hifo)
            .unwrap();

        assert_eq!(result.cost_basis.unwrap().number, dec!(1000.00)); // 5 * 200
        assert_eq!(inv.units("AAPL"), dec!(25));
    }

    #[test]
    fn test_hifo_spans_multiple_lots() {
        // When reducing more than the highest-cost lot holds, HIFO should
        // continue to the next highest
        let mut inv = Inventory::new();

        let cost_low = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost_high = Cost::new(dec!(200.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost_low));
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost_high));

        // Reduce 8: 5 from high (200) + 3 from low (100)
        let result = inv
            .reduce(&Amount::new(dec!(-8), "AAPL"), None, BookingMethod::Hifo)
            .unwrap();

        // Cost basis: 5*200 + 3*100 = 1300
        assert_eq!(result.cost_basis.unwrap().number, dec!(1300.00));
        assert_eq!(inv.units("AAPL"), dec!(2));
    }

    #[test]
    fn test_hifo_with_cost_spec_filter() {
        // Cost spec should filter lots before HIFO ordering
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(200.00), "EUR").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2));

        // Filter to USD lots only
        let spec = CostSpec::empty().with_currency("USD");
        let result = inv
            .reduce(
                &Amount::new(dec!(-5), "AAPL"),
                Some(&spec),
                BookingMethod::Hifo,
            )
            .unwrap();

        assert_eq!(result.cost_basis.unwrap().number, dec!(500.00)); // 5 * 100 USD
    }

    #[test]
    fn test_hifo_short_position() {
        // HIFO with short positions: covering shorts should work correctly
        let mut inv = Inventory::new();

        let cost_low = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost_high = Cost::new(dec!(200.00), "USD").with_date(date(2024, 2, 1));

        // Short positions (negative units)
        inv.add(Position::with_cost(
            Amount::new(dec!(-10), "AAPL"),
            cost_low,
        ));
        inv.add(Position::with_cost(
            Amount::new(dec!(-10), "AAPL"),
            cost_high,
        ));

        // Cover 5 shares (positive = reduce short position)
        // HIFO should pick the highest-cost short lot (200)
        let result = inv
            .reduce(&Amount::new(dec!(5), "AAPL"), None, BookingMethod::Hifo)
            .unwrap();

        assert_eq!(result.cost_basis.unwrap().number, dec!(1000.00)); // 5 * 200
        assert_eq!(inv.units("AAPL"), dec!(-15));
    }

    // --- AVERAGE ---

    #[test]
    fn test_average_weighted_cost() {
        // AVERAGE should compute weighted average across lots with different costs
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(200.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2));

        // Average cost = (10*100 + 10*200) / 20 = 150
        let result = inv
            .reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Average)
            .unwrap();

        // Cost basis: 5 * 150 = 750
        assert_eq!(result.cost_basis.unwrap().number, dec!(750.00));
        assert_eq!(inv.units("AAPL"), dec!(15));
    }

    #[test]
    fn test_average_merges_into_single_position() {
        // After AVERAGE reduction, inventory should have a single simple position
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(200.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2));

        inv.reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Average)
            .unwrap();

        // Should have exactly one AAPL position remaining
        let aapl_positions: Vec<_> = inv
            .positions
            .iter()
            .filter(|p| p.units.currency.as_ref() == "AAPL")
            .collect();
        assert_eq!(aapl_positions.len(), 1);
        assert_eq!(aapl_positions[0].units.number, dec!(15));
    }

    #[test]
    fn test_average_uneven_lots() {
        // Weighted average with unequal lot sizes
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(200.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(30), "AAPL"), cost1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2));

        // Average cost = (30*100 + 10*200) / 40 = 5000/40 = 125
        let result = inv
            .reduce(
                &Amount::new(dec!(-10), "AAPL"),
                None,
                BookingMethod::Average,
            )
            .unwrap();

        assert_eq!(result.cost_basis.unwrap().number, dec!(1250.00)); // 10 * 125
    }

    // --- NONE ---

    #[test]
    fn test_none_booking_with_cost_positions() {
        // NONE booking should work even when positions have costs
        let mut inv = Inventory::new();

        let cost = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost));

        let result = inv
            .reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::None)
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(5));
        // NONE delegates to reduce_ordered (FIFO) internally, so cost basis is computed
        assert!(result.cost_basis.is_some());
        assert_eq!(result.cost_basis.unwrap().number, dec!(500.00));
    }

    #[test]
    fn test_none_booking_short_cover() {
        // Covering a short position with NONE booking
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(-100), "USD")));

        // Positive amount should reduce the negative position
        let result = inv
            .reduce(&Amount::new(dec!(30), "USD"), None, BookingMethod::None)
            .unwrap();

        assert_eq!(inv.units("USD"), dec!(-70));
        assert!(!result.matched.is_empty());
    }

    #[test]
    fn test_none_booking_empty_inventory_augments() {
        // NONE booking on empty inventory should augment
        let mut inv = Inventory::new();

        let result = inv
            .reduce(&Amount::new(dec!(50), "USD"), None, BookingMethod::None)
            .unwrap();

        assert_eq!(inv.units("USD"), dec!(50));
        assert!(result.matched.is_empty()); // Augmentation, not reduction
    }

    // --- Cross-method: short positions ---

    #[test]
    fn test_fifo_short_position_cover() {
        // FIFO: cover short positions (oldest short first)
        let mut inv = Inventory::new();

        let cost_old = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost_new = Cost::new(dec!(200.00), "USD").with_date(date(2024, 3, 1));

        inv.add(Position::with_cost(
            Amount::new(dec!(-10), "AAPL"),
            cost_old,
        ));
        inv.add(Position::with_cost(
            Amount::new(dec!(-10), "AAPL"),
            cost_new,
        ));

        // Cover 5 shares — FIFO should pick oldest short (cost 100)
        let result = inv
            .reduce(&Amount::new(dec!(5), "AAPL"), None, BookingMethod::Fifo)
            .unwrap();

        assert_eq!(result.cost_basis.unwrap().number, dec!(500.00)); // 5 * 100
        assert_eq!(inv.units("AAPL"), dec!(-15));
    }

    #[test]
    fn test_lifo_short_position_cover() {
        // LIFO: cover short positions (newest short first)
        let mut inv = Inventory::new();

        let cost_old = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost_new = Cost::new(dec!(200.00), "USD").with_date(date(2024, 3, 1));

        inv.add(Position::with_cost(
            Amount::new(dec!(-10), "AAPL"),
            cost_old,
        ));
        inv.add(Position::with_cost(
            Amount::new(dec!(-10), "AAPL"),
            cost_new,
        ));

        // Cover 5 shares — LIFO should pick newest short (cost 200)
        let result = inv
            .reduce(&Amount::new(dec!(5), "AAPL"), None, BookingMethod::Lifo)
            .unwrap();

        assert_eq!(result.cost_basis.unwrap().number, dec!(1000.00)); // 5 * 200
        assert_eq!(inv.units("AAPL"), dec!(-15));
    }

    // === AccountedBookingError Display tests ===
    //
    // These tests pin the canonical user-facing wording for every variant
    // of `AccountedBookingError`. The whole point of unifying booking-error
    // Display into `rustledger-core` (#750) is that there's a single source
    // of truth — and a single source of truth with no tests is one refactor
    // away from drifting again, which is exactly the failure mode that
    // produced #748. Any change to the Display strings below will break
    // these tests, forcing the author to consciously re-check pta-standards
    // conformance assertions and downstream user tooling.

    // =========================================================================
    // Regression test for issue #875 / beancount#889
    //
    // When a sell-without-cost-spec leaves a negative simple position in the
    // inventory, a subsequent augmentation WITH a cost spec should NOT be
    // misclassified as a reduction. `is_reduced_by` must only consider
    // cost-bearing positions when the incoming posting has a cost spec.
    // =========================================================================

    #[test]
    fn test_is_reduced_by_ignores_simple_positions_when_has_cost_spec() {
        // Regression test for issue #875 / beancount#889.
        //
        // Scenario:
        //   1. Buy 100 HOOG {1.50 EUR}  -> inventory: [100 HOOG {1.50 EUR}]
        //   2. Sell 25 HOOG @ 1.60 EUR   -> inventory: [100 HOOG {1.50 EUR}, -25 HOOG (simple)]
        //   3. Buy 50 HOOG {1.70 EUR}    -> should be augmentation, NOT reduction
        //
        // Before fix: is_reduced_by saw the -25 HOOG simple position and
        // incorrectly reported that +50 HOOG would reduce the inventory.
        let mut inv = Inventory::new();

        // Step 1: buy 100 HOOG with cost
        let cost = Cost::new(dec!(1.50), "EUR").with_date(date(2024, 1, 10));
        inv.add(Position::with_cost(Amount::new(dec!(100), "HOOG"), cost));

        // Step 2: sell 25 HOOG without cost spec (simple position)
        inv.add(Position::simple(Amount::new(dec!(-25), "HOOG")));

        // Step 3: check if buying 50 HOOG with cost spec would be a reduction
        let buy_units = Amount::new(dec!(50), "HOOG");

        // With has_cost_spec=true, only cost-bearing positions should be
        // considered. The 100 HOOG {1.50 EUR} is positive and so is the
        // incoming 50 HOOG -> same sign -> NOT a reduction.
        assert!(
            !inv.is_reduced_by(&buy_units, ReductionScope::CostBearingOnly),
            "augmentation with cost spec should NOT be treated as reduction \
             when only a simple (no-cost) position has opposite sign"
        );

        // With AllPositions, all positions are considered,
        // including the -25 HOOG simple position -> IS a reduction.
        assert!(
            inv.is_reduced_by(&buy_units, ReductionScope::AllPositions),
            "without cost spec filter, the -25 HOOG simple position \
             should cause is_reduced_by to return true"
        );
    }

    #[test]
    fn test_accounted_error_display_insufficient_units() {
        let err = BookingError::InsufficientUnits {
            currency: "AAPL".into(),
            requested: dec!(15),
            available: dec!(10),
        }
        .with_account("Assets:Stock".into());
        let rendered = format!("{err}");

        // Pinned by pta-standards `reduction-exceeds-inventory`
        // (`error_contains: ["not enough"]`). See #748 / #749.
        assert!(
            rendered.contains("not enough"),
            "must contain 'not enough' (pta-standards): {rendered}"
        );
        assert!(
            rendered.contains("Assets:Stock"),
            "must contain account name: {rendered}"
        );
        assert!(
            rendered.contains("15") && rendered.contains("10"),
            "must contain requested and available amounts: {rendered}"
        );
    }

    #[test]
    fn test_accounted_error_display_no_matching_lot() {
        let err = BookingError::NoMatchingLot {
            currency: "AAPL".into(),
            cost_spec: CostSpec::empty(),
        }
        .with_account("Assets:Stock".into());
        let rendered = format!("{err}");

        assert!(
            rendered.contains("No matching lot"),
            "must contain 'No matching lot': {rendered}"
        );
        assert!(
            rendered.contains("AAPL"),
            "must contain currency: {rendered}"
        );
        assert!(
            rendered.contains("Assets:Stock"),
            "must contain account name: {rendered}"
        );
    }

    #[test]
    fn test_accounted_error_display_ambiguous_match() {
        let err = BookingError::AmbiguousMatch {
            num_matches: 3,
            currency: "AAPL".into(),
        }
        .with_account("Assets:Stock".into());
        let rendered = format!("{err}");

        assert!(
            rendered.contains("Ambiguous"),
            "must contain 'Ambiguous': {rendered}"
        );
        assert!(
            rendered.contains("AAPL"),
            "must contain currency: {rendered}"
        );
        assert!(
            rendered.contains("Assets:Stock"),
            "must contain account name: {rendered}"
        );
        assert!(
            rendered.contains('3'),
            "must contain match count: {rendered}"
        );
    }

    #[test]
    fn test_accounted_error_display_currency_mismatch_renders_as_no_matching_lot() {
        // CurrencyMismatch is semantically a specialization of NoMatchingLot
        // (there is no lot for the given currency in this inventory) and the
        // canonical Display collapses them into the same user-facing phrasing
        // so that consumers filtering on E4001 don't need to special-case it.
        // This variant is defensive — no `Inventory::reduce` path currently
        // emits it — but we still pin its rendering in case a future emission
        // site is added.
        let err = BookingError::CurrencyMismatch {
            expected: "USD".into(),
            got: "EUR".into(),
        }
        .with_account("Assets:Cash".into());
        let rendered = format!("{err}");

        assert!(
            rendered.contains("No matching lot"),
            "CurrencyMismatch must render as 'No matching lot' for E4001 \
             consistency: {rendered}"
        );
        assert!(
            rendered.contains("EUR"),
            "must contain the mismatched (got) currency: {rendered}"
        );
        assert!(
            rendered.contains("Assets:Cash"),
            "must contain account name: {rendered}"
        );
    }
}
