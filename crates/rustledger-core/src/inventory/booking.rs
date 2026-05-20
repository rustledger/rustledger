//! Booking method implementations for Inventory.
//!
//! This module contains the implementation of all booking methods (STRICT, FIFO,
//! LIFO, HIFO, AVERAGE, NONE) used to reduce positions from an inventory.

use rust_decimal::Decimal;
use rust_decimal::prelude::Signed;

use smallvec::{SmallVec, smallvec};

use super::{BookingError, BookingMethod, BookingResult, Inventory, MatchedLots};
use crate::{Amount, Cost, CostSpec, Currency, Position};

/// Compute weighted-average cost from a set of positions.
///
/// Returns `(avg_cost_per_unit, cost_currency)` or `None` if no positions have cost info.
/// Returns `Err(CurrencyMismatch)` if positions have costs in different currencies.
fn average_cost_from_positions(
    positions: &[&Position],
    total_units: Decimal,
) -> Result<Option<(Decimal, Currency)>, BookingError> {
    let mut total_cost = Decimal::ZERO;
    let mut cost_currency: Option<Currency> = None;
    let mut has_any_cost = false;

    for pos in positions {
        if let Some(cost) = &pos.cost {
            has_any_cost = true;
            if let Some(ref cc) = cost_currency {
                if *cc != cost.currency {
                    return Err(BookingError::CurrencyMismatch {
                        expected: cc.clone(),
                        got: cost.currency.clone(),
                    });
                }
            } else {
                cost_currency = Some(cost.currency.clone());
            }
            total_cost += pos.units.number * cost.number;
        }
    }

    if !has_any_cost || cost_currency.is_none() {
        return Ok(None);
    }

    Ok(Some((total_cost / total_units, cost_currency.unwrap())))
}

impl Inventory {
    /// Try reducing positions without modifying the inventory.
    ///
    /// This is a read-only version of `reduce()` that returns what would be matched
    /// without actually modifying the inventory. Useful for previewing booking results
    /// before committing.
    ///
    /// # Arguments
    ///
    /// * `units` - The units to reduce (negative for selling)
    /// * `cost_spec` - Optional cost specification for matching lots
    /// * `method` - The booking method to use
    ///
    /// # Returns
    ///
    /// Returns a `BookingResult` with the positions that would be matched and cost basis,
    /// or a `BookingError` if the reduction cannot be performed.
    pub fn try_reduce(
        &self,
        units: &Amount,
        cost_spec: Option<&CostSpec>,
        method: BookingMethod,
    ) -> Result<BookingResult, BookingError> {
        let spec = cost_spec.cloned().unwrap_or_default();

        // {*} merge operator: use average-cost semantics (read-only preview)
        if spec.merge {
            return self.try_reduce_average(units);
        }

        match method {
            BookingMethod::Strict | BookingMethod::StrictWithSize => {
                self.try_reduce_strict(units, &spec, method == BookingMethod::StrictWithSize)
            }
            BookingMethod::Fifo => self.try_reduce_ordered(units, &spec, false),
            BookingMethod::Lifo => self.try_reduce_ordered(units, &spec, true),
            BookingMethod::Hifo => self.try_reduce_hifo(units, &spec),
            BookingMethod::Average => self.try_reduce_average(units),
            BookingMethod::None => self.try_reduce_ordered(units, &CostSpec::default(), false),
        }
    }

    /// Try `STRICT`/`STRICT_WITH_SIZE` booking without modifying inventory.
    fn try_reduce_strict(
        &self,
        units: &Amount,
        spec: &CostSpec,
        with_size: bool,
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
                self.try_reduce_from_lot(idx, units)
            }
            n => {
                if with_size {
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
                            self.try_reduce_ordered(units, spec, false)
                        } else {
                            Err(BookingError::AmbiguousMatch {
                                num_matches: n,
                                currency: units.currency.clone(),
                            })
                        }
                    } else {
                        let idx = exact_matches[0];
                        self.try_reduce_from_lot(idx, units)
                    }
                } else {
                    // STRICT: fall back to FIFO when multiple match
                    self.try_reduce_ordered(units, spec, false)
                }
            }
        }
    }

    /// Try ordered (FIFO/LIFO) booking without modifying inventory.
    fn try_reduce_ordered(
        &self,
        units: &Amount,
        spec: &CostSpec,
        reverse: bool,
    ) -> Result<BookingResult, BookingError> {
        let mut remaining = units.number.abs();
        let mut matched: MatchedLots = SmallVec::new();
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

        // Sort by date for correct FIFO/LIFO ordering
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

            // Record what we would match (using split which is read-only)
            let (taken, _) = pos.split(take * pos.units.number.signum());
            matched.push(taken);

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

        Ok(BookingResult {
            matched,
            cost_basis: cost_currency.map(|c| Amount::new(cost_basis, c)),
        })
    }

    /// Try HIFO booking without modifying inventory.
    fn try_reduce_hifo(
        &self,
        units: &Amount,
        spec: &CostSpec,
    ) -> Result<BookingResult, BookingError> {
        let mut remaining = units.number.abs();
        let mut matched: MatchedLots = SmallVec::new();
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
        matching.sort_by_key(|(_, cost)| std::cmp::Reverse(*cost));

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

            // Record what we would match
            let (taken, _) = pos.split(take * pos.units.number.signum());
            matched.push(taken);

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

        Ok(BookingResult {
            matched,
            cost_basis: cost_currency.map(|c| Amount::new(cost_basis, c)),
        })
    }

    /// Try AVERAGE booking without modifying inventory.
    fn try_reduce_average(&self, units: &Amount) -> Result<BookingResult, BookingError> {
        let matching: Vec<&Position> = self
            .positions
            .iter()
            .filter(|p| p.units.currency == units.currency && !p.is_empty())
            .collect();

        let total_units: Decimal = matching.iter().map(|p| p.units.number).sum();

        if total_units.is_zero() {
            return Err(BookingError::InsufficientUnits {
                currency: units.currency.clone(),
                requested: units.number.abs(),
                available: Decimal::ZERO,
            });
        }

        let reduction = units.number.abs();
        if reduction > total_units.abs() {
            return Err(BookingError::InsufficientUnits {
                currency: units.currency.clone(),
                requested: reduction,
                available: total_units.abs(),
            });
        }

        let cost_basis = average_cost_from_positions(&matching, total_units)?
            .map(|(avg_cost, currency)| Amount::new(reduction * avg_cost, currency));

        let matched: MatchedLots = matching.into_iter().cloned().collect();

        Ok(BookingResult {
            matched,
            cost_basis,
        })
    }

    /// Try reducing from a specific lot without modifying inventory.
    fn try_reduce_from_lot(
        &self,
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

        let cost_basis = pos.cost.as_ref().map(|c| c.total_cost(requested));
        let (matched, _) = pos.split(requested * pos.units.number.signum());

        Ok(BookingResult {
            matched: smallvec![matched],
            cost_basis,
        })
    }
}

impl Inventory {
    /// STRICT booking: require exactly one matching lot, unless either:
    ///
    /// - all matching lots are identical in cost, in which case the choice
    ///   between them is irrelevant and we fall back to the same ordering as
    ///   FIFO (oldest `cost.date` first — see [`Self::reduce_ordered`]), or
    /// - the reduction exactly matches the total units available across the
    ///   matching lots (full liquidation), in which case all of them may be
    ///   drained together without ambiguity.
    ///
    /// If multiple lots with *different* costs match and the reduction does
    /// not qualify for the full-liquidation exception — for example a
    /// wildcard reduction `-5 AAPL {}` against an inventory holding both
    /// `{150 USD}` and `{160 USD}` — the reduction is genuinely ambiguous and
    /// we return `AmbiguousMatch`, matching Python beancount's
    /// `AmbiguousMatchError` and the formal `STRICTCorrect.tla` specification.
    ///
    /// # The "interchangeable lots" heuristic
    ///
    /// We treat two matched lots as interchangeable when their `(cost.number,
    /// cost.currency)` agree — the user-visible monetary identity. We
    /// deliberately ignore `cost.date` and `cost.label`: the user's cost spec
    /// could not have constrained those fields without naming them, so two
    /// lots that differ only on date/label could not have been distinguished
    /// by the spec the user wrote, and the date-ordered fallback is
    /// unambiguous within that equivalence class.
    ///
    /// A stricter spec-derived check would compare each pair of matched lots
    /// on every cost field the spec did *not* constrain. The simpler
    /// number+currency check matches Python beancount's behavior for the
    /// real-world cases we know about (see
    /// `test_reduce_strict_multiple_match_with_identical_costs_uses_fifo` and
    /// the `test_validate_multiple_lot_match_uses_fifo` integration test for
    /// the same-cost-different-date case).
    pub(super) fn reduce_strict(
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
                // Are the matched lots financially interchangeable? Two lots
                // count as identical if they have the same cost number + cost
                // currency — the user-visible monetary identity. Date and label
                // differences don't make a reduction ambiguous because the user
                // could not have observed a different outcome based on the cost
                // spec they wrote. Beancount falls back to FIFO in that case.
                let first_key = self.positions[matching_indices[0]]
                    .cost
                    .as_ref()
                    .map(|c| (c.number, c.currency.clone()));
                let all_same_value = matching_indices.iter().skip(1).all(|&i| {
                    let key = self.positions[i]
                        .cost
                        .as_ref()
                        .map(|c| (c.number, c.currency.clone()));
                    key == first_key
                });

                if all_same_value {
                    return self.reduce_ordered(units, spec, false);
                }

                // Total match exception: if the reduction equals the sum of all
                // matching lots, the user is selling the entire matched
                // inventory and the lot choice doesn't matter — accept it.
                let total_units: Decimal = matching_indices
                    .iter()
                    .map(|&i| self.positions[i].units.number.abs())
                    .sum();
                if total_units == units.number.abs() {
                    return self.reduce_ordered(units, spec, false);
                }

                Err(BookingError::AmbiguousMatch {
                    num_matches: n,
                    currency: units.currency.clone(),
                })
            }
        }
    }

    /// `STRICT_WITH_SIZE` booking: like STRICT, but exact-size matches accept oldest lot.
    pub(super) fn reduce_strict_with_size(
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
    pub(super) fn reduce_fifo(
        &mut self,
        units: &Amount,
        spec: &CostSpec,
    ) -> Result<BookingResult, BookingError> {
        self.reduce_ordered(units, spec, false)
    }

    /// LIFO booking: reduce from newest lots first.
    pub(super) fn reduce_lifo(
        &mut self,
        units: &Amount,
        spec: &CostSpec,
    ) -> Result<BookingResult, BookingError> {
        self.reduce_ordered(units, spec, true)
    }

    /// HIFO booking: reduce from highest-cost lots first.
    pub(super) fn reduce_hifo(
        &mut self,
        units: &Amount,
        spec: &CostSpec,
    ) -> Result<BookingResult, BookingError> {
        let mut remaining = units.number.abs();
        let mut matched: MatchedLots = SmallVec::new();
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
        matching.sort_by_key(|(_, cost)| std::cmp::Reverse(*cost));

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
        self.rebuild_index();

        Ok(BookingResult {
            matched,
            cost_basis: cost_currency.map(|c| Amount::new(cost_basis, c)),
        })
    }

    /// Reduce in order (FIFO or LIFO).
    pub(super) fn reduce_ordered(
        &mut self,
        units: &Amount,
        spec: &CostSpec,
        reverse: bool,
    ) -> Result<BookingResult, BookingError> {
        let mut remaining = units.number.abs();
        let mut matched: MatchedLots = SmallVec::new();
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

        // Get cost currency from first lot (all lots of same commodity have same cost currency)
        if let Some(&first_idx) = indices.first()
            && let Some(cost) = &self.positions[first_idx].cost
        {
            cost_currency = Some(cost.currency.clone());
        }

        for idx in indices {
            if remaining.is_zero() {
                break;
            }

            let pos = &mut self.positions[idx];
            let available = pos.units.number.abs();
            let take = remaining.min(available);

            // Calculate cost basis for this portion
            if let Some(cost) = &pos.cost {
                cost_basis += take * cost.number;
            }

            // Record what we matched
            let (taken, _) = pos.split(take * pos.units.number.signum());
            matched.push(taken);

            // Reduce the lot - modify in place to avoid cloning
            let reduction = if units.number.is_sign_negative() {
                -take
            } else {
                take
            };
            pos.units.number += reduction;

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
        self.rebuild_index();

        Ok(BookingResult {
            matched,
            cost_basis: cost_currency.map(|c| Amount::new(cost_basis, c)),
        })
    }

    /// AVERAGE booking: merge all lots of the currency.
    pub(super) fn reduce_average(&mut self, units: &Amount) -> Result<BookingResult, BookingError> {
        let matching: Vec<&Position> = self
            .positions
            .iter()
            .filter(|p| p.units.currency == units.currency && !p.is_empty())
            .collect();

        let total_units: Decimal = matching.iter().map(|p| p.units.number).sum();

        if total_units.is_zero() {
            return Err(BookingError::InsufficientUnits {
                currency: units.currency.clone(),
                requested: units.number.abs(),
                available: Decimal::ZERO,
            });
        }

        let reduction = units.number.abs();
        if reduction > total_units.abs() {
            return Err(BookingError::InsufficientUnits {
                currency: units.currency.clone(),
                requested: reduction,
                available: total_units.abs(),
            });
        }

        let cost_basis = average_cost_from_positions(&matching, total_units)?
            .map(|(avg_cost, currency)| Amount::new(reduction * avg_cost, currency));

        let matched: MatchedLots = matching.into_iter().cloned().collect();
        let new_units = total_units + units.number;

        // Remove all positions of this currency
        self.positions
            .retain(|p| p.units.currency != units.currency);

        // Add back the remainder if non-zero
        if !new_units.is_zero() {
            self.positions.push_back(Position::simple(Amount::new(
                new_units,
                units.currency.clone(),
            )));
        }

        self.rebuild_index();

        Ok(BookingResult {
            matched,
            cost_basis,
        })
    }

    /// Cost merge `{*}`: merge all lots of the currency into a single
    /// weighted-average-cost lot, then reduce from it.
    ///
    /// Example: 10 AAPL {150 USD} + 10 AAPL {160 USD} merged = 20 AAPL {155 USD}.
    /// Reducing 5 AAPL {*} takes 5 from the merged 20 AAPL {155 USD} lot.
    pub(super) fn reduce_merge(&mut self, units: &Amount) -> Result<BookingResult, BookingError> {
        // Only merge lots with opposite sign (same as other reduce methods).
        // This prevents accidentally netting long and short positions.
        let matching: Vec<(usize, &Position)> = self
            .positions
            .iter()
            .enumerate()
            .filter(|(_, p)| {
                p.units.currency == units.currency
                    && !p.is_empty()
                    && p.units.number.is_sign_positive() != units.number.is_sign_positive()
            })
            .collect();

        if matching.is_empty() {
            return Err(BookingError::InsufficientUnits {
                currency: units.currency.clone(),
                requested: units.number.abs(),
                available: Decimal::ZERO,
            });
        }

        let total_units: Decimal = matching.iter().map(|(_, p)| p.units.number).sum();
        let reduction = units.number.abs();

        if reduction > total_units.abs() {
            return Err(BookingError::InsufficientUnits {
                currency: units.currency.clone(),
                requested: reduction,
                available: total_units.abs(),
            });
        }

        // Compute weighted-average cost from matching lots.
        let matching_refs: Vec<&Position> = matching.iter().map(|(_, p)| *p).collect();
        let (avg_cost, cost_currency) =
            match average_cost_from_positions(&matching_refs, total_units)? {
                Some(result) => result,
                None => return self.reduce_average(units),
            };

        let cost_basis = Some(Amount::new(reduction * avg_cost, cost_currency.clone()));

        // Return a single synthetic matched position representing the merged lot.
        // This prevents the booking engine from expanding the posting into multiple
        // postings (one per original lot), which would be incorrect for {*}.
        let make_avg_cost = || Cost {
            number: avg_cost,
            currency: cost_currency.clone(),
            date: None,
            label: None,
        };

        let matched: MatchedLots = smallvec![Position::with_cost(
            Amount::new(units.number.abs(), units.currency.clone()),
            make_avg_cost(),
        )];

        // Remove all matching lots of this currency
        let matching_indices: std::collections::HashSet<usize> =
            matching.iter().map(|(i, _)| *i).collect();
        let mut idx = 0;
        self.positions.retain(|_| {
            let keep = !matching_indices.contains(&idx);
            idx += 1;
            keep
        });

        // Add back a single merged lot with the remainder
        let remaining = total_units + units.number; // units.number is negative for reductions
        if !remaining.is_zero() {
            self.positions.push_back(Position::with_cost(
                Amount::new(remaining, units.currency.clone()),
                make_avg_cost(),
            ));
        }

        self.rebuild_index();

        Ok(BookingResult {
            matched,
            cost_basis,
        })
    }

    /// NONE booking: reduce without matching lots.
    pub(super) fn reduce_none(&mut self, units: &Amount) -> Result<BookingResult, BookingError> {
        // For NONE booking, we just reduce the total without caring about lots
        let total_units = self.units(&units.currency);

        // Check we have enough in the right direction
        if total_units.signum() == units.number.signum() || total_units.is_zero() {
            // This is an augmentation, not a reduction - just add it
            self.add(Position::simple(units.clone()));
            return Ok(BookingResult {
                matched: SmallVec::new(),
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
    pub(super) fn reduce_from_lot(
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
        let currency = pos.units.currency.clone();
        let new_units = pos.units.number + units.number;
        let new_pos = Position {
            units: Amount::new(new_units, currency.clone()),
            cost: pos.cost.clone(),
        };
        self.positions[idx] = new_pos;

        // Update units cache incrementally (units.number is negative for reductions)
        if let Some(cached) = self.units_cache.get_mut(&currency) {
            *cached += units.number;
        }

        // Remove if empty and rebuild simple_index
        if self.positions[idx].is_empty() {
            self.positions.remove(idx);
            // Only rebuild simple_index when position is removed
            self.simple_index.clear();
            for (i, p) in self.positions.iter().enumerate() {
                if p.cost.is_none() {
                    self.simple_index.insert(p.units.currency.clone(), i);
                }
            }
        }

        Ok(BookingResult {
            matched: smallvec![matched],
            cost_basis,
        })
    }
}
