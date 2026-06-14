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

#[cfg(test)]
mod reduction_tests {
    //! Direct unit tests for the read-only `try_reduce_*` booking paths.
    //!
    //! These pin exact cost-basis, lot selection, and guard behavior so
    //! the lot-reduction mutants surfaced by the #1309 audit are killed
    //! (the public mutating `reduce_*` path was covered indirectly, but
    //! the `try_reduce_*` preview path had no direct assertions).
    use crate::{Amount, BookingMethod, Cost, CostSpec, Inventory, Position, naive_date};
    use rust_decimal::Decimal;
    use rust_decimal_macros::dec;

    fn d(n: i64) -> Decimal {
        Decimal::from(n)
    }

    /// A cost-bearing lot of `units` STK at `cost` USD, dated 2024-01-`day`.
    fn lot(units: i64, cost: i64, day: u32) -> Position {
        Position::with_cost(
            Amount::new(d(units), "STK"),
            Cost::new(d(cost), "USD").with_date(naive_date(2024, 1, day).unwrap()),
        )
    }

    fn mk(lots: impl IntoIterator<Item = Position>) -> Inventory {
        let mut i = Inventory::new();
        for l in lots {
            i.add(l);
        }
        i
    }

    fn sell_stk(n: i64) -> Amount {
        Amount::new(d(-n), "STK")
    }

    fn try_reduce(inv: &Inventory, units: &Amount, method: BookingMethod) -> super::BookingResult {
        inv.try_reduce(units, Some(&CostSpec::default()), method)
            .expect("reduction should succeed")
    }

    fn basis(r: &super::BookingResult) -> Decimal {
        r.cost_basis.as_ref().expect("cost basis present").number
    }

    // ---- FIFO / LIFO ordered ------------------------------------------

    #[test]
    fn fifo_partial_multilot_cost_basis_and_order() {
        // 10 @ $100 (older), 10 @ $200 (newer); sell 15.
        let inv = mk([lot(10, 100, 1), lot(10, 200, 2)]);
        let r = try_reduce(&inv, &sell_stk(15), BookingMethod::Fifo);
        // FIFO: 10@100 + 5@200 = 1000 + 1000 = 2000.
        assert_eq!(basis(&r), dec!(2000));
        assert_eq!(r.matched.len(), 2);
        assert_eq!(r.matched[0].units.number.abs(), dec!(10));
        assert_eq!(r.matched[0].cost.as_ref().unwrap().number, dec!(100));
        assert_eq!(r.matched[1].units.number.abs(), dec!(5));
        assert_eq!(r.matched[1].cost.as_ref().unwrap().number, dec!(200));
    }

    #[test]
    fn lifo_takes_newest_lot_first() {
        let inv = mk([lot(10, 100, 1), lot(10, 200, 2)]);
        let r = try_reduce(&inv, &sell_stk(15), BookingMethod::Lifo);
        // LIFO: 10@200 + 5@100 = 2000 + 500 = 2500 (distinguishes the
        // `reverse` flag from FIFO's 2000).
        assert_eq!(basis(&r), dec!(2500));
        assert_eq!(r.matched[0].cost.as_ref().unwrap().number, dec!(200));
    }

    #[test]
    fn fifo_single_lot_partial_cost_basis() {
        let inv = mk([lot(10, 100, 1)]);
        let r = try_reduce(&inv, &sell_stk(3), BookingMethod::Fifo);
        assert_eq!(basis(&r), dec!(300)); // 3 * 100
    }

    // ---- HIFO ---------------------------------------------------------

    #[test]
    fn hifo_takes_highest_cost_lot_first() {
        // costs 100, 300, 200 → HIFO order 300, 200, 100.
        let inv = mk([lot(10, 100, 1), lot(10, 300, 2), lot(10, 200, 3)]);
        let r = try_reduce(&inv, &sell_stk(15), BookingMethod::Hifo);
        // 10@300 + 5@200 = 3000 + 1000 = 4000.
        assert_eq!(basis(&r), dec!(4000));
        assert_eq!(r.matched[0].cost.as_ref().unwrap().number, dec!(300));
        assert_eq!(r.matched[1].cost.as_ref().unwrap().number, dec!(200));
    }

    // ---- AVERAGE ------------------------------------------------------

    #[test]
    fn average_cost_basis_partial() {
        // 10 @ $100, 30 @ $200 → 40 units, $7000 total, avg $175.
        let inv = mk([lot(10, 100, 1), lot(30, 200, 2)]);
        let r = try_reduce(&inv, &sell_stk(20), BookingMethod::Average);
        assert_eq!(basis(&r), dec!(3500)); // 20 * 175
    }

    #[test]
    fn average_reduce_exact_total_succeeds() {
        // Reducing exactly the held quantity must succeed (kills
        // `reduction > total` → `>=`/`==`).
        let inv = mk([lot(10, 100, 1), lot(30, 200, 2)]);
        let r = try_reduce(&inv, &sell_stk(40), BookingMethod::Average);
        assert_eq!(basis(&r), dec!(7000)); // 40 * 175
    }

    #[test]
    fn average_over_reduction_errors() {
        // Reducing more than held must error (kills `>` → `<`).
        let inv = mk([lot(10, 100, 1)]);
        let err = inv
            .try_reduce(
                &sell_stk(20),
                Some(&CostSpec::default()),
                BookingMethod::Average,
            )
            .unwrap_err();
        assert!(matches!(err, super::BookingError::InsufficientUnits { .. }));
    }

    // ---- Filter isolation (currency / sign) ---------------------------
    // One fixture per method: an unrelated OTH lot plus the real STK lot.
    // A correct reducer touches ONLY the real STK lot; the currency `==`
    // and the `&&` connecting it would pull OTH in (or drop the real
    // one), changing the basis. (A zero-units "empty" lot is intentionally
    // NOT added here: `Inventory::add` drops empty positions on insert, so
    // the `!is_empty()` filter clause is unreachable for add-built
    // inventories and can't be exercised this way.)

    fn isolation_inv() -> Inventory {
        let mut i = Inventory::new();
        i.add(Position::with_cost(
            Amount::new(dec!(10), "OTH"), // different currency: must be ignored
            Cost::new(dec!(888), "USD").with_date(naive_date(2024, 1, 1).unwrap()),
        ));
        i.add(lot(10, 100, 2)); // the real STK lot
        i
    }

    fn assert_isolated(method: BookingMethod) {
        let inv = isolation_inv();
        let r = try_reduce(&inv, &sell_stk(5), method);
        assert_eq!(
            basis(&r),
            dec!(500),
            "must reduce only the real STK lot (5 * 100)"
        );
        assert!(
            r.matched.iter().all(|p| p.units.currency.as_ref() == "STK"),
            "no non-STK lot should be matched"
        );
    }

    #[test]
    fn fifo_filters_currency() {
        assert_isolated(BookingMethod::Fifo);
    }

    #[test]
    fn hifo_filters_currency() {
        assert_isolated(BookingMethod::Hifo);
    }

    #[test]
    fn strict_filters_currency() {
        assert_isolated(BookingMethod::Strict);
    }

    #[test]
    fn average_filters_currency() {
        // average filters by currency + non-empty (no cost-spec / sign filter).
        let inv = isolation_inv();
        let r = try_reduce(&inv, &sell_stk(5), BookingMethod::Average);
        // Only the STK lot participates: 10 units @ $100 → avg $100 → 5 * 100.
        assert_eq!(basis(&r), dec!(500));
    }

    // ---- Sign guard ---------------------------------------------------

    #[test]
    fn does_not_match_same_sign_lot() {
        // A short (negative) STK lot must NOT satisfy a sell (negative
        // units): same sign. Only the long lot is reducible. Kills the
        // `signum() != signum()` → `==` mutant (== would match the short
        // lot or nothing).
        let mut i = Inventory::new();
        i.add(lot(-10, 50, 1)); // short lot, same sign as a sell
        i.add(lot(10, 100, 2)); // long lot
        let r = try_reduce(&i, &sell_stk(5), BookingMethod::Fifo);
        assert_eq!(basis(&r), dec!(500)); // 5 * 100 from the long lot only
        assert!(r.matched.iter().all(|p| p.units.number.is_sign_positive()));
    }

    #[test]
    fn strict_rejects_when_only_same_sign_lot_present() {
        // STRICT against an inventory holding ONLY a same-sign (short)
        // lot must return NoMatchingLot — the single reducible lot fails
        // `can_reduce`, leaving zero matches. This pins all three `&&`
        // connectors in `try_reduce_strict`'s filter: each `&& -> ||`
        // mutant wrongly admits the short lot (currency==STK or the
        // always-true `matches_cost_spec` on the default spec satisfies
        // the disjunction), turning 0 matches into 1 and succeeding via
        // `try_reduce_from_lot` instead of erroring.
        let mut i = Inventory::new();
        i.add(lot(-10, 100, 1)); // short STK only; a sell is the same sign
        let res = i.try_reduce(
            &sell_stk(5),
            Some(&CostSpec::default()),
            BookingMethod::Strict,
        );
        assert!(
            matches!(res, Err(super::BookingError::NoMatchingLot { .. })),
            "strict reduction against a same-sign-only inventory must not match; got {res:?}"
        );
    }

    // ---- Insufficient-units accounting --------------------------------

    #[test]
    fn fifo_insufficient_reports_available() {
        // `available = requested - remaining`; kills the `-` → `+`/`/`
        // mutant in the insufficient branch.
        let inv = mk([lot(10, 100, 1)]);
        let err = inv
            .try_reduce(
                &sell_stk(15),
                Some(&CostSpec::default()),
                BookingMethod::Fifo,
            )
            .unwrap_err();
        match err {
            super::BookingError::InsufficientUnits {
                requested,
                available,
                ..
            } => {
                assert_eq!(requested, dec!(15));
                assert_eq!(available, dec!(10)); // 15 requested - 5 remaining
            }
            other => panic!("expected InsufficientUnits, got {other:?}"),
        }
    }

    // ---- STRICT single-lot path (try_reduce_from_lot) -----------------

    #[test]
    fn strict_single_lot_partial_cost_basis() {
        // Exactly one matching lot → try_reduce_from_lot; partial take.
        let inv = mk([lot(10, 100, 1)]);
        let r = try_reduce(&inv, &sell_stk(4), BookingMethod::Strict);
        assert_eq!(basis(&r), dec!(400)); // 4 * 100
    }

    #[test]
    fn strict_single_lot_over_reduction_errors() {
        // from_lot `requested > available` guard.
        let inv = mk([lot(10, 100, 1)]);
        let err = inv
            .try_reduce(
                &sell_stk(11),
                Some(&CostSpec::default()),
                BookingMethod::Strict,
            )
            .unwrap_err();
        assert!(matches!(err, super::BookingError::InsufficientUnits { .. }));
    }

    #[test]
    fn strict_single_lot_exact_full_reduction_succeeds() {
        // requested == available must succeed (kills from_lot `>` → `>=`).
        let inv = mk([lot(10, 100, 1)]);
        let r = try_reduce(&inv, &sell_stk(10), BookingMethod::Strict);
        assert_eq!(basis(&r), dec!(1000));
    }

    // ---- HIFO matched units + insufficient accounting ----------------

    #[test]
    fn hifo_matched_units_and_insufficient_available() {
        let inv = mk([lot(10, 100, 1), lot(10, 300, 2)]);
        let r = try_reduce(&inv, &sell_stk(8), BookingMethod::Hifo);
        // 8 taken from the $300 lot (kills the split `take * signum -> +`).
        assert_eq!(r.matched[0].units.number.abs(), dec!(8));
        let err = inv
            .try_reduce(
                &sell_stk(25),
                Some(&CostSpec::default()),
                BookingMethod::Hifo,
            )
            .unwrap_err();
        match err {
            super::BookingError::InsufficientUnits { available, .. } => {
                assert_eq!(available, dec!(20)); // 20 held; kills `abs - remaining` mutants
            }
            other => panic!("expected InsufficientUnits, got {other:?}"),
        }
    }

    #[test]
    fn strict_from_lot_matched_units() {
        let inv = mk([lot(10, 100, 1)]);
        let r = try_reduce(&inv, &sell_stk(4), BookingMethod::Strict);
        assert_eq!(r.matched[0].units.number.abs(), dec!(4)); // kills from_lot split `* -> +`
    }

    // ---- StrictWithSize ----------------------------------------------

    #[test]
    fn strict_with_size_picks_exact_size_lot() {
        let inv = mk([lot(10, 100, 1), lot(5, 200, 2)]);
        let r = try_reduce(&inv, &sell_stk(5), BookingMethod::StrictWithSize);
        assert_eq!(basis(&r), dec!(1000)); // 5 @ $200, the exact-size lot
    }

    #[test]
    fn strict_with_size_ambiguous_without_exact_or_total() {
        let inv = mk([lot(10, 100, 1), lot(10, 200, 2)]);
        let err = inv
            .try_reduce(
                &sell_stk(5),
                Some(&CostSpec::default()),
                BookingMethod::StrictWithSize,
            )
            .unwrap_err();
        assert!(matches!(err, super::BookingError::AmbiguousMatch { .. }));
    }

    #[test]
    fn strict_with_size_total_match_falls_back_to_fifo() {
        let inv = mk([lot(10, 100, 1), lot(10, 200, 2)]);
        let r = try_reduce(&inv, &sell_stk(20), BookingMethod::StrictWithSize);
        assert_eq!(basis(&r), dec!(3000)); // total match → FIFO: 1000 + 2000
    }

    // ---- Mutating reduce() path (reduce_*) ----------------------------

    #[test]
    fn reduce_fifo_commits_and_basis() {
        let mut inv = mk([lot(10, 100, 1), lot(10, 200, 2)]);
        let r = inv
            .reduce(
                &sell_stk(15),
                Some(&CostSpec::default()),
                BookingMethod::Fifo,
            )
            .unwrap();
        assert_eq!(r.cost_basis.unwrap().number, dec!(2000));
        assert_eq!(inv.units("STK"), dec!(5)); // 20 - 15
    }

    #[test]
    fn reduce_hifo_commits_basis_units_insufficient() {
        let mut inv = mk([lot(10, 100, 1), lot(10, 300, 2)]);
        let r = inv
            .reduce(
                &sell_stk(15),
                Some(&CostSpec::default()),
                BookingMethod::Hifo,
            )
            .unwrap();
        assert_eq!(r.cost_basis.unwrap().number, dec!(3500)); // 10@300 + 5@100
        assert_eq!(r.matched[0].units.number.abs(), dec!(10)); // kills reduce_hifo split `* -> +`
        let mut inv2 = mk([lot(10, 100, 1)]);
        let err = inv2
            .reduce(
                &sell_stk(25),
                Some(&CostSpec::default()),
                BookingMethod::Hifo,
            )
            .unwrap_err();
        match err {
            super::BookingError::InsufficientUnits { available, .. } => {
                assert_eq!(available, dec!(10));
            }
            other => panic!("expected InsufficientUnits, got {other:?}"),
        }
    }

    #[test]
    fn reduce_average_only_matching_currency() {
        let mut i = Inventory::new();
        i.add(lot(10, 100, 2));
        i.add(Position::with_cost(
            Amount::new(dec!(10), "OTH"),
            Cost::new(dec!(888), "USD").with_date(naive_date(2024, 1, 1).unwrap()),
        ));
        let r = i
            .reduce(
                &sell_stk(5),
                Some(&CostSpec::default()),
                BookingMethod::Average,
            )
            .unwrap();
        assert_eq!(r.cost_basis.unwrap().number, dec!(500)); // only the STK lot
    }

    #[test]
    fn reduce_from_lot_matched_and_remaining_units() {
        let mut inv = mk([lot(10, 100, 1)]);
        let r = inv
            .reduce(
                &sell_stk(4),
                Some(&CostSpec::default()),
                BookingMethod::Strict,
            )
            .unwrap();
        assert_eq!(r.matched[0].units.number.abs(), dec!(4)); // kills reduce_from_lot split `* -> +`
        // Assert the stored POSITION units directly, not `units()` — the
        // latter reads a separate incremental cache, so it would not catch
        // a bug in `new_units = pos.units.number + units.number`.
        let remaining: Vec<_> = inv.position_list();
        assert_eq!(remaining.len(), 1);
        assert_eq!(remaining[0].units.number, dec!(6)); // 10 + (-4); kills `+ -> -`/`*`
        assert_eq!(inv.units("STK"), dec!(6)); // cache stays consistent
    }

    #[test]
    fn reduce_merge_filters_currency_sign_and_preserves_other_lots() {
        // Merge two long STK lots; a short STK lot (same sign as the
        // sell) and an unrelated OTH lot must be excluded from the merge
        // AND survive in the inventory.
        let mut inv = Inventory::new();
        inv.add(lot(10, 100, 1)); // long STK
        inv.add(lot(30, 200, 2)); // long STK
        inv.add(lot(-5, 999, 3)); // short STK — excluded by the sign filter
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "OTH"), // different currency — excluded
            Cost::new(dec!(888), "USD").with_date(naive_date(2024, 1, 4).unwrap()),
        ));
        let spec = CostSpec {
            merge: true,
            ..CostSpec::default()
        };
        let r = inv
            .reduce(&sell_stk(20), Some(&spec), BookingMethod::Strict)
            .unwrap();
        // Only the two long STK lots merge: 40 units @ avg $175 → 20 * 175.
        // Including the short (sign) or OTH (currency) lot would change this.
        assert_eq!(r.cost_basis.unwrap().number, dec!(3500));
        // The excluded lots must still be present (kills the retain-index mutant).
        assert!(
            inv.position_list()
                .iter()
                .any(|p| p.units.currency.as_ref() == "OTH" && p.units.number == dec!(10)),
            "OTH lot must survive the merge"
        );
        assert!(
            inv.position_list()
                .iter()
                .any(|p| p.units.currency.as_ref() == "STK" && p.units.number == dec!(-5)),
            "short STK lot must survive the merge"
        );
    }

    #[test]
    fn reduce_none_exact_succeeds_over_reduction_errors() {
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(10), "STK")));
        assert!(
            inv.reduce(&sell_stk(10), None, BookingMethod::None).is_ok(),
            "exact NONE reduction should succeed"
        );
        let mut inv2 = Inventory::new();
        inv2.add(Position::simple(Amount::new(dec!(10), "STK")));
        let err = inv2
            .reduce(&sell_stk(15), None, BookingMethod::None)
            .unwrap_err();
        assert!(matches!(err, super::BookingError::InsufficientUnits { .. }));
    }

    #[test]
    fn reduce_merge_uses_weighted_average() {
        let mut inv = mk([lot(10, 100, 1), lot(30, 200, 2)]);
        let spec = CostSpec {
            merge: true,
            ..CostSpec::default()
        };
        let r = inv
            .reduce(&sell_stk(20), Some(&spec), BookingMethod::Strict)
            .unwrap();
        assert_eq!(r.cost_basis.unwrap().number, dec!(3500)); // 20 @ avg $175
        assert_eq!(inv.units("STK"), dec!(20)); // 40 - 20
    }
}
