//! Booking method implementations for Inventory.
//!
//! This module contains the implementation of all booking methods (STRICT,
//! `STRICT_WITH_SIZE`, FIFO, LIFO, HIFO, AVERAGE, NONE) used to reduce positions
//! from an inventory.

use rust_decimal::Decimal;
use rust_decimal::prelude::Signed;

use smallvec::{SmallVec, smallvec};

use super::{BookingError, BookingMethod, BookingResult, Inventory, MatchedLots, OverflowError};
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
            // Checked: the product needs the sum of its operands' digits, so
            // it can leave range well below the ceiling (#1863).
            total_cost = pos
                .units
                .number
                .checked_mul(cost.number)
                .and_then(|v| total_cost.checked_add(v))
                .ok_or_else(|| {
                    BookingError::Overflow(OverflowError {
                        currency: cost.currency.clone(),
                    })
                })?;
        }
    }

    if !has_any_cost || cost_currency.is_none() {
        return Ok(None);
    }

    Ok(Some((total_cost / total_units, cost_currency.unwrap())))
}

/// A reduction computed from `&Inventory` but not yet applied.
///
/// The two variants mirror the two commit shapes the booking methods already
/// had: the single-lot path maintains its caches incrementally, the multi-lot
/// path rewrites lots and then rebuilds. Keeping them distinct means
/// splitting preview from commit costs the commit path nothing.
pub(super) enum ReductionPlan {
    /// One lot reduced to `new_units`.
    FromLot {
        /// Index of the lot in `positions`.
        idx: usize,
        /// What that lot's units number becomes.
        new_units: Decimal,
    },
    /// `(index, new units number)` pairs, applied in order.
    Updates(SmallVec<[(usize, Decimal); 1]>),
}

impl Inventory {
    /// Try reducing positions without modifying the inventory.
    ///
    /// The read-only preview of [`Self::reduce`]: returns exactly what
    /// `reduce` would return — the same matched lots and cost basis on
    /// success, the same error otherwise — without mutating `self`.
    ///
    /// Implemented as `reduce` on a clone, so it is equivalent BY
    /// CONSTRUCTION. It previously re-implemented every booking method's
    /// selection logic in a parallel `try_*` tree, which drifted from the
    /// mutating path in three places (STRICT ambiguity, NONE shorting, `{*}`
    /// merge dispatch) — the recurring one-logic-two-paths class (#1648,
    /// #1663, #1686). The clone is cheap: `positions` is an
    /// `imbl::Vector`, so cloning is O(1) structural sharing and `reduce`'s
    /// copy-on-write rebuild touches only the clone. The
    /// `try_reduce_predicts_reduce` property test pins the equivalence.
    ///
    /// # Arguments
    ///
    /// * `units` - The units to reduce (negative for selling)
    /// * `cost_spec` - Optional cost specification for matching lots
    /// * `method` - The booking method to use
    ///
    /// # Errors
    ///
    /// Exactly the errors [`Self::reduce`] would return for the same input.
    pub fn try_reduce(
        &self,
        units: &Amount,
        cost_spec: Option<&CostSpec>,
        method: BookingMethod,
    ) -> Result<BookingResult, BookingError> {
        let spec = cost_spec.cloned().unwrap_or_default();

        // Planned methods answer from `&self`. The rest still preview by
        // cloning — correct, just O(lots). Converting them is mechanical and
        // follows the same shape; these are simply not the ones the profiling
        // shapes exercise.
        if spec.merge {
            return self.clone().reduce(units, cost_spec, method);
        }
        match method {
            BookingMethod::Strict => self.plan_strict(units, &spec).map(|(r, _)| r),
            BookingMethod::Fifo => self.plan_ordered(units, &spec, false).map(|(r, _)| r),
            BookingMethod::Lifo => self.plan_ordered(units, &spec, true).map(|(r, _)| r),
            BookingMethod::StrictWithSize
            | BookingMethod::Hifo
            | BookingMethod::Average
            | BookingMethod::None => self.clone().reduce(units, cost_spec, method),
        }
    }

    /// Apply a [`ReductionPlan`] produced by one of the `plan_*` methods.
    fn commit_plan(&mut self, plan: &ReductionPlan, units: &Amount) {
        match plan {
            ReductionPlan::FromLot { idx, new_units } => {
                self.commit_from_lot(*idx, units, *new_units);
            }
            ReductionPlan::Updates(updates) => self.commit_updates(updates),
        }
    }

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
        let (result, plan) = self.plan_strict(units, spec)?;
        self.commit_plan(&plan, units);
        Ok(result)
    }

    /// The read-only half of [`Self::reduce_strict`].
    ///
    /// STRICT is a dispatcher: one match delegates to the single-lot path,
    /// financially-interchangeable or wholly-consumed multi-matches fall back
    /// to FIFO ordering, and anything else is ambiguous and mutates nothing.
    /// This mirrors that dispatch by delegating to the same two planners the
    /// mutating path uses. See [`Self::plan_from_lot`] for why the selection
    /// logic must not be duplicated into `try_reduce`.
    pub(super) fn plan_strict(
        &self,
        units: &Amount,
        spec: &CostSpec,
    ) -> Result<(BookingResult, ReductionPlan), BookingError> {
        // Candidates from the cost index when the spec names a per-unit cost,
        // otherwise every lot — a spec without one can match anything. Both
        // arms apply the SAME predicate, so the index never decides a match;
        // it only narrows what the predicate is run on.
        //
        // That asymmetry is the whole safety argument, and it only runs one
        // way. A STALE entry is harmless: it names a tombstone or a lot that
        // no longer matches, and the predicate discards it. A MISSING entry is
        // NOT: the lot is never offered to the predicate at all, so a
        // reduction that should have matched it reports no matching lot or
        // books as an augmentation and duplicates the position. Index
        // maintenance is therefore a correctness obligation, not an
        // optimization — `draining_a_lot_removes_it_from_the_cost_index` and
        // the `add`/rebuild mutations are what hold it.
        let matching_indices: Vec<usize> = match self.cost_candidates(units, spec) {
            Some(slots) => slots
                .into_iter()
                .filter(|i| {
                    // `get`, not `[]`: indexing a tombstone panics, and a
                    // stale entry must not be able to crash on user data. With
                    // `get` it is merely a wasted candidate, which the
                    // predicate discards anyway.
                    self.positions.get(*i).is_some_and(|p| {
                        p.units.currency == units.currency
                            && !p.is_empty()
                            && p.can_reduce(units)
                            && p.matches_cost_spec(spec)
                    })
                })
                .collect(),
            None => self
                .positions
                .iter_slots()
                .filter(|(_, p)| {
                    p.units.currency == units.currency
                        && !p.is_empty()
                        && p.can_reduce(units)
                        && p.matches_cost_spec(spec)
                })
                .map(|(i, _)| i)
                .collect(),
        };

        match matching_indices.len() {
            0 => Err(BookingError::NoMatchingLot {
                currency: units.currency.clone(),
                cost_spec: spec.clone(),
            }),
            1 => {
                let idx = matching_indices[0];
                let (result, new_units) = self.plan_from_lot(idx, units)?;
                Ok((result, ReductionPlan::FromLot { idx, new_units }))
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
                    let (result, updates) = self.plan_ordered(units, spec, false)?;
                    return Ok((result, ReductionPlan::Updates(updates)));
                }

                // Total match exception: if the reduction equals the sum of all
                // matching lots, the user is selling the entire matched
                // inventory and the lot choice doesn't matter — accept it.
                let total_units: Decimal = matching_indices
                    .iter()
                    .map(|&i| self.positions[i].units.number.abs())
                    .sum();
                if total_units == units.number.abs() {
                    let (result, updates) = self.plan_ordered(units, spec, false)?;
                    return Ok((result, ReductionPlan::Updates(updates)));
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
            .iter_slots()
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
            .iter_slots()
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

        // Check sufficiency BEFORE mutating any lot: a failed reduction must
        // leave the inventory untouched (same invariant as `reduce_ordered`;
        // see the comment there and `booking_properties.rs`).
        let available: Decimal = indices
            .iter()
            .map(|&i| self.positions[i].units.number.abs())
            .sum();
        if available < remaining {
            return Err(BookingError::InsufficientUnits {
                currency: units.currency.clone(),
                requested: remaining,
                available,
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
                // Checked, not clamped: a clamped cost basis becomes a
                // fabricated capital gain (#1863).
                //
                // DEFENSE-IN-DEPTH, not a currently-reachable fix: no ledger
                // was found that gets here with an overflowing accumulation —
                // to sum two in-range cost bases past the ceiling, the
                // reducing posting's own weight must exceed it too, and that
                // is reported earlier (verified by removing this check and
                // re-running the multi-lot fixtures, which still did not
                // panic). Kept because reachability rests on those upstream
                // checks, and a future caller reaching `reduce` directly must
                // not resurrect the panic.
                cost_basis = take
                    .checked_mul(cost.number)
                    .and_then(|v| cost_basis.checked_add(v))
                    .ok_or_else(|| {
                        BookingError::Overflow(OverflowError {
                            currency: cost.currency.clone(),
                        })
                    })?;
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
        let (result, updates) = self.plan_ordered(units, spec, reverse)?;
        self.commit_updates(&updates);
        Ok(result)
    }

    /// The read-only half of [`Self::reduce_ordered`]: pick the lots, check
    /// sufficiency, and compute what would be matched — without touching a
    /// single position.
    ///
    /// Returns the result alongside `(index, new units number)` pairs for the
    /// caller to apply. See [`Self::plan_from_lot`] for why the split exists
    /// and why the selection logic must not be duplicated into `try_reduce`.
    pub(super) fn plan_ordered(
        &self,
        units: &Amount,
        spec: &CostSpec,
        reverse: bool,
    ) -> Result<(BookingResult, SmallVec<[(usize, Decimal); 1]>), BookingError> {
        let mut remaining = units.number.abs();
        let mut matched: MatchedLots = SmallVec::new();
        let mut cost_basis = Decimal::ZERO;
        let mut cost_currency = None;

        // Get indices of matching positions
        let mut indices: Vec<usize> = self
            .positions
            .iter_slots()
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

        // Check sufficiency BEFORE mutating any lot: a failed reduction must
        // leave the inventory untouched. The validator reduces against the
        // live `LedgerState` inventories, so a partial drain on the error
        // path would corrupt every later balance assertion on the account
        // (found by the failed-reduce-must-not-mutate property in
        // `rustledger-booking/tests/booking_properties.rs`).
        let available: Decimal = indices
            .iter()
            .map(|&i| self.positions[i].units.number.abs())
            .sum();
        if available < remaining {
            return Err(BookingError::InsufficientUnits {
                currency: units.currency.clone(),
                requested: remaining,
                available,
            });
        }

        let mut updates: SmallVec<[(usize, Decimal); 1]> = SmallVec::new();
        for idx in indices {
            if remaining.is_zero() {
                break;
            }

            let pos = &self.positions[idx];
            let available = pos.units.number.abs();
            let take = remaining.min(available);

            // Calculate cost basis for this portion (checked — see the
            // matching site in the FIFO/LIFO ladder above).
            if let Some(cost) = &pos.cost {
                cost_basis = take
                    .checked_mul(cost.number)
                    .and_then(|v| cost_basis.checked_add(v))
                    .ok_or_else(|| {
                        BookingError::Overflow(OverflowError {
                            currency: cost.currency.clone(),
                        })
                    })?;
            }

            // Record what we matched
            let (taken, _) = pos.split(take * pos.units.number.signum());
            matched.push(taken);

            // What the lot WOULD become. Recorded rather than applied so the
            // preview path can run this same loop against `&self`.
            let reduction = if units.number.is_sign_negative() {
                -take
            } else {
                take
            };
            updates.push((idx, pos.units.number + reduction));

            remaining -= take;
        }

        Ok((
            BookingResult {
                matched,
                cost_basis: cost_currency.map(|c| Amount::new(cost_basis, c)),
            },
            updates,
        ))
    }

    /// Apply `(index, new units)` pairs from a plan, then restore the caches.
    ///
    /// `retain` + `rebuild_index` exactly as the fused `reduce_ordered` did —
    /// the multi-lot path always paid an O(lots) cache rebuild, and changing
    /// that is a separate question from removing the preview's clone.
    fn commit_updates(&mut self, updates: &[(usize, Decimal)]) {
        for &(idx, new_units) in updates {
            self.positions[idx].units.number = new_units;
        }
        self.positions.retain(|p| !p.is_empty());
        self.rebuild_index();
    }

    /// AVERAGE booking: merge all lots of the currency.
    ///
    /// Stricter than Python: beancount does NOT implement this method.
    /// `beancount.parser.booking_method.booking_method_AVERAGE` raises
    /// `AmbiguousMatchError("AVERAGE method is not supported")`, with the real
    /// implementation left commented out ("DISABLED - This is the code for
    /// AVERAGE, which is currently disabled"). `Booking.AVERAGE` exists in the
    /// enum and is accepted in an `open` directive, so a ledger declaring it
    /// parses and then books nothing.
    ///
    /// Two consequences worth knowing before changing anything here:
    ///
    /// * The compat oracle cannot referee this. There is no reference answer
    ///   to diff against, so correctness rests on the definition — the merged
    ///   lot's cost is the cost-weighted average of the lots it replaces — and
    ///   on the two rledger surfaces agreeing.
    /// * That is exactly why #1985 survived: BQL netted by lot key and produced
    ///   a dangling negative position where reports produced the merged lot,
    ///   and no differential test could see it. The internal parity guard
    ///   (`query_report_realization_parity_test`) is what caught it.
    pub(super) fn reduce_average(&mut self, units: &Amount) -> Result<BookingResult, BookingError> {
        let matching: Vec<&Position> = self
            .positions
            .iter()
            .filter(|p| p.units.currency == units.currency && !p.is_empty())
            .collect();

        let total_units: Decimal = matching
            .iter()
            .try_fold(Decimal::ZERO, |acc, p| acc.checked_add(p.units.number))
            .ok_or_else(|| {
                BookingError::Overflow(OverflowError {
                    currency: units.currency.clone(),
                })
            })?;

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

        let avg = average_cost_from_positions(&matching, total_units)?;
        let cost_basis = avg
            .as_ref()
            .map(|(avg_cost, currency)| {
                reduction
                    .checked_mul(*avg_cost)
                    .map(|n| Amount::new(n, currency.clone()))
                    .ok_or_else(|| {
                        BookingError::Overflow(OverflowError {
                            currency: currency.clone(),
                        })
                    })
            })
            .transpose()?;

        // Build a position of `number` units of the reduced currency at the
        // average cost (or costless if the lots had no cost).
        let at_avg_cost = |number: Decimal| -> Position {
            let amount = Amount::new(number, units.currency.clone());
            match &avg {
                Some((avg_cost, currency)) => {
                    Position::with_cost(amount, Cost::new(*avg_cost, currency.clone()))
                }
                None => Position::simple(amount),
            }
        };

        // A reduction under AVERAGE matches a SINGLE synthetic lot of the
        // reduced quantity at the average cost, not every underlying lot.
        // Returning the full lot set made the consumer (book.rs) expand the
        // reduction into one posting per lot and remove the entire position
        // (and book a garbage gain). The taken units carry the *inventory* sign
        // (`total_units.signum()`), matching the FIFO/ordered convention — so
        // covering a short (negative pool) yields a negative matched lot.
        let matched: MatchedLots = smallvec![at_avg_cost(reduction * total_units.signum())];

        let new_units = total_units + units.number;

        // Remove all positions of this currency
        self.positions
            .retain(|p| p.units.currency != units.currency);

        // Add back the remainder (if non-zero) at the average cost, so a later
        // reduction sees the correct basis instead of a costless position.
        if !new_units.is_zero() {
            self.positions.push(at_avg_cost(new_units));
        }

        self.rebuild_index();

        Ok(BookingResult {
            matched,
            cost_basis,
        })
    }

    /// Collapse every cost-bearing lot of each currency into a single
    /// weighted-average-cost lot. Cost-less (cash) positions are left untouched.
    ///
    /// This realizes the balance of an AVERAGE-booked account, where all lots of
    /// a commodity share one running cost. The journal keeps the real per-lot
    /// costs; only this realized view merges them (matching hledger's pool
    /// model). A currency whose lots net to zero is removed; a currency whose
    /// lots have mismatched cost currencies is left untouched.
    ///
    /// # Errors
    ///
    /// [`OverflowError`] when a currency's lots sum outside `rust_decimal`'s
    /// range. The merged view is a realized balance, so a clamped total would
    /// be rendered as an exact position (#1863).
    pub fn merge_average(&mut self) -> Result<(), OverflowError> {
        let currencies: std::collections::BTreeSet<Currency> = self
            .positions
            .iter()
            .filter(|p| p.cost.is_some())
            .map(|p| p.units.currency.clone())
            .collect();

        for currency in currencies {
            let (total_units, avg) = {
                let matching: Vec<&Position> = self
                    .positions
                    .iter()
                    .filter(|p| p.units.currency == currency && p.cost.is_some())
                    .collect();
                let total_units: Decimal = matching
                    .iter()
                    .try_fold(Decimal::ZERO, |acc, p| acc.checked_add(p.units.number))
                    .ok_or_else(|| OverflowError {
                        currency: currency.clone(),
                    })?;
                let avg = if total_units.is_zero() {
                    None
                } else {
                    average_cost_from_positions(&matching, total_units)
                        .ok()
                        .flatten()
                };
                (total_units, avg)
            };

            // Couldn't average a non-zero position (cost-currency mismatch):
            // leave its lots untouched rather than corrupt them.
            if !total_units.is_zero() && avg.is_none() {
                continue;
            }

            self.positions
                .retain(|p| !(p.units.currency == currency && p.cost.is_some()));
            if let Some((avg_cost, cost_currency)) = avg {
                self.positions.push(Position::with_cost(
                    Amount::new(total_units, currency.clone()),
                    Cost::new(avg_cost, cost_currency),
                ));
            }
        }
        self.rebuild_index();
        Ok(())
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
            .iter_slots()
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

        let cost_basis = Some(Amount::new(
            reduction.checked_mul(avg_cost).ok_or_else(|| {
                BookingError::Overflow(OverflowError {
                    currency: cost_currency.clone(),
                })
            })?,
            cost_currency.clone(),
        ));

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
        self.positions
            .retain_slots(|slot, _| !matching_indices.contains(&slot));

        // Add back a single merged lot with the remainder
        let remaining = total_units + units.number; // units.number is negative for reductions
        if !remaining.is_zero() {
            self.positions.push(Position::with_cost(
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
            self.add(Position::simple(units.clone()))?;
            return Ok(BookingResult {
                matched: SmallVec::new(),
                cost_basis: None,
            });
        }

        let available = total_units.abs();
        let requested = units.number.abs();

        if requested > available {
            // NONE performs no booking, so shorts are always allowed —
            // matching beancount's NONE semantics and NONECorrect.tla. This
            // arm previously returned InsufficientUnits, which made the
            // outcome depend on whether zero was crossed in one step (0 → -2
            // was allowed above; +1 → -1 was rejected here). Found by the
            // TLA+ behavior-replay suite (#1686): consume everything
            // available, then carry the remainder as a negative (short)
            // simple position.
            let sign = units.number.signum();
            let consumed = Amount::new(available * sign, units.currency.clone());
            let result = self.reduce_ordered(&consumed, &CostSpec::default(), false)?;
            self.add(Position::simple(Amount::new(
                (requested - available) * sign,
                units.currency.clone(),
            )))?;
            return Ok(result);
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
        let (result, new_units) = self.plan_from_lot(idx, units)?;
        self.commit_from_lot(idx, units, new_units);
        Ok(result)
    }

    /// The read-only half of [`Self::reduce_from_lot`]: everything up to the
    /// first mutation, returning what WOULD be matched plus the lot's new
    /// units number.
    ///
    /// Split out so `try_reduce` can answer from `&self`. It used to be
    /// `self.clone().reduce(..)`, which deep-copied every lot in the account
    /// to preview a reduction that touches one of them — the dominant
    /// superlinear term in the pipeline (`Position::clone` grew 104x for 10x
    /// the input on the `investment` profiling shape).
    ///
    /// Selection logic lives HERE and only here; the mutating path calls this
    /// too. That is deliberate — `try_reduce` duplicating `reduce`'s selection
    /// is the exact drift that `try_reduce_equivalence` exists to police, and
    /// it had already bitten once before that test was written.
    pub(super) fn plan_from_lot(
        &self,
        idx: usize,
        units: &Amount,
    ) -> Result<(BookingResult, Decimal), BookingError> {
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
        let cost_basis = pos
            .cost
            .as_ref()
            .map(|c| {
                c.total_cost(requested).ok_or_else(|| {
                    BookingError::Overflow(OverflowError {
                        currency: c.currency.clone(),
                    })
                })
            })
            .transpose()?;

        // Record matched
        let (matched, _) = pos.split(requested * pos.units.number.signum());

        // Python scale rule, same as `Inventory::add` — see
        // `crate::decimal::add_python_scale`. A reduction that brings a lot
        // through zero would otherwise drop the scale here while `add` kept
        // it, so the same lot would render differently depending on whether
        // it was last touched by an add or a reduce.
        let new_units = crate::decimal::add_python_scale(pos.units.number, units.number);

        Ok((
            BookingResult {
                matched: smallvec![matched],
                cost_basis,
            },
            new_units,
        ))
    }

    /// The mutating half of [`Self::reduce_from_lot`], applying a
    /// [`Self::plan_from_lot`] result.
    ///
    /// Keeps the incremental cache maintenance the single-lot path always
    /// had: a full `rebuild_index` here would be O(lots) on the commit path
    /// that this split is meant to keep cheap.
    fn commit_from_lot(&mut self, idx: usize, units: &Amount, new_units: Decimal) {
        let currency = self.positions[idx].units.currency.clone();
        let new_pos = Position {
            units: Amount::new(new_units, currency.clone()),
            cost: self.positions[idx].cost.clone(),
        };
        // Drop the old classification before overwriting: a reduction can take
        // a lot through zero and flip its sign bucket.
        self.sign_index_bump(idx, -1);
        self.positions[idx] = new_pos;
        self.sign_index_bump(idx, 1);

        // Update units cache incrementally (units.number is negative for reductions)
        if let Some(stats) = self.units_cache.get_mut(&currency) {
            stats.total = crate::decimal::add_python_scale(stats.total, units.number);
        }

        // Remove if empty, then repair `simple_index`.
        if self.positions[idx].is_empty() {
            self.sign_index_bump(idx, -1);
            self.cost_index_remove(idx);
            self.positions.remove(idx);

            // Removing shifts every later position down one, so the stored
            // indices past `idx` are now off by one. Patch the MAP rather than
            // rescanning the positions to rebuild it.
            //
            // `simple_index` holds at most one entry per currency — cost-less
            // lots of a currency merge into a single lot — so this is O(number
            // of currencies), against O(lots) for the rescan it replaces. On
            // an investment account, where every lot carries a cost and the
            // map is EMPTY, the rescan walked the entire lot list to find
            // nothing at all; it grew 164x for 10x the input on the
            // `investment` profiling shape.
            //
            // Nothing shifted: removal leaves a tombstone, so every
            // surviving lot keeps its slot. Only the entry naming the removed
            // lot has to go — and it CAN name it, because an empty cost spec
            // matches a cost-less position (`matches_cost_spec`:
            // `(None, true) => true`), so STRICT can select and drain one.
            //
            // Before tombstones this also decremented the later entries to
            // follow the shift. Keeping that now would renumber indices that
            // did not move, pointing `add`'s merge at a tombstone — which is
            // exactly what `removing_a_lot_repairs_the_index_of_a_later_cost_less_lot`
            // caught.
            self.simple_index.retain(|_, stored| *stored != idx);
        }
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
            i.add(l).expect("fixture fits in Decimal");
        }
        i
    }

    fn sell_stk(n: i64) -> Amount {
        Amount::new(d(-n), "STK")
    }

    /// A cost-basis overflow part-way through a multi-lot reduction must leave
    /// the inventory untouched.
    ///
    /// `reduce_ordered` states the rule itself — "a failed reduction must
    /// leave the inventory untouched" — and enforced it for the sufficiency
    /// check, which runs up front. The overflow check did NOT get the same
    /// treatment: it lived inside the mutation loop, so a reduction that
    /// overflowed on the third lot returned `Err` with the first two already
    /// drained. The validator reduces against live `LedgerState` inventories,
    /// so that partial drain corrupts every later balance assertion on the
    /// account.
    ///
    /// Computing the whole plan before committing any of it makes the rule
    /// hold for both checks by construction.
    #[test]
    fn an_overflowing_multi_lot_reduction_leaves_the_inventory_untouched() {
        // Two lots whose combined cost basis cannot be represented: each is
        // two thirds of the range, so the first accumulates fine and the sum
        // overflows on the second.
        let huge = Decimal::MAX / Decimal::from(3) * Decimal::from(2);
        let mut inv = Inventory::new();
        for day in 1..=2 {
            let mut cost = Cost::new(huge, "USD");
            cost.date = naive_date(2024, 1, day);
            inv.add(Position::with_cost(Amount::new(Decimal::ONE, "AAPL"), cost))
                .expect("lots fit individually");
        }
        let before: Vec<Position> = inv.positions().cloned().collect();
        assert_eq!(before.len(), 2, "fixture must hold two distinct lots");

        let err = inv
            .reduce(
                &Amount::new(Decimal::from(-2), "AAPL"),
                Some(&CostSpec::default()),
                BookingMethod::Fifo,
            )
            .expect_err("the combined cost basis overflows");
        assert!(
            matches!(err, super::BookingError::Overflow(_)),
            "expected an overflow, got {err:?}",
        );

        let after: Vec<Position> = inv.positions().cloned().collect();
        assert_eq!(
            after, before,
            "the failed reduction drained lots anyway — a partial mutation on \
             the error path is what this pins",
        );
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
        ))
        .expect("fixture fits in Decimal");
        i.add(lot(10, 100, 2)).expect("fixture fits in Decimal"); // the real STK lot
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
        i.add(lot(-10, 50, 1)).expect("fixture fits in Decimal"); // short lot, same sign as a sell
        i.add(lot(10, 100, 2)).expect("fixture fits in Decimal"); // long lot
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
        i.add(lot(-10, 100, 1)).expect("fixture fits in Decimal"); // short STK only; a sell is the same sign
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
    fn reduce_on_large_shared_inventory_does_not_corrupt() {
        // Regression: the rich-workload profiler found a heap-corruption /
        // SIGSEGV when reducing an inventory that had been cloned (imbl O(1)
        // structural share, as the booking engine does for working copies).
        // In-place mutation of the SHARED imbl `Vector` double-freed the interned
        // `Arc<str>` inside `Position`. Needs >64 distinct lots so the `Vector`
        // spans multiple Arc-backed chunks — the representation that actually
        // shares (and corrupted). Without the fix this aborts/segfaults on drop.
        // 100 distinct-cost lots (>64 = the imbl chunk size) so the `Vector`
        // spans multiple Arc-backed chunks — the shared representation that
        // corrupted. Day stays a valid 1..=28 (lots remain distinct by cost).
        // The Miri CI job (`rustledger-core`, strict provenance) executes this
        // and flags the use-after-free deterministically when the guard is gone.
        let mut inv = mk((0i64..100).map(|i| lot(10, 100 + i, ((i % 28) + 1) as u32)));
        let snapshot = inv.clone(); // structurally shares chunks with `inv`
        inv.reduce(
            &sell_stk(700),
            Some(&CostSpec::default()),
            BookingMethod::Fifo,
        )
        .unwrap();
        assert_eq!(inv.units("STK"), dec!(300)); // 1000 - 700
        // The shared snapshot stays independent and intact; `units` re-reads
        // every interned currency, and dropping both must not double-free.
        assert_eq!(snapshot.units("STK"), dec!(1000));
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
        i.add(lot(10, 100, 2)).expect("fixture fits in Decimal");
        i.add(Position::with_cost(
            Amount::new(dec!(10), "OTH"),
            Cost::new(dec!(888), "USD").with_date(naive_date(2024, 1, 1).unwrap()),
        ))
        .expect("fixture fits in Decimal");
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
    fn reduce_average_partial_multi_lot_matches_single_synthetic_lot() {
        // Regression: a partial AVERAGE sale across multiple lots matches a
        // SINGLE synthetic lot of the reduced quantity at the average cost, not
        // every underlying lot. Returning the full lot set made the consumer
        // (book.rs) expand the reduction into one posting per lot, emptying the
        // position and booking a garbage gain.
        let mut i = Inventory::new();
        i.add(lot(10, 150, 1)).expect("fixture fits in Decimal");
        i.add(lot(10, 170, 2)).expect("fixture fits in Decimal");
        let r = i
            .reduce(
                &sell_stk(5),
                Some(&CostSpec::default()),
                BookingMethod::Average,
            )
            .unwrap();

        // One synthetic matched lot at the average cost {160}; basis 5*160=800.
        // Long pool: the matched lot carries the inventory (positive) sign.
        assert_eq!(r.matched.len(), 1);
        assert_eq!(r.cost_basis.as_ref().unwrap().number, dec!(800));
        assert_eq!(r.matched[0].cost.as_ref().unwrap().number, dec!(160));
        assert_eq!(r.matched[0].units.number, dec!(5));

        // 15 STK remain as a single lot carrying the average cost {160}.
        assert_eq!(i.units("STK"), dec!(15));
        let remaining: Vec<&Position> = i
            .positions()
            .filter(|p| p.units.currency == "STK")
            .collect();
        assert_eq!(remaining.len(), 1);
        assert_eq!(remaining[0].cost.as_ref().unwrap().number, dec!(160));
    }

    #[test]
    fn reduce_average_short_cover_matched_lot_carries_inventory_sign() {
        // Covering a short (positive units reducing a negative pool) must return
        // a matched lot with the inventory (negative) sign, like FIFO/ordered.
        let mut i = Inventory::new();
        i.add(Position::with_cost(
            Amount::new(dec!(-10), "STK"),
            Cost::new(dec!(150), "USD"),
        ))
        .expect("fixture fits in Decimal");
        let r = i
            .reduce(
                &Amount::new(dec!(5), "STK"),
                Some(&CostSpec::default()),
                BookingMethod::Average,
            )
            .unwrap();
        assert_eq!(r.matched.len(), 1);
        assert_eq!(r.matched[0].units.number, dec!(-5));
        // Short pool shrinks from -10 to -5.
        assert_eq!(i.units("STK"), dec!(-5));
    }

    #[test]
    fn merge_average_collapses_lots_to_single_weighted_lot() {
        // The realized balance of an AVERAGE account is one pool at the
        // weighted-average cost: (10*150 + 10*170 - 5*160) / 15 = 160.
        let mut i = Inventory::new();
        i.add(lot(10, 150, 1)).expect("fixture fits in Decimal");
        i.add(lot(10, 170, 2)).expect("fixture fits in Decimal");
        i.add(Position::with_cost(
            Amount::new(dec!(-5), "STK"),
            Cost::new(dec!(160), "USD"),
        ))
        .expect("fixture fits in Decimal");
        i.merge_average().expect("fixture fits in Decimal");
        let stk: Vec<&Position> = i
            .positions()
            .filter(|p| p.units.currency == "STK")
            .collect();
        assert_eq!(stk.len(), 1);
        assert_eq!(stk[0].units.number, dec!(15));
        assert_eq!(stk[0].cost.as_ref().unwrap().number, dec!(160));
    }

    #[test]
    fn merge_average_net_zero_removes_lots() {
        let mut i = Inventory::new();
        i.add(lot(10, 150, 1)).expect("fixture fits in Decimal");
        i.add(Position::with_cost(
            Amount::new(dec!(-10), "STK"),
            Cost::new(dec!(160), "USD"),
        ))
        .expect("fixture fits in Decimal");
        i.merge_average().expect("fixture fits in Decimal");
        assert_eq!(
            i.positions().filter(|p| p.units.currency == "STK").count(),
            0
        );
    }

    #[test]
    fn merge_average_leaves_costless_positions_untouched() {
        let mut i = Inventory::new();
        i.add(Position::simple(Amount::new(dec!(100), "USD")))
            .expect("fixture fits in Decimal");
        i.add(lot(10, 150, 1)).expect("fixture fits in Decimal");
        i.merge_average().expect("fixture fits in Decimal");
        // Cash stays; the single STK lot stays a single lot.
        assert_eq!(i.units("USD"), dec!(100));
        assert_eq!(
            i.positions().filter(|p| p.units.currency == "STK").count(),
            1
        );
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
        inv.add(lot(10, 100, 1)).expect("fixture fits in Decimal"); // long STK
        inv.add(lot(30, 200, 2)).expect("fixture fits in Decimal"); // long STK
        inv.add(lot(-5, 999, 3)).expect("fixture fits in Decimal"); // short STK — excluded by the sign filter
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "OTH"), // different currency — excluded
            Cost::new(dec!(888), "USD").with_date(naive_date(2024, 1, 4).unwrap()),
        ))
        .expect("fixture fits in Decimal");
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
    fn reduce_none_exact_succeeds_over_reduction_shorts() {
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(10), "STK")))
            .expect("fixture fits in Decimal");
        assert!(
            inv.reduce(&sell_stk(10), None, BookingMethod::None).is_ok(),
            "exact NONE reduction should succeed"
        );
        // NONE performs no booking, so over-reduction shorts past zero
        // instead of erroring (#1686 — previously InsufficientUnits, which
        // made the outcome depend on whether zero was crossed in one step).
        let mut inv2 = Inventory::new();
        inv2.add(Position::simple(Amount::new(dec!(10), "STK")))
            .expect("fixture fits in Decimal");
        assert!(
            inv2.reduce(&sell_stk(15), None, BookingMethod::None)
                .is_ok(),
            "NONE over-reduction must short, not error (#1686)"
        );
        assert_eq!(inv2.units("STK"), dec!(-5));
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
