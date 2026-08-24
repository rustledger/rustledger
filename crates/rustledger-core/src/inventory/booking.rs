//! Booking method implementations for Inventory.
//!
//! This module contains the implementation of all booking methods (STRICT,
//! `STRICT_WITH_SIZE`, FIFO, LIFO, HIFO, AVERAGE, NONE) used to reduce positions
//! from an inventory.

use jiff::civil::Date as NaiveDate;
use rust_decimal::Decimal;
use rust_decimal::prelude::Signed;

use smallvec::{SmallVec, smallvec};

use super::{
    BookingError, BookingMethod, BookingResult, Inventory, LotOrder, MatchedLots, OverflowError,
};
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

/// What a `{*}` merge would do, computed without doing it.
///
/// The plan half of [`Inventory::reduce_merge`]; see [`Inventory::plan_merge`].
struct MergePlan {
    /// Slots that merge into the pool.
    matching_indices: std::collections::HashSet<usize>,
    /// Units held across those slots.
    total_units: Decimal,
    /// The pool's per-unit cost, or `None` when the lots carry no cost.
    pool: Option<Amount>,
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
            BookingMethod::Fifo => self
                .plan_ordered(units, &spec, LotOrder::Date)
                .map(|(r, _)| r),
            BookingMethod::Lifo => self
                .plan_ordered(units, &spec, LotOrder::DateDescending)
                .map(|(r, _)| r),
            BookingMethod::Hifo => self.plan_hifo(units, &spec).map(|(r, _)| r),
            BookingMethod::StrictWithSize => {
                self.plan_strict_with_size(units, &spec).map(|(r, _)| r)
            }
            BookingMethod::Average | BookingMethod::None => {
                self.clone().reduce(units, cost_spec, method)
            }
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
                // Two or more lots match, so the spec the user wrote does not
                // name one. STRICT's contract is to refuse to guess, and this
                // arm is deliberately the whole of it — the only escape is the
                // total-match exception below.
                //
                // The one escape besides that is lots which are identical in
                // EVERY cost field — number, currency, date and label. Those
                // are indistinguishable by construction, so draining them in
                // date order cannot be observed.
                //
                // This used to compare the number and currency ALONE, on the
                // stated grounds that "the user could not have observed a
                // different outcome" and that "beancount falls back to FIFO in
                // that case". Both were wrong (#2097). Beancount's
                // `booking_method_STRICT` has no fallback at all: more than one
                // match is the total-match exception or an
                // `AmbiguousMatchError`. And ignoring the date made the outcome
                // very much observable — selling 16 of
                // `4 GLOB {74.09, 2022-05-10}` + `16 GLOB {74.09, 2024-02-09}`
                // leaves 4 GLOB dated 2024 under FIFO and 4 GLOB dated 2022
                // under any other choice. Same cost basis, which is what made
                // it quiet, but a different HOLDING PERIOD — and this codebase
                // acts on holding periods, in `report capgains`'s short/long
                // split and in the per-lot IRR eligibility predicate. That is a
                // tax-visible decision, made silently, under the one booking
                // method whose entire purpose is to make the user state it.
                //
                // Why keep the narrowed form rather than delete it outright:
                // beancount's `Inventory` is keyed by `(currency, cost)`, so
                // two buys of the same commodity at the same price on the same
                // day are ONE position there and can never be ambiguous. Ours
                // stays two lots, so deleting this arm would reject a ledger
                // beancount accepts — a very ordinary one. Comparing the full
                // cost reproduces beancount's observable behavior without
                // changing how positions are stored; merging them at `add`
                // would be the more faithful model and a much larger change
                // (`Inventory::len` counts lots, and `currency_accounts`
                // branches on it).
                //
                // The user disambiguates by naming the lot: `{74.09 USD,
                // 2022-05-10}`, a label, or an account booked FIFO/HIFO if
                // they genuinely do not care which goes.
                let first_cost = self.positions[matching_indices[0]].cost.as_ref();
                let all_indistinguishable = matching_indices
                    .iter()
                    .skip(1)
                    .all(|&i| self.positions[i].cost.as_ref() == first_cost);

                if all_indistinguishable {
                    let (result, updates) = self.plan_ordered(units, spec, LotOrder::Date)?;
                    return Ok((result, ReductionPlan::Updates(updates)));
                }

                // Total match exception: if the reduction equals the sum of all
                // matching lots, every matched lot is consumed, so no lot
                // survives to carry a date and the choice cannot be observed.
                // Beancount has this same exception, and for the same reason.
                let total_units: Decimal = matching_indices
                    .iter()
                    .map(|&i| self.positions[i].units.number.abs())
                    .sum();
                if total_units == units.number.abs() {
                    let (result, updates) = self.plan_ordered(units, spec, LotOrder::Date)?;
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
    /// `STRICT_WITH_SIZE`: an explicit cost, disambiguated by lot size.
    ///
    /// Planned from `&self` so `try_reduce` can preview it without copying the
    /// inventory. It used to be reachable only through `self.clone().reduce()`
    /// — an O(lots) copy per reducing posting, which is quadratic across a
    /// ledger and was most of this method's cost (#2091). The conversion is the
    /// one #2061 left as "mechanical" when it split STRICT, FIFO and LIFO.
    pub(super) fn plan_strict_with_size(
        &self,
        units: &Amount,
        spec: &CostSpec,
    ) -> Result<(BookingResult, ReductionPlan), BookingError> {
        // Narrow through the cost index before filtering, the way `plan_strict`
        // does. This walked every slot in the account on every reduction. A
        // spec naming a cost has a handful of candidates; one that names none
        // still scans, because it can match anything.
        let candidates: Vec<usize> = self.cost_candidates(units, spec).unwrap_or_else(|| {
            self.positions
                .iter_slots()
                .filter(|(_, p)| p.units.currency == units.currency)
                .map(|(i, _)| i)
                .collect()
        });
        let matching_indices: Vec<usize> = candidates
            .into_iter()
            .filter(|&i| {
                self.positions.get(i).is_some_and(|p| {
                    p.units.currency == units.currency
                        && !p.is_empty()
                        && p.can_reduce(units)
                        && p.matches_cost_spec(spec)
                })
            })
            .collect();

        let from_lot = |idx: usize| {
            self.plan_from_lot(idx, units)
                .map(|(result, new_units)| (result, ReductionPlan::FromLot { idx, new_units }))
        };

        match matching_indices.len() {
            0 => Err(BookingError::NoMatchingLot {
                currency: units.currency.clone(),
                cost_spec: spec.clone(),
            }),
            1 => from_lot(matching_indices[0]),
            n => {
                // A lot of exactly the reduction's size disambiguates. When
                // SEVERAL do, the OLDEST wins — beancount sorts the size
                // matches by `cost.date` and takes the first, and the choice
                // is observable in both the basis realized and the holding
                // period of whatever survives.
                //
                // This used to take the first candidate in slot order, which
                // is insertion order. That is usually date order and so
                // usually agreed by accident, but a lot carrying an explicit
                // cost date (`{100.00 USD, 2030-01-01}`) is inserted when its
                // transaction is booked and dated whenever the user said. Buy
                // 10 X {100.00, 2030-01-01} then 10 X {200.00, 2020-01-01} and
                // sell 10 X {}: beancount sells the 2020 lot and leaves 1000
                // USD of basis, slot order sells the 2030 lot and leaves 2000.
                // Neither reports anything.
                //
                // Ties break on slot index so the result stays deterministic
                // when two size matches share a date; `None` dates sort last,
                // since a booked lot always has one and an unbooked lot is not
                // the one the user meant.
                let exact = matching_indices
                    .iter()
                    .copied()
                    .filter(|&i| self.positions[i].units.number.abs() == units.number.abs())
                    .min_by_key(|&i| {
                        (
                            self.positions[i]
                                .cost
                                .as_ref()
                                .and_then(|c| c.date)
                                .map_or((1, NaiveDate::MAX), |d| (0, d)),
                            i,
                        )
                    });
                if let Some(idx) = exact {
                    return from_lot(idx);
                }
                // Total match exception: selling the whole matched inventory
                // makes the choice of lot irrelevant.
                let total_units: Decimal = matching_indices
                    .iter()
                    .map(|&i| self.positions[i].units.number.abs())
                    .sum();
                if total_units == units.number.abs() {
                    let (result, updates) = self.plan_ordered(units, spec, LotOrder::Date)?;
                    return Ok((result, ReductionPlan::Updates(updates)));
                }
                Err(BookingError::AmbiguousMatch {
                    num_matches: n,
                    currency: units.currency.clone(),
                })
            }
        }
    }

    pub(super) fn reduce_strict_with_size(
        &mut self,
        units: &Amount,
        spec: &CostSpec,
    ) -> Result<BookingResult, BookingError> {
        let (result, plan) = self.plan_strict_with_size(units, spec)?;
        self.commit_plan(&plan, units);
        Ok(result)
    }

    pub(super) fn reduce_fifo(
        &mut self,
        units: &Amount,
        spec: &CostSpec,
    ) -> Result<BookingResult, BookingError> {
        self.reduce_ordered(units, spec, LotOrder::Date)
    }

    /// LIFO booking: reduce from newest lots first.
    pub(super) fn reduce_lifo(
        &mut self,
        units: &Amount,
        spec: &CostSpec,
    ) -> Result<BookingResult, BookingError> {
        self.reduce_ordered(units, spec, LotOrder::DateDescending)
    }

    /// HIFO booking: reduce from highest-cost lots first.
    /// HIFO booking: take from the most expensive lots first.
    ///
    /// The plan half of the ordered walk with a cost key, which is all HIFO
    /// ever was. It used to carry its own copy of that walk — scan every slot,
    /// sort the survivors by cost, sum them for sufficiency, then take — which
    /// is O(lots) per reduction and was 18s on a 20,000-transaction ledger
    /// against FIFO's 0.27s (#2091). Sharing `plan_ordered` gives it the
    /// maintained index, the early stop, and a plan half so `try_reduce` can
    /// preview without cloning the inventory.
    pub(super) fn plan_hifo(
        &self,
        units: &Amount,
        spec: &CostSpec,
    ) -> Result<(BookingResult, SmallVec<[(usize, Decimal); 1]>), BookingError> {
        self.plan_ordered(units, spec, LotOrder::CostDescending)
    }

    pub(super) fn reduce_hifo(
        &mut self,
        units: &Amount,
        spec: &CostSpec,
    ) -> Result<BookingResult, BookingError> {
        let (result, updates) = self.plan_hifo(units, spec)?;
        self.commit_updates(&updates);
        Ok(result)
    }

    pub(super) fn reduce_ordered(
        &mut self,
        units: &Amount,
        spec: &CostSpec,
        order: LotOrder,
    ) -> Result<BookingResult, BookingError> {
        let (result, updates) = self.plan_ordered(units, spec, order)?;
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
        order: LotOrder,
    ) -> Result<(BookingResult, SmallVec<[(usize, Decimal); 1]>), BookingError> {
        let mut remaining = units.number.abs();
        let mut matched: MatchedLots = SmallVec::new();
        let mut cost_basis = Decimal::ZERO;
        let mut cost_currency = None;

        // Candidates in FIFO order.
        //
        // `ordered_index` already holds this currency's lots — every one of
        // them, cost-less included, since an empty spec matches those too — in
        // (date, slot) order, so the common path neither scans every slot nor
        // sorts per call. It did both, once per reduction, and `{}` is how
        // FIFO sells are written — so that was the normal case (#2083).
        //
        // The predicate still runs per candidate: the index knows nothing
        // about sign, emptiness or what this spec matches, and a stale entry
        // for a drained lot is expected, since removal is best-effort.
        let scanned: Option<Vec<usize>> =
            if self.ordered_candidates(&units.currency, order).is_some() {
                None
            } else {
                // No index — a shared snapshot, or one never rebuilt. Scanning is
                // the only correct answer, and it is what this always did.
                let mut all: Vec<usize> = self
                    .positions
                    .iter_slots()
                    .filter(|(_, p)| p.units.currency == units.currency)
                    .map(|(i, _)| i)
                    .collect();
                all.sort_by_key(|&i| (self.order_key(order, i), i));
                Some(all)
            };
        let candidates: &[usize] = match &scanned {
            Some(all) => all,
            None => self
                .ordered_candidates(&units.currency, order)
                .expect("the branch above proved it is Some"),
        };

        let keeps = |i: usize| {
            self.positions.get(i).is_some_and(|p| {
                p.units.currency == units.currency
                    && !p.is_empty()
                    && p.units.number.signum() != units.number.signum()
                    && p.matches_cost_spec(spec)
            })
        };

        // Sufficiency used to be checked up front, by summing every matching
        // lot before taking any. That was needed when this function mutated;
        // since the plan/commit split (#2061) it only computes and the caller
        // commits, so exhausting the walk reports the same shortfall with the
        // same total, having visited the same lots. The invariant it protected
        // — a failed reduction leaves the inventory untouched — is structural
        // now, and `booking_properties.rs` still pins it.
        let mut updates: SmallVec<[(usize, Decimal); 1]> = SmallVec::new();
        let mut seen_any = false;
        let mut available_total = Decimal::ZERO;
        let mut overflow: Option<OverflowError> = None;

        // Always forward. The direction of a method lives in its `order_key`,
        // never here: reversing the WALK reverses the slot tiebreak along with
        // the sort key, which is how LIFO came to take the last of two
        // same-date lots while FIFO and HIFO take the first (#2115).
        for idx in candidates.iter().copied() {
            if !keeps(idx) {
                continue;
            }
            seen_any = true;
            let pos = &self.positions[idx];
            available_total += pos.units.number.abs();
            let available = pos.units.number.abs();
            let take = remaining.min(available);

            // Calculate cost basis for this portion (checked — see the
            // matching site in the FIFO/LIFO ladder above).
            if let Some(cost) = &pos.cost {
                if cost_currency.is_none() {
                    cost_currency = Some(cost.currency.clone());
                }
                // Recorded, not returned. Sufficiency used to be settled before
                // any basis arithmetic ran, so a reduction that was BOTH short
                // of units and unrepresentable reported the shortfall — the
                // actionable half. Returning here would report the overflow
                // instead, which is a behavior change nothing asked for.
                match take
                    .checked_mul(cost.number)
                    .and_then(|v| cost_basis.checked_add(v))
                {
                    Some(v) => cost_basis = v,
                    None => {
                        overflow.get_or_insert_with(|| OverflowError {
                            currency: cost.currency.clone(),
                        });
                    }
                }
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

            // Covered: stop here rather than walking the rest of the account.
            // `available_total` is left partial on purpose — it feeds the
            // shortfall message only, which is unreachable once the reduction
            // is satisfied. Walking on to complete a number nobody reads is
            // what made this O(lots): the spec is concrete by the time `apply`
            // re-derives, so most later lots fail the predicate and the loop
            // ran the cost comparison against every one of them.
            if remaining.is_zero() {
                break;
            }
        }

        // No lot of this currency matched the spec at all.
        if !seen_any {
            return Err(BookingError::NoMatchingLot {
                currency: units.currency.clone(),
                cost_spec: spec.clone(),
            });
        }
        // Lots matched but did not cover the reduction. Reported with the same
        // total the up-front sum produced, because reaching here means the
        // walk visited every matching lot.
        if !remaining.is_zero() {
            return Err(BookingError::InsufficientUnits {
                currency: units.currency.clone(),
                requested: units.number.abs(),
                available: available_total,
            });
        }
        // Only now: the reduction is satisfiable, so the arithmetic is what
        // failed.
        if let Some(error) = overflow {
            return Err(BookingError::Overflow(error));
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
    /// Apply a multi-lot plan, repairing the caches rather than rebuilding
    /// them.
    ///
    /// This used to `retain` away the drained lots and then `rebuild_index()`,
    /// which is two walks of every slot plus a rehash of every key — per
    /// reduction. In a FIFO ledger, where reductions are frequent and lots
    /// accumulate, that is the whole cost: 20k transactions took 8.9s, of
    /// which 7.1s was the rebuild (#2083).
    ///
    /// `updates` already names every slot that changed, so the repair is
    /// proportional to the lots the reduction touched rather than to the lots
    /// the account holds. Same treatment `commit_from_lot` got in #2063, for
    /// the same reason; this is the multi-lot half of that change.
    fn commit_updates(&mut self, updates: &[(usize, Decimal)]) {
        // Every update names a lot of the same currency, because every producer
        // of `ReductionPlan::Updates` filters on `units.currency` before
        // planning. This repair DEPENDS on that — it adjusts one currency's
        // running total — where the old `rebuild_index()` recomputed them all
        // and so could not notice the invariant being violated.
        //
        // Checked here rather than after the loop: by then the drained lots are
        // tombstones, and indexing one panics.
        debug_assert!(
            updates.windows(2).all(|pair| {
                self.positions[pair[0].0].units.currency == self.positions[pair[1].0].units.currency
            }),
            "commit_updates was given lots of more than one currency; the units \
             cache is adjusted per currency and would silently drift",
        );

        let mut delta = Decimal::ZERO;
        let mut currency = None;

        for &(idx, new_units) in updates {
            let previous = self.positions[idx].units.number;
            delta += new_units - previous;
            if currency.is_none() {
                currency = Some(self.positions[idx].units.currency.clone());
            }

            // Drop the old classification before overwriting: a reduction can
            // take a lot through zero and flip its sign bucket.
            self.sign_index_bump(idx, -1);
            self.positions[idx].units.number = new_units;
            self.sign_index_bump(idx, 1);

            if self.positions[idx].is_empty() {
                self.sign_index_bump(idx, -1);
                self.cost_index_remove(idx);
                self.positions.remove(idx);
                // Removal leaves a tombstone, so no surviving lot is
                // renumbered and only the entry naming this lot has to go. An
                // empty cost spec matches a cost-less position, so ordered
                // selection can drain one and this map can name it.
                self.units_cache
                    .values_mut()
                    .filter(|stats| stats.simple_slot == Some(idx))
                    .for_each(|stats| stats.simple_slot = None);
            }
        }

        // One adjustment for the whole plan: see the assertion at the top.
        if let Some(currency) = currency
            && let Some(stats) = self.units_cache.get_mut(&currency)
        {
            stats.total = crate::decimal::add_python_scale(stats.total, delta);
        }
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

    /// What `{*}` would merge, computed from `&self`.
    ///
    /// The selection half of [`Self::reduce_merge`], split out so the pool cost
    /// can be known WITHOUT building it (#2068). `reduce_merge` is the only
    /// mutating caller and it goes through here, so there is one implementation
    /// of "which lots merge and at what average" — the duplication that the
    /// plan/commit split (#2061) exists to prevent.
    ///
    /// `pool` is `None` when the matched lots carry no cost, which is
    /// `reduce_merge`'s AVERAGE fallback rather than an error.
    fn plan_merge(&self, units: &Amount) -> Result<MergePlan, BookingError> {
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

        let matching_refs: Vec<&Position> = matching.iter().map(|(_, p)| *p).collect();
        let pool = average_cost_from_positions(&matching_refs, total_units)?
            .map(|(number, currency)| Amount::new(number, currency));

        Ok(MergePlan {
            matching_indices: matching.iter().map(|(i, _)| *i).collect(),
            total_units,
            pool,
        })
    }

    /// The per-unit pool cost `{*}` would produce here, without producing it.
    ///
    /// `Ok(None)` means there is no pool cost to compare against — cost-less
    /// lots, where `{*}` degrades to AVERAGE. Errors are the ones the reduction
    /// itself would raise (no matching lots, insufficient units); a caller
    /// checking a precondition should let the reduction report them rather than
    /// pre-empting it, so that one function keeps owning the message.
    ///
    /// Exists so `BookingEngine::apply` can verify a carried `{*}` against the
    /// cost booking recorded BEFORE the merge mutates anything (#2068).
    pub fn merged_pool_cost(&self, units: &Amount) -> Result<Option<Amount>, BookingError> {
        Ok(self.plan_merge(units)?.pool)
    }

    /// Cost merge `{*}`: merge all lots of the currency into a single
    /// weighted-average-cost lot, then reduce from it.
    ///
    /// Example: 10 AAPL {150 USD} + 10 AAPL {160 USD} merged = 20 AAPL {155 USD}.
    /// Reducing 5 AAPL {*} takes 5 from the merged 20 AAPL {155 USD} lot.
    pub(super) fn reduce_merge(&mut self, units: &Amount) -> Result<BookingResult, BookingError> {
        let plan = self.plan_merge(units)?;
        let MergePlan {
            matching_indices,
            total_units,
            pool: Some(pool),
        } = plan
        else {
            // Cost-less lots: there is no pool to build (`plan_merge` says so),
            // so `{*}` degrades to AVERAGE, exactly as before the plan split.
            return self.reduce_average(units);
        };
        let reduction = units.number.abs();
        let (avg_cost, cost_currency) = (pool.number, pool.currency);

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
            let result = self.reduce_ordered(&consumed, &CostSpec::default(), LotOrder::Date)?;
            self.add(Position::simple(Amount::new(
                (requested - available) * sign,
                units.currency.clone(),
            )))?;
            return Ok(result);
        }

        // Reduce positions proportionally (simplified: just reduce first matching)
        self.reduce_ordered(units, &CostSpec::default(), LotOrder::Date)
    }

    /// Reduce from a specific lot.
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
            self.units_cache
                .values_mut()
                .filter(|stats| stats.simple_slot == Some(idx))
                .for_each(|stats| stats.simple_slot = None);
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
    use super::LotOrder;
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

    /// A multi-lot reduction removes what it drained, and nothing else.
    ///
    /// `commit_updates` used to `retain(|p| !p.is_empty())` over the whole
    /// inventory, so any reduction that crossed two lots also swept away every
    /// unrelated zero-unit position as a side effect. Zero-unit lots are not
    /// scrap: `Inventory::len` counts them and `currency_accounts` branches on
    /// `len() == 1`, so sweeping them changed what other surfaces reported
    /// depending on whether a reduction happened to be multi-lot.
    #[test]
    fn a_multi_lot_reduction_leaves_unrelated_empty_lots_alone() {
        let mut inv = mk([lot(10, 100, 1), lot(10, 200, 2)]);
        // An unrelated zero-unit position in another commodity. Netted to
        // zero rather than added as zero: `add` drops a zero-unit position
        // outright, so the only way one exists is a cost-less lot merging
        // through zero — which is exactly the case `Inventory::len`'s contract
        // is about.
        inv.add(Position::simple(Amount::new(d(5), "ZERO")))
            .expect("fixture fits in Decimal");
        inv.add(Position::simple(Amount::new(d(-5), "ZERO")))
            .expect("fixture fits in Decimal");
        let before = inv.len();

        // Cross both STK lots, draining the first.
        inv.reduce(
            &Amount::new(d(-15), "STK"),
            Some(&CostSpec::default()),
            BookingMethod::Fifo,
        )
        .expect("15 of 20 units are there");

        assert_eq!(
            inv.len(),
            before - 1,
            "exactly the drained lot should be gone: the untouched zero-unit \
             position is not this reduction's business",
        );
    }

    /// Insufficiency outranks overflow, as it did before the walk was made lazy.
    #[test]
    fn insufficient_units_are_reported_even_when_the_basis_would_overflow() {
        // A lot whose cost basis cannot be represented, and a reduction asking
        // for more units than exist.
        let huge = Decimal::MAX / d(2);
        let mut inv = Inventory::new();
        inv.add(Position::with_cost(
            Amount::new(d(10), "STK"),
            Cost::new(huge, "USD").with_date(naive_date(2024, 1, 1).unwrap()),
        ))
        .expect("fixture fits in Decimal");

        let err = inv
            .plan_ordered(
                &Amount::new(d(-99), "STK"),
                &CostSpec::default(),
                LotOrder::Date,
            )
            .expect_err("99 units are not there");
        assert!(
            matches!(err, crate::BookingError::InsufficientUnits { .. }),
            "the shortfall is the actionable error, not the arithmetic it would \
             have done on the way: {err:?}",
        );
    }

    /// HIFO takes costed lots before cost-less ones.
    ///
    /// A cost-less lot has no cost to compare, and an empty cost spec matches
    /// it, so it is a candidate. The scan this replaced counted it as zero
    /// before reversing, which put it last; ordering on `Option<Decimal>`
    /// would put it FIRST, because `None` sorts before `Some`. Same lots,
    /// opposite lot chosen.
    #[test]
    fn hifo_takes_costed_lots_before_costless_ones() {
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(d(10), "STK")))
            .expect("fixture fits in Decimal");
        inv.add(lot(10, 100, 1)).expect("fixture fits in Decimal");

        let result = inv
            .reduce(
                &Amount::new(d(-5), "STK"),
                Some(&CostSpec::default()),
                BookingMethod::Hifo,
            )
            .expect("5 of 20 units are there");

        assert_eq!(
            result.matched[0].cost.as_ref().map(|c| c.number),
            Some(d(100)),
            "the 100 USD lot outranks the cost-less one",
        );
        assert_eq!(
            result.cost_basis.map(|b| b.number),
            Some(d(500)),
            "and the basis comes from it",
        );
    }

    /// The ordered index selects exactly what the scan selects (#2083).
    ///
    /// `plan_ordered` used to sort every matching lot on every call; it now
    /// walks a maintained (date, slot) index and stops once the reduction is
    /// covered. That is only sound if the index reproduces the scan's order
    /// exactly — including the stable-sort tiebreak, `None` dates sorting
    /// first, and lots added out of date order — so this runs both paths over
    /// the same inventory and compares.
    ///
    /// Clearing `ordered_index` is what forces the scan: an empty index is
    /// how a shared snapshot looks, and the fallback exists for exactly that.
    ///
    /// What this does NOT check is whether the ORDER is the right one. Both
    /// sides call `order_key`, so reversing it moves them together and this
    /// test stays green — verified by mutating it. The orderings themselves
    /// are pinned by the method tests (`test_hifo_reduces_highest_cost_first`,
    /// `test_fifo_respects_dates` and their neighbors), which is the division
    /// of labor: those say what order a method takes lots in, this says the
    /// index reproduces whatever that order is.
    #[test]
    fn the_ordered_index_selects_what_the_scan_selects() {
        // Deliberately awkward: out-of-order dates, a duplicate date, a
        // date-less lot, a second currency, and a cost-less lot.
        let mut inv = Inventory::new();
        for lot in [
            lot(10, 100, 5),
            lot(10, 101, 2),
            lot(10, 102, 9),
            lot(10, 103, 2),
            Position::with_cost(Amount::new(d(10), "STK"), Cost::new(d(104), "USD")),
            Position::with_cost(Amount::new(d(10), "OTH"), Cost::new(d(105), "USD")),
            Position::simple(Amount::new(d(10), "STK")),
        ] {
            inv.add(lot).expect("fixture fits in Decimal");
        }

        let specs = [
            CostSpec::default(),
            CostSpec {
                number: Some(crate::CostNumber::PerUnit { value: d(101) }),
                currency: Some("USD".into()),
                ..CostSpec::default()
            },
            CostSpec {
                date: Some(naive_date(2024, 1, 2).unwrap()),
                ..CostSpec::default()
            },
        ];

        for order in [
            LotOrder::Date,
            // LIFO's ordering. It used to be `(Date, reverse: true)`; the
            // direction moved into the key so the slot tiebreak stops being
            // reversed with it (#2115).
            LotOrder::DateDescending,
            // HIFO: the cost ordering added in #2091. Its tiebreak has to match
            // the `sort_by_key(Reverse(cost))` it replaced — stable, so equal
            // costs stayed in ascending slot order.
            LotOrder::CostDescending,
        ] {
            for spec in &specs {
                {
                    for take in [1i64, 15, 45] {
                        let units = Amount::new(d(-take), "STK");

                        // Build it explicitly: `reduce` is what normally triggers
                        // the build, and calling `plan_ordered` directly would
                        // otherwise leave the index empty and compare the scan
                        // against itself. That vacuous version of this test passed
                        // against a deliberately reversed tiebreak.
                        let mut indexing = inv.clone();
                        indexing.build_ordered_index(order);
                        assert!(
                            indexing.ordered_index.is_some(),
                            "the fixture must produce an index, or this test compares \
                         the scan against itself",
                        );
                        let indexed = indexing.plan_ordered(&units, spec, order);

                        let mut scanning = inv.clone();
                        scanning.ordered_index = None;
                        let scanned = scanning.plan_ordered(&units, spec, order);

                        match (indexed, scanned) {
                            (Ok((a_result, a_updates)), Ok((b_result, b_updates))) => {
                                assert_eq!(
                                    a_updates, b_updates,
                                    "index and scan chose different lots for {spec:?} \
                                 take={take}",
                                );
                                assert_eq!(
                                    a_result.cost_basis, b_result.cost_basis,
                                    "index and scan disagree on cost basis for {spec:?} \
                                 take={take}",
                                );
                            }
                            (Err(a), Err(b)) => assert_eq!(
                                a.to_string(),
                                b.to_string(),
                                "index and scan report different errors for {spec:?} \
                             take={take}",
                            ),
                            (a, b) => panic!(
                                "index and scan disagree on success for {spec:?} \
                             order={order:?} take={take}: {a:?} vs {b:?}"
                            ),
                        }
                    }
                }
            }
        }
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
        // `DateDescending` ordering from FIFO's 2000).
        assert_eq!(basis(&r), dec!(2500));
        assert_eq!(r.matched[0].cost.as_ref().unwrap().number, dec!(200));
    }

    /// Every ordered method breaks a tie the same way: the lot that appears
    /// FIRST in the file wins.
    ///
    /// This is the property a reversed walk silently broke. LIFO used to take
    /// the LAST of two same-date lots while FIFO and HIFO took the first,
    /// because `candidates.iter().rev()` reversed the slot tiebreak along with
    /// the sort key (#2115). Nothing caught it: the tiebreak is invisible to
    /// any assertion on units or total basis, so `test_hifo_with_tie_breaking`
    /// — whose whole subject is this — passed with the tiebreak reversed at
    /// every sort site, because all of its lots share one cost.
    ///
    /// Each case below ties on the key its OWN method sorts by, so the primary
    /// key cannot decide the outcome and only the tiebreak can. Asserting on
    /// the identity of the consumed lot rather than on its value is the point:
    /// consuming the wrong lot at the same total is exactly the failure that
    /// hides from a basis assertion.
    #[test]
    fn ordered_methods_break_ties_on_insertion_order() {
        // Same date, two costs. FIFO and LIFO both sort on date, so neither
        // can separate these by its primary key.
        for method in [BookingMethod::Fifo, BookingMethod::Lifo] {
            let inv = mk([lot(1, 10, 3), lot(1, 12, 3)]);
            let r = try_reduce(&inv, &sell_stk(1), method);
            assert_eq!(
                r.matched[0].cost.as_ref().unwrap().number,
                dec!(10),
                "{method:?} must consume the FIRST of two same-date lots, not the last",
            );
        }

        // Same cost, two dates. HIFO sorts on cost, so its primary key cannot
        // separate these.
        let inv = mk([lot(1, 11, 3), lot(1, 11, 4)]);
        let r = try_reduce(&inv, &sell_stk(1), BookingMethod::Hifo);
        assert_eq!(
            r.matched[0].cost.as_ref().unwrap().date,
            Some(naive_date(2024, 1, 3).unwrap()),
            "HIFO must consume the FIRST of two same-cost lots, not the last",
        );
    }

    /// A date-less lot is consumed LAST under LIFO, not first.
    ///
    /// `DateDescending` holds `Reverse<Option<NaiveDate>>`, so `None` — which
    /// normally sorts before every `Some` — lands at the END. That is where
    /// the reversed walk it replaced left date-less lots, so this is the half
    /// of the #2115 change that must NOT move.
    ///
    /// The distinction is one layer of nesting: `Option<Reverse<NaiveDate>>`
    /// is equally plausible to write and puts date-less lots FIRST. No other
    /// test separates the two. `the_ordered_index_selects_what_the_scan_selects`
    /// calls `order_key` on both sides, so it moves with any change to the
    /// key, and every other LIFO test uses dated lots only.
    #[test]
    fn lifo_takes_the_date_less_lot_last() {
        let mut inv = Inventory::new();
        // Date-less first in the file, so slot order alone would take it first
        // and cannot be what produces the expected answer.
        inv.add(Position::with_cost(
            Amount::new(d(10), "STK"),
            Cost::new(d(100), "USD"),
        ))
        .expect("fixture fits in Decimal");
        inv.add(lot(10, 200, 1)).expect("fixture fits in Decimal");

        let r = try_reduce(&inv, &sell_stk(15), BookingMethod::Lifo);
        assert_eq!(
            r.matched[0].cost.as_ref().unwrap().number,
            dec!(200),
            "LIFO must reach the DATED lot before the date-less one",
        );
        // 10 @200 then 5 @100 = 2500. Date-less-first would be 2000.
        assert_eq!(basis(&r), dec!(2500));
    }

    /// A lot acquired AFTER the index exists lands in LIFO order too.
    ///
    /// `ordered_index` is built on the first ordered reduction and then
    /// maintained by `ordered_index_insert` on every later `add`. Those are
    /// two different code paths and only the first one was covered:
    /// `the_ordered_index_selects_what_the_scan_selects` calls
    /// `build_ordered_index` directly, so it never exercises an incremental
    /// insert at all.
    ///
    /// The distinction matters most for `DateDescending`, where a newly
    /// acquired lot is the NEWEST and therefore belongs at the FRONT — the
    /// opposite end from where every ascending order puts it. An insert that
    /// appended would be invisible to FIFO and wrong for LIFO.
    #[test]
    fn lifo_orders_a_lot_added_after_the_index_was_built() {
        let mut inv = mk([lot(10, 100, 1), lot(10, 200, 2)]);

        // Forces the index to exist; 20 held, take 5 off the newest (day 2).
        let first = inv
            .reduce(&sell_stk(5), None, BookingMethod::Lifo)
            .expect("15 units remain");
        assert_eq!(first.matched[0].cost.as_ref().unwrap().number, dec!(200));

        // Acquired last, so LIFO must reach it FIRST — and it has to travel
        // to the front of a descending index to get there.
        inv.add(lot(10, 300, 3)).expect("fixture fits in Decimal");

        let r = inv
            .reduce(&sell_stk(10), None, BookingMethod::Lifo)
            .expect("25 units remain");
        assert_eq!(
            r.matched[0].cost.as_ref().unwrap().number,
            dec!(300),
            "a lot added after the index was built must still sort newest-first",
        );
        assert_eq!(basis(&r), dec!(3000));
    }

    /// Reordering INTERCHANGEABLE acquisitions does not change what is
    /// consumed.
    ///
    /// Two lots agreeing on commodity, cost, cost currency, date and label are
    /// interchangeable: no recorded attribute separates them, so `add` stores
    /// them as ONE position. That is what makes the outcome independent of the
    /// order they happen to be written in, and it is why a cost basis no
    /// longer depends on an editing accident (#2118).
    ///
    /// Before this rule, `A B C` and `A C B` disagreed by 50 USD of remaining
    /// basis on exactly these fixtures.
    ///
    /// Both code paths are exercised deliberately. `try_reduce` on a fresh
    /// inventory sorts a scanned list; a reduction after the index exists
    /// places later acquisitions through `ordered_index_insert`.
    #[test]
    fn interchangeable_lots_consume_independently_of_write_order() {
        let a = || lot(10, 10, 2);
        let b = || lot(10, 20, 2);
        let c = || lot(10, 10, 2);

        // A and C merge, so any ledger writing B after the first acquisition
        // holds the same two positions and consumes identically.
        let consumed = |lots: [Position; 3]| -> Vec<(Decimal, Decimal)> {
            let inv = mk(lots);
            assert_eq!(inv.len(), 2, "A and C are interchangeable: one position");
            try_reduce(&inv, &sell_stk(15), BookingMethod::Fifo)
                .matched
                .iter()
                .map(|m| (m.cost.as_ref().unwrap().number, m.units.number.abs()))
                .collect()
        };

        let after_first = [
            ("A B C", consumed([a(), b(), c()])),
            ("A C B", consumed([a(), c(), b()])),
            ("C A B", consumed([c(), a(), b()])),
            ("C B A", consumed([c(), b(), a()])),
        ];
        for (name, got) in &after_first {
            assert_eq!(
                got,
                &vec![(dec!(10), dec!(15))],
                "{name}: 15 units all come from the merged 10.00 position",
            );
        }

        // The same property through the MAINTAINED INDEX rather than the scan.
        let via_index = |lots: [Position; 3]| -> Vec<Decimal> {
            let mut inv = mk([lots[0].clone()]);
            inv.reduce(&sell_stk(1), None, BookingMethod::Fifo)
                .expect("one unit is there");
            for l in &lots[1..] {
                inv.add(l.clone()).expect("fixture fits in Decimal");
            }
            inv.reduce(&sell_stk(14), None, BookingMethod::Fifo)
                .expect("29 units remain")
                .matched
                .iter()
                .map(|m| m.cost.as_ref().unwrap().number)
                .collect()
        };
        assert_eq!(
            via_index([a(), b(), c()]),
            via_index([a(), c(), b()]),
            "the maintained index must order merged lots the same way the scan does",
        );

        // B written FIRST is distinguishable and legitimately differs: it is
        // not interchangeable with either of the others.
        for (name, lots) in [("B A C", [b(), a(), c()]), ("B C A", [b(), c(), a()])] {
            let inv = mk(lots);
            let got: Vec<Decimal> = try_reduce(&inv, &sell_stk(15), BookingMethod::Fifo)
                .matched
                .iter()
                .map(|m| m.cost.as_ref().unwrap().number)
                .collect();
            assert_eq!(
                got,
                vec![dec!(20), dec!(10)],
                "{name}: B first must be consumed first, got {got:?}",
            );
        }
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
    fn strict_with_size_takes_the_oldest_of_several_exact_size_lots() {
        // #2097. Two lots of the reduction's size, so size alone does not
        // disambiguate. Beancount sorts the size matches by `cost.date` and
        // takes the first; the choice decides both the basis realized and the
        // holding period of what survives.
        //
        // The lots are built in the OPPOSITE order to their dates, which is
        // what the old `find`-first-in-slot-order got wrong. Slot order is
        // insertion order and usually matches date order by accident — but a
        // lot carrying an explicit cost date is inserted when its transaction
        // books and dated whenever the user wrote. Verified against beancount
        // 3.2.3, which leaves the 100-cost lot standing.
        let inv = mk([lot(10, 100, 20), lot(10, 200, 5)]);
        let r = try_reduce(&inv, &sell_stk(10), BookingMethod::StrictWithSize);
        assert_eq!(
            basis(&r),
            dec!(2000),
            "must realize the OLDEST size match (day 5, cost 200), not the \
             first one stored (day 20, cost 100)"
        );
    }

    /// Two size matches sharing a date resolve by insertion order.
    ///
    /// The date comparison cannot separate these, so only the `i` in
    /// `min_by_key`'s key decides — and the comment above it promises a
    /// deterministic result. Nothing pinned that: reversing the slot tiebreak
    /// to `Reverse(i)` leaves all 485 core tests passing.
    ///
    /// Determinism here is not decoration. `report capgains` splits short from
    /// long on the surviving lot's acquisition date, and per-lot IRR keys
    /// eligibility off it, so a reduction that picks arbitrarily between two
    /// same-date lots moves tax figures between runs.
    #[test]
    fn strict_with_size_breaks_a_date_tie_by_insertion_order() {
        // Same date, same size, different costs — so the choice is visible in
        // the basis and nothing but the tiebreak can make it.
        let inv = mk([lot(10, 100, 7), lot(10, 200, 7)]);
        let r = try_reduce(&inv, &sell_stk(10), BookingMethod::StrictWithSize);
        assert_eq!(
            basis(&r),
            dec!(1000),
            "must take the FIRST of two same-date size matches (cost 100)",
        );
    }

    /// An undated size match loses to a dated one.
    ///
    /// `map_or((1, NaiveDate::MAX), ..)` sorts `None` last, on the reasoning
    /// that a booked lot always carries a date and an unbooked one is not what
    /// the user meant. That is a real decision — `None` sorts BEFORE `Some`
    /// naturally, so the encoding exists precisely to override it — and it was
    /// unpinned: flipping it to sort `None` first leaves the whole core suite
    /// green, along with `rustledger`, `rustledger-validate` and
    /// `rustledger-query`.
    #[test]
    fn strict_with_size_prefers_a_dated_lot_over_an_undated_lot() {
        let mut inv = Inventory::new();
        // Undated FIRST, so insertion order alone would pick it and cannot
        // be what produces the expected answer.
        inv.add(Position::with_cost(
            Amount::new(d(10), "STK"),
            Cost::new(d(100), "USD"),
        ))
        .expect("fixture fits in Decimal");
        inv.add(lot(10, 200, 9)).expect("fixture fits in Decimal");

        let r = try_reduce(&inv, &sell_stk(10), BookingMethod::StrictWithSize);
        assert_eq!(
            basis(&r),
            dec!(2000),
            "must take the DATED size match (cost 200), not the undated one",
        );
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

        // The basis alone cannot tell FIFO from LIFO here: a total match
        // consumes every matching lot, so any order sums to 3000. The name of
        // this test is about the ORDER, so assert it — flipping the fallback
        // to LIFO used to leave this green.
        assert_eq!(
            r.matched
                .iter()
                .map(|p| p.cost.as_ref().map(|c| c.number))
                .collect::<Vec<_>>(),
            vec![Some(dec!(100)), Some(dec!(200))],
            "oldest lot first",
        );
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
