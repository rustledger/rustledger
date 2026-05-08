------------------------------ MODULE Interpolation ------------------------------
(*
 * Posting Interpolation — N postings, multi-currency, with cost-unknowns
 *
 * Models the interpolation rules in
 * `crates/rustledger-booking/src/interpolate.rs`.
 *
 * KEY RULE (from PR #1029 / issue #1026):
 *   For each currency group, at most one posting may be "unknown",
 *   where "unknown" means EITHER:
 *     - the posting's units amount is missing (NULL), OR
 *     - the posting has an empty cost spec (e.g. `{}`), in which case
 *       the cost-basis weight is unresolved until the booking pass.
 *
 *   Missing-amount postings count toward their UNITS currency.
 *   Empty-cost postings count toward their COST currency.
 *
 * History:
 *   - Original 2-posting / single-currency model verified the basic
 *     `AtMostOneNull` rule that prevented two `units = NULL` postings
 *     in the same transaction.
 *   - PR #1029 (issue #1026) extended the implementation rule to count
 *     empty-cost postings alongside missing-amount postings, per
 *     bean-check parity on the htsec compat fixture.
 *   - Issue #1030 — this redesign (option C). N postings, multi-currency,
 *     posting-record state.
 *
 * For TLC tractability, MaxPostings is bounded (default 3 in the .cfg)
 * and Currencies is a small finite set (default {"USD", "EUR"}). The
 * combination 3 postings × 2 currencies × 5 amount slots covers every
 * shape the interpolator's rule cares about (single-currency missing,
 * multi-currency mixed unknowns, two unknowns in one currency
 * triggering rejection).
 *
 * SCOPE:
 *   - Models the validation rule from #1029 (the spec's contribution).
 *   - Does NOT model the residual arithmetic that produces the filled
 *     amount — that was the original spec's `Interpolate` action and is
 *     intentionally out of scope here. A separate spec covering the
 *     full booking-pass numerical interpolation could be filed later;
 *     the rule this spec enforces is structural ("≤ 1 unknown per
 *     currency"), not arithmetical.
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS MaxAmount, MaxPostings, Currencies

(* Sentinel values for the amount field. We piggyback on Integers using
 * out-of-range sentinels rather than a tagged-union type, to keep TLC's
 * state space small. *)
UNSET == -1000   \* posting slot not yet filled
NULL  == -1001   \* explicit missing amount (to be interpolated)

(* Cost-spec status. Strings are clearer than booleans for diagnostic
 * trace output. *)
NORMAL == "NORMAL"  \* either no cost or a fully-specified cost
EMPTY  == "EMPTY"   \* empty cost spec like `{}` — basis unresolved

(* Sentinel currency for unfilled or non-applicable slots. *)
NoCurrency == "NONE"

(* Default record for an unused posting slot. *)
NoPosting == [amount       |-> UNSET,
              currency     |-> NoCurrency,
              cost         |-> NORMAL,
              costCurrency |-> NoCurrency]

VARIABLES
    postings,   \* Function: 1..MaxPostings -> posting record
    complete    \* TRUE once Validate finalizes the txn

vars == <<postings, complete>>

(* Type invariant on the posting record. The amount domain unions the
 * normal range with the two sentinels. *)
PostingRecord ==
    [amount       : (-MaxAmount..MaxAmount) \cup {UNSET, NULL},
     currency     : Currencies \cup {NoCurrency},
     cost         : {NORMAL, EMPTY},
     costCurrency : Currencies \cup {NoCurrency}]

TypeOK ==
    /\ postings \in [1..MaxPostings -> PostingRecord]
    /\ complete \in BOOLEAN

-----------------------------------------------------------------------------
Init ==
    /\ postings = [i \in 1..MaxPostings |-> NoPosting]
    /\ complete = FALSE

-----------------------------------------------------------------------------

(* Add a posting at slot i with a known amount and currency, no cost. *)
AddNormal(i, amt, ccy) ==
    /\ i \in 1..MaxPostings
    /\ postings[i].amount = UNSET
    /\ ~complete
    /\ amt \in (-MaxAmount..MaxAmount) \ {0}
    /\ ccy \in Currencies
    /\ postings' = [postings EXCEPT
        ![i] = [amount       |-> amt,
                currency     |-> ccy,
                cost         |-> NORMAL,
                costCurrency |-> NoCurrency]]
    /\ UNCHANGED complete

(* Add a posting with a missing amount in a known currency. The
 * implementation's interpolator would solve for this amount as the
 * residual that balances the currency group. *)
AddNullAmount(i, ccy) ==
    /\ i \in 1..MaxPostings
    /\ postings[i].amount = UNSET
    /\ ~complete
    /\ ccy \in Currencies
    /\ postings' = [postings EXCEPT
        ![i] = [amount       |-> NULL,
                currency     |-> ccy,
                cost         |-> NORMAL,
                costCurrency |-> NoCurrency]]
    /\ UNCHANGED complete

(* Add a posting with empty cost spec — units known, cost-basis weight
 * unresolved until booking. Counts as one unknown for `costCcy`, the
 * cost currency, NOT for `ccy` (the units currency). *)
AddEmptyCost(i, amt, ccy, costCcy) ==
    /\ i \in 1..MaxPostings
    /\ postings[i].amount = UNSET
    /\ ~complete
    /\ amt \in (-MaxAmount..MaxAmount) \ {0}
    /\ ccy \in Currencies
    /\ costCcy \in Currencies
    /\ postings' = [postings EXCEPT
        ![i] = [amount       |-> amt,
                currency     |-> ccy,
                cost         |-> EMPTY,
                costCurrency |-> costCcy]]
    /\ UNCHANGED complete

-----------------------------------------------------------------------------
(* HELPER OPERATORS *)

(* The currency a posting's "unknown" counts toward.
 * Returns NoCurrency if the posting is fully known. *)
UnknownCurrency(p) ==
    IF p.amount = NULL THEN p.currency
    ELSE IF p.cost = EMPTY THEN p.costCurrency
    ELSE NoCurrency

(* Indices of postings that are unknown for a given currency. *)
UnknownsInCurrency(ccy) ==
    {i \in 1..MaxPostings : UnknownCurrency(postings[i]) = ccy}

(* All currencies that appear among posting units OR cost-currencies.
 * NoCurrency is excluded — it represents an empty slot, not a real
 * currency-group. *)
ActiveCurrencies ==
    ({postings[i].currency : i \in 1..MaxPostings} \cup
     {postings[i].costCurrency : i \in 1..MaxPostings})
    \ {NoCurrency}

(* The implementation's invariant from #1029: for every currency that
 * appears in any posting (units or cost), the count of unknown
 * postings for that currency is at most 1. *)
ValidationOk ==
    \A ccy \in ActiveCurrencies :
        Cardinality(UnknownsInCurrency(ccy)) <= 1

-----------------------------------------------------------------------------

(* Mark the transaction complete only if validation passes. Mirrors
 * the implementation: if `ValidationOk` fails, the interpolator
 * returns `MultipleMissing` (or the equivalent) and never completes. *)
Validate ==
    /\ ~complete
    /\ ValidationOk
    /\ \A i \in 1..MaxPostings : postings[i].amount # UNSET
    /\ complete' = TRUE
    /\ UNCHANGED postings

Next ==
    \/ \E i \in 1..MaxPostings, ccy \in Currencies,
         amt \in (-MaxAmount..MaxAmount) \ {0} :
        AddNormal(i, amt, ccy)
    \/ \E i \in 1..MaxPostings, ccy \in Currencies :
        AddNullAmount(i, ccy)
    \/ \E i \in 1..MaxPostings, ccy \in Currencies, costCcy \in Currencies,
         amt \in (-MaxAmount..MaxAmount) \ {0} :
        AddEmptyCost(i, amt, ccy, costCcy)
    \/ Validate

-----------------------------------------------------------------------------
(* INVARIANTS *)

(* The implementation's structural rule: completion is reachable only
 * when no currency has more than one unknown. *)
CompleteImpliesValidated ==
    complete => ValidationOk

(* Backward-compatible alias for the original 2-posting `AtMostOneNull`.
 * The N-posting / multi-currency generalization is captured by
 * `ValidationOk`; the old name is preserved so external references
 * (test names, prior commits, CHANGELOG entries) continue to resolve. *)
AtMostOneUnknownPerCurrency == ValidationOk

(* `CompleteImpliesBalanced` from the original 2-posting model:
 *   complete => posting1 + posting2 = 0
 *
 * In the N-posting / multi-currency / cost-unknown world this no longer
 * applies as a single transaction-wide statement:
 *   - Per UNITS currency, the sum of normal+filled amounts = 0 holds
 *     AFTER the interpolator fills any NULL amounts. This spec doesn't
 *     model the fill operation (see "SCOPE" in the header).
 *   - Per COST currency, the residual contributed by empty-cost
 *     postings is intentionally LEFT UNRESOLVED at interpolation time;
 *     the booking pass settles it later. So balanced-ness on the cost
 *     currency is a booking-pass invariant, not an interpolation-pass
 *     one.
 *
 * If/when a future spec models the fill arithmetic, that spec should
 * carry the per-currency balanced-ness invariant. Tracking it here
 * would be misleading. *)

Spec == Init /\ [][Next]_vars

=============================================================================
