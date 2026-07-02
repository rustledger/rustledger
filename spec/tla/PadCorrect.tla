------------------------------ MODULE PadCorrect ------------------------------
(*
 * Verify pad-directive semantics (beancount `pad`).
 *
 * A pad directive arms a pending pad on an account; the NEXT balance
 * assertion on that account absorbs the difference by synthesizing a
 * padding transaction, so the assertion holds exactly:
 *
 *   pad amount = asserted - actual   (inserted just before the balance)
 *
 * Modeled per the implementation in `rustledger-booking/src/pad.rs`:
 * - a newer pad REPLACES a still-pending one;
 * - a balance assertion with no pending pad must simply match (the model
 *   only emits legal balances — failing unpadded assertions are validator
 *   territory, not pad-engine semantics);
 * - single account, single currency. The implementation's sub-account
 *   summing semantic (a balance assertion covers the account subtree) is
 *   deliberately OUT of model scope — it is pinned by integration tests.
 *
 * The replay (rustledger-booking/tests/tla_behavior_replay.rs) drives the
 * real `process_pads` with the directive sequence and checks the
 * synthesized pad amounts and final balances.
 *)

EXTENDS Integers

CONSTANTS MaxAmount, MaxOperations

VARIABLES
    actual,         \* True balance including synthesized pads
    padPending,     \* A pad directive is armed and awaiting a balance
    opCount

vars == <<actual, padPending, opCount>>

-----------------------------------------------------------------------------
Init ==
    /\ actual = 0
    /\ padPending = FALSE
    /\ opCount = 0

-----------------------------------------------------------------------------
(* A transaction posting to the account. *)
AddTxn(amt) ==
    /\ amt # 0
    /\ opCount < MaxOperations
    /\ actual' = actual + amt
    /\ UNCHANGED padPending
    /\ opCount' = opCount + 1

(* Arm a pad. Arming while one is pending replaces it (same observable
   state — the implementation swaps the pending entry). *)
AddPad ==
    /\ opCount < MaxOperations
    /\ padPending' = TRUE
    /\ UNCHANGED actual
    /\ opCount' = opCount + 1

(* A balance assertion. With a pad pending, the pad absorbs the difference
   and the balance lands exactly on the asserted value; without one, the
   model only emits assertions that already hold. *)
AddBalance(asserted) ==
    /\ opCount < MaxOperations
    /\ IF padPending
       THEN actual' = asserted
       ELSE /\ asserted = actual
            /\ UNCHANGED actual
    /\ padPending' = FALSE
    /\ opCount' = opCount + 1

Next ==
    \/ \E amt \in (-MaxAmount..MaxAmount) \ {0} : AddTxn(amt)
    \/ AddPad
    \/ \E b \in -MaxAmount..MaxAmount : AddBalance(b)

-----------------------------------------------------------------------------
TypeOK ==
    /\ actual \in Int
    /\ padPending \in BOOLEAN
    /\ opCount \in Nat

-----------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

=============================================================================
