------------------------------ MODULE NONECorrect ------------------------------
(*
 * Verify NONE booking method correctness.
 *
 * NONE is the most permissive booking method:
 * - Allows reduction without matching lots
 * - Can go negative (short positions allowed)
 * - No cost basis matching required
 *
 * Key property: NONE always allows reduction (never fails due to lot matching)
 * Conservation still holds: what goes in must come out eventually
 *)

EXTENDS Integers

CONSTANTS MaxUnits, MaxOperations

VARIABLES
    balance,        \* Current balance (can be negative for short positions)
    totalAdded,     \* Total units ever added
    totalReduced,   \* Total units ever reduced
    opCount         \* Operation count (to bound state space)

vars == <<balance, totalAdded, totalReduced, opCount>>

-----------------------------------------------------------------------------
Init ==
    /\ balance = 0
    /\ totalAdded = 0
    /\ totalReduced = 0
    /\ opCount = 0

-----------------------------------------------------------------------------
(* Add units - always succeeds *)
AddUnits(units) ==
    /\ units > 0
    /\ opCount < MaxOperations
    /\ balance' = balance + units
    /\ totalAdded' = totalAdded + units
    /\ opCount' = opCount + 1
    /\ UNCHANGED totalReduced

(* NONE reduction - ALWAYS succeeds (no lot matching required) *)
(* This is the key property: NONE never fails *)
ReduceNONE(units) ==
    /\ units > 0
    /\ opCount < MaxOperations
    /\ balance' = balance - units  \* Can go negative!
    /\ totalReduced' = totalReduced + units
    /\ opCount' = opCount + 1
    /\ UNCHANGED totalAdded

Next ==
    \/ \E u \in 1..MaxUnits : AddUnits(u)
    \/ \E u \in 1..MaxUnits : ReduceNONE(u)

-----------------------------------------------------------------------------
(* INVARIANTS *)

(* Conservation: balance = totalAdded - totalReduced *)
ConservationInvariant ==
    balance = totalAdded - totalReduced

(* Total added is always non-negative *)
NonNegativeAdded ==
    totalAdded >= 0

(* Total reduced is always non-negative *)
NonNegativeReduced ==
    totalReduced >= 0

(* Key property of NONE: balance CAN be negative (short positions) *)
(* This is NOT an invariant violation - it's expected behavior *)
(* We verify this by NOT having a NonNegativeBalance invariant *)

TypeOK ==
    /\ balance \in -MaxUnits*MaxOperations..MaxUnits*MaxOperations
    /\ totalAdded \in 0..MaxUnits*MaxOperations
    /\ totalReduced \in 0..MaxUnits*MaxOperations
    /\ opCount \in 0..MaxOperations

-----------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

=============================================================================
