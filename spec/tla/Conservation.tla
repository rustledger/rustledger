------------------------------ MODULE Conservation ------------------------------
(*
 * Conservation of Units - Core Accounting Invariant
 *
 * This spec verifies the fundamental property of inventory management:
 *   units_in_inventory + units_reduced = units_added
 *
 * This catches bugs where units are created from nothing or disappear.
 * Similar to Cardano's UTxO conservation: inputs = outputs + fees
 *)

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    MaxUnits,       \* Maximum units per operation
    MaxOperations   \* Maximum number of operations to explore

VARIABLES
    inventory,      \* Current units in inventory (can be negative for shorts)
    totalAdded,     \* Running total of all units ever added
    totalReduced,   \* Running total of all units ever reduced
    opCount         \* Number of operations performed

vars == <<inventory, totalAdded, totalReduced, opCount>>

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ inventory = 0
    /\ totalAdded = 0
    /\ totalReduced = 0
    /\ opCount = 0

-----------------------------------------------------------------------------
(* Actions *)

(* Add units to inventory *)
Add(units) ==
    /\ units > 0
    /\ units <= MaxUnits
    /\ opCount < MaxOperations
    /\ inventory' = inventory + units
    /\ totalAdded' = totalAdded + units
    /\ opCount' = opCount + 1
    /\ UNCHANGED totalReduced

(* Reduce units from inventory (must have sufficient units) *)
Reduce(units) ==
    /\ units > 0
    /\ units <= MaxUnits
    /\ units <= inventory  \* Can't reduce more than available
    /\ opCount < MaxOperations
    /\ inventory' = inventory - units
    /\ totalReduced' = totalReduced + units
    /\ opCount' = opCount + 1
    /\ UNCHANGED totalAdded

(* Allow reducing to negative (short selling) *)
ReduceShort(units) ==
    /\ units > 0
    /\ units <= MaxUnits
    /\ opCount < MaxOperations
    /\ inventory' = inventory - units
    /\ totalReduced' = totalReduced + units
    /\ opCount' = opCount + 1
    /\ UNCHANGED totalAdded

Next ==
    \/ \E u \in 1..MaxUnits : Add(u)
    \/ \E u \in 1..MaxUnits : Reduce(u)
    \* Uncomment to allow short selling:
    \* \/ \E u \in 1..MaxUnits : ReduceShort(u)

-----------------------------------------------------------------------------
(* INVARIANTS - The properties we verify *)

(* THE CORE INVARIANT: Conservation of units *)
(* What's in inventory + what's been taken out = what was put in *)
ConservationInvariant ==
    inventory + totalReduced = totalAdded

(* Units reduced can never exceed units added *)
ReduceBoundInvariant ==
    totalReduced <= totalAdded

(* Inventory is non-negative (unless short selling allowed) *)
NonNegativeInventory ==
    inventory >= 0

(* Totals are always non-negative *)
NonNegativeTotals ==
    /\ totalAdded >= 0
    /\ totalReduced >= 0

(* Type invariant *)
TypeOK ==
    /\ inventory \in Int
    /\ totalAdded \in Nat
    /\ totalReduced \in Nat
    /\ opCount \in Nat

-----------------------------------------------------------------------------
(* Spec *)

Spec == Init /\ [][Next]_vars

=============================================================================
