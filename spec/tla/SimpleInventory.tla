--------------------------- MODULE SimpleInventory ---------------------------
(* Minimal working spec to demonstrate TLA+ model checking *)

EXTENDS Integers, FiniteSets

CONSTANTS MaxUnits

VARIABLES units, totalAdded, totalReduced

vars == <<units, totalAdded, totalReduced>>

Init ==
    /\ units = 0
    /\ totalAdded = 0
    /\ totalReduced = 0

Add(n) ==
    /\ n > 0
    /\ n <= MaxUnits
    /\ units + n <= MaxUnits * 2
    /\ units' = units + n
    /\ totalAdded' = totalAdded + n
    /\ UNCHANGED totalReduced

Reduce(n) ==
    /\ n > 0
    /\ n <= units
    /\ units' = units - n
    /\ totalReduced' = totalReduced + n
    /\ UNCHANGED totalAdded

Next == \E n \in 1..MaxUnits : Add(n) \/ Reduce(n)

(* THE KEY INVARIANT: Conservation of units *)
ConservationInv == units + totalReduced = totalAdded

(* Can't reduce more than we added *)
ReduceBoundInv == totalReduced <= totalAdded

(* Units never negative *)
NonNegativeInv == units >= 0

Spec == Init /\ [][Next]_vars

=============================================================================
