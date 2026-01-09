--------------------------- MODULE BuggyInventory ---------------------------
(* This spec has a BUG - TLC will find it! *)

EXTENDS Integers

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
    /\ units' = units + n
    /\ totalAdded' = totalAdded + n
    /\ UNCHANGED totalReduced

(* BUG: We reduce n units but only record n-1 in totalReduced! *)
(* This is like a real bug where you forget to account for something *)
Reduce(n) ==
    /\ n > 0
    /\ n <= units
    /\ units' = units - n
    /\ totalReduced' = totalReduced + (n - 1)  \* <-- BUG: should be n!
    /\ UNCHANGED totalAdded

Next == \E n \in 1..MaxUnits : Add(n) \/ Reduce(n)

(* This invariant WILL BE VIOLATED because of the bug *)
ConservationInv == units + totalReduced = totalAdded

Spec == Init /\ [][Next]_vars

=============================================================================
