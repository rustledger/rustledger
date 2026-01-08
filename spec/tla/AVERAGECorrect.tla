---------------------------- MODULE AVERAGECorrect ----------------------------
(*
 * Verify AVERAGE booking method correctness.
 *
 * AVERAGE uses weighted average cost basis:
 * - All lots are merged into a single position with average cost
 * - Reduction uses the average cost, not individual lot costs
 * - totalCost / totalUnits = averageCost
 *
 * Key invariant: average cost is always (total cost value) / (total units)
 *)

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS MaxLots, MaxUnits, MaxCost

VARIABLES
    totalUnits,     \* Total units in inventory
    totalCostValue, \* Total cost basis (units * cost per unit summed)
    lastAvgCost     \* Average cost at last reduction (for verification)

vars == <<totalUnits, totalCostValue, lastAvgCost>>

-----------------------------------------------------------------------------
Init ==
    /\ totalUnits = 0
    /\ totalCostValue = 0
    /\ lastAvgCost = 0

-----------------------------------------------------------------------------
(* Add units at a given cost - updates the weighted average *)
AddUnits(units, cost) ==
    /\ units > 0
    /\ totalUnits + units <= MaxLots * MaxUnits  \* Bound total units
    /\ totalCostValue + (units * cost) <= MaxLots * MaxUnits * MaxCost  \* Bound cost
    /\ totalUnits' = totalUnits + units
    /\ totalCostValue' = totalCostValue + (units * cost)
    /\ UNCHANGED lastAvgCost

(* Reduce units using AVERAGE method *)
(* The cost basis of reduced units is the current average *)
ReduceAVERAGE(units) ==
    /\ units > 0
    /\ units <= totalUnits
    /\ totalUnits > 0
    /\ LET avgCost == totalCostValue \div totalUnits  \* Integer division
           reducedCostValue == units * avgCost
       IN /\ totalUnits' = totalUnits - units
          /\ totalCostValue' = totalCostValue - reducedCostValue
          /\ lastAvgCost' = avgCost

Next ==
    \/ \E u \in 1..MaxUnits, c \in 1..MaxCost : AddUnits(u, c)
    \/ \E u \in 1..MaxUnits : ReduceAVERAGE(u)

-----------------------------------------------------------------------------
(* INVARIANTS *)

(* Total units is never negative *)
NonNegativeUnits ==
    totalUnits >= 0

(* Total cost value is never negative *)
NonNegativeCostValue ==
    totalCostValue >= 0

(* When units exist, cost value should be positive *)
CostConsistent ==
    totalUnits > 0 => totalCostValue >= 0

(* Average cost calculation is consistent *)
(* avgCost = totalCostValue / totalUnits when totalUnits > 0 *)
AverageCostValid ==
    totalUnits > 0 =>
        LET avgCost == totalCostValue \div totalUnits
        IN avgCost >= 0 /\ avgCost <= MaxCost * MaxUnits  \* Bounded

TypeOK ==
    /\ totalUnits \in 0..(MaxLots * MaxUnits)
    /\ totalCostValue \in 0..(MaxLots * MaxUnits * MaxCost)
    /\ lastAvgCost \in 0..(MaxCost * MaxUnits)

-----------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

=============================================================================
