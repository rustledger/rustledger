---------------------------- MODULE AVERAGECorrect ----------------------------
(*
 * Verify AVERAGE booking method correctness — EXACT arithmetic.
 *
 * AVERAGE uses weighted average cost basis: all lots merge into a single
 * pool, and a reduction removes value proportionally:
 *
 *     value' = value * (totalUnits - units) / totalUnits
 *
 * The previous version of this spec computed the average with INTEGER
 * division (`\div`), which made the pool value model-inexact — the Rust
 * implementation divides exactly (in 28-digit Decimal), so the behavior
 * replay could only check the units abstraction. This version tracks the
 * pool value as an exact rational `valueNum / valueDen` (kept normalized by
 * GCD), so the replay checks value conformance too (within the
 * implementation's documented Decimal-rounding tolerance).
 *
 * Exactness buys an invariant the integer model could not state:
 * ZeroUnitsZeroValue — a full liquidation empties the pool EXACTLY.
 *)

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS MaxLots, MaxUnits, MaxCost, MaxOperations

VARIABLES
    totalUnits,     \* Total units in the pool
    valueNum,       \* Pool cost value, numerator   (value = valueNum / valueDen)
    valueDen,       \* Pool cost value, denominator (>= 1, coprime with valueNum)
    opCount         \* Number of operations performed (bounds the state space)

vars == <<totalUnits, valueNum, valueDen, opCount>>

-----------------------------------------------------------------------------
(* Exact-rational helpers *)

RECURSIVE GCDrec(_, _)
GCDrec(a, b) == IF b = 0 THEN a ELSE GCDrec(b, a % b)

GCD(a, b) == IF a = 0 THEN b ELSE GCDrec(a, b)

(* Normalized numerator/denominator of n/d. *)
NormNum(n, d) == n \div GCD(n, d)
NormDen(n, d) == d \div GCD(n, d)

-----------------------------------------------------------------------------
Init ==
    /\ totalUnits = 0
    /\ valueNum = 0
    /\ valueDen = 1
    /\ opCount = 0

-----------------------------------------------------------------------------
(* Add units at an integer per-unit cost: value += units * cost.
   Adding an integer amount cannot change the (normalized) denominator:
   gcd(valueNum + k * valueDen, valueDen) = gcd(valueNum, valueDen) = 1. *)
AddUnits(units, cost) ==
    /\ units > 0
    /\ opCount < MaxOperations
    /\ totalUnits + units <= MaxLots * MaxUnits
    /\ totalUnits' = totalUnits + units
    /\ valueNum' = valueNum + units * cost * valueDen
    /\ valueDen' = valueDen
    /\ opCount' = opCount + 1

(* Reduce units at the average cost — exactly:
   value' = value * (totalUnits - units) / totalUnits. *)
ReduceAVERAGE(units) ==
    /\ units > 0
    /\ units <= totalUnits
    /\ totalUnits > 0
    /\ opCount < MaxOperations
    /\ LET n == valueNum * (totalUnits - units)
           d == valueDen * totalUnits
       IN /\ valueNum' = NormNum(n, d)
          /\ valueDen' = NormDen(n, d)
    /\ totalUnits' = totalUnits - units
    /\ opCount' = opCount + 1

Next ==
    \/ \E u \in 1..MaxUnits, c \in 1..MaxCost : AddUnits(u, c)
    \/ \E u \in 1..MaxUnits : ReduceAVERAGE(u)

-----------------------------------------------------------------------------
(* INVARIANTS *)

NonNegativeUnits ==
    totalUnits >= 0

(* The pool value is non-negative and the denominator well-formed. *)
NonNegativeValue ==
    /\ valueNum >= 0
    /\ valueDen >= 1

(* Full liquidation empties the pool EXACTLY — expressible only with exact
   arithmetic (the integer-division model leaked truncation residue). *)
ZeroUnitsZeroValue ==
    totalUnits = 0 => valueNum = 0

(* The average cost stays within the cost bounds the units were bought at:
   totalUnits <= value <= totalUnits * MaxCost (per-unit costs are 1..MaxCost). *)
ValueWithinCostBounds ==
    totalUnits > 0 =>
        /\ valueNum <= totalUnits * MaxCost * valueDen
        /\ valueNum >= totalUnits * valueDen

(* The rational is kept normalized, so states are canonical. *)
Normalized ==
    GCD(valueNum, valueDen) = 1

TypeOK ==
    /\ totalUnits \in Nat
    /\ valueNum \in Nat
    /\ valueDen \in Nat \ {0}
    /\ opCount \in Nat

-----------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

=============================================================================
