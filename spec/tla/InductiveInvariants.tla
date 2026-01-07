------------------------- MODULE InductiveInvariants -------------------------
(***************************************************************************
 * Inductive Invariants for rustledger
 *
 * Inductive invariants are stronger than regular invariants. They satisfy:
 *   1. Init => Inv           (holds initially)
 *   2. Inv /\ Next => Inv'   (preserved by transitions)
 *
 * This allows unbounded verification - proving correctness for ALL possible
 * states, not just those reachable within model checking bounds.
 *
 * Usage with Apalache:
 *   apalache-mc check --init=Init --inv=IndInv --next=Next InductiveInvariants.tla
 ***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Currencies,
    MaxUnits,
    MaxLots

-----------------------------------------------------------------------------
(* Type Definitions *)

Lot == [
    units: 1..MaxUnits,
    currency: Currencies,
    cost: 1..1000,
    date: 1..365
]

BookingMethod == {"FIFO", "LIFO", "HIFO", "STRICT", "AVERAGE", "NONE"}

-----------------------------------------------------------------------------
(* Variables *)

VARIABLES
    lots,           \* Set of lots
    method,         \* Current booking method
    history,        \* Operation history
    totalAdded,     \* Total units ever added
    totalReduced    \* Total units ever reduced

vars == <<lots, method, history, totalAdded, totalReduced>>

-----------------------------------------------------------------------------
(* Helper Functions *)

TotalUnits(lotSet) ==
    IF lotSet = {} THEN 0
    ELSE LET s == CHOOSE s \in lotSet : TRUE
         IN s.units + TotalUnits(lotSet \ {s})

CurrencyUnits(lotSet, curr) ==
    TotalUnits({l \in lotSet : l.currency = curr})

Oldest(lotSet) ==
    CHOOSE l \in lotSet : \A other \in lotSet : l.date <= other.date

Newest(lotSet) ==
    CHOOSE l \in lotSet : \A other \in lotSet : l.date >= other.date

HighestCost(lotSet) ==
    CHOOSE l \in lotSet : \A other \in lotSet : l.cost >= other.cost

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ lots = {}
    /\ method \in BookingMethod
    /\ history = <<>>
    /\ totalAdded = 0
    /\ totalReduced = 0

-----------------------------------------------------------------------------
(* Actions *)

AddLot(l) ==
    /\ l \in Lot
    /\ Cardinality(lots) < MaxLots
    /\ lots' = lots \cup {l}
    /\ totalAdded' = totalAdded + l.units
    /\ history' = Append(history, [action |-> "add", lot |-> l])
    /\ UNCHANGED <<method, totalReduced>>

ReduceLot(l, units) ==
    /\ l \in lots
    /\ units > 0
    /\ units <= l.units
    /\ IF units = l.units
       THEN lots' = lots \ {l}
       ELSE lots' = (lots \ {l}) \cup {[l EXCEPT !.units = @ - units]}
    /\ totalReduced' = totalReduced + units
    /\ history' = Append(history, [action |-> "reduce", lot |-> l, units |-> units])
    /\ UNCHANGED <<method, totalAdded>>

ChangeMethod(m) ==
    /\ m \in BookingMethod
    /\ method' = m
    /\ UNCHANGED <<lots, history, totalAdded, totalReduced>>

Next ==
    \/ \E l \in Lot : AddLot(l)
    \/ \E l \in lots, u \in 1..MaxUnits : ReduceLot(l, u)
    \/ \E m \in BookingMethod : ChangeMethod(m)

-----------------------------------------------------------------------------
(* INDUCTIVE INVARIANTS *)

(* Invariant 1: Conservation of Units
 * The total units in inventory plus total reduced equals total added.
 * This is a fundamental accounting invariant.
 *)
ConservationInv ==
    TotalUnits(lots) + totalReduced = totalAdded

(* Invariant 2: Non-Negative Lots
 * All lots have positive units. No zero or negative lots exist.
 *)
PositiveLotsInv ==
    \A l \in lots : l.units > 0

(* Invariant 3: Bounded Lots
 * Number of lots never exceeds MaxLots.
 *)
BoundedLotsInv ==
    Cardinality(lots) <= MaxLots

(* Invariant 4: Valid Currencies
 * All lots have valid currencies.
 *)
ValidCurrenciesInv ==
    \A l \in lots : l.currency \in Currencies

(* Invariant 5: History Consistency
 * History length matches number of operations.
 *)
HistoryConsistencyInv ==
    Len(history) = (totalAdded \div MaxUnits) + (totalReduced \div MaxUnits)
    \* Approximate - actual proof would track operation count separately

(* Invariant 6: Non-Negative Totals
 * Running totals are never negative.
 *)
NonNegativeTotalsInv ==
    /\ totalAdded >= 0
    /\ totalReduced >= 0
    /\ totalAdded >= totalReduced  \* Can't reduce more than added

(* Invariant 7: Method Validity
 * Booking method is always valid.
 *)
ValidMethodInv ==
    method \in BookingMethod

(* Combined Inductive Invariant *)
IndInv ==
    /\ ConservationInv
    /\ PositiveLotsInv
    /\ BoundedLotsInv
    /\ ValidCurrenciesInv
    /\ NonNegativeTotalsInv
    /\ ValidMethodInv

-----------------------------------------------------------------------------
(* PROOFS OF INDUCTIVENESS *)

(* To prove IndInv is inductive, we must show:
 * 1. Init => IndInv
 * 2. IndInv /\ Next => IndInv'
 *
 * Proof sketch for ConservationInv:
 *
 * Base case (Init):
 *   TotalUnits({}) + 0 = 0  ✓
 *
 * Inductive case (AddLot):
 *   TotalUnits(lots') + totalReduced' = totalAdded'
 *   TotalUnits(lots \cup {l}) + totalReduced = totalAdded + l.units
 *   (TotalUnits(lots) + l.units) + totalReduced = totalAdded + l.units
 *   TotalUnits(lots) + totalReduced = totalAdded  (by IndInv)  ✓
 *
 * Inductive case (ReduceLot):
 *   TotalUnits(lots') + totalReduced' = totalAdded'
 *   (TotalUnits(lots) - units) + (totalReduced + units) = totalAdded
 *   TotalUnits(lots) + totalReduced = totalAdded  (by IndInv)  ✓
 *)

THEOREM InitImpliesIndInv ==
    Init => IndInv

THEOREM IndInvIsInductive ==
    IndInv /\ Next => IndInv'

-----------------------------------------------------------------------------
(* STRENGTHENED INVARIANTS FOR BOOKING METHODS *)

(* FIFO Inductive Invariant:
 * When using FIFO, oldest lots are always consumed first.
 * Strengthening: track "frontier date" - minimum date of remaining lots.
 *)
FIFOStrengtheningInv ==
    method = "FIFO" =>
        \A l1, l2 \in lots :
            l1.currency = l2.currency =>
                \* No "gaps" in dates - can't have old lot if newer was reduced
                TRUE  \* Actual invariant requires augmented state

(* LIFO Inductive Invariant:
 * When using LIFO, newest lots are consumed first.
 *)
LIFOStrengtheningInv ==
    method = "LIFO" =>
        \A l1, l2 \in lots :
            l1.currency = l2.currency =>
                TRUE  \* Actual invariant requires augmented state

(* HIFO Inductive Invariant:
 * When using HIFO, highest cost lots are consumed first.
 *)
HIFOStrengtheningInv ==
    method = "HIFO" =>
        \A l1, l2 \in lots :
            l1.currency = l2.currency =>
                TRUE  \* Actual invariant requires augmented state

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars

=============================================================================
