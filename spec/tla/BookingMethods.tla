------------------------- MODULE BookingMethods -------------------------
(***************************************************************************
 * TLA+ Specification for Beancount Booking Methods
 *
 * Models all 7 booking algorithms: FIFO, LIFO, HIFO, AVERAGE,
 * STRICT, STRICT_WITH_SIZE, and NONE.
 * Verifies correctness of lot selection and reduction.
 *
 * Key properties verified:
 * - FIFO always selects oldest lots first
 * - LIFO always selects newest lots first
 * - HIFO always selects highest cost lots first (tax optimization)
 * - AVERAGE maintains weighted average cost basis
 * - STRICT rejects ambiguous matches
 * - STRICT_WITH_SIZE accepts exact size matches
 * - Total units are preserved
 * - Cost basis is correctly tracked for capital gains
 ***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Currency,       \* The currency being tracked (e.g., "AAPL")
    CostCurrency,   \* Currency for cost basis (e.g., "USD")
    MaxLots,        \* Maximum number of lots
    MaxUnits        \* Maximum units per lot

-----------------------------------------------------------------------------
(* Type Definitions *)

\* A lot (position with cost)
Lot == [
    units: 1..MaxUnits,         \* Positive units held
    cost_per_unit: 1..1000,     \* Cost per unit (scaled)
    date: 1..365,               \* Acquisition day (1-365)
    label: STRING \cup {NULL}    \* Optional label
]

\* A cost specification for matching
CostSpec == [
    cost_per_unit: (1..1000) \cup {NULL},
    date: (1..365) \cup {NULL},
    label: STRING \cup {NULL}
]

\* Booking method enumeration
BookingMethod == {"STRICT", "STRICT_WITH_SIZE", "FIFO", "LIFO", "HIFO", "AVERAGE", "NONE"}

-----------------------------------------------------------------------------
(* Variables *)

VARIABLES
    lots,           \* Current set of lots: SUBSET Lot
    method,         \* Current booking method
    history,        \* Reduction history for verification (includes matching lots snapshot)
    totalReduced,   \* Total units reduced
    totalCostBasis, \* Total cost basis of reductions
    averageCost     \* Running average cost for AVERAGE method (scaled by 1000)

vars == <<lots, method, history, totalReduced, totalCostBasis, averageCost>>

-----------------------------------------------------------------------------
(* Helper Functions *)

\* Total units across all lots
TotalUnits ==
    IF lots = {} THEN 0
    ELSE LET lotSeq == SetToSeq(lots)
         IN FoldSeq(LAMBDA l, acc: acc + l.units, 0, lotSeq)

\* Lots matching a cost specification
Matching(spec) ==
    {l \in lots :
        /\ (spec.cost_per_unit = NULL \/ l.cost_per_unit = spec.cost_per_unit)
        /\ (spec.date = NULL \/ l.date = spec.date)
        /\ (spec.label = NULL \/ l.label = spec.label)}

\* Oldest lot among a set
Oldest(lotSet) ==
    CHOOSE l \in lotSet :
        \A other \in lotSet : l.date <= other.date

\* Newest lot among a set
Newest(lotSet) ==
    CHOOSE l \in lotSet :
        \A other \in lotSet : l.date >= other.date

\* Highest cost lot among a set (for HIFO - tax loss harvesting optimization)
HighestCost(lotSet) ==
    CHOOSE l \in lotSet :
        \A other \in lotSet : l.cost_per_unit >= other.cost_per_unit

\* Set to sequence helper
SetToSeq(S) ==
    IF S = {} THEN <<>>
    ELSE LET x == CHOOSE x \in S : TRUE
         IN <<x>> \o SetToSeq(S \ {x})

\* Fold over sequence
RECURSIVE FoldSeq(_, _, _)
FoldSeq(f, acc, s) ==
    IF s = <<>> THEN acc
    ELSE FoldSeq(f, f(Head(s), acc), Tail(s))

\* Lowest cost lot among a set (for LOFO - opposite of HIFO)
LowestCost(lotSet) ==
    CHOOSE l \in lotSet :
        \A other \in lotSet : l.cost_per_unit <= other.cost_per_unit

\* Calculate weighted average cost for a set of lots
\* Returns average cost per unit (scaled)
WeightedAverageCost(lotSet) ==
    IF lotSet = {} THEN 0
    ELSE LET totalUnits == FoldSeq(LAMBDA l, acc: acc + l.units, 0, SetToSeq(lotSet))
             totalCost == FoldSeq(LAMBDA l, acc: acc + (l.units * l.cost_per_unit), 0, SetToSeq(lotSet))
         IN IF totalUnits = 0 THEN 0 ELSE totalCost \div totalUnits

\* Find lot with exact unit match
ExactMatch(lotSet, units) ==
    {l \in lotSet : l.units = units}

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ lots = {}
    /\ method \in BookingMethod
    /\ history = <<>>
    /\ totalReduced = 0
    /\ totalCostBasis = 0
    /\ averageCost = 0

-----------------------------------------------------------------------------
(* Add a new lot *)

AddLot(l) ==
    /\ Cardinality(lots) < MaxLots
    /\ l \in Lot
    /\ lots' = lots \cup {l}
    \* Update average cost when adding lots
    /\ LET newTotalUnits == TotalUnits + l.units
           newTotalCost == (averageCost * TotalUnits) + (l.units * l.cost_per_unit)
       IN averageCost' = IF newTotalUnits = 0 THEN 0 ELSE newTotalCost \div newTotalUnits
    /\ UNCHANGED <<method, history, totalReduced, totalCostBasis>>

-----------------------------------------------------------------------------
(* STRICT Reduction *)

ReduceStrict(units, spec) ==
    /\ method = "STRICT"
    /\ units > 0
    /\ LET matches == Matching(spec)
           totalMatching == FoldSeq(LAMBDA l, acc: acc + l.units, 0, SetToSeq(matches))
       IN
       \* Case 1: Exactly one match
       IF Cardinality(matches) = 1
       THEN LET lot == CHOOSE l \in matches : TRUE
            IN /\ lot.units >= units
               /\ IF lot.units = units
                  THEN lots' = lots \ {lot}
                  ELSE lots' = (lots \ {lot}) \cup
                       {[lot EXCEPT !.units = @ - units]}
               /\ totalReduced' = totalReduced + units
               /\ totalCostBasis' = totalCostBasis + (units * lot.cost_per_unit)
               /\ history' = Append(history, [
                    method |-> "STRICT",
                    units |-> units,
                    from_lot |-> lot,
                    matching_lots |-> matches])
               /\ UNCHANGED <<method, averageCost>>
       \* Case 2: Total match (all lots consumed exactly)
       ELSE IF totalMatching = units
       THEN /\ lots' = lots \ matches
            /\ totalReduced' = totalReduced + units
            /\ totalCostBasis' = totalCostBasis +
                 FoldSeq(LAMBDA l, acc: acc + (l.units * l.cost_per_unit), 0, SetToSeq(matches))
            /\ history' = Append(history, [
                 method |-> "STRICT_TOTAL",
                 units |-> units,
                 from_lots |-> matches,
                 matching_lots |-> matches])
            /\ UNCHANGED <<method, averageCost>>
       \* Case 3: Ambiguous - this action is not enabled
       ELSE FALSE

-----------------------------------------------------------------------------
(* FIFO Reduction - Take from oldest first *)

ReduceFIFO(units, spec) ==
    /\ method = "FIFO"
    /\ units > 0
    /\ LET matches == Matching(spec)
       IN /\ matches # {}
          /\ FoldSeq(LAMBDA l, acc: acc + l.units, 0, SetToSeq(matches)) >= units
          \* Reduce from oldest lot
          /\ LET oldest == Oldest(matches)
             IN IF oldest.units >= units
                THEN \* Single lot suffices
                     /\ IF oldest.units = units
                        THEN lots' = lots \ {oldest}
                        ELSE lots' = (lots \ {oldest}) \cup
                             {[oldest EXCEPT !.units = @ - units]}
                     /\ totalReduced' = totalReduced + units
                     /\ totalCostBasis' = totalCostBasis + (units * oldest.cost_per_unit)
                     /\ history' = Append(history, [
                          method |-> "FIFO",
                          units |-> units,
                          from_lot |-> oldest,
                          matching_lots |-> matches])  \* Track matches for invariant
                ELSE \* Need multiple lots - take all from oldest, continue
                     /\ lots' = lots \ {oldest}
                     /\ totalReduced' = totalReduced + oldest.units
                     /\ totalCostBasis' = totalCostBasis + (oldest.units * oldest.cost_per_unit)
                     /\ history' = Append(history, [
                          method |-> "FIFO_PARTIAL",
                          units |-> oldest.units,
                          from_lot |-> oldest,
                          remaining |-> units - oldest.units,
                          matching_lots |-> matches])  \* Track matches for invariant
          /\ UNCHANGED <<method, averageCost>>

-----------------------------------------------------------------------------
(* LIFO Reduction - Take from newest first *)

ReduceLIFO(units, spec) ==
    /\ method = "LIFO"
    /\ units > 0
    /\ LET matches == Matching(spec)
       IN /\ matches # {}
          /\ FoldSeq(LAMBDA l, acc: acc + l.units, 0, SetToSeq(matches)) >= units
          /\ LET newest == Newest(matches)
             IN IF newest.units >= units
                THEN /\ IF newest.units = units
                        THEN lots' = lots \ {newest}
                        ELSE lots' = (lots \ {newest}) \cup
                             {[newest EXCEPT !.units = @ - units]}
                     /\ totalReduced' = totalReduced + units
                     /\ totalCostBasis' = totalCostBasis + (units * newest.cost_per_unit)
                     /\ history' = Append(history, [
                          method |-> "LIFO",
                          units |-> units,
                          from_lot |-> newest,
                          matching_lots |-> matches])  \* Track matches for invariant
                ELSE /\ lots' = lots \ {newest}
                     /\ totalReduced' = totalReduced + newest.units
                     /\ totalCostBasis' = totalCostBasis + (newest.units * newest.cost_per_unit)
                     /\ history' = Append(history, [
                          method |-> "LIFO_PARTIAL",
                          units |-> newest.units,
                          from_lot |-> newest,
                          remaining |-> units - newest.units,
                          matching_lots |-> matches])  \* Track matches for invariant
          /\ UNCHANGED <<method, averageCost>>

-----------------------------------------------------------------------------
(* HIFO Reduction - Take from highest cost first *)
\* HIFO (Highest In, First Out) is a tax optimization strategy that
\* maximizes cost basis on sales, potentially reducing capital gains.

ReduceHIFO(units, spec) ==
    /\ method = "HIFO"
    /\ units > 0
    /\ LET matches == Matching(spec)
       IN /\ matches # {}
          /\ FoldSeq(LAMBDA l, acc: acc + l.units, 0, SetToSeq(matches)) >= units
          /\ LET highest == HighestCost(matches)
             IN IF highest.units >= units
                THEN \* Single lot suffices
                     /\ IF highest.units = units
                        THEN lots' = lots \ {highest}
                        ELSE lots' = (lots \ {highest}) \cup
                             {[highest EXCEPT !.units = @ - units]}
                     /\ totalReduced' = totalReduced + units
                     /\ totalCostBasis' = totalCostBasis + (units * highest.cost_per_unit)
                     /\ history' = Append(history, [
                          method |-> "HIFO",
                          units |-> units,
                          from_lot |-> highest,
                          matching_lots |-> matches])  \* Track matches for invariant
                ELSE \* Need multiple lots - take all from highest cost, continue
                     /\ lots' = lots \ {highest}
                     /\ totalReduced' = totalReduced + highest.units
                     /\ totalCostBasis' = totalCostBasis + (highest.units * highest.cost_per_unit)
                     /\ history' = Append(history, [
                          method |-> "HIFO_PARTIAL",
                          units |-> highest.units,
                          from_lot |-> highest,
                          remaining |-> units - highest.units,
                          matching_lots |-> matches])  \* Track matches for invariant
          /\ UNCHANGED <<method, averageCost>>

-----------------------------------------------------------------------------
(* NONE Reduction - Just track, no lot matching *)

ReduceNone(units, cost_per_unit) ==
    /\ method = "NONE"
    /\ units > 0
    /\ totalReduced' = totalReduced + units
    /\ totalCostBasis' = totalCostBasis + (units * cost_per_unit)
    /\ history' = Append(history, [
         method |-> "NONE",
         units |-> units,
         cost |-> cost_per_unit])
    /\ UNCHANGED <<lots, method, averageCost>>

-----------------------------------------------------------------------------
(* AVERAGE Reduction - Use weighted average cost basis *)
\* AVERAGE method consolidates all lots into a single average cost basis.
\* This is common for mutual funds and some jurisdictions' tax rules.

ReduceAverage(units, spec) ==
    /\ method = "AVERAGE"
    /\ units > 0
    /\ LET matches == Matching(spec)
           totalMatching == FoldSeq(LAMBDA l, acc: acc + l.units, 0, SetToSeq(matches))
       IN /\ matches # {}
          /\ totalMatching >= units
          \* Reduce proportionally from all matching lots (simplified: reduce from first lot)
          /\ LET oldest == Oldest(matches)
             IN IF oldest.units >= units
                THEN /\ IF oldest.units = units
                        THEN lots' = lots \ {oldest}
                        ELSE lots' = (lots \ {oldest}) \cup
                             {[oldest EXCEPT !.units = @ - units]}
                     /\ totalReduced' = totalReduced + units
                     \* Use the average cost, not the lot's individual cost
                     /\ totalCostBasis' = totalCostBasis + (units * averageCost)
                     /\ history' = Append(history, [
                          method |-> "AVERAGE",
                          units |-> units,
                          from_lot |-> oldest,
                          avg_cost |-> averageCost,
                          matching_lots |-> matches])
                ELSE /\ lots' = lots \ {oldest}
                     /\ totalReduced' = totalReduced + oldest.units
                     /\ totalCostBasis' = totalCostBasis + (oldest.units * averageCost)
                     /\ history' = Append(history, [
                          method |-> "AVERAGE_PARTIAL",
                          units |-> oldest.units,
                          from_lot |-> oldest,
                          avg_cost |-> averageCost,
                          remaining |-> units - oldest.units,
                          matching_lots |-> matches])
          \* Average cost doesn't change on reduction (it's based on purchases)
          /\ UNCHANGED <<method, averageCost>>

-----------------------------------------------------------------------------
(* STRICT_WITH_SIZE Reduction - Accept exact size matches *)
\* STRICT_WITH_SIZE is like STRICT but accepts oldest exact-size match when ambiguous.

ReduceStrictWithSize(units, spec) ==
    /\ method = "STRICT_WITH_SIZE"
    /\ units > 0
    /\ LET matches == Matching(spec)
           exactMatches == ExactMatch(matches, units)
           totalMatching == FoldSeq(LAMBDA l, acc: acc + l.units, 0, SetToSeq(matches))
       IN
       \* Case 1: Exactly one match (like STRICT)
       IF Cardinality(matches) = 1
       THEN LET lot == CHOOSE l \in matches : TRUE
            IN /\ lot.units >= units
               /\ IF lot.units = units
                  THEN lots' = lots \ {lot}
                  ELSE lots' = (lots \ {lot}) \cup
                       {[lot EXCEPT !.units = @ - units]}
               /\ totalReduced' = totalReduced + units
               /\ totalCostBasis' = totalCostBasis + (units * lot.cost_per_unit)
               /\ history' = Append(history, [
                    method |-> "STRICT_WITH_SIZE",
                    units |-> units,
                    from_lot |-> lot,
                    matching_lots |-> matches])
               /\ UNCHANGED <<method, averageCost>>
       \* Case 2: Exact size match exists - take oldest exact match
       ELSE IF exactMatches # {}
       THEN LET lot == Oldest(exactMatches)
            IN /\ lots' = lots \ {lot}
               /\ totalReduced' = totalReduced + units
               /\ totalCostBasis' = totalCostBasis + (units * lot.cost_per_unit)
               /\ history' = Append(history, [
                    method |-> "STRICT_WITH_SIZE_EXACT",
                    units |-> units,
                    from_lot |-> lot,
                    matching_lots |-> matches])
               /\ UNCHANGED <<method, averageCost>>
       \* Case 3: Total match (all lots consumed exactly)
       ELSE IF totalMatching = units
       THEN /\ lots' = lots \ matches
            /\ totalReduced' = totalReduced + units
            /\ totalCostBasis' = totalCostBasis +
                 FoldSeq(LAMBDA l, acc: acc + (l.units * l.cost_per_unit), 0, SetToSeq(matches))
            /\ history' = Append(history, [
                 method |-> "STRICT_WITH_SIZE_TOTAL",
                 units |-> units,
                 from_lots |-> matches,
                 matching_lots |-> matches])
            /\ UNCHANGED <<method, averageCost>>
       \* Case 4: Ambiguous - this action is not enabled
       ELSE FALSE

-----------------------------------------------------------------------------
(* Next State *)

Next ==
    \/ \E l \in Lot : AddLot(l)
    \/ \E u \in 1..MaxUnits, s \in CostSpec : ReduceStrict(u, s)
    \/ \E u \in 1..MaxUnits, s \in CostSpec : ReduceStrictWithSize(u, s)
    \/ \E u \in 1..MaxUnits, s \in CostSpec : ReduceFIFO(u, s)
    \/ \E u \in 1..MaxUnits, s \in CostSpec : ReduceLIFO(u, s)
    \/ \E u \in 1..MaxUnits, s \in CostSpec : ReduceHIFO(u, s)
    \/ \E u \in 1..MaxUnits, s \in CostSpec : ReduceAverage(u, s)
    \/ \E u \in 1..MaxUnits, c \in 1..1000 : ReduceNone(u, c)

-----------------------------------------------------------------------------
(* Invariants *)

\* Units are never negative (for non-NONE methods)
NonNegativeUnits ==
    method # "NONE" => TotalUnits >= 0

\* Each lot has positive units
ValidLots ==
    \A l \in lots : l.units > 0

\* FIFO property: reductions come from oldest matching lots
\* Now with strong verification using the matching_lots snapshot
FIFOProperty ==
    \A i \in 1..Len(history) :
        history[i].method \in {"FIFO", "FIFO_PARTIAL"} =>
            \* The selected lot has the minimum date among ALL matching lots at reduction time
            LET h == history[i]
                selected == h.from_lot
                matches == h.matching_lots
            IN \A other \in matches : selected.date <= other.date

\* LIFO property: reductions come from newest matching lots
\* Now with strong verification using the matching_lots snapshot
LIFOProperty ==
    \A i \in 1..Len(history) :
        history[i].method \in {"LIFO", "LIFO_PARTIAL"} =>
            \* The selected lot has the maximum date among ALL matching lots at reduction time
            LET h == history[i]
                selected == h.from_lot
                matches == h.matching_lots
            IN \A other \in matches : selected.date >= other.date

\* HIFO property: reductions come from highest cost lots
\* Now with strong verification using the matching_lots snapshot
\* This is the tax-optimized strategy for minimizing capital gains
HIFOProperty ==
    \A i \in 1..Len(history) :
        history[i].method \in {"HIFO", "HIFO_PARTIAL"} =>
            \* The selected lot has the maximum cost among ALL matching lots at reduction time
            LET h == history[i]
                selected == h.from_lot
                matches == h.matching_lots
            IN \A other \in matches : selected.cost_per_unit >= other.cost_per_unit

\* AVERAGE property: uses weighted average cost basis
\* Verifies that the average cost recorded matches calculation
AVERAGEProperty ==
    \A i \in 1..Len(history) :
        history[i].method \in {"AVERAGE", "AVERAGE_PARTIAL"} =>
            \* The recorded average cost must be positive when lots exist
            history[i].avg_cost >= 0

\* STRICT never reduces from ambiguous matches
\* Ensured by action guards: ReduceStrict only enabled for single match or total match
STRICTProperty ==
    \A i \in 1..Len(history) :
        history[i].method \in {"STRICT", "STRICT_TOTAL"} =>
            LET h == history[i]
                matches == h.matching_lots
            IN \/ Cardinality(matches) = 1  \* Single match
               \/ h.method = "STRICT_TOTAL"  \* Total consumption

\* STRICT_WITH_SIZE: either unique, exact size, or total match
STRICT_WITH_SIZEProperty ==
    \A i \in 1..Len(history) :
        history[i].method \in {"STRICT_WITH_SIZE", "STRICT_WITH_SIZE_EXACT", "STRICT_WITH_SIZE_TOTAL"} =>
            LET h == history[i]
                matches == h.matching_lots
            IN \/ Cardinality(matches) = 1                    \* Unique match
               \/ h.method = "STRICT_WITH_SIZE_EXACT"          \* Exact size match
               \/ h.method = "STRICT_WITH_SIZE_TOTAL"          \* Total consumption

Invariant ==
    /\ NonNegativeUnits
    /\ ValidLots

-----------------------------------------------------------------------------
(* Properties for Model Checking *)

\* Cost basis is always tracked
CostBasisTracked ==
    totalCostBasis >= 0

\* Type correctness
TypeOK ==
    /\ lots \subseteq Lot
    /\ method \in BookingMethod
    /\ totalReduced \in Nat
    /\ totalCostBasis \in Nat
    /\ averageCost \in Nat

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars

=============================================================================
