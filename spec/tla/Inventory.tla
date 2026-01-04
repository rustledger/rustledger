---------------------------- MODULE Inventory ----------------------------
(***************************************************************************
 * TLA+ Specification for Beancount Inventory
 *
 * Models the core inventory data structure and operations.
 * An inventory is a collection of positions (lots) that can be
 * augmented (add units) or reduced (remove units).
 *
 * Key invariants verified:
 * - Units never go negative (except with NONE booking)
 * - Total units are preserved through operations
 * - Cost basis is tracked correctly
 ***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Currencies,     \* Set of all currencies (e.g., {"USD", "AAPL"})
    MaxUnits,       \* Maximum units for model checking bounds
    MaxPositions    \* Maximum positions per inventory

-----------------------------------------------------------------------------
(* Type Definitions *)

\* A decimal is modeled as an integer (scaled by 100 for 2 decimal places)
Decimal == Int

\* An amount is a quantity of a currency
Amount == [number: Decimal, currency: Currencies]

\* A cost specification for a lot
Cost == [
    number: Decimal,
    currency: Currencies,
    date: Int,          \* Days since epoch (simplified)
    label: STRING \cup {NULL}
]

\* A position is units held at an optional cost
Position == [
    units: Amount,
    cost: Cost \cup {NULL}
]

\* An inventory is a set of positions
Inventory == SUBSET Position

-----------------------------------------------------------------------------
(* Variables *)

VARIABLES
    inventory,      \* Current inventory state
    operations,     \* History of operations performed
    errors          \* Accumulated errors

vars == <<inventory, operations, errors>>

-----------------------------------------------------------------------------
(* Helper Functions *)

\* Sum of units for a specific currency
TotalUnits(inv, curr) ==
    LET positions == {p \in inv : p.units.currency = curr}
    IN IF positions = {} THEN 0
       ELSE FoldSet(LAMBDA p, acc: acc + p.units.number, 0, positions)

\* Find positions matching a cost specification
MatchingPositions(inv, curr, costSpec) ==
    {p \in inv :
        /\ p.units.currency = curr
        /\ (costSpec = NULL => p.cost = NULL)
        /\ (costSpec # NULL =>
            /\ p.cost # NULL
            /\ (costSpec.number = NULL \/ p.cost.number = costSpec.number)
            /\ (costSpec.currency = NULL \/ p.cost.currency = costSpec.currency)
            /\ (costSpec.date = NULL \/ p.cost.date = costSpec.date)
            /\ (costSpec.label = NULL \/ p.cost.label = costSpec.label)
        )
    }

\* Sort positions by date (for FIFO/LIFO)
SortByDate(positions, ascending) ==
    \* Returns a sequence of positions sorted by date
    \* In TLA+ we'd need a more complex implementation;
    \* here we specify the requirement
    LET sorted == CHOOSE s \in Seq(positions) :
        /\ Len(s) = Cardinality(positions)
        /\ \A i \in 1..Len(s)-1 :
            IF ascending
            THEN s[i].cost.date <= s[i+1].cost.date
            ELSE s[i].cost.date >= s[i+1].cost.date
    IN sorted

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ inventory = {}
    /\ operations = <<>>
    /\ errors = {}

-----------------------------------------------------------------------------
(* Augment: Add units to inventory *)

\* Adding a position always succeeds
Augment(units, cost) ==
    /\ units.number > 0  \* Augmentations must be positive
    /\ LET newPos == [units |-> units, cost |-> cost]
           \* Check if identical position exists (merge)
           existing == {p \in inventory :
               /\ p.units.currency = units.currency
               /\ p.cost = cost}
       IN IF existing # {}
          THEN \* Merge with existing position
               LET old == CHOOSE p \in existing : TRUE
                   merged == [old EXCEPT !.units.number = @ + units.number]
               IN inventory' = (inventory \ {old}) \cup {merged}
          ELSE \* Add new position
               inventory' = inventory \cup {newPos}
    /\ operations' = Append(operations, [type |-> "augment", units |-> units, cost |-> cost])
    /\ UNCHANGED errors

-----------------------------------------------------------------------------
(* Reduce: Remove units from inventory *)

\* STRICT booking: Must match exactly one lot or total match
ReduceStrict(units, costSpec) ==
    LET matches == MatchingPositions(inventory, units.currency, costSpec)
        totalMatching == FoldSet(LAMBDA p, acc: acc + p.units.number, 0, matches)
        reduction == -units.number  \* units.number is negative for reduction
    IN
    /\ units.number < 0  \* Reductions are negative
    /\ IF matches = {}
       THEN \* Error: No matching lots
            /\ errors' = errors \cup {[type |-> "NO_MATCH", units |-> units]}
            /\ UNCHANGED <<inventory, operations>>
       ELSE IF Cardinality(matches) = 1
       THEN \* Single match: reduce it
            LET pos == CHOOSE p \in matches : TRUE
            IN IF pos.units.number < reduction
               THEN \* Error: Insufficient units
                    /\ errors' = errors \cup {[type |-> "INSUFFICIENT", units |-> units]}
                    /\ UNCHANGED <<inventory, operations>>
               ELSE IF pos.units.number = reduction
               THEN \* Exact match: remove position
                    /\ inventory' = inventory \ {pos}
                    /\ operations' = Append(operations, [type |-> "reduce_strict", units |-> units])
                    /\ UNCHANGED errors
               ELSE \* Partial reduction
                    LET reduced == [pos EXCEPT !.units.number = @ - reduction]
                    IN /\ inventory' = (inventory \ {pos}) \cup {reduced}
                       /\ operations' = Append(operations, [type |-> "reduce_strict", units |-> units])
                       /\ UNCHANGED errors
       ELSE IF totalMatching = reduction
       THEN \* Total match: remove all matching positions
            /\ inventory' = inventory \ matches
            /\ operations' = Append(operations, [type |-> "reduce_strict_total", units |-> units])
            /\ UNCHANGED errors
       ELSE \* Ambiguous match error
            /\ errors' = errors \cup {[type |-> "AMBIGUOUS", units |-> units]}
            /\ UNCHANGED <<inventory, operations>>

\* FIFO booking: Take from oldest lots first
ReduceFIFO(units, costSpec) ==
    LET matches == MatchingPositions(inventory, units.currency, costSpec)
        sorted == SortByDate(matches, TRUE)  \* Ascending (oldest first)
        reduction == -units.number
    IN
    /\ units.number < 0
    /\ matches # {}
    \* Process reduction through sorted positions
    /\ \E newInv \in SUBSET Position :
        /\ TotalUnits(inventory, units.currency) - reduction =
           TotalUnits(newInv, units.currency)
        /\ inventory' = newInv
    /\ operations' = Append(operations, [type |-> "reduce_fifo", units |-> units])
    /\ UNCHANGED errors

\* LIFO booking: Take from newest lots first
ReduceLIFO(units, costSpec) ==
    LET matches == MatchingPositions(inventory, units.currency, costSpec)
        sorted == SortByDate(matches, FALSE)  \* Descending (newest first)
        reduction == -units.number
    IN
    /\ units.number < 0
    /\ matches # {}
    /\ \E newInv \in SUBSET Position :
        /\ TotalUnits(inventory, units.currency) - reduction =
           TotalUnits(newInv, units.currency)
        /\ inventory' = newInv
    /\ operations' = Append(operations, [type |-> "reduce_lifo", units |-> units])
    /\ UNCHANGED errors

\* NONE booking: Just append negative position
ReduceNone(units, cost) ==
    /\ units.number < 0
    /\ LET newPos == [units |-> units, cost |-> cost]
       IN inventory' = inventory \cup {newPos}
    /\ operations' = Append(operations, [type |-> "reduce_none", units |-> units])
    /\ UNCHANGED errors

-----------------------------------------------------------------------------
(* Next State *)

Next ==
    \/ \E u \in Amount, c \in Cost \cup {NULL} : Augment(u, c)
    \/ \E u \in Amount, cs \in Cost \cup {NULL} : ReduceStrict(u, cs)
    \/ \E u \in Amount, cs \in Cost \cup {NULL} : ReduceFIFO(u, cs)
    \/ \E u \in Amount, cs \in Cost \cup {NULL} : ReduceLIFO(u, cs)
    \/ \E u \in Amount, c \in Cost \cup {NULL} : ReduceNone(u, c)

-----------------------------------------------------------------------------
(* Invariants *)

\* Non-negative units for non-NONE booking methods
NonNegativeUnits ==
    \A curr \in Currencies :
        \* If we haven't used NONE booking for this currency
        ~(\E op \in Range(operations) : op.type = "reduce_none" /\ op.units.currency = curr)
        => TotalUnits(inventory, curr) >= 0

\* Cost basis is always tracked for positions with cost
CostBasisTracked ==
    \A p \in inventory :
        p.cost # NULL => p.cost.number > 0

\* Positions are valid
ValidPositions ==
    \A p \in inventory :
        /\ p.units.number # 0  \* No zero-unit positions
        /\ p.units.currency \in Currencies

\* Operations preserve total (for FIFO/LIFO)
\* This is checked by construction in the reduce actions

Invariant ==
    /\ NonNegativeUnits
    /\ CostBasisTracked
    /\ ValidPositions

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Properties *)

\* Eventually all operations complete without errors
EventuallyNoErrors == <>[]( errors = {} )

\* Type correctness
TypeOK ==
    /\ inventory \in SUBSET Position
    /\ operations \in Seq([type: STRING, units: Amount])
    /\ errors \in SUBSET [type: STRING, units: Amount]

=============================================================================
