---------------------------- MODULE InventoryTyped ----------------------------
(***************************************************************************
 * Apalache-Typed Inventory Specification
 *
 * This module adds Apalache type annotations to the Inventory spec for
 * improved symbolic model checking. Type annotations help Apalache:
 * - Understand the structure of complex data types
 * - Generate more efficient SMT constraints
 * - Find bugs in unbounded state spaces
 *
 * Usage: apalache-mc check --config=InventoryTyped.cfg InventoryTyped.tla
 ***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, Apalache

CONSTANTS
    \* @type: Set(Str);
    Currencies,
    \* @type: Int;
    MaxUnits,
    \* @type: Int;
    MaxPositions

-----------------------------------------------------------------------------
(* Type Definitions with Apalache Annotations *)

\* @typeAlias: DECIMAL = Int;
\* @typeAlias: AMOUNT = { number: Int, currency: Str };
\* @typeAlias: COST = { number: Int, currency: Str, date: Int, label: Str };
\* @typeAlias: POSITION = { units: AMOUNT, cost: COST };
\* @typeAlias: OPERATION = { type: Str, units: AMOUNT, cost: COST };
\* @typeAlias: ERROR = { type: Str, units: AMOUNT };

-----------------------------------------------------------------------------
(* Variables with Type Annotations *)

VARIABLES
    \* @type: Set(POSITION);
    inventory,
    \* @type: Seq(OPERATION);
    operations,
    \* @type: Set(ERROR);
    errors

vars == <<inventory, operations, errors>>

-----------------------------------------------------------------------------
(* Helper Functions with Type Annotations *)

\* @type: (Set(POSITION), Str) => Int;
TotalUnits(inv, curr) ==
    LET
        \* @type: Set(POSITION);
        positions == {p \in inv : p.units.currency = curr}
    IN IF positions = {} THEN 0
       ELSE LET
           \* @type: Seq(POSITION);
           posSeq == SetAsFun(positions)
       IN FoldSet(LAMBDA p, acc: acc + p.units.number, 0, positions)

\* @type: (Set(POSITION), Str, COST) => Set(POSITION);
MatchingPositions(inv, curr, costSpec) ==
    {p \in inv :
        /\ p.units.currency = curr
        /\ (costSpec.number = 0 \/ p.cost.number = costSpec.number)
        /\ (costSpec.currency = "" \/ p.cost.currency = costSpec.currency)
        /\ (costSpec.date = 0 \/ p.cost.date = costSpec.date)
    }

\* @type: (Set(POSITION)) => POSITION;
OldestPosition(positions) ==
    CHOOSE p \in positions :
        \A other \in positions : p.cost.date <= other.cost.date

\* @type: (Set(POSITION)) => POSITION;
NewestPosition(positions) ==
    CHOOSE p \in positions :
        \A other \in positions : p.cost.date >= other.cost.date

-----------------------------------------------------------------------------
(* Initial State *)

\* @type: Bool;
Init ==
    /\ inventory = {}
    /\ operations = <<>>
    /\ errors = {}

-----------------------------------------------------------------------------
(* Augment: Add units to inventory *)

\* @type: (AMOUNT, COST) => Bool;
Augment(units, cost) ==
    /\ units.number > 0
    /\ LET
           \* @type: POSITION;
           newPos == [units |-> units, cost |-> cost]
           \* @type: Set(POSITION);
           existing == {p \in inventory :
               /\ p.units.currency = units.currency
               /\ p.cost = cost}
       IN IF existing # {}
          THEN LET
                   \* @type: POSITION;
                   old == CHOOSE p \in existing : TRUE
                   \* @type: POSITION;
                   merged == [old EXCEPT !.units.number = @ + units.number]
               IN inventory' = (inventory \ {old}) \cup {merged}
          ELSE inventory' = inventory \cup {newPos}
    /\ operations' = Append(operations, [type |-> "augment", units |-> units, cost |-> cost])
    /\ UNCHANGED errors

-----------------------------------------------------------------------------
(* Reduce with FIFO booking *)

\* @type: (AMOUNT, COST) => Bool;
ReduceFIFO(units, costSpec) ==
    /\ units.number < 0
    /\ LET
           \* @type: Set(POSITION);
           matches == MatchingPositions(inventory, units.currency, costSpec)
           \* @type: Int;
           reduction == -units.number
       IN /\ matches # {}
          /\ LET
                 \* @type: POSITION;
                 oldest == OldestPosition(matches)
             IN /\ oldest.units.number >= reduction
                /\ IF oldest.units.number = reduction
                   THEN inventory' = inventory \ {oldest}
                   ELSE LET
                            \* @type: POSITION;
                            reduced == [oldest EXCEPT !.units.number = @ - reduction]
                        IN inventory' = (inventory \ {oldest}) \cup {reduced}
    /\ operations' = Append(operations, [type |-> "reduce_fifo", units |-> units, cost |-> costSpec])
    /\ UNCHANGED errors

-----------------------------------------------------------------------------
(* Reduce with LIFO booking *)

\* @type: (AMOUNT, COST) => Bool;
ReduceLIFO(units, costSpec) ==
    /\ units.number < 0
    /\ LET
           \* @type: Set(POSITION);
           matches == MatchingPositions(inventory, units.currency, costSpec)
           \* @type: Int;
           reduction == -units.number
       IN /\ matches # {}
          /\ LET
                 \* @type: POSITION;
                 newest == NewestPosition(matches)
             IN /\ newest.units.number >= reduction
                /\ IF newest.units.number = reduction
                   THEN inventory' = inventory \ {newest}
                   ELSE LET
                            \* @type: POSITION;
                            reduced == [newest EXCEPT !.units.number = @ - reduction]
                        IN inventory' = (inventory \ {newest}) \cup {reduced}
    /\ operations' = Append(operations, [type |-> "reduce_lifo", units |-> units, cost |-> costSpec])
    /\ UNCHANGED errors

-----------------------------------------------------------------------------
(* Next State *)

\* @type: Bool;
Next ==
    \/ \E u \in [number: 1..MaxUnits, currency: Currencies],
          c \in [number: 1..100, currency: Currencies, date: 1..365, label: {""}] :
        Augment(u, c)
    \/ \E u \in [number: (-MaxUnits)..(-1), currency: Currencies],
          cs \in [number: 0..100, currency: Currencies \cup {""}, date: 0..365, label: {""}] :
        ReduceFIFO(u, cs)
    \/ \E u \in [number: (-MaxUnits)..(-1), currency: Currencies],
          cs \in [number: 0..100, currency: Currencies \cup {""}, date: 0..365, label: {""}] :
        ReduceLIFO(u, cs)

-----------------------------------------------------------------------------
(* Invariants *)

\* @type: Bool;
NonNegativeUnits ==
    \A curr \in Currencies :
        ~(\E i \in DOMAIN operations : operations[i].type = "reduce_none")
        => TotalUnits(inventory, curr) >= 0

\* @type: Bool;
ValidPositions ==
    \A p \in inventory :
        /\ p.units.number # 0
        /\ p.units.currency \in Currencies

\* @type: Bool;
Invariant ==
    /\ NonNegativeUnits
    /\ ValidPositions

-----------------------------------------------------------------------------
(* Type Invariant for Apalache *)

\* @type: Bool;
TypeOK ==
    /\ \A p \in inventory :
        /\ p.units.number \in Int
        /\ p.units.currency \in Currencies
        /\ p.cost.number \in Int
        /\ p.cost.date \in Int
    /\ \A op \in Range(operations) :
        op.type \in {"augment", "reduce_fifo", "reduce_lifo", "reduce_none"}

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars

=============================================================================
