-------------------------- MODULE InventoryProofs --------------------------
(***************************************************************************
 * TLAPS Proofs for Inventory Invariants
 *
 * This module contains formal proofs using the TLA+ Proof System (TLAPS).
 * It proves that critical invariants are maintained by all operations.
 *
 * To check proofs:
 *   tlapm InventoryProofs.tla
 *
 * Prerequisites:
 *   - TLAPS installed (https://tla.msr-inria.inria.fr/tlaps/)
 *   - Isabelle/TLA+ backend or Zenon prover
 *
 * See ROADMAP.md Phase 4 for context.
 ***************************************************************************)

EXTENDS Inventory, TLAPS

-----------------------------------------------------------------------------
(* Helper lemmas *)

\* Lemma: Empty inventory has zero units for any currency
LEMMA EmptyInventoryZeroUnits ==
    ASSUME NEW curr \in Currencies
    PROVE  TotalUnits({}, curr) = 0
PROOF
  <1>1. {p \in {} : p.units.currency = curr} = {}
    OBVIOUS
  <1>2. QED
    BY <1>1 DEF TotalUnits

\* Lemma: Adding a positive position increases units
LEMMA AugmentIncreasesUnits ==
    ASSUME NEW inv \in Inventory,
           NEW units \in Amount,
           NEW cost \in Cost \cup {NULL},
           units.number > 0
    PROVE  TotalUnits(inv \cup {[units |-> units, cost |-> cost]}, units.currency)
           > TotalUnits(inv, units.currency)
PROOF
  <1>1. [units |-> units, cost |-> cost] \in Position
    BY DEF Position
  <1>2. [units |-> units, cost |-> cost].units.number = units.number
    OBVIOUS
  <1>3. units.number > 0
    BY <1>2
  <1>4. QED
    BY <1>1, <1>3 DEF TotalUnits

-----------------------------------------------------------------------------
(* Main Theorems *)

\* Theorem: Init establishes all invariants
THEOREM InitEstablishesInvariant ==
    Init => Invariant
PROOF
  <1>1. Init => inventory = {}
    BY DEF Init
  <1>2. Init => operations = <<>>
    BY DEF Init
  <1>3. Init => errors = {}
    BY DEF Init
  <1>4. inventory = {} => NonNegativeUnits
    <2>1. SUFFICES ASSUME inventory = {},
                          NEW curr \in Currencies,
                          ~(\E op \in Range(operations) :
                              op.type = "reduce_none" /\ op.units.currency = curr)
                   PROVE  TotalUnits(inventory, curr) >= 0
      BY DEF NonNegativeUnits
    <2>2. TotalUnits({}, curr) = 0
      BY EmptyInventoryZeroUnits
    <2>3. 0 >= 0
      OBVIOUS
    <2>4. QED
      BY <2>2, <2>3
  <1>5. inventory = {} => ValidPositions
    BY DEF ValidPositions
  <1>6. inventory = {} => CostBasisTracked
    BY DEF CostBasisTracked
  <1>7. QED
    BY <1>1, <1>4, <1>5, <1>6 DEF Invariant

\* Theorem: Augment preserves NonNegativeUnits
THEOREM AugmentPreservesNonNegative ==
    ASSUME Invariant,
           NEW units \in Amount,
           NEW cost \in Cost \cup {NULL},
           units.number > 0,
           Augment(units, cost)
    PROVE  NonNegativeUnits'
PROOF
  <1>1. NonNegativeUnits
    BY DEF Invariant
  <1>2. units.number > 0
    OBVIOUS
  <1>3. CASE \E p \in inventory : p.units.currency = units.currency /\ p.cost = cost
    \* Merging case: units only increase
    <2>1. \E old \in inventory :
            /\ old.units.currency = units.currency
            /\ old.cost = cost
            /\ inventory' = (inventory \ {old}) \cup
                {[old EXCEPT !.units.number = @ + units.number]}
      BY <1>3 DEF Augment
    <2>2. TotalUnits(inventory', units.currency) >= TotalUnits(inventory, units.currency)
      BY <2>1, <1>2
    <2>3. QED
      BY <1>1, <2>2 DEF NonNegativeUnits
  <1>4. CASE ~\E p \in inventory : p.units.currency = units.currency /\ p.cost = cost
    \* New position case: units increase
    <2>1. inventory' = inventory \cup {[units |-> units, cost |-> cost]}
      BY <1>4 DEF Augment
    <2>2. TotalUnits(inventory', units.currency) > TotalUnits(inventory, units.currency)
      BY <2>1, <1>2, AugmentIncreasesUnits
    <2>3. QED
      BY <1>1, <2>2 DEF NonNegativeUnits
  <1>5. QED
    BY <1>3, <1>4

\* Theorem: Invariant is preserved by all actions
THEOREM InvariantPreserved ==
    Invariant /\ [Next]_vars => Invariant'
PROOF
  <1>1. SUFFICES ASSUME Invariant, [Next]_vars
                 PROVE  Invariant'
    OBVIOUS
  <1>2. CASE UNCHANGED vars
    BY <1>2 DEF Invariant, NonNegativeUnits, ValidPositions, CostBasisTracked, vars
  <1>3. CASE Next
    <2>1. CASE \E u \in Amount, c \in Cost \cup {NULL} : Augment(u, c)
      \* Augment preserves all invariants
      <3>1. NonNegativeUnits'
        BY <2>1, AugmentPreservesNonNegative DEF Next
      <3>2. ValidPositions'
        \* New position has non-zero units (precondition u.number > 0)
        BY <2>1 DEF Augment, ValidPositions
      <3>3. CostBasisTracked'
        \* Cost basis unchanged or new position has cost from precondition
        BY <2>1 DEF Augment, CostBasisTracked
      <3>4. QED
        BY <3>1, <3>2, <3>3 DEF Invariant
    <2>2. CASE \E u \in Amount, cs \in Cost \cup {NULL} : ReduceStrict(u, cs)
      \* ReduceStrict either errors (no change) or properly reduces
      BY <2>2 DEF ReduceStrict, Invariant, NonNegativeUnits, ValidPositions
    <2>3. CASE \E u \in Amount, cs \in Cost \cup {NULL} : ReduceFIFO(u, cs)
      \* FIFO preserves total units property
      BY <2>3 DEF ReduceFIFO, Invariant, NonNegativeUnits
    <2>4. CASE \E u \in Amount, cs \in Cost \cup {NULL} : ReduceLIFO(u, cs)
      \* LIFO preserves total units property
      BY <2>4 DEF ReduceLIFO, Invariant, NonNegativeUnits
    <2>5. CASE \E u \in Amount, c \in Cost \cup {NULL} : ReduceNone(u, c)
      \* NONE allows negative, but NonNegativeUnits exempts it
      BY <2>5 DEF ReduceNone, Invariant, NonNegativeUnits
    <2>6. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
  <1>4. QED
    BY <1>2, <1>3

\* Main Safety Theorem: Invariant holds in all reachable states
THEOREM Safety ==
    Spec => []Invariant
PROOF
  <1>1. Init => Invariant
    BY InitEstablishesInvariant
  <1>2. Invariant /\ [Next]_vars => Invariant'
    BY InvariantPreserved
  <1>3. QED
    BY <1>1, <1>2, PTL DEF Spec

=============================================================================
