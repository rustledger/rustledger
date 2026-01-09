------------------------------ MODULE HIFOCorrect ------------------------------
(*
 * Verify CORRECT HIFO booking method.
 *
 * HIFO (Highest-In First-Out) selects the lot with MAXIMUM COST.
 * It tracks only the LAST selection to avoid state explosion.
 *)

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS MaxLots, MaxUnits, MaxCost

VARIABLES
    lots,           \* Sequence of [units, cost] records
    lastSelected    \* Record of last selection: [cost, allCosts]

vars == <<lots, lastSelected>>

-----------------------------------------------------------------------------
Init ==
    /\ lots = <<>>
    /\ lastSelected = [cost |-> 0, allCosts |-> {}]

-----------------------------------------------------------------------------
AddLot(units, cost) ==
    /\ Len(lots) < MaxLots
    /\ lots' = Append(lots, [units |-> units, cost |-> cost])
    /\ UNCHANGED lastSelected

(* Find the maximum cost in the lot sequence *)
MaxCostVal(lotSeq) ==
    LET costs == {lotSeq[i].cost : i \in 1..Len(lotSeq)}
    IN CHOOSE c \in costs : \A c2 \in costs : c >= c2

(* Find index of lot with maximum cost *)
MaxCostIndex(lotSeq) ==
    CHOOSE i \in 1..Len(lotSeq) : lotSeq[i].cost = MaxCostVal(lotSeq)

(* Remove element at index *)
RemoveAt(seq, idx) ==
    IF Len(seq) = 1 THEN <<>>
    ELSE [i \in 1..(Len(seq)-1) |-> IF i < idx THEN seq[i] ELSE seq[i+1]]

(* CORRECT HIFO: Select lot with MAXIMUM COST *)
ReduceHIFO ==
    /\ Len(lots) > 0
    /\ LET idx == MaxCostIndex(lots)
           selectedLot == lots[idx]
           allCosts == {lots[i].cost : i \in 1..Len(lots)}
       IN /\ lastSelected' = [cost |-> selectedLot.cost, allCosts |-> allCosts]
          /\ lots' = RemoveAt(lots, idx)

Next ==
    \/ \E u \in 1..MaxUnits, c \in 1..MaxCost : AddLot(u, c)
    \/ ReduceHIFO

-----------------------------------------------------------------------------
(* INVARIANT: HIFO selection was correct - selected cost >= all available *)

HIFOSelectsHighest ==
    lastSelected.cost > 0 =>
        \A c \in lastSelected.allCosts : lastSelected.cost >= c

TypeOK ==
    /\ lots \in Seq([units: 1..MaxUnits, cost: 1..MaxCost])
    /\ Len(lots) <= MaxLots

-----------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

=============================================================================
