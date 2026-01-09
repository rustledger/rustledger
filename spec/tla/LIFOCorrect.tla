------------------------------ MODULE LIFOCorrect ------------------------------
(*
 * Verify CORRECT LIFO booking method.
 *
 * LIFO (Last-In First-Out) selects the lot with MAXIMUM DATE.
 * It tracks only the LAST selection to avoid state explosion.
 *)

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS MaxLots, MaxUnits, MaxDate

VARIABLES
    lots,           \* Sequence of [units, date] records
    lastSelected    \* Record of last selection: [date, allDates]

vars == <<lots, lastSelected>>

-----------------------------------------------------------------------------
Init ==
    /\ lots = <<>>
    /\ lastSelected = [date |-> 0, allDates |-> {}]

-----------------------------------------------------------------------------
AddLot(units, date) ==
    /\ Len(lots) < MaxLots
    /\ lots' = Append(lots, [units |-> units, date |-> date])
    /\ UNCHANGED lastSelected

(* Find the maximum date in the lot sequence *)
MaxDateVal(lotSeq) ==
    LET dates == {lotSeq[i].date : i \in 1..Len(lotSeq)}
    IN CHOOSE d \in dates : \A d2 \in dates : d >= d2

(* Find index of lot with maximum date *)
MaxDateIndex(lotSeq) ==
    CHOOSE i \in 1..Len(lotSeq) : lotSeq[i].date = MaxDateVal(lotSeq)

(* Remove element at index *)
RemoveAt(seq, idx) ==
    IF Len(seq) = 1 THEN <<>>
    ELSE [i \in 1..(Len(seq)-1) |-> IF i < idx THEN seq[i] ELSE seq[i+1]]

(* CORRECT LIFO: Select lot with MAXIMUM DATE *)
ReduceLIFO ==
    /\ Len(lots) > 0
    /\ LET idx == MaxDateIndex(lots)
           selectedLot == lots[idx]
           allDates == {lots[i].date : i \in 1..Len(lots)}
       IN /\ lastSelected' = [date |-> selectedLot.date, allDates |-> allDates]
          /\ lots' = RemoveAt(lots, idx)

Next ==
    \/ \E u \in 1..MaxUnits, d \in 1..MaxDate : AddLot(u, d)
    \/ ReduceLIFO

-----------------------------------------------------------------------------
(* INVARIANT: LIFO selection was correct - selected date >= all available *)

LIFOSelectsNewest ==
    lastSelected.date > 0 =>
        \A d \in lastSelected.allDates : lastSelected.date >= d

TypeOK ==
    /\ lots \in Seq([units: 1..MaxUnits, date: 1..MaxDate])
    /\ Len(lots) <= MaxLots

-----------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

=============================================================================
