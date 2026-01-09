------------------------------ MODULE FIFOCorrect ------------------------------
(*
 * Verify CORRECT FIFO booking method.
 *
 * This spec models the FIXED Rust behavior: FIFO selects by DATE (minimum).
 * It tracks only the LAST selection to avoid state explosion.
 *)

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS MaxLots, MaxUnits, MaxDate

VARIABLES
    lots,           \* Sequence of [units, date] records
    lastSelected    \* Record of last selection: [date, allDates] or empty

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

(* Find the minimum date in the lot sequence *)
MinDate(lotSeq) ==
    LET dates == {lotSeq[i].date : i \in 1..Len(lotSeq)}
    IN CHOOSE d \in dates : \A d2 \in dates : d <= d2

(* Find index of lot with minimum date *)
MinDateIndex(lotSeq) ==
    CHOOSE i \in 1..Len(lotSeq) : lotSeq[i].date = MinDate(lotSeq)

(* Remove element at index *)
RemoveAt(seq, idx) ==
    IF Len(seq) = 1 THEN <<>>
    ELSE [i \in 1..(Len(seq)-1) |-> IF i < idx THEN seq[i] ELSE seq[i+1]]

(* CORRECT FIFO: Select lot with MINIMUM DATE *)
ReduceFIFO ==
    /\ Len(lots) > 0
    /\ LET idx == MinDateIndex(lots)
           selectedLot == lots[idx]
           allDates == {lots[i].date : i \in 1..Len(lots)}
       IN /\ lastSelected' = [date |-> selectedLot.date, allDates |-> allDates]
          /\ lots' = RemoveAt(lots, idx)

Next ==
    \/ \E u \in 1..MaxUnits, d \in 1..MaxDate : AddLot(u, d)
    \/ ReduceFIFO

-----------------------------------------------------------------------------
(* INVARIANT: FIFO selection was correct - selected date <= all available *)

FIFOSelectsOldest ==
    lastSelected.date > 0 =>
        \A d \in lastSelected.allDates : lastSelected.date <= d

TypeOK ==
    /\ lots \in Seq([units: 1..MaxUnits, date: 1..MaxDate])
    /\ Len(lots) <= MaxLots

-----------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

=============================================================================
