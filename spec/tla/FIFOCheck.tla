-------------------------------- MODULE FIFOCheck --------------------------------
(*
 * Verify FIFO booking method correctness.
 *
 * This spec models the actual Rust inventory behavior and checks whether
 * FIFO always selects the oldest lot.
 *
 * KEY INSIGHT: The Rust code relies on insertion order, not date sorting.
 * This spec checks if that's always correct.
 *)

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS MaxLots, MaxUnits, MaxDate

VARIABLES
    lots,           \* Sequence of [units, date] records
    reductionLog    \* History of reductions: [selected_date, all_dates]

vars == <<lots, reductionLog>>

-----------------------------------------------------------------------------
(* Type definitions *)

Lot == [units: 1..MaxUnits, date: 1..MaxDate]

TypeOK ==
    /\ lots \in Seq(Lot)
    /\ Len(lots) <= MaxLots

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ lots = <<>>
    /\ reductionLog = <<>>

-----------------------------------------------------------------------------
(* Actions *)

(* Add a new lot - can be added with ANY date, not necessarily in order *)
AddLot(units, date) ==
    /\ Len(lots) < MaxLots
    /\ units > 0
    /\ lots' = Append(lots, [units |-> units, date |-> date])
    /\ UNCHANGED reductionLog

(* Reduce using FIFO - takes from FIRST lot in sequence (insertion order) *)
(* This models the actual Rust behavior *)
ReduceFIFO(units) ==
    /\ Len(lots) > 0
    /\ units > 0
    /\ units <= lots[1].units  \* Can only reduce what's available in first lot
    /\ LET firstLot == lots[1]
           allDates == {lots[i].date : i \in 1..Len(lots)}
       IN /\ reductionLog' = Append(reductionLog,
               [selected |-> firstLot.date, available |-> allDates])
          /\ IF units = firstLot.units
             THEN lots' = Tail(lots)  \* Remove exhausted lot
             ELSE lots' = <<[units |-> firstLot.units - units,
                             date |-> firstLot.date]>> \o Tail(lots)

Next ==
    \/ \E u \in 1..MaxUnits, d \in 1..MaxDate : AddLot(u, d)
    \/ \E u \in 1..MaxUnits : ReduceFIFO(u)

-----------------------------------------------------------------------------
(* THE KEY INVARIANT: FIFO must select the OLDEST lot *)

FIFOSelectsOldest ==
    \A i \in 1..Len(reductionLog) :
        LET r == reductionLog[i]
            selectedDate == r.selected
            allDates == r.available
        IN \A d \in allDates : selectedDate <= d

(* If this invariant fails, it means FIFO didn't pick the oldest lot *)

-----------------------------------------------------------------------------
(* Spec *)

Spec == Init /\ [][Next]_vars

=============================================================================
