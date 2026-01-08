------------------------------ MODULE Interpolation ------------------------------
(*
 * NULL Posting Interpolation
 *
 * Verifies:
 * - At most one NULL (missing) amount per transaction
 * - NULL is filled with the balancing amount
 * - Transaction balances after interpolation
 *
 * Uses "UNSET" for uninitialized slots, "NULL" for explicit missing amounts.
 *)

EXTENDS Integers

CONSTANTS MaxAmount

\* Special values outside normal range
UNSET == -1000      \* Posting slot not yet used
NULL == -1001       \* Explicit NULL (to be interpolated)

VARIABLES
    posting1,       \* First posting amount
    posting2,       \* Second posting amount
    hasNull,        \* Whether we have a NULL posting
    complete        \* Whether transaction is complete

vars == <<posting1, posting2, hasNull, complete>>

-----------------------------------------------------------------------------
Init ==
    /\ posting1 = UNSET
    /\ posting2 = UNSET
    /\ hasNull = FALSE
    /\ complete = FALSE

-----------------------------------------------------------------------------
(* Add first posting with amount *)
AddPosting1(amt) ==
    /\ posting1 = UNSET
    /\ ~complete
    /\ posting1' = amt
    /\ UNCHANGED <<posting2, hasNull, complete>>

(* Add second posting with amount *)
AddPosting2(amt) ==
    /\ posting1 # UNSET
    /\ posting2 = UNSET
    /\ ~complete
    /\ posting2' = amt
    /\ UNCHANGED <<posting1, hasNull, complete>>

(* Mark second posting as NULL (to be interpolated) *)
AddPosting2Null ==
    /\ posting1 # UNSET
    /\ posting1 # NULL
    /\ posting2 = UNSET
    /\ ~hasNull
    /\ ~complete
    /\ posting2' = NULL
    /\ hasNull' = TRUE
    /\ UNCHANGED <<posting1, complete>>

(* Interpolate: fill NULL with balancing amount *)
Interpolate ==
    /\ posting1 # UNSET
    /\ posting2 = NULL
    /\ hasNull
    /\ ~complete
    /\ posting2' = -posting1  \* Balance the transaction
    /\ complete' = TRUE
    /\ UNCHANGED <<posting1, hasNull>>

(* Complete with explicit amounts (must balance) *)
CompleteBalanced ==
    /\ posting1 # UNSET
    /\ posting2 # UNSET
    /\ posting2 # NULL
    /\ ~complete
    /\ posting1 + posting2 = 0
    /\ complete' = TRUE
    /\ UNCHANGED <<posting1, posting2, hasNull>>

Next ==
    \/ \E amt \in (-MaxAmount..MaxAmount) \ {0} : AddPosting1(amt)
    \/ \E amt \in (-MaxAmount..MaxAmount) \ {0} : AddPosting2(amt)
    \/ AddPosting2Null
    \/ Interpolate
    \/ CompleteBalanced

-----------------------------------------------------------------------------
(* INVARIANTS *)

(* At most one NULL posting *)
AtMostOneNull ==
    ~(posting1 = NULL /\ posting2 = NULL)

(* After completion, transaction is balanced *)
CompleteImpliesBalanced ==
    complete =>
        /\ posting1 # UNSET
        /\ posting2 # UNSET
        /\ posting2 # NULL
        /\ posting1 + posting2 = 0

(* hasNull flag tracks whether NULL was used (even after interpolation) *)
HasNullAccurate ==
    hasNull => (posting2 = NULL \/ complete)

Spec == Init /\ [][Next]_vars

=============================================================================
