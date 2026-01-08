--------------------------- MODULE ValidationCorrect ---------------------------
(*
 * Balance Assertion Validation
 *
 * Verifies:
 * - Balance assertions only fail when there's a mismatch
 * - Balance errors persist once detected
 * - Running balance tracking is accurate
 *
 * This models rustledger-validate's balance assertion logic.
 *)

EXTENDS Integers

CONSTANTS
    MaxUnits,       \* Maximum units per operation
    MaxOperations   \* Maximum operations to track

VARIABLES
    balance,            \* Current actual balance
    hasError,           \* Whether a balance error has been detected
    errorExpected,      \* Expected value at time of first error (if any)
    errorActual,        \* Actual balance at time of first error (if any)
    operations          \* Number of operations performed

vars == <<balance, hasError, errorExpected, errorActual, operations>>

UNSET == -1  \* Value for unset error details

-----------------------------------------------------------------------------
Init ==
    /\ balance = 0
    /\ hasError = FALSE
    /\ errorExpected = UNSET
    /\ errorActual = UNSET
    /\ operations = 0

-----------------------------------------------------------------------------
(* Add units to balance (posting) *)
AddUnits(units) ==
    /\ operations < MaxOperations
    /\ units > 0
    /\ units <= MaxUnits
    /\ balance' = balance + units
    /\ operations' = operations + 1
    /\ UNCHANGED <<hasError, errorExpected, errorActual>>

(* Remove units from balance (posting) *)
RemoveUnits(units) ==
    /\ operations < MaxOperations
    /\ units > 0
    /\ units <= MaxUnits
    /\ balance >= units  \* Can't go negative (for most account types)
    /\ balance' = balance - units
    /\ operations' = operations + 1
    /\ UNCHANGED <<hasError, errorExpected, errorActual>>

(* Check balance assertion - matches *)
AssertBalanceMatches(exp) ==
    /\ operations < MaxOperations
    /\ exp = balance
    /\ exp >= 0
    /\ exp <= MaxUnits * MaxOperations
    /\ operations' = operations + 1
    /\ UNCHANGED <<balance, hasError, errorExpected, errorActual>>

(* Check balance assertion - mismatch detected (first error) *)
AssertBalanceMismatchFirst(wrongExp) ==
    /\ operations < MaxOperations
    /\ wrongExp # balance
    /\ wrongExp >= 0
    /\ wrongExp <= MaxUnits * MaxOperations
    /\ ~hasError  \* Only capture first error
    /\ hasError' = TRUE
    /\ errorExpected' = wrongExp
    /\ errorActual' = balance
    /\ operations' = operations + 1
    /\ UNCHANGED <<balance>>

(* Check balance assertion - mismatch detected (subsequent error) *)
AssertBalanceMismatchSubsequent(wrongExp) ==
    /\ operations < MaxOperations
    /\ wrongExp # balance
    /\ wrongExp >= 0
    /\ wrongExp <= MaxUnits * MaxOperations
    /\ hasError  \* Already have an error
    /\ operations' = operations + 1
    /\ UNCHANGED <<balance, hasError, errorExpected, errorActual>>

Next ==
    \/ \E units \in 1..MaxUnits : AddUnits(units)
    \/ \E units \in 1..MaxUnits : RemoveUnits(units)
    \/ \E exp \in 0..(MaxUnits * MaxOperations) : AssertBalanceMatches(exp)
    \/ \E exp \in 0..(MaxUnits * MaxOperations) : AssertBalanceMismatchFirst(exp)
    \/ \E exp \in 0..(MaxUnits * MaxOperations) : AssertBalanceMismatchSubsequent(exp)

-----------------------------------------------------------------------------
(* INVARIANTS *)

(* Balance is always non-negative *)
NonNegativeBalance ==
    balance >= 0

(* If error was detected, the first error assertion was indeed a mismatch *)
ErrorMeansFirstMismatch ==
    hasError => (errorExpected # errorActual)

(* Error details are set iff hasError *)
ErrorDetailsConsistent ==
    hasError <=> (errorExpected # UNSET /\ errorActual # UNSET)

(* Operations are bounded *)
OperationsBounded ==
    operations <= MaxOperations

(* Balance doesn't exceed maximum possible *)
BalanceBounded ==
    balance <= MaxUnits * MaxOperations

(* Type invariant *)
TypeOK ==
    /\ balance \in 0..(MaxUnits * MaxOperations)
    /\ hasError \in BOOLEAN
    /\ errorExpected \in {UNSET} \cup (0..(MaxUnits * MaxOperations))
    /\ errorActual \in {UNSET} \cup (0..(MaxUnits * MaxOperations))
    /\ operations \in 0..MaxOperations

Spec == Init /\ [][Next]_vars

=============================================================================
