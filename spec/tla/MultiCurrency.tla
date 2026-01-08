------------------------------ MODULE MultiCurrency ------------------------------
(*
 * Multi-Currency Conservation
 *
 * Extends Conservation.tla to track multiple currencies independently.
 * Each currency has its own conservation invariant:
 *   inventory[c] + totalReduced[c] = totalAdded[c]
 *
 * This catches bugs where currency mixing causes units to appear/disappear.
 *)

EXTENDS Integers, FiniteSets

CONSTANTS
    Currencies,     \* Set of currencies: {"USD", "AAPL", "GOOG"}
    MaxUnits,       \* Maximum units per operation
    MaxOperations   \* Maximum number of operations

VARIABLES
    inventory,      \* inventory[currency] = current units
    totalAdded,     \* totalAdded[currency] = total ever added
    totalReduced,   \* totalReduced[currency] = total ever reduced
    opCount         \* Number of operations performed

vars == <<inventory, totalAdded, totalReduced, opCount>>

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ inventory = [c \in Currencies |-> 0]
    /\ totalAdded = [c \in Currencies |-> 0]
    /\ totalReduced = [c \in Currencies |-> 0]
    /\ opCount = 0

-----------------------------------------------------------------------------
(* Actions *)

(* Add units of a specific currency *)
Add(currency, units) ==
    /\ currency \in Currencies
    /\ units > 0
    /\ units <= MaxUnits
    /\ opCount < MaxOperations
    /\ inventory' = [inventory EXCEPT ![currency] = @ + units]
    /\ totalAdded' = [totalAdded EXCEPT ![currency] = @ + units]
    /\ opCount' = opCount + 1
    /\ UNCHANGED totalReduced

(* Reduce units of a specific currency *)
Reduce(currency, units) ==
    /\ currency \in Currencies
    /\ units > 0
    /\ units <= MaxUnits
    /\ units <= inventory[currency]  \* Can't reduce more than available
    /\ opCount < MaxOperations
    /\ inventory' = [inventory EXCEPT ![currency] = @ - units]
    /\ totalReduced' = [totalReduced EXCEPT ![currency] = @ + units]
    /\ opCount' = opCount + 1
    /\ UNCHANGED totalAdded

Next ==
    \/ \E c \in Currencies, u \in 1..MaxUnits : Add(c, u)
    \/ \E c \in Currencies, u \in 1..MaxUnits : Reduce(c, u)

-----------------------------------------------------------------------------
(* INVARIANTS *)

(* Conservation holds for EACH currency independently *)
ConservationPerCurrency ==
    \A c \in Currencies :
        inventory[c] + totalReduced[c] = totalAdded[c]

(* No currency can have negative inventory *)
NonNegativeInventory ==
    \A c \in Currencies : inventory[c] >= 0

(* Reduced can never exceed added for any currency *)
ReduceBoundPerCurrency ==
    \A c \in Currencies : totalReduced[c] <= totalAdded[c]

(* Type invariant *)
TypeOK ==
    /\ \A c \in Currencies : inventory[c] \in Int
    /\ \A c \in Currencies : totalAdded[c] \in Nat
    /\ \A c \in Currencies : totalReduced[c] \in Nat
    /\ opCount \in Nat

-----------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

=============================================================================
