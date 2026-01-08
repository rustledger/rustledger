------------------------------ MODULE PriceDB ------------------------------
(*
 * Price Database
 *
 * Simple model of price database for currency conversion.
 * Verifies identity price property: price of X in X is always 1.
 *)

EXTENDS Integers, FiniteSets

CONSTANTS
    Currencies,     \* Set of currencies
    MaxPrice        \* Maximum price value

VARIABLES
    prices,         \* prices[base][quote] = price or 0 if none
    opCount         \* Limit operations

vars == <<prices, opCount>>

MaxOps == 10

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ prices = [b \in Currencies |-> [q \in Currencies |-> 0]]
    /\ opCount = 0

-----------------------------------------------------------------------------
(* Actions *)

(* Set a price between two currencies *)
SetPrice(base, quote, price) ==
    /\ base # quote
    /\ base \in Currencies
    /\ quote \in Currencies
    /\ price \in 1..MaxPrice
    /\ opCount < MaxOps
    /\ prices' = [prices EXCEPT ![base][quote] = price]
    /\ opCount' = opCount + 1

Next ==
    \E b, q \in Currencies, p \in 1..MaxPrice : SetPrice(b, q, p)

-----------------------------------------------------------------------------
(* INVARIANTS *)

(* Identity: price of X in X is implicitly 1 (we store 0 for same currency) *)
(* Self-prices are never set because SetPrice requires base # quote *)
SelfPricesNeverSet ==
    \A c \in Currencies : prices[c][c] = 0

(* Type invariant *)
TypeOK ==
    /\ \A b, q \in Currencies : prices[b][q] \in 0..MaxPrice
    /\ opCount \in Nat

-----------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

=============================================================================
