------------------------------ MODULE PriceDB ------------------------------
(*
 * Price Database
 *
 * Simple model of price database for currency conversion.
 * Verifies identity price property: price of X in X is always 1.
 *
 * Direction supersession (#1759): the two directions of a currency
 * pair share ONE rate timeline, exactly like Python beancount's
 * build_price_map (which materializes both directions of every price
 * and picks by date recency). Setting base->quote therefore CLEARS
 * quote->base: the newer write is authoritative for the pair, and
 * the implementation derives the opposite direction as the
 * reciprocal.
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

(* Set a price between two currencies. The pair has one timeline:
   the newer write supersedes the opposite direction (#1759), so the
   inverse entry is cleared — the implementation derives it as the
   reciprocal of this rate. *)
SetPrice(base, quote, price) ==
    /\ base # quote
    /\ base \in Currencies
    /\ quote \in Currencies
    /\ price \in 1..MaxPrice
    /\ opCount < MaxOps
    /\ prices' = [prices EXCEPT ![base][quote] = price, ![quote][base] = 0]
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

(* At most one direction of a pair holds a rate: every SetPrice
   clears its inverse, so both-nonzero states are unreachable. *)
OneDirectionPerPair ==
    \A b, q \in Currencies :
        (b # q /\ prices[b][q] # 0) => prices[q][b] = 0

-----------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

=============================================================================
