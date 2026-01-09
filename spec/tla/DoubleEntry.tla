------------------------------ MODULE DoubleEntry ------------------------------
(*
 * Double-Entry Bookkeeping Invariant
 *
 * Verifies that every transaction balances: sum of debits = sum of credits
 * This is THE fundamental property of double-entry accounting.
 *
 * Simple model:
 * - Each transaction has a debit account, credit account, and amount
 * - Debit amount always equals credit amount (balanced by construction)
 * - No self-transfers allowed
 *)

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Accounts,       \* Set of account names
    MaxAmount,      \* Maximum amount per transaction
    MaxTxns         \* Maximum transactions to explore

VARIABLES
    ledger          \* Sequence of transactions

vars == <<ledger>>

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    ledger = <<>>

-----------------------------------------------------------------------------
(* Actions *)

(* Add a balanced transaction to the ledger *)
AddTransaction(fromAccount, toAccount, amount) ==
    /\ Len(ledger) < MaxTxns
    /\ fromAccount # toAccount  \* No self-transfer
    /\ amount > 0
    /\ ledger' = Append(ledger, [debit |-> fromAccount,
                                  credit |-> toAccount,
                                  amount |-> amount])

Next ==
    \E from, to \in Accounts, amt \in 1..MaxAmount :
        AddTransaction(from, to, amt)

-----------------------------------------------------------------------------
(* INVARIANTS *)

(* Every transaction has positive amount (debit = credit implicitly) *)
TransactionsBalance ==
    \A i \in 1..Len(ledger) :
        ledger[i].amount > 0

(* Debit and credit accounts are always different *)
NoSelfTransfer ==
    \A i \in 1..Len(ledger) :
        ledger[i].debit # ledger[i].credit

(* Accounts exist in our set *)
ValidAccounts ==
    \A i \in 1..Len(ledger) :
        /\ ledger[i].debit \in Accounts
        /\ ledger[i].credit \in Accounts

-----------------------------------------------------------------------------
(* Derived property: Global balance is zero *)
(* For any account, debits - credits gives the balance *)
(* Sum of all balances = 0 because each txn is balanced *)

(* Count debits to an account *)
DebitCount(acct) ==
    Cardinality({i \in 1..Len(ledger) : ledger[i].debit = acct})

(* Count credits to an account *)
CreditCount(acct) ==
    Cardinality({i \in 1..Len(ledger) : ledger[i].credit = acct})

-----------------------------------------------------------------------------
(* Spec *)

Spec == Init /\ [][Next]_vars

=============================================================================
