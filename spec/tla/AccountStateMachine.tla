-------------------------- MODULE AccountStateMachine --------------------------
(*
 * Account Lifecycle State Machine
 *
 * Verifies:
 * - Accounts transition: unopened → open → closed
 * - Cannot reopen a closed account
 * - Cannot post to unopened or closed accounts
 * - Cannot close account with non-zero balance
 *)

EXTENDS Integers

CONSTANTS Accounts, MaxBalance

VARIABLES
    state,      \* Account → {"unopened", "open", "closed"}
    balance     \* Account → balance (simplified: single currency)

vars == <<state, balance>>

States == {"unopened", "open", "closed"}

-----------------------------------------------------------------------------
Init ==
    /\ state = [a \in Accounts |-> "unopened"]
    /\ balance = [a \in Accounts |-> 0]

-----------------------------------------------------------------------------
(* Open an account *)
OpenAccount(a) ==
    /\ state[a] = "unopened"
    /\ state' = [state EXCEPT ![a] = "open"]
    /\ UNCHANGED balance

(* Close an account - must have zero balance *)
CloseAccount(a) ==
    /\ state[a] = "open"
    /\ balance[a] = 0
    /\ state' = [state EXCEPT ![a] = "closed"]
    /\ UNCHANGED balance

(* Post to account (credit or debit) *)
Post(a, amount) ==
    /\ state[a] = "open"
    /\ balance[a] + amount >= -MaxBalance
    /\ balance[a] + amount <= MaxBalance
    /\ balance' = [balance EXCEPT ![a] = @ + amount]
    /\ UNCHANGED state

(* Transfer between accounts *)
Transfer(from, to, amount) ==
    /\ from # to
    /\ state[from] = "open"
    /\ state[to] = "open"
    /\ amount > 0
    /\ balance[from] >= amount
    /\ balance[to] + amount <= MaxBalance
    /\ balance' = [balance EXCEPT ![from] = @ - amount, ![to] = @ + amount]
    /\ UNCHANGED state

Next ==
    \/ \E a \in Accounts : OpenAccount(a)
    \/ \E a \in Accounts : CloseAccount(a)
    \/ \E a \in Accounts, amt \in (-MaxBalance..MaxBalance) \ {0} : Post(a, amt)
    \/ \E from, to \in Accounts, amt \in 1..MaxBalance : Transfer(from, to, amt)

-----------------------------------------------------------------------------
(* INVARIANTS *)

(* Type invariant *)
TypeOK ==
    /\ \A a \in Accounts : state[a] \in States
    /\ \A a \in Accounts : balance[a] \in -MaxBalance..MaxBalance

(* Closed accounts have zero balance *)
ClosedHaveZeroBalance ==
    \A a \in Accounts : state[a] = "closed" => balance[a] = 0

(* State transitions are monotonic: can't go backwards *)
(* This is verified by the action definitions themselves *)

(* No posting to non-open accounts *)
(* Verified by Post action requiring state[a] = "open" *)

Spec == Init /\ [][Next]_vars

=============================================================================
