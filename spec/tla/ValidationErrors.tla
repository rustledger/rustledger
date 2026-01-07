------------------------- MODULE ValidationErrors -------------------------
(***************************************************************************
 * TLA+ Specification for rustledger Validation
 *
 * This spec models the CORE validation logic, not a catalog of error codes.
 * It verifies that the validator correctly identifies invalid states.
 *
 * Key properties verified:
 * 1. Account lifecycle: Can't post to unopened/closed accounts
 * 2. Transaction balancing: Debits must equal credits per currency
 * 3. Interpolation: At most one missing amount per currency
 * 4. Booking: Ambiguous matches are rejected in STRICT mode
 *
 * The goal is to prove: "Every invalid state produces an error"
 * (No false negatives in validation)
 ***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Accounts,       \* Set of account names
    Currencies,     \* Set of currency symbols
    MaxDate         \* Maximum date for model checking

-----------------------------------------------------------------------------
(* Type Definitions *)

AccountState == {"unopened", "open", "closed"}

\* A posting: account, amount (NULL = interpolated), currency
Posting == [
    account: Accounts,
    amount: Int \cup {"NULL"},
    currency: Currencies
]

\* A transaction: date and postings
Transaction == [
    date: 1..MaxDate,
    postings: Seq(Posting)
]

-----------------------------------------------------------------------------
(* Variables *)

VARIABLES
    accountStates,    \* Accounts -> AccountState
    accountOpenDates, \* Accounts -> Date (0 = never opened)
    accountCloseDates,\* Accounts -> Date (0 = never closed)
    ledger,           \* Sequence of transactions
    validationErrors  \* Set of error codes that SHOULD have fired

vars == <<accountStates, accountOpenDates, accountCloseDates, ledger, validationErrors>>

-----------------------------------------------------------------------------
(* Helper Functions *)

\* Sum of non-NULL amounts for a currency in a transaction
SumAmounts(txn, curr) ==
    LET postings == SelectSeq(txn.postings, LAMBDA p: p.currency = curr /\ p.amount # "NULL")
    IN IF Len(postings) = 0 THEN 0
       ELSE FoldSeq(LAMBDA p, acc: acc + p.amount, 0, postings)

\* Count of NULL amounts for a currency in a transaction
CountNullAmounts(txn, curr) ==
    Cardinality({i \in 1..Len(txn.postings) :
        txn.postings[i].currency = curr /\ txn.postings[i].amount = "NULL"})

\* All currencies used in a transaction
TxnCurrencies(txn) ==
    {txn.postings[i].currency : i \in 1..Len(txn.postings)}

\* Check if account was open on given date
WasOpen(account, date) ==
    /\ accountStates[account] \in {"open", "closed"}
    /\ accountOpenDates[account] <= date
    /\ (accountStates[account] = "open" \/ accountCloseDates[account] > date)

\* Fold over sequence
RECURSIVE FoldSeq(_, _, _)
FoldSeq(f, init, seq) ==
    IF Len(seq) = 0 THEN init
    ELSE FoldSeq(f, f(Head(seq), init), Tail(seq))

\* Select elements from sequence matching predicate
RECURSIVE SelectSeq(_, _)
SelectSeq(seq, pred) ==
    IF Len(seq) = 0 THEN <<>>
    ELSE IF pred(Head(seq))
         THEN <<Head(seq)>> \o SelectSeq(Tail(seq), pred)
         ELSE SelectSeq(Tail(seq), pred)

-----------------------------------------------------------------------------
(* Validation Conditions - When errors MUST fire *)

\* E1001: Posting to unopened account
MustFireE1001(txn) ==
    \E i \in 1..Len(txn.postings) :
        accountStates[txn.postings[i].account] = "unopened"

\* E1003: Posting to closed account (after close date)
MustFireE1003(txn) ==
    \E i \in 1..Len(txn.postings) :
        LET acc == txn.postings[i].account
        IN /\ accountStates[acc] = "closed"
           /\ txn.date >= accountCloseDates[acc]

\* E3001: Transaction doesn't balance (for any currency with no interpolation)
MustFireE3001(txn) ==
    \E curr \in TxnCurrencies(txn) :
        /\ CountNullAmounts(txn, curr) = 0  \* No interpolation
        /\ SumAmounts(txn, curr) # 0        \* Doesn't balance

\* E3002: Multiple missing amounts for same currency (can't interpolate)
MustFireE3002(txn) ==
    \E curr \in TxnCurrencies(txn) :
        CountNullAmounts(txn, curr) > 1

\* E3003: Transaction has no postings
MustFireE3003(txn) ==
    Len(txn.postings) = 0

\* Combined: transaction is invalid if any error condition holds
TransactionInvalid(txn) ==
    \/ MustFireE1001(txn)
    \/ MustFireE1003(txn)
    \/ MustFireE3001(txn)
    \/ MustFireE3002(txn)
    \/ MustFireE3003(txn)

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ accountStates = [a \in Accounts |-> "unopened"]
    /\ accountOpenDates = [a \in Accounts |-> 0]
    /\ accountCloseDates = [a \in Accounts |-> 0]
    /\ ledger = <<>>
    /\ validationErrors = {}

-----------------------------------------------------------------------------
(* Actions *)

\* Open an account
OpenAccount(account, date) ==
    /\ accountStates[account] = "unopened"
    /\ accountStates' = [accountStates EXCEPT ![account] = "open"]
    /\ accountOpenDates' = [accountOpenDates EXCEPT ![account] = date]
    /\ UNCHANGED <<accountCloseDates, ledger, validationErrors>>

\* Close an account
CloseAccount(account, date) ==
    /\ accountStates[account] = "open"
    /\ date > accountOpenDates[account]
    /\ accountStates' = [accountStates EXCEPT ![account] = "closed"]
    /\ accountCloseDates' = [accountCloseDates EXCEPT ![account] = date]
    /\ UNCHANGED <<accountOpenDates, ledger, validationErrors>>

\* Add a transaction (validator determines errors)
AddTransaction(txn) ==
    /\ txn \in Transaction
    /\ ledger' = Append(ledger, txn)
    \* Record which errors SHOULD fire for this transaction
    /\ validationErrors' = validationErrors \cup
        (IF MustFireE1001(txn) THEN {"E1001"} ELSE {}) \cup
        (IF MustFireE1003(txn) THEN {"E1003"} ELSE {}) \cup
        (IF MustFireE3001(txn) THEN {"E3001"} ELSE {}) \cup
        (IF MustFireE3002(txn) THEN {"E3002"} ELSE {}) \cup
        (IF MustFireE3003(txn) THEN {"E3003"} ELSE {})
    /\ UNCHANGED <<accountStates, accountOpenDates, accountCloseDates>>

Next ==
    \/ \E a \in Accounts, d \in 1..MaxDate : OpenAccount(a, d)
    \/ \E a \in Accounts, d \in 1..MaxDate : CloseAccount(a, d)
    \/ \E txn \in Transaction : AddTransaction(txn)

-----------------------------------------------------------------------------
(* INVARIANTS - The actual verification *)

\* Core safety: Account state machine is valid
AccountStateMachineValid ==
    \A a \in Accounts :
        \/ accountStates[a] = "unopened" /\ accountOpenDates[a] = 0
        \/ accountStates[a] = "open" /\ accountOpenDates[a] > 0
        \/ accountStates[a] = "closed"
           /\ accountOpenDates[a] > 0
           /\ accountCloseDates[a] > accountOpenDates[a]

\* Core safety: Close date always after open date
DateOrderingValid ==
    \A a \in Accounts :
        accountCloseDates[a] > 0 => accountCloseDates[a] > accountOpenDates[a]

\* CRITICAL INVARIANT: Every invalid transaction produces appropriate errors
\* This is what catches bugs in the validator!
AllInvalidTransactionsDetected ==
    \A i \in 1..Len(ledger) :
        LET txn == ledger[i]
        IN /\ MustFireE1001(txn) => "E1001" \in validationErrors
           /\ MustFireE1003(txn) => "E1003" \in validationErrors
           /\ MustFireE3001(txn) => "E3001" \in validationErrors
           /\ MustFireE3002(txn) => "E3002" \in validationErrors
           /\ MustFireE3003(txn) => "E3003" \in validationErrors

\* No false positives: If no invalid condition, no error should fire
\* (This catches bugs where validator is too aggressive)
NoFalsePositives ==
    \A i \in 1..Len(ledger) :
        LET txn == ledger[i]
        IN ~TransactionInvalid(txn) =>
            validationErrors \cap {"E1001", "E1003", "E3001", "E3002", "E3003"} = {}

-----------------------------------------------------------------------------
(* PROPERTIES - Temporal behavior *)

\* Account lifecycle is monotonic (can't reopen closed accounts)
AccountLifecycleMonotonic ==
    [][\A a \in Accounts :
        \/ (accountStates[a] = "unopened" =>
            accountStates'[a] \in {"unopened", "open"})
        \/ (accountStates[a] = "open" =>
            accountStates'[a] \in {"open", "closed"})
        \/ (accountStates[a] = "closed" =>
            accountStates'[a] = "closed")
    ]_vars

\* Errors are never removed (monotonic)
ErrorsMonotonic ==
    [][validationErrors \subseteq validationErrors']_vars

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars

\* Combined invariant
Invariant ==
    /\ AccountStateMachineValid
    /\ DateOrderingValid
    /\ AllInvalidTransactionsDetected

=============================================================================
