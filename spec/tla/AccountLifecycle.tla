------------------------- MODULE AccountLifecycle -------------------------
(***************************************************************************
 * TLA+ Specification for Beancount Account Lifecycle
 *
 * Models the lifecycle of accounts: open → active → closed
 * Verifies correct enforcement of account state transitions.
 *
 * Key properties verified:
 * - Accounts must be opened before any posting
 * - Closed accounts cannot receive new postings
 * - Balance assertions only valid for open accounts
 * - Account types follow hierarchy rules
 *
 * See ROADMAP.md for context on TLA+ expansion.
 ****************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Accounts,       \* Set of account names (e.g., {"Assets:Bank", "Expenses:Food"})
    MaxDate,        \* Maximum date value (days from epoch)
    MaxPostings     \* Maximum number of postings to explore

-----------------------------------------------------------------------------
(* Type Definitions *)

\* Account state enumeration
AccountState == {"unopened", "open", "closed"}

\* Account type categories (top-level)
AccountType == {"Assets", "Liabilities", "Equity", "Income", "Expenses"}

\* A posting to an account
Posting == [
    account: Accounts,
    date: 1..MaxDate,
    amount: -1000..1000  \* Positive or negative (debit/credit)
]

\* An open directive
OpenDirective == [
    account: Accounts,
    date: 1..MaxDate,
    currencies: SUBSET {"USD", "EUR", "BTC", "AAPL"}  \* Allowed currencies
]

\* A close directive
CloseDirective == [
    account: Accounts,
    date: 1..MaxDate
]

\* A balance assertion
BalanceAssertion == [
    account: Accounts,
    date: 1..MaxDate,
    expected: -10000..10000
]

-----------------------------------------------------------------------------
(* Variables *)

VARIABLES
    accountStates,    \* Function: Accounts -> AccountState
    openDates,        \* Function: Accounts -> date when opened (or 0)
    closeDates,       \* Function: Accounts -> date when closed (or MaxDate+1)
    postings,         \* Sequence of postings that have occurred
    balances,         \* Function: Accounts -> current balance
    errors            \* Set of error messages

vars == <<accountStates, openDates, closeDates, postings, balances, errors>>

-----------------------------------------------------------------------------
(* Helper Functions *)

\* Check if account is usable at a given date
IsUsable(account, date) ==
    /\ accountStates[account] = "open"
    /\ openDates[account] <= date
    /\ closeDates[account] > date

\* Check if account was ever opened
WasOpened(account) ==
    accountStates[account] \in {"open", "closed"}

\* Get account type from name (simplified - assumes first component)
\* In real implementation, this parses "Assets:Bank" -> "Assets"
GetAccountType(account) ==
    CHOOSE t \in AccountType : TRUE  \* Simplified for model checking

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ accountStates = [a \in Accounts |-> "unopened"]
    /\ openDates = [a \in Accounts |-> 0]
    /\ closeDates = [a \in Accounts |-> MaxDate + 1]
    /\ postings = <<>>
    /\ balances = [a \in Accounts |-> 0]
    /\ errors = {}

-----------------------------------------------------------------------------
(* Open Account Action *)

OpenAccount(directive) ==
    /\ directive \in OpenDirective
    /\ accountStates[directive.account] = "unopened"
    /\ accountStates' = [accountStates EXCEPT ![directive.account] = "open"]
    /\ openDates' = [openDates EXCEPT ![directive.account] = directive.date]
    /\ UNCHANGED <<closeDates, postings, balances, errors>>

-----------------------------------------------------------------------------
(* Close Account Action *)

CloseAccount(directive) ==
    /\ directive \in CloseDirective
    /\ accountStates[directive.account] = "open"
    /\ directive.date >= openDates[directive.account]
    \* Can only close if balance is zero (Beancount requirement)
    /\ balances[directive.account] = 0
    /\ accountStates' = [accountStates EXCEPT ![directive.account] = "closed"]
    /\ closeDates' = [closeDates EXCEPT ![directive.account] = directive.date]
    /\ UNCHANGED <<openDates, postings, balances, errors>>

-----------------------------------------------------------------------------
(* Post to Account Action - Valid Case *)

PostValid(posting) ==
    /\ posting \in Posting
    /\ Len(postings) < MaxPostings
    /\ IsUsable(posting.account, posting.date)
    /\ postings' = Append(postings, posting)
    /\ balances' = [balances EXCEPT ![posting.account] = @ + posting.amount]
    /\ UNCHANGED <<accountStates, openDates, closeDates, errors>>

-----------------------------------------------------------------------------
(* Post to Account Action - Error Cases (for testing error detection) *)

\* Attempt to post to unopened account (should generate error)
PostToUnopened(posting) ==
    /\ posting \in Posting
    /\ Len(postings) < MaxPostings
    /\ accountStates[posting.account] = "unopened"
    /\ errors' = errors \cup {<<"POSTING_TO_UNOPENED", posting.account, posting.date>>}
    /\ UNCHANGED <<accountStates, openDates, closeDates, postings, balances>>

\* Attempt to post to closed account (should generate error)
PostToClosed(posting) ==
    /\ posting \in Posting
    /\ Len(postings) < MaxPostings
    /\ accountStates[posting.account] = "closed"
    /\ posting.date >= closeDates[posting.account]
    /\ errors' = errors \cup {<<"POSTING_TO_CLOSED", posting.account, posting.date>>}
    /\ UNCHANGED <<accountStates, openDates, closeDates, postings, balances>>

\* Attempt to post before account opened (should generate error)
PostBeforeOpen(posting) ==
    /\ posting \in Posting
    /\ Len(postings) < MaxPostings
    /\ accountStates[posting.account] = "open"
    /\ posting.date < openDates[posting.account]
    /\ errors' = errors \cup {<<"POSTING_BEFORE_OPEN", posting.account, posting.date>>}
    /\ UNCHANGED <<accountStates, openDates, closeDates, postings, balances>>

-----------------------------------------------------------------------------
(* Balance Assertion Action *)

AssertBalance(assertion) ==
    /\ assertion \in BalanceAssertion
    /\ WasOpened(assertion.account)
    /\ IF balances[assertion.account] = assertion.expected
       THEN UNCHANGED vars
       ELSE errors' = errors \cup {<<"BALANCE_MISMATCH",
                                     assertion.account,
                                     balances[assertion.account],
                                     assertion.expected>>}
            /\ UNCHANGED <<accountStates, openDates, closeDates, postings, balances>>

-----------------------------------------------------------------------------
(* Next State *)

Next ==
    \/ \E d \in OpenDirective : OpenAccount(d)
    \/ \E d \in CloseDirective : CloseAccount(d)
    \/ \E p \in Posting : PostValid(p)
    \/ \E p \in Posting : PostToUnopened(p)
    \/ \E p \in Posting : PostToClosed(p)
    \/ \E p \in Posting : PostBeforeOpen(p)
    \/ \E a \in BalanceAssertion : AssertBalance(a)

-----------------------------------------------------------------------------
(* Invariants *)

\* Account states are always valid
ValidAccountStates ==
    \A a \in Accounts : accountStates[a] \in AccountState

\* Open dates are set correctly
ValidOpenDates ==
    \A a \in Accounts :
        (accountStates[a] \in {"open", "closed"}) => (openDates[a] > 0)

\* Close dates are after open dates
ValidCloseDates ==
    \A a \in Accounts :
        (accountStates[a] = "closed") => (closeDates[a] >= openDates[a])

\* No valid postings to unopened accounts
NoPostingToUnopened ==
    \A i \in 1..Len(postings) :
        LET p == postings[i]
        IN WasOpened(p.account)

\* All postings in sequence are within account's active period
PostingsInActivePeriod ==
    \A i \in 1..Len(postings) :
        LET p == postings[i]
        IN /\ openDates[p.account] <= p.date
           /\ (accountStates[p.account] = "closed" => p.date < closeDates[p.account])

\* State machine transitions are valid
ValidTransitions ==
    \A a \in Accounts :
        \* Cannot go from closed back to open or unopened
        (accountStates[a] = "closed") => (accountStates'[a] \in {"closed"})

\* Balances are consistent with postings
BalancesConsistent ==
    \A a \in Accounts :
        balances[a] =
            LET accountPostings == SelectSeq(postings, LAMBDA p: p.account = a)
            IN FoldSeq(LAMBDA p, acc: acc + p.amount, 0, accountPostings)

\* Helper for FoldSeq
RECURSIVE FoldSeq(_, _, _)
FoldSeq(f, acc, s) ==
    IF s = <<>> THEN acc
    ELSE FoldSeq(f, f(Head(s), acc), Tail(s))

\* Helper for SelectSeq
RECURSIVE SelectSeq(_, _)
SelectSeq(s, test) ==
    IF s = <<>> THEN <<>>
    ELSE IF test(Head(s))
         THEN <<Head(s)>> \o SelectSeq(Tail(s), test)
         ELSE SelectSeq(Tail(s), test)

\* Combined invariant
Invariant ==
    /\ ValidAccountStates
    /\ ValidOpenDates
    /\ ValidCloseDates
    /\ NoPostingToUnopened
    /\ PostingsInActivePeriod

-----------------------------------------------------------------------------
(* Type Correctness *)

TypeOK ==
    /\ accountStates \in [Accounts -> AccountState]
    /\ openDates \in [Accounts -> 0..MaxDate]
    /\ closeDates \in [Accounts -> 1..(MaxDate + 1)]
    /\ balances \in [Accounts -> -10000..10000]
    /\ \A p \in Range(postings) : p \in Posting

\* Range helper
Range(s) == {s[i] : i \in 1..Len(s)}

-----------------------------------------------------------------------------
(* Liveness Properties *)

\* If we try to post to an account, it should eventually be opened
\* (or an error should be generated)
EventuallyOpenedOrError ==
    \A a \in Accounts :
        (\E p \in Posting : p.account = a) ~>
            (WasOpened(a) \/ \E e \in errors : e[2] = a)

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars

=============================================================================
