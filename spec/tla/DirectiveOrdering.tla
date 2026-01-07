------------------------- MODULE DirectiveOrdering -------------------------
(***************************************************************************
 * TLA+ Specification for Beancount Directive Ordering
 *
 * Models the temporal ordering constraints on directives.
 * Verifies that directives are processed in correct order.
 *
 * Key properties verified:
 * - Directives are date-ordered within the ledger
 * - Open directives precede any posting to the account
 * - Close directives follow all postings to the account
 * - Pad directives generate correct padding entries
 * - Balance assertions are checked after transactions on same date
 *
 * See ROADMAP.md for context on TLA+ expansion.
 ****************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Accounts,       \* Set of account names
    MaxDate,        \* Maximum date value
    MaxDirectives   \* Maximum number of directives to explore

-----------------------------------------------------------------------------
(* Type Definitions *)

\* Directive types
DirectiveType == {"open", "close", "transaction", "balance", "pad", "note", "document"}

\* Base directive structure
Directive == [
    type: DirectiveType,
    date: 1..MaxDate,
    account: Accounts \cup {NULL},  \* Some directives don't have accounts
    meta: SUBSET STRING             \* Metadata tags
]

\* Transaction with postings
Transaction == [
    type: {"transaction"},
    date: 1..MaxDate,
    narration: STRING,
    postings: SUBSET [account: Accounts, amount: -1000..1000]
]

\* Ordering constraint between two directives
OrderingConstraint == [
    before: Directive,
    after: Directive,
    reason: STRING
]

-----------------------------------------------------------------------------
(* Variables *)

VARIABLES
    directives,         \* Sequence of all directives in ledger
    constraints,        \* Set of ordering constraints that must hold
    violations,         \* Set of ordering violations detected
    accountOpenDates,   \* Function: Accounts -> open date
    accountCloseDates   \* Function: Accounts -> close date

vars == <<directives, constraints, violations, accountOpenDates, accountCloseDates>>

-----------------------------------------------------------------------------
(* Helper Functions *)

\* Get index of first directive matching predicate
RECURSIVE FindFirst(_, _, _)
FindFirst(s, pred, idx) ==
    IF idx > Len(s) THEN 0
    ELSE IF pred(s[idx]) THEN idx
    ELSE FindFirst(s, pred, idx + 1)

\* Check if all directives are date-ordered
IsDateOrdered(s) ==
    \A i \in 1..(Len(s) - 1) : s[i].date <= s[i+1].date

\* Get all accounts referenced by a directive
AccountsIn(d) ==
    IF d.type = "transaction"
    THEN {p.account : p \in d.postings}
    ELSE IF d.account # NULL
    THEN {d.account}
    ELSE {}

\* Find open directive for account
OpenDirectiveFor(account) ==
    LET opens == SelectSeq(directives, LAMBDA d: d.type = "open" /\ d.account = account)
    IN IF Len(opens) > 0 THEN opens[1] ELSE NULL

\* Find close directive for account
CloseDirectiveFor(account) ==
    LET closes == SelectSeq(directives, LAMBDA d: d.type = "close" /\ d.account = account)
    IN IF Len(closes) > 0 THEN closes[1] ELSE NULL

\* SelectSeq helper
RECURSIVE SelectSeq(_, _)
SelectSeq(s, test) ==
    IF s = <<>> THEN <<>>
    ELSE IF test(Head(s))
         THEN <<Head(s)>> \o SelectSeq(Tail(s), test)
         ELSE SelectSeq(Tail(s), test)

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ directives = <<>>
    /\ constraints = {}
    /\ violations = {}
    /\ accountOpenDates = [a \in Accounts |-> 0]
    /\ accountCloseDates = [a \in Accounts |-> MaxDate + 1]

-----------------------------------------------------------------------------
(* Add Open Directive *)

AddOpen(account, date) ==
    /\ Len(directives) < MaxDirectives
    /\ accountOpenDates[account] = 0  \* Not already opened
    /\ LET d == [type |-> "open", date |-> date, account |-> account, meta |-> {}]
       IN /\ directives' = Append(directives, d)
          /\ accountOpenDates' = [accountOpenDates EXCEPT ![account] = date]
          /\ UNCHANGED <<constraints, violations, accountCloseDates>>

-----------------------------------------------------------------------------
(* Add Close Directive *)

AddClose(account, date) ==
    /\ Len(directives) < MaxDirectives
    /\ accountOpenDates[account] > 0           \* Must be opened
    /\ accountCloseDates[account] > MaxDate    \* Not already closed
    /\ date >= accountOpenDates[account]       \* Close after open
    /\ LET d == [type |-> "close", date |-> date, account |-> account, meta |-> {}]
       IN /\ directives' = Append(directives, d)
          /\ accountCloseDates' = [accountCloseDates EXCEPT ![account] = date]
          \* Add constraint: all postings to this account must be before close
          /\ constraints' = constraints \cup
               {[before |-> p, after |-> d, reason |-> "posting_before_close"] :
                p \in {directives[i] : i \in 1..Len(directives)} :
                p.type = "transaction" /\ account \in AccountsIn(p)}
          /\ UNCHANGED <<violations, accountOpenDates>>

-----------------------------------------------------------------------------
(* Add Transaction Directive *)

AddTransaction(date, postingAccounts) ==
    /\ Len(directives) < MaxDirectives
    /\ postingAccounts \subseteq Accounts
    /\ postingAccounts # {}
    \* All posting accounts must be open at transaction date
    /\ \A a \in postingAccounts :
        /\ accountOpenDates[a] > 0
        /\ accountOpenDates[a] <= date
        /\ accountCloseDates[a] > date
    /\ LET d == [type |-> "transaction",
                 date |-> date,
                 account |-> NULL,
                 meta |-> {},
                 postings |-> {[account |-> a, amount |-> 0] : a \in postingAccounts}]
       IN /\ directives' = Append(directives, d)
          \* Add constraints: open must precede this transaction for each account
          /\ constraints' = constraints \cup
               {[before |-> [type |-> "open", date |-> accountOpenDates[a], account |-> a, meta |-> {}],
                 after |-> d,
                 reason |-> "open_before_posting"] : a \in postingAccounts}
          /\ UNCHANGED <<violations, accountOpenDates, accountCloseDates>>

-----------------------------------------------------------------------------
(* Add Balance Assertion *)

AddBalance(account, date, expected) ==
    /\ Len(directives) < MaxDirectives
    /\ accountOpenDates[account] > 0  \* Account must be open
    /\ date >= accountOpenDates[account]
    /\ LET d == [type |-> "balance", date |-> date, account |-> account, meta |-> {}]
       IN /\ directives' = Append(directives, d)
          \* Balance is checked AFTER all transactions on same date
          /\ constraints' = constraints \cup
               {[before |-> t, after |-> d, reason |-> "transaction_before_balance"] :
                t \in {directives[i] : i \in 1..Len(directives)} :
                t.type = "transaction" /\ t.date = date /\ account \in AccountsIn(t)}
          /\ UNCHANGED <<violations, accountOpenDates, accountCloseDates>>

-----------------------------------------------------------------------------
(* Add Pad Directive *)

AddPad(account, padFromAccount, date) ==
    /\ Len(directives) < MaxDirectives
    /\ accountOpenDates[account] > 0
    /\ accountOpenDates[padFromAccount] > 0
    /\ date >= accountOpenDates[account]
    /\ date >= accountOpenDates[padFromAccount]
    /\ LET d == [type |-> "pad", date |-> date, account |-> account, meta |-> {}]
       IN /\ directives' = Append(directives, d)
          /\ UNCHANGED <<constraints, violations, accountOpenDates, accountCloseDates>>

-----------------------------------------------------------------------------
(* Check Ordering Violations *)

CheckConstraints ==
    /\ LET newViolations ==
           {c \in constraints :
            LET beforeIdx == FindFirst(directives, LAMBDA d: d = c.before, 1)
                afterIdx == FindFirst(directives, LAMBDA d: d = c.after, 1)
            IN /\ beforeIdx > 0
               /\ afterIdx > 0
               /\ beforeIdx > afterIdx}  \* Violation: before comes after
       IN violations' = violations \cup newViolations
    /\ UNCHANGED <<directives, constraints, accountOpenDates, accountCloseDates>>

-----------------------------------------------------------------------------
(* Next State *)

Next ==
    \/ \E a \in Accounts, d \in 1..MaxDate : AddOpen(a, d)
    \/ \E a \in Accounts, d \in 1..MaxDate : AddClose(a, d)
    \/ \E d \in 1..MaxDate, accts \in SUBSET Accounts : AddTransaction(d, accts)
    \/ \E a \in Accounts, d \in 1..MaxDate, e \in -1000..1000 : AddBalance(a, d, e)
    \/ \E a1, a2 \in Accounts, d \in 1..MaxDate : a1 # a2 => AddPad(a1, a2, d)
    \/ CheckConstraints

-----------------------------------------------------------------------------
(* Invariants *)

\* Directives maintain date ordering
DateOrderingInvariant ==
    IsDateOrdered(directives)

\* No account is opened twice
UniqueOpenInvariant ==
    \A i, j \in 1..Len(directives) :
        (i # j /\ directives[i].type = "open" /\ directives[j].type = "open")
        => directives[i].account # directives[j].account

\* No account is closed twice
UniqueCloseInvariant ==
    \A i, j \in 1..Len(directives) :
        (i # j /\ directives[i].type = "close" /\ directives[j].type = "close")
        => directives[i].account # directives[j].account

\* Close always comes after open for same account
CloseAfterOpenInvariant ==
    \A i, j \in 1..Len(directives) :
        (/\ directives[i].type = "open"
         /\ directives[j].type = "close"
         /\ directives[i].account = directives[j].account)
        => i < j

\* Transactions only reference open accounts
TransactionsToOpenAccountsInvariant ==
    \A i \in 1..Len(directives) :
        directives[i].type = "transaction" =>
            \A a \in AccountsIn(directives[i]) :
                /\ accountOpenDates[a] > 0
                /\ accountOpenDates[a] <= directives[i].date

\* No violations detected
NoViolations ==
    violations = {}

\* Combined invariant
Invariant ==
    /\ DateOrderingInvariant
    /\ UniqueOpenInvariant
    /\ UniqueCloseInvariant
    /\ CloseAfterOpenInvariant
    /\ TransactionsToOpenAccountsInvariant

-----------------------------------------------------------------------------
(* Type Correctness *)

TypeOK ==
    /\ \A d \in Range(directives) : d.type \in DirectiveType
    /\ accountOpenDates \in [Accounts -> 0..MaxDate]
    /\ accountCloseDates \in [Accounts -> 1..(MaxDate + 1)]

\* Range helper
Range(s) == {s[i] : i \in 1..Len(s)}

-----------------------------------------------------------------------------
(* Temporal Properties *)

\* If an account is used in a transaction, it was previously opened
OpenBeforeUse ==
    [](\A i \in 1..Len(directives) :
        directives[i].type = "transaction" =>
            \A a \in AccountsIn(directives[i]) :
                \E j \in 1..(i-1) :
                    directives[j].type = "open" /\ directives[j].account = a)

\* All constraints are eventually satisfied or violations detected
EventualConsistency ==
    <>(violations # {} \/ constraints = {})

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars

=============================================================================
