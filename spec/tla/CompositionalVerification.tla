--------------------- MODULE CompositionalVerification ---------------------
(***************************************************************************
 * Compositional Verification for rustledger
 *
 * This module composes multiple TLA+ specifications to verify cross-cutting
 * properties that span multiple components:
 *
 * Components composed:
 * - Inventory: lot management
 * - Booking: reduction algorithms
 * - Validation: error detection
 * - Account Lifecycle: open/close semantics
 *
 * Cross-cutting properties verified:
 * - Booking reductions respect account lifecycle
 * - Validation errors are raised for closed accounts
 * - Inventory consistency across all operations
 ***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Accounts,       \* Set of account names
    Currencies,     \* Set of currencies
    MaxUnits,       \* Maximum units
    MaxDate         \* Maximum date (days)

-----------------------------------------------------------------------------
(* TYPE DEFINITIONS *)

AccountState == {"unopened", "open", "closed"}

Lot == [
    units: 1..MaxUnits,
    currency: Currencies,
    cost: 1..1000,
    date: 1..MaxDate
]

Posting == [
    account: Accounts,
    units: (-MaxUnits)..MaxUnits,
    currency: Currencies,
    date: 1..MaxDate
]

ValidationError == [
    code: {"E1001", "E1002", "E1003", "E3001", "E3002", "E4001"},
    account: Accounts \cup {""},
    message: STRING
]

BookingMethod == {"FIFO", "LIFO", "HIFO", "STRICT", "AVERAGE", "NONE"}

-----------------------------------------------------------------------------
(* VARIABLES - Combined state from all components *)

VARIABLES
    \* Account Lifecycle state
    accountStates,      \* Function: Accounts -> AccountState
    accountOpenDates,   \* Function: Accounts -> Date
    accountCloseDates,  \* Function: Accounts -> Date

    \* Inventory state (per account)
    inventories,        \* Function: Accounts -> Set(Lot)
    bookingMethods,     \* Function: Accounts -> BookingMethod

    \* Validation state
    errors,             \* Set of ValidationError

    \* Transaction state
    currentDate,        \* Current transaction date
    postings            \* Current transaction postings

accountVars == <<accountStates, accountOpenDates, accountCloseDates>>
inventoryVars == <<inventories, bookingMethods>>
validationVars == <<errors>>
transactionVars == <<currentDate, postings>>

vars == <<accountVars, inventoryVars, validationVars, transactionVars>>

-----------------------------------------------------------------------------
(* HELPER FUNCTIONS *)

\* Check if account is open on a given date
IsOpen(account, date) ==
    /\ accountStates[account] \in {"open", "closed"}
    /\ accountOpenDates[account] <= date
    /\ (accountStates[account] = "open" \/ date < accountCloseDates[account])

\* Total units for an account's inventory
TotalUnits(account, curr) ==
    LET inv == inventories[account]
        matching == {l \in inv : l.currency = curr}
    IN IF matching = {} THEN 0
       ELSE LET seq == SetToSeq(matching)
            IN FoldSeq(LAMBDA l, acc: acc + l.units, 0, seq)

\* Set to sequence conversion
RECURSIVE SetToSeq(_)
SetToSeq(S) ==
    IF S = {} THEN <<>>
    ELSE LET x == CHOOSE x \in S : TRUE
         IN <<x>> \o SetToSeq(S \ {x})

\* Fold over sequence
RECURSIVE FoldSeq(_, _, _)
FoldSeq(f, acc, s) ==
    IF s = <<>> THEN acc
    ELSE FoldSeq(f, f(Head(s), acc), Tail(s))

\* Oldest lot in a set
Oldest(lotSet) ==
    CHOOSE l \in lotSet : \A other \in lotSet : l.date <= other.date

-----------------------------------------------------------------------------
(* INITIAL STATE *)

Init ==
    /\ accountStates = [a \in Accounts |-> "unopened"]
    /\ accountOpenDates = [a \in Accounts |-> 0]
    /\ accountCloseDates = [a \in Accounts |-> 0]
    /\ inventories = [a \in Accounts |-> {}]
    /\ bookingMethods = [a \in Accounts |-> "FIFO"]
    /\ errors = {}
    /\ currentDate = 1
    /\ postings = <<>>

-----------------------------------------------------------------------------
(* ACCOUNT LIFECYCLE ACTIONS *)

OpenAccount(account, date) ==
    /\ accountStates[account] = "unopened"
    /\ date >= currentDate
    /\ accountStates' = [accountStates EXCEPT ![account] = "open"]
    /\ accountOpenDates' = [accountOpenDates EXCEPT ![account] = date]
    /\ UNCHANGED <<accountCloseDates, inventoryVars, validationVars, transactionVars>>

CloseAccount(account, date) ==
    /\ accountStates[account] = "open"
    /\ date >= currentDate
    /\ date > accountOpenDates[account]
    \* Check inventory is empty (or NONE booking allows negative)
    /\ \/ inventories[account] = {}
       \/ bookingMethods[account] = "NONE"
    /\ accountStates' = [accountStates EXCEPT ![account] = "closed"]
    /\ accountCloseDates' = [accountCloseDates EXCEPT ![account] = date]
    /\ UNCHANGED <<accountOpenDates, inventoryVars, validationVars, transactionVars>>

SetBookingMethod(account, method) ==
    /\ accountStates[account] = "open"
    /\ method \in BookingMethod
    /\ bookingMethods' = [bookingMethods EXCEPT ![account] = method]
    /\ UNCHANGED <<accountVars, inventories, validationVars, transactionVars>>

-----------------------------------------------------------------------------
(* INVENTORY ACTIONS WITH VALIDATION *)

\* Add to inventory with lifecycle check
AddToInventory(account, lot) ==
    /\ lot \in Lot
    /\ IF ~IsOpen(account, lot.date)
       THEN \* Validation error: posting to non-open account
            /\ errors' = errors \cup {[
                   code |-> "E1001",
                   account |-> account,
                   message |-> "Account not open"]}
            /\ UNCHANGED <<accountVars, inventoryVars, transactionVars>>
       ELSE \* Valid: add to inventory
            /\ inventories' = [inventories EXCEPT
                   ![account] = @ \cup {lot}]
            /\ UNCHANGED <<accountVars, bookingMethods, validationVars, transactionVars>>

\* Reduce from inventory with lifecycle and booking check
ReduceFromInventory(account, currency, units, date) ==
    /\ units > 0
    /\ IF ~IsOpen(account, date)
       THEN \* Validation error: posting to non-open account
            /\ errors' = errors \cup {[
                   code |-> "E1001",
                   account |-> account,
                   message |-> "Account not open"]}
            /\ UNCHANGED <<accountVars, inventoryVars, transactionVars>>
       ELSE
            LET inv == inventories[account]
                matching == {l \in inv : l.currency = currency}
                total == TotalUnits(account, currency)
                method == bookingMethods[account]
            IN IF matching = {} /\ method # "NONE"
               THEN \* Validation error: no matching lots
                    /\ errors' = errors \cup {[
                           code |-> "E4001",
                           account |-> account,
                           message |-> "No matching lots"]}
                    /\ UNCHANGED <<accountVars, inventoryVars, transactionVars>>
               ELSE IF total < units /\ method # "NONE"
               THEN \* Validation error: insufficient units
                    /\ errors' = errors \cup {[
                           code |-> "E4001",
                           account |-> account,
                           message |-> "Insufficient units"]}
                    /\ UNCHANGED <<accountVars, inventoryVars, transactionVars>>
               ELSE \* Valid: perform reduction based on booking method
                    LET oldest == IF matching # {} THEN Oldest(matching) ELSE [units |-> 0]
                    IN /\ IF method = "NONE"
                          THEN inventories' = inventories  \* NONE doesn't track lots
                          ELSE IF oldest.units <= units
                          THEN inventories' = [inventories EXCEPT
                                   ![account] = @ \ {oldest}]
                          ELSE inventories' = [inventories EXCEPT
                                   ![account] = (@ \ {oldest}) \cup
                                       {[oldest EXCEPT !.units = @ - units]}]
                       /\ UNCHANGED <<accountVars, bookingMethods, validationVars, transactionVars>>

-----------------------------------------------------------------------------
(* TRANSACTION ACTIONS *)

\* Process a complete transaction
ProcessTransaction(date, posts) ==
    /\ date >= currentDate
    /\ posts \in Seq(Posting)
    /\ Len(posts) >= 2  \* Transactions need at least 2 postings
    \* Check all accounts are open
    /\ \A i \in 1..Len(posts) :
        LET p == posts[i]
        IN IF ~IsOpen(p.account, date)
           THEN errors' = errors \cup {[
                    code |-> "E1001",
                    account |-> p.account,
                    message |-> "Account not open"]}
           ELSE UNCHANGED errors
    /\ currentDate' = date
    /\ postings' = posts
    /\ UNCHANGED <<accountVars, inventoryVars>>

\* Advance date
AdvanceDate ==
    /\ currentDate < MaxDate
    /\ currentDate' = currentDate + 1
    /\ UNCHANGED <<accountVars, inventoryVars, validationVars, postings>>

-----------------------------------------------------------------------------
(* NEXT STATE *)

Next ==
    \/ \E a \in Accounts, d \in 1..MaxDate : OpenAccount(a, d)
    \/ \E a \in Accounts, d \in 1..MaxDate : CloseAccount(a, d)
    \/ \E a \in Accounts, m \in BookingMethod : SetBookingMethod(a, m)
    \/ \E a \in Accounts, l \in Lot : AddToInventory(a, l)
    \/ \E a \in Accounts, c \in Currencies, u \in 1..MaxUnits, d \in 1..MaxDate :
        ReduceFromInventory(a, c, u, d)
    \/ AdvanceDate

-----------------------------------------------------------------------------
(* COMPOSITIONAL INVARIANTS *)

\* Invariant 1: Lifecycle-Inventory Consistency
\* Closed accounts with non-NONE booking must have empty inventory
LifecycleInventoryConsistency ==
    \A a \in Accounts :
        (accountStates[a] = "closed" /\ bookingMethods[a] # "NONE")
        => inventories[a] = {}

\* Invariant 2: No Orphan Inventory
\* Inventory can only exist for opened accounts
NoOrphanInventory ==
    \A a \in Accounts :
        inventories[a] # {} => accountStates[a] \in {"open", "closed"}

\* Invariant 3: Booking Method Requires Open Account
\* Non-default booking methods only for open accounts
BookingMethodConsistency ==
    \A a \in Accounts :
        bookingMethods[a] # "FIFO" => accountStates[a] = "open"

\* Invariant 4: Error Consistency
\* E1001 errors only for non-open accounts
ErrorConsistency ==
    \A e \in errors :
        e.code = "E1001" =>
            e.account \in Accounts /\ ~IsOpen(e.account, currentDate)

\* Invariant 5: Date Ordering
\* Close date always after open date
DateOrdering ==
    \A a \in Accounts :
        accountStates[a] = "closed" =>
            accountOpenDates[a] < accountCloseDates[a]

\* Combined Compositional Invariant
CompositionalInvariant ==
    /\ LifecycleInventoryConsistency
    /\ NoOrphanInventory
    /\ BookingMethodConsistency
    /\ DateOrdering

-----------------------------------------------------------------------------
(* CROSS-CUTTING PROPERTIES *)

\* Property: All operations respect account lifecycle
AllOperationsRespectLifecycle ==
    \A a \in Accounts :
        (inventories[a] # {} \/ bookingMethods[a] # "FIFO")
        => accountStates[a] = "open"

\* Property: Validation catches all lifecycle violations
ValidationCatchesLifecycleViolations ==
    \A a \in Accounts :
        (~IsOpen(a, currentDate) /\ inventories[a] # {})
        => \E e \in errors : e.account = a /\ e.code = "E1001"

\* Property: Booking methods are used correctly
BookingMethodsUsedCorrectly ==
    \A a \in Accounts :
        inventories[a] # {} =>
            \/ bookingMethods[a] \in BookingMethod
            \/ \E e \in errors : e.account = a

-----------------------------------------------------------------------------
(* SPECIFICATION *)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ \A a \in Accounts : accountStates[a] \in AccountState
    /\ \A a \in Accounts : accountOpenDates[a] \in 0..MaxDate
    /\ \A a \in Accounts : accountCloseDates[a] \in 0..MaxDate
    /\ \A a \in Accounts : inventories[a] \subseteq Lot
    /\ \A a \in Accounts : bookingMethods[a] \in BookingMethod
    /\ currentDate \in 1..MaxDate

=============================================================================
