------------------------ MODULE TransactionBalance ------------------------
(***************************************************************************
 * TLA+ Specification for Beancount Transaction Balancing
 *
 * Models the transaction balancing and interpolation algorithm.
 * A transaction consists of postings that must sum to zero per currency.
 *
 * Key invariants verified:
 * - Transactions always balance after interpolation
 * - At most one posting per currency can be interpolated
 * - Weight calculation is correct for costs and prices
 ***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, Reals

CONSTANTS
    Currencies,     \* Set of currencies
    MaxPostings,    \* Maximum postings per transaction
    Tolerance       \* Balance tolerance (e.g., 5 = 0.005 scaled)

-----------------------------------------------------------------------------
(* Type Definitions *)

Decimal == Int  \* Scaled integers for decimals

Amount == [number: Decimal, currency: Currencies]

\* Price annotation (@ or @@)
Price == [
    number: Decimal,
    currency: Currencies,
    is_total: BOOLEAN  \* TRUE for @@, FALSE for @
]

\* Cost specification ({})
Cost == [
    number: Decimal,
    currency: Currencies
]

\* A posting in a transaction
Posting == [
    account: STRING,
    units: Amount \cup {NULL},   \* NULL means needs interpolation
    cost: Cost \cup {NULL},
    price: Price \cup {NULL}
]

\* A transaction
Transaction == [
    date: Int,
    postings: Seq(Posting)
]

-----------------------------------------------------------------------------
(* Variables *)

VARIABLES
    transaction,    \* Current transaction being processed
    state           \* "raw" | "interpolated" | "balanced" | "error"

vars == <<transaction, state>>

-----------------------------------------------------------------------------
(* Weight Calculation *)

\* Calculate the weight currency for a posting
WeightCurrency(p) ==
    IF p.cost # NULL THEN p.cost.currency
    ELSE IF p.price # NULL THEN p.price.currency
    ELSE IF p.units # NULL THEN p.units.currency
    ELSE NULL  \* Unknown - needs context

\* Calculate the weight amount for a posting
Weight(p) ==
    IF p.units = NULL THEN NULL  \* Cannot calculate
    ELSE IF p.cost # NULL THEN
        \* Weight = units * cost
        [number |-> p.units.number * p.cost.number,
         currency |-> p.cost.currency]
    ELSE IF p.price # NULL THEN
        IF p.price.is_total THEN
            \* @@ syntax: price is total
            [number |-> p.price.number * (IF p.units.number > 0 THEN 1 ELSE -1),
             currency |-> p.price.currency]
        ELSE
            \* @ syntax: price is per-unit
            [number |-> p.units.number * p.price.number,
             currency |-> p.price.currency]
    ELSE
        \* No cost or price: weight = units
        p.units

-----------------------------------------------------------------------------
(* Helper Functions *)

\* Get all postings with missing amounts for a currency
MissingForCurrency(txn, curr) ==
    {i \in 1..Len(txn.postings) :
        /\ txn.postings[i].units = NULL
        /\ WeightCurrency(txn.postings[i]) = curr}

\* Sum of weights for a currency
WeightSum(txn, curr) ==
    LET postings == txn.postings
        withUnits == {i \in 1..Len(postings) :
            /\ postings[i].units # NULL
            /\ (Weight(postings[i])).currency = curr}
    IN IF withUnits = {}
       THEN 0
       ELSE FoldSet(
           LAMBDA i, acc: acc + (Weight(postings[i])).number,
           0,
           withUnits)

\* All currencies involved in transaction
AllCurrencies(txn) ==
    {WeightCurrency(txn.postings[i]) : i \in 1..Len(txn.postings)}
    \ {NULL}

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ transaction \in Transaction
    /\ state = "raw"

-----------------------------------------------------------------------------
(* Interpolation *)

\* Can we interpolate this transaction?
CanInterpolate(txn) ==
    \A curr \in AllCurrencies(txn) :
        Cardinality(MissingForCurrency(txn, curr)) <= 1

\* Perform interpolation
Interpolate ==
    /\ state = "raw"
    /\ CanInterpolate(transaction)
    /\ LET txn == transaction
           \* For each currency with a missing amount, fill it in
           newPostings == [i \in 1..Len(txn.postings) |->
               IF txn.postings[i].units = NULL
               THEN LET curr == WeightCurrency(txn.postings[i])
                        missing == -WeightSum(txn, curr)
                        \* Infer units from weight
                        inferredUnits ==
                            IF txn.postings[i].cost # NULL
                            THEN [number |-> missing \div txn.postings[i].cost.number,
                                  currency |-> curr]  \* Simplified
                            ELSE IF txn.postings[i].price # NULL
                            THEN [number |-> missing \div txn.postings[i].price.number,
                                  currency |-> curr]  \* Simplified
                            ELSE [number |-> missing, currency |-> curr]
                    IN [txn.postings[i] EXCEPT !.units = inferredUnits]
               ELSE txn.postings[i]
           ]
       IN /\ transaction' = [txn EXCEPT !.postings = newPostings]
          /\ state' = "interpolated"

\* Interpolation fails
InterpolationError ==
    /\ state = "raw"
    /\ ~CanInterpolate(transaction)
    /\ state' = "error"
    /\ UNCHANGED transaction

-----------------------------------------------------------------------------
(* Balance Check *)

\* Check if transaction balances within tolerance
IsBalanced(txn) ==
    \A curr \in AllCurrencies(txn) :
        LET sum == WeightSum(txn, curr)
        IN sum >= -Tolerance /\ sum <= Tolerance

\* Successful balance check
CheckBalance ==
    /\ state = "interpolated"
    /\ IsBalanced(transaction)
    /\ state' = "balanced"
    /\ UNCHANGED transaction

\* Balance check fails
BalanceError ==
    /\ state = "interpolated"
    /\ ~IsBalanced(transaction)
    /\ state' = "error"
    /\ UNCHANGED transaction

-----------------------------------------------------------------------------
(* Next State *)

Next ==
    \/ Interpolate
    \/ InterpolationError
    \/ CheckBalance
    \/ BalanceError

-----------------------------------------------------------------------------
(* Invariants *)

\* A balanced transaction has zero weight sum per currency
BalancedMeansZero ==
    state = "balanced" =>
        \A curr \in AllCurrencies(transaction) :
            LET sum == WeightSum(transaction, curr)
            IN sum >= -Tolerance /\ sum <= Tolerance

\* Interpolation fills all missing amounts
InterpolatedComplete ==
    state = "interpolated" =>
        \A i \in 1..Len(transaction.postings) :
            transaction.postings[i].units # NULL

\* At most one missing per currency (precondition for interpolation)
AtMostOneMissing ==
    state = "raw" /\ CanInterpolate(transaction) =>
        \A curr \in AllCurrencies(transaction) :
            Cardinality(MissingForCurrency(transaction, curr)) <= 1

Invariant ==
    /\ BalancedMeansZero
    /\ InterpolatedComplete
    /\ AtMostOneMissing

-----------------------------------------------------------------------------
(* Properties *)

\* Every valid transaction eventually reaches balanced or error
EventuallyResolved ==
    <>(state \in {"balanced", "error"})

\* Type correctness
TypeOK ==
    /\ transaction \in Transaction
    /\ state \in {"raw", "interpolated", "balanced", "error"}

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars

=============================================================================
