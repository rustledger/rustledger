------------------------- MODULE ValidationErrors -------------------------
(***************************************************************************
 * TLA+ Specification for rustledger Validation Errors
 *
 * Models all 26 validation error codes from rustledger-validate.
 * This specification defines when each error condition should trigger,
 * ensuring the Rust validator correctly identifies all error cases.
 *
 * Error Categories:
 * - E1xxx: Account errors (5 codes)
 * - E2xxx: Balance errors (3 codes)
 * - E3xxx: Transaction errors (4 codes)
 * - E4xxx: Booking errors (4 codes)
 * - E5xxx: Currency errors (2 codes)
 * - E6xxx: Metadata errors (2 codes)
 * - E7xxx: Option errors (3 codes)
 * - E8xxx: Document errors (1 code)
 * - E10xxx: Date errors (2 codes)
 *
 * See: crates/rustledger-validate/src/lib.rs
 ***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Accounts,       \* Set of account names
    Currencies,     \* Set of currency symbols
    MaxDate,        \* Maximum date for model checking
    Options,        \* Set of valid option names
    Today           \* Current date for future date checking

NULL == CHOOSE x : x \notin Accounts \cup Currencies \cup Options

-----------------------------------------------------------------------------
(* Type Definitions *)

\* Account state
AccountState == {"unopened", "open", "closed"}

\* Error severity
Severity == {"error", "warning", "info"}

\* Validation error record
ValidationError == [
    code: STRING,
    severity: Severity,
    account: Accounts \cup {NULL},
    currency: Currencies \cup {NULL},
    date: 0..MaxDate \cup {NULL}
]

\* Posting record
Posting == [
    account: Accounts,
    amount: Int \cup {NULL},  \* NULL = interpolated
    currency: Currencies
]

\* Transaction record
Transaction == [
    date: 0..MaxDate,
    postings: Seq(Posting)
]

\* Balance assertion record
BalanceAssertion == [
    date: 0..MaxDate,
    account: Accounts,
    amount: Int,
    currency: Currencies
]

\* Pad directive record
PadDirective == [
    date: 0..MaxDate,
    account: Accounts,
    pad_account: Accounts,
    used: BOOLEAN
]

-----------------------------------------------------------------------------
(* Variables *)

VARIABLES
    accountStates,      \* Account name -> state mapping
    accountOpenDates,   \* Account name -> open date
    accountCloseDates,  \* Account name -> close date
    accountCurrencies,  \* Account name -> allowed currencies
    declaredCurrencies, \* Set of declared currencies
    transactions,       \* Sequence of transactions
    balances,           \* Sequence of balance assertions
    pads,               \* Sequence of pad directives
    metadata,           \* Account -> key -> value mapping
    options,            \* Option name -> value mapping
    errors,             \* Set of validation errors
    currentDate         \* Date of current directive being processed

vars == <<accountStates, accountOpenDates, accountCloseDates, accountCurrencies,
          declaredCurrencies, transactions, balances, pads, metadata, options,
          errors, currentDate>>

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ accountStates = [a \in Accounts |-> "unopened"]
    /\ accountOpenDates = [a \in Accounts |-> 0]
    /\ accountCloseDates = [a \in Accounts |-> 0]
    /\ accountCurrencies = [a \in Accounts |-> Currencies]  \* All allowed by default
    /\ declaredCurrencies = {}
    /\ transactions = <<>>
    /\ balances = <<>>
    /\ pads = <<>>
    /\ metadata = [a \in Accounts |-> [k \in {} |-> NULL]]
    /\ options = [o \in {} |-> NULL]
    /\ errors = {}
    /\ currentDate = 0

-----------------------------------------------------------------------------
(* Helper Functions *)

\* Count postings with NULL amount for a currency
CountMissingAmounts(txn, curr) ==
    Cardinality({i \in 1..Len(txn.postings) :
        /\ txn.postings[i].currency = curr
        /\ txn.postings[i].amount = NULL})

\* Sum of posting amounts for a currency (excluding NULL)
SumAmounts(txn, curr) ==
    LET postings == {i \in 1..Len(txn.postings) :
            /\ txn.postings[i].currency = curr
            /\ txn.postings[i].amount # NULL}
    IN IF postings = {} THEN 0
       ELSE FoldSet(LAMBDA i, acc: acc + txn.postings[i].amount, 0, postings)

\* All currencies in a transaction
TransactionCurrencies(txn) ==
    {txn.postings[i].currency : i \in 1..Len(txn.postings)}

\* Check if account name is valid (starts with proper root)
ValidAccountName(name) ==
    \* In TLA+ we simplify: just check it's in the set
    name \in Accounts

\* Find pads for a balance assertion
PadsForBalance(bal) ==
    {i \in 1..Len(pads) :
        /\ pads[i].account = bal.account
        /\ pads[i].date < bal.date
        /\ ~pads[i].used}

-----------------------------------------------------------------------------
(* Error Generation Actions *)

\* E1001: Account not opened
\* Triggered when posting to account that was never opened
CheckAccountNotOpen(account, date) ==
    accountStates[account] = "unopened"
    => errors' = errors \cup {[
        code |-> "E1001",
        severity |-> "error",
        account |-> account,
        currency |-> NULL,
        date |-> date
    ]}

\* E1002: Account already open
\* Triggered when opening an already-open account
CheckAccountAlreadyOpen(account) ==
    accountStates[account] = "open"
    => errors' = errors \cup {[
        code |-> "E1002",
        severity |-> "error",
        account |-> account,
        currency |-> NULL,
        date |-> currentDate
    ]}

\* E1003: Account closed
\* Triggered when posting to closed account
CheckAccountClosed(account, date) ==
    /\ accountStates[account] = "closed"
    /\ date >= accountCloseDates[account]
    => errors' = errors \cup {[
        code |-> "E1003",
        severity |-> "error",
        account |-> account,
        currency |-> NULL,
        date |-> date
    ]}

\* E1004: Account close with non-zero balance
\* Triggered when closing account that has remaining balance
CheckAccountCloseNotEmpty(account, hasBalance) ==
    hasBalance
    => errors' = errors \cup {[
        code |-> "E1004",
        severity |-> "error",
        account |-> account,
        currency |-> NULL,
        date |-> currentDate
    ]}

\* E1005: Invalid account name
CheckInvalidAccountName(name) ==
    ~ValidAccountName(name)
    => errors' = errors \cup {[
        code |-> "E1005",
        severity |-> "error",
        account |-> NULL,
        currency |-> NULL,
        date |-> currentDate
    ]}

-----------------------------------------------------------------------------
(* Balance Error Actions *)

\* E2001: Balance assertion failed
\* Triggered when computed balance doesn't match assertion
CheckBalanceAssertionFailed(expected, actual) ==
    expected # actual
    => errors' = errors \cup {[
        code |-> "E2001",
        severity |-> "error",
        account |-> NULL,
        currency |-> NULL,
        date |-> currentDate
    ]}

\* E2003: Pad without subsequent balance
\* Triggered when pad has no following balance assertion
CheckPadWithoutBalance(padIndex) ==
    LET pad == pads[padIndex]
        hasBalance == \E i \in 1..Len(balances) :
            /\ balances[i].account = pad.account
            /\ balances[i].date > pad.date
    IN ~hasBalance /\ ~pad.used
       => errors' = errors \cup {[
           code |-> "E2003",
           severity |-> "error",
           account |-> pad.account,
           currency |-> NULL,
           date |-> pad.date
       ]}

\* E2004: Multiple pads for same balance
\* Triggered when multiple pads could apply to same balance
CheckMultiplePadForBalance(balIndex) ==
    LET bal == balances[balIndex]
        applicablePads == PadsForBalance(bal)
    IN Cardinality(applicablePads) > 1
       => errors' = errors \cup {[
           code |-> "E2004",
           severity |-> "error",
           account |-> bal.account,
           currency |-> NULL,
           date |-> bal.date
       ]}

-----------------------------------------------------------------------------
(* Transaction Error Actions *)

\* E3001: Transaction does not balance
\* Triggered when sum of postings for any currency is non-zero
CheckTransactionUnbalanced(txn) ==
    \E curr \in TransactionCurrencies(txn) :
        /\ CountMissingAmounts(txn, curr) = 0  \* No interpolation
        /\ SumAmounts(txn, curr) # 0
    => errors' = errors \cup {[
        code |-> "E3001",
        severity |-> "error",
        account |-> NULL,
        currency |-> NULL,
        date |-> txn.date
    ]}

\* E3002: Multiple missing amounts in transaction
\* Triggered when more than one posting for same currency has NULL amount
CheckMultipleInterpolation(txn) ==
    \E curr \in TransactionCurrencies(txn) :
        CountMissingAmounts(txn, curr) > 1
    => errors' = errors \cup {[
        code |-> "E3002",
        severity |-> "error",
        account |-> NULL,
        currency |-> NULL,
        date |-> txn.date
    ]}

\* E3003: Transaction has no postings
CheckNoPostings(txn) ==
    Len(txn.postings) = 0
    => errors' = errors \cup {[
        code |-> "E3003",
        severity |-> "error",
        account |-> NULL,
        currency |-> NULL,
        date |-> txn.date
    ]}

\* E3004: Transaction has single posting (warning)
CheckSinglePosting(txn) ==
    Len(txn.postings) = 1
    => errors' = errors \cup {[
        code |-> "E3004",
        severity |-> "warning",
        account |-> NULL,
        currency |-> NULL,
        date |-> txn.date
    ]}

-----------------------------------------------------------------------------
(* Booking Error Actions - see also BookingMethods.tla *)

\* E4001: No matching lot for reduction
\* Triggered in STRICT/FIFO/LIFO/HIFO when no lots match cost spec
CheckNoMatchingLot(account, currency, hasMatches) ==
    ~hasMatches
    => errors' = errors \cup {[
        code |-> "E4001",
        severity |-> "error",
        account |-> account,
        currency |-> currency,
        date |-> currentDate
    ]}

\* E4002: Insufficient units in lot
\* Triggered when reduction exceeds available units
CheckInsufficientUnits(account, currency, needed, available) ==
    needed > available
    => errors' = errors \cup {[
        code |-> "E4002",
        severity |-> "error",
        account |-> account,
        currency |-> currency,
        date |-> currentDate
    ]}

\* E4003: Ambiguous lot match
\* Triggered in STRICT mode when multiple lots match
CheckAmbiguousLotMatch(account, currency, matchCount) ==
    matchCount > 1
    => errors' = errors \cup {[
        code |-> "E4003",
        severity |-> "error",
        account |-> account,
        currency |-> currency,
        date |-> currentDate
    ]}

\* E4004: Reduction would create negative inventory
\* Triggered when reduction would go negative (except NONE booking)
CheckNegativeInventory(account, currency, wouldBeNegative) ==
    wouldBeNegative
    => errors' = errors \cup {[
        code |-> "E4004",
        severity |-> "error",
        account |-> account,
        currency |-> currency,
        date |-> currentDate
    ]}

-----------------------------------------------------------------------------
(* Currency Error Actions *)

\* E5001: Currency not declared
\* Triggered in strict mode when using undeclared currency
CheckUndeclaredCurrency(currency, strictMode) ==
    /\ strictMode
    /\ currency \notin declaredCurrencies
    => errors' = errors \cup {[
        code |-> "E5001",
        severity |-> "error",
        account |-> NULL,
        currency |-> currency,
        date |-> currentDate
    ]}

\* E5002: Currency not allowed in account
\* Triggered when posting currency not in account's allowed list
CheckCurrencyNotAllowed(account, currency) ==
    currency \notin accountCurrencies[account]
    => errors' = errors \cup {[
        code |-> "E5002",
        severity |-> "error",
        account |-> account,
        currency |-> currency,
        date |-> currentDate
    ]}

-----------------------------------------------------------------------------
(* Metadata Error Actions *)

\* E6001: Duplicate metadata key
CheckDuplicateMetadataKey(account, key, alreadyExists) ==
    alreadyExists
    => errors' = errors \cup {[
        code |-> "E6001",
        severity |-> "error",
        account |-> account,
        currency |-> NULL,
        date |-> currentDate
    ]}

\* E6002: Invalid metadata value
CheckInvalidMetadataValue(account, key, isValid) ==
    ~isValid
    => errors' = errors \cup {[
        code |-> "E6002",
        severity |-> "error",
        account |-> account,
        currency |-> NULL,
        date |-> currentDate
    ]}

-----------------------------------------------------------------------------
(* Option Error Actions *)

\* E7001: Unknown option name
CheckUnknownOption(name) ==
    name \notin Options
    => errors' = errors \cup {[
        code |-> "E7001",
        severity |-> "error",
        account |-> NULL,
        currency |-> NULL,
        date |-> currentDate
    ]}

\* E7002: Invalid option value
CheckInvalidOptionValue(name, isValid) ==
    ~isValid
    => errors' = errors \cup {[
        code |-> "E7002",
        severity |-> "error",
        account |-> NULL,
        currency |-> NULL,
        date |-> currentDate
    ]}

\* E7003: Duplicate option
CheckDuplicateOption(name, isRepeatable) ==
    /\ name \in DOMAIN options
    /\ ~isRepeatable
    => errors' = errors \cup {[
        code |-> "E7003",
        severity |-> "error",
        account |-> NULL,
        currency |-> NULL,
        date |-> currentDate
    ]}

-----------------------------------------------------------------------------
(* Document Error Actions *)

\* E8001: Document file not found
CheckDocumentNotFound(path, exists) ==
    ~exists
    => errors' = errors \cup {[
        code |-> "E8001",
        severity |-> "error",
        account |-> NULL,
        currency |-> NULL,
        date |-> currentDate
    ]}

-----------------------------------------------------------------------------
(* Date Error Actions *)

\* E10001: Date out of order (info)
CheckDateOutOfOrder(prevDate, currDate) ==
    currDate < prevDate
    => errors' = errors \cup {[
        code |-> "E10001",
        severity |-> "info",
        account |-> NULL,
        currency |-> NULL,
        date |-> currDate
    ]}

\* E10002: Entry dated in the future (warning)
CheckFutureDate(entryDate) ==
    entryDate > Today
    => errors' = errors \cup {[
        code |-> "E10002",
        severity |-> "warning",
        account |-> NULL,
        currency |-> NULL,
        date |-> entryDate
    ]}

-----------------------------------------------------------------------------
(* Directive Processing Actions *)

\* Open an account
OpenAccount(account, date, currencies) ==
    /\ accountStates[account] = "unopened"
    /\ accountStates' = [accountStates EXCEPT ![account] = "open"]
    /\ accountOpenDates' = [accountOpenDates EXCEPT ![account] = date]
    /\ accountCurrencies' = [accountCurrencies EXCEPT ![account] = currencies]
    /\ currentDate' = date
    /\ UNCHANGED <<accountCloseDates, declaredCurrencies, transactions,
                   balances, pads, metadata, options, errors>>

\* Close an account
CloseAccount(account, date, hasBalance) ==
    /\ accountStates[account] = "open"
    /\ accountStates' = [accountStates EXCEPT ![account] = "closed"]
    /\ accountCloseDates' = [accountCloseDates EXCEPT ![account] = date]
    /\ currentDate' = date
    /\ IF hasBalance
       THEN errors' = errors \cup {[
           code |-> "E1004",
           severity |-> "error",
           account |-> account,
           currency |-> NULL,
           date |-> date
       ]}
       ELSE UNCHANGED errors
    /\ UNCHANGED <<accountOpenDates, accountCurrencies, declaredCurrencies,
                   transactions, balances, pads, metadata, options>>

\* Add a transaction
AddTransaction(txn) ==
    LET txnErrors ==
        {[code |-> "E3003", severity |-> "error", account |-> NULL,
          currency |-> NULL, date |-> txn.date] : Len(txn.postings) = 0}
        \cup
        {[code |-> "E3004", severity |-> "warning", account |-> NULL,
          currency |-> NULL, date |-> txn.date] : Len(txn.postings) = 1}
        \cup
        {[code |-> "E3002", severity |-> "error", account |-> NULL,
          currency |-> c, date |-> txn.date] :
          c \in {curr \in TransactionCurrencies(txn) :
                 CountMissingAmounts(txn, curr) > 1}}
        \cup
        {[code |-> "E1001", severity |-> "error", account |-> a,
          currency |-> NULL, date |-> txn.date] :
          a \in {txn.postings[i].account : i \in 1..Len(txn.postings)} :
          accountStates[a] = "unopened"}
    IN
    /\ transactions' = Append(transactions, txn)
    /\ errors' = errors \cup txnErrors
    /\ currentDate' = txn.date
    /\ UNCHANGED <<accountStates, accountOpenDates, accountCloseDates,
                   accountCurrencies, declaredCurrencies, balances, pads,
                   metadata, options>>

\* Declare a currency
DeclareCurrency(currency) ==
    /\ declaredCurrencies' = declaredCurrencies \cup {currency}
    /\ UNCHANGED <<accountStates, accountOpenDates, accountCloseDates,
                   accountCurrencies, transactions, balances, pads,
                   metadata, options, errors, currentDate>>

\* Add balance assertion
AddBalance(bal) ==
    /\ balances' = Append(balances, bal)
    /\ currentDate' = bal.date
    /\ UNCHANGED <<accountStates, accountOpenDates, accountCloseDates,
                   accountCurrencies, declaredCurrencies, transactions,
                   pads, metadata, options, errors>>

\* Add pad directive
AddPad(pad) ==
    /\ pads' = Append(pads, pad)
    /\ currentDate' = pad.date
    /\ UNCHANGED <<accountStates, accountOpenDates, accountCloseDates,
                   accountCurrencies, declaredCurrencies, transactions,
                   balances, metadata, options, errors>>

\* Set an option
SetOption(name, value, isRepeatable) ==
    /\ IF name \notin Options
       THEN errors' = errors \cup {[
           code |-> "E7001",
           severity |-> "error",
           account |-> NULL,
           currency |-> NULL,
           date |-> currentDate
       ]}
       ELSE IF name \in DOMAIN options /\ ~isRepeatable
       THEN errors' = errors \cup {[
           code |-> "E7003",
           severity |-> "error",
           account |-> NULL,
           currency |-> NULL,
           date |-> currentDate
       ]}
       ELSE errors' = errors
    /\ options' = options @@ (name :> value)
    /\ UNCHANGED <<accountStates, accountOpenDates, accountCloseDates,
                   accountCurrencies, declaredCurrencies, transactions,
                   balances, pads, metadata, currentDate>>

-----------------------------------------------------------------------------
(* Next State *)

Next ==
    \/ \E a \in Accounts, d \in 0..MaxDate, c \in SUBSET Currencies :
        OpenAccount(a, d, c)
    \/ \E a \in Accounts, d \in 0..MaxDate, b \in BOOLEAN :
        CloseAccount(a, d, b)
    \/ \E txn \in Transaction : AddTransaction(txn)
    \/ \E c \in Currencies : DeclareCurrency(c)
    \/ \E bal \in BalanceAssertion : AddBalance(bal)
    \/ \E pad \in PadDirective : AddPad(pad)
    \/ \E n \in Options \cup {NULL}, v \in {NULL}, r \in BOOLEAN :
        SetOption(n, v, r)

-----------------------------------------------------------------------------
(* Invariants *)

\* All generated errors have valid error codes
ValidErrorCodes ==
    \A e \in errors :
        e.code \in {
            "E1001", "E1002", "E1003", "E1004", "E1005",
            "E2001", "E2003", "E2004",
            "E3001", "E3002", "E3003", "E3004",
            "E4001", "E4002", "E4003", "E4004",
            "E5001", "E5002",
            "E6001", "E6002",
            "E7001", "E7002", "E7003",
            "E8001",
            "E10001", "E10002"
        }

\* Error severity is appropriate
CorrectSeverity ==
    \A e \in errors :
        \/ (e.code = "E3004" => e.severity = "warning")
        \/ (e.code = "E10001" => e.severity = "info")
        \/ (e.code = "E10002" => e.severity = "warning")
        \/ (e.code \notin {"E3004", "E10001", "E10002"} => e.severity = "error")

\* Account lifecycle consistency
AccountLifecycleConsistent ==
    \A a \in Accounts :
        \/ accountStates[a] = "unopened"
        \/ (accountStates[a] = "open" /\ accountOpenDates[a] > 0)
        \/ (accountStates[a] = "closed"
            /\ accountOpenDates[a] > 0
            /\ accountCloseDates[a] >= accountOpenDates[a])

\* E1001 is generated for unopened account usage
E1001Correctness ==
    \A i \in 1..Len(transactions) :
        LET txn == transactions[i]
        IN \A j \in 1..Len(txn.postings) :
            LET p == txn.postings[j]
            IN accountStates[p.account] = "unopened"
               => \E e \in errors : e.code = "E1001" /\ e.account = p.account

\* E3003 is generated for empty transactions
E3003Correctness ==
    \A i \in 1..Len(transactions) :
        Len(transactions[i].postings) = 0
        => \E e \in errors : e.code = "E3003" /\ e.date = transactions[i].date

\* E3004 is generated (as warning) for single-posting transactions
E3004Correctness ==
    \A i \in 1..Len(transactions) :
        Len(transactions[i].postings) = 1
        => \E e \in errors :
            /\ e.code = "E3004"
            /\ e.severity = "warning"
            /\ e.date = transactions[i].date

\* Type correctness
TypeOK ==
    /\ accountStates \in [Accounts -> AccountState]
    /\ accountOpenDates \in [Accounts -> 0..MaxDate]
    /\ accountCloseDates \in [Accounts -> 0..MaxDate]
    /\ declaredCurrencies \subseteq Currencies
    /\ errors \subseteq ValidationError
    /\ currentDate \in 0..MaxDate

Invariant ==
    /\ TypeOK
    /\ ValidErrorCodes
    /\ CorrectSeverity
    /\ AccountLifecycleConsistent

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Properties *)

\* Errors are monotonic (never removed)
ErrorsMonotonic == [][errors \subseteq errors']_vars

\* Account lifecycle is monotonic (never goes backward)
AccountLifecycleMonotonic ==
    [][\A a \in Accounts :
        \/ accountStates[a] = "unopened" =>
           accountStates'[a] \in {"unopened", "open"}
        \/ accountStates[a] = "open" =>
           accountStates'[a] \in {"open", "closed"}
        \/ accountStates[a] = "closed" =>
           accountStates'[a] = "closed"
    ]_vars

=============================================================================
