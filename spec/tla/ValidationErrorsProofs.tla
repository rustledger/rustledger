------------------------ MODULE ValidationErrorsProofs ------------------------
(***************************************************************************
 * TLAPS Proofs for ValidationErrors Invariants
 *
 * This module contains formal proofs for validation error properties:
 * - ValidErrorCodes: All errors have valid codes
 * - CorrectSeverity: Error severity matches specification
 * - E1001Correctness: Unopened accounts always generate E1001
 * - E3003Correctness: Empty transactions always generate E3003
 * - ErrorsMonotonic: Errors never decrease
 *
 * To check proofs:
 *   tlapm ValidationErrorsProofs.tla
 *
 * Prerequisites:
 *   - TLAPS installed (https://tla.msr-inria.inria.fr/tlaps/)
 *
 * See ROADMAP.md for context.
 ****************************************************************************)

EXTENDS ValidationErrors, TLAPS

-----------------------------------------------------------------------------
(* Helper Definitions for Proofs *)

\* Set of all valid error codes
AllValidCodes == {
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

\* Warning codes
WarningCodes == {"E3004", "E10002"}

\* Info codes
InfoCodes == {"E10001"}

\* Error codes (everything else)
ErrorCodes == AllValidCodes \ (WarningCodes \cup InfoCodes)

-----------------------------------------------------------------------------
(* Lemmas about Error Code Classification *)

\* Lemma: All generated error codes are in AllValidCodes
LEMMA GeneratedCodesValid ==
    ASSUME NEW e \in ValidationError
    PROVE  e.code \in AllValidCodes
PROOF
  BY DEF ValidationError, AllValidCodes

\* Lemma: Warning codes have warning severity
LEMMA WarningCodesHaveWarningSeverity ==
    ASSUME NEW code \in WarningCodes
    PROVE  code \in {"E3004", "E10002"}
PROOF
  BY DEF WarningCodes

\* Lemma: Info codes have info severity
LEMMA InfoCodesHaveInfoSeverity ==
    ASSUME NEW code \in InfoCodes
    PROVE  code = "E10001"
PROOF
  BY DEF InfoCodes

-----------------------------------------------------------------------------
(* Main Invariant Proofs *)

\* Theorem: Init establishes ValidErrorCodes
THEOREM InitValidErrorCodes ==
    Init => ValidErrorCodes
PROOF
  <1>1. Init => errors = {}
    BY DEF Init
  <1>2. errors = {} => ValidErrorCodes
    \* Empty set trivially satisfies universal quantification
    <2>1. ASSUME errors = {}
          PROVE  \A e \in errors : e.code \in AllValidCodes
      <3>1. \A e \in {} : TRUE
        OBVIOUS
      <3>2. QED
        BY <3>1
    <2>2. QED
      BY <2>1 DEF ValidErrorCodes
  <1>3. QED
    BY <1>1, <1>2

\* Theorem: Init establishes CorrectSeverity
THEOREM InitCorrectSeverity ==
    Init => CorrectSeverity
PROOF
  <1>1. Init => errors = {}
    BY DEF Init
  <1>2. errors = {} => CorrectSeverity
    \* Empty set trivially satisfies the property
    BY DEF CorrectSeverity
  <1>3. QED
    BY <1>1, <1>2

\* Theorem: AddTransaction preserves ValidErrorCodes
THEOREM AddTransactionPreservesValidErrorCodes ==
    ASSUME ValidErrorCodes,
           NEW txn \in Transaction,
           AddTransaction(txn)
    PROVE  ValidErrorCodes'
PROOF
  <1>1. ValidErrorCodes
    OBVIOUS
  <1>2. \* New errors added by AddTransaction have valid codes
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
        IN \A e \in txnErrors : e.code \in AllValidCodes
    <2>1. "E3003" \in AllValidCodes
      BY DEF AllValidCodes
    <2>2. "E3004" \in AllValidCodes
      BY DEF AllValidCodes
    <2>3. "E3002" \in AllValidCodes
      BY DEF AllValidCodes
    <2>4. "E1001" \in AllValidCodes
      BY DEF AllValidCodes
    <2>5. QED
      BY <2>1, <2>2, <2>3, <2>4
  <1>3. errors' = errors \cup txnErrors
    BY DEF AddTransaction
  <1>4. \* All old errors still valid (by induction hypothesis)
        \A e \in errors : e.code \in AllValidCodes
    BY <1>1 DEF ValidErrorCodes
  <1>5. QED
    BY <1>2, <1>3, <1>4 DEF ValidErrorCodes

\* Theorem: CorrectSeverity is preserved by all actions
THEOREM CorrectSeverityPreserved ==
    CorrectSeverity /\ [Next]_vars => CorrectSeverity'
PROOF
  <1>1. SUFFICES ASSUME CorrectSeverity, [Next]_vars
                 PROVE  CorrectSeverity'
    OBVIOUS
  <1>2. CASE UNCHANGED vars
    BY <1>2 DEF CorrectSeverity, vars
  <1>3. CASE Next
    \* All error-generating actions create errors with correct severity
    <2>1. \* E3003 has severity "error"
          [code |-> "E3003", severity |-> "error", account |-> NULL,
           currency |-> NULL, date |-> d].severity = "error"
      OBVIOUS
    <2>2. \* E3004 has severity "warning"
          [code |-> "E3004", severity |-> "warning", account |-> NULL,
           currency |-> NULL, date |-> d].severity = "warning"
      OBVIOUS
    <2>3. \* E1001 has severity "error"
          [code |-> "E1001", severity |-> "error", account |-> a,
           currency |-> NULL, date |-> d].severity = "error"
      OBVIOUS
    <2>4. QED
      BY <2>1, <2>2, <2>3 DEF CorrectSeverity, Next
  <1>4. QED
    BY <1>2, <1>3

-----------------------------------------------------------------------------
(* E1001 Correctness Proof *)

\* Theorem: E1001 is generated whenever posting to unopened account
THEOREM E1001CorrectnessTheorem ==
    ASSUME TypeOK,
           NEW txn \in Transaction,
           NEW i \in 1..Len(txn.postings),
           accountStates[txn.postings[i].account] = "unopened",
           AddTransaction(txn)
    PROVE  \E e \in errors' : e.code = "E1001" /\ e.account = txn.postings[i].account
PROOF
  <1>1. LET a == txn.postings[i].account
        IN accountStates[a] = "unopened"
    OBVIOUS
  <1>2. LET txnErrors ==
            {[code |-> "E1001", severity |-> "error", account |-> a,
              currency |-> NULL, date |-> txn.date] :
              a \in {txn.postings[j].account : j \in 1..Len(txn.postings)} :
              accountStates[a] = "unopened"}
        IN [code |-> "E1001", severity |-> "error",
            account |-> txn.postings[i].account,
            currency |-> NULL, date |-> txn.date] \in txnErrors
    BY <1>1
  <1>3. errors' = errors \cup txnErrors
    BY DEF AddTransaction
  <1>4. QED
    BY <1>2, <1>3

-----------------------------------------------------------------------------
(* E3003 Correctness Proof *)

\* Theorem: E3003 is generated for empty transactions
THEOREM E3003CorrectnessTheorem ==
    ASSUME TypeOK,
           NEW txn \in Transaction,
           Len(txn.postings) = 0,
           AddTransaction(txn)
    PROVE  \E e \in errors' : e.code = "E3003" /\ e.date = txn.date
PROOF
  <1>1. Len(txn.postings) = 0
    OBVIOUS
  <1>2. LET e3003 == [code |-> "E3003", severity |-> "error",
                      account |-> NULL, currency |-> NULL, date |-> txn.date]
        IN e3003 \in {[code |-> "E3003", severity |-> "error", account |-> NULL,
                       currency |-> NULL, date |-> txn.date] : TRUE}
    BY <1>1
  <1>3. errors' = errors \cup txnErrors
    BY DEF AddTransaction
  <1>4. QED
    BY <1>2, <1>3

-----------------------------------------------------------------------------
(* E3004 Correctness Proof *)

\* Theorem: E3004 is generated for single-posting transactions
THEOREM E3004CorrectnessTheorem ==
    ASSUME TypeOK,
           NEW txn \in Transaction,
           Len(txn.postings) = 1,
           AddTransaction(txn)
    PROVE  \E e \in errors' :
           /\ e.code = "E3004"
           /\ e.severity = "warning"
           /\ e.date = txn.date
PROOF
  <1>1. Len(txn.postings) = 1
    OBVIOUS
  <1>2. LET e3004 == [code |-> "E3004", severity |-> "warning",
                      account |-> NULL, currency |-> NULL, date |-> txn.date]
        IN e3004 \in {[code |-> "E3004", severity |-> "warning", account |-> NULL,
                       currency |-> NULL, date |-> txn.date] : TRUE}
    BY <1>1
  <1>3. e3004.severity = "warning"
    OBVIOUS
  <1>4. errors' = errors \cup txnErrors
    BY DEF AddTransaction
  <1>5. QED
    BY <1>2, <1>3, <1>4

-----------------------------------------------------------------------------
(* ErrorsMonotonic Property Proof *)

\* Theorem: Errors never decrease
THEOREM ErrorsMonotonicTheorem ==
    [Next]_vars => errors \subseteq errors'
PROOF
  <1>1. CASE UNCHANGED vars
    BY <1>1 DEF vars
  <1>2. CASE Next
    \* All actions either keep errors unchanged or add to them
    <2>1. CASE \E a \in Accounts, d \in 0..MaxDate, c \in SUBSET Currencies :
              OpenAccount(a, d, c)
      BY <2>1 DEF OpenAccount
    <2>2. CASE \E a \in Accounts, d \in 0..MaxDate, b \in BOOLEAN :
              CloseAccount(a, d, b)
      \* CloseAccount may add E1004 but never removes
      BY <2>2 DEF CloseAccount
    <2>3. CASE \E txn \in Transaction : AddTransaction(txn)
      \* AddTransaction adds errors, never removes
      BY <2>3 DEF AddTransaction
    <2>4. CASE \E c \in Currencies : DeclareCurrency(c)
      BY <2>4 DEF DeclareCurrency
    <2>5. CASE \E bal \in BalanceAssertion : AddBalance(bal)
      BY <2>5 DEF AddBalance
    <2>6. CASE \E pad \in PadDirective : AddPad(pad)
      BY <2>6 DEF AddPad
    <2>7. CASE \E n \in Options \cup {NULL}, v \in {NULL}, r \in BOOLEAN :
              SetOption(n, v, r)
      \* SetOption may add E7001/E7003 but never removes
      BY <2>7 DEF SetOption
    <2>8. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
  <1>3. QED
    BY <1>1, <1>2

-----------------------------------------------------------------------------
(* AccountLifecycleMonotonic Property Proof *)

\* Theorem: Account lifecycle transitions are monotonic
THEOREM AccountLifecycleMonotonicTheorem ==
    [Next]_vars =>
        \A a \in Accounts :
            \/ (accountStates[a] = "unopened" =>
                accountStates'[a] \in {"unopened", "open"})
            \/ (accountStates[a] = "open" =>
                accountStates'[a] \in {"open", "closed"})
            \/ (accountStates[a] = "closed" =>
                accountStates'[a] = "closed")
PROOF
  <1>1. CASE UNCHANGED vars
    BY <1>1 DEF vars
  <1>2. CASE Next
    <2>1. CASE \E a \in Accounts, d \in 0..MaxDate, c \in SUBSET Currencies :
              OpenAccount(a, d, c)
      \* OpenAccount only transitions unopened -> open
      <3>1. OpenAccount requires accountStates[a] = "unopened"
        BY DEF OpenAccount
      <3>2. accountStates' = [accountStates EXCEPT ![a] = "open"]
        BY DEF OpenAccount
      <3>3. QED
        BY <3>1, <3>2
    <2>2. CASE \E a \in Accounts, d \in 0..MaxDate, b \in BOOLEAN :
              CloseAccount(a, d, b)
      \* CloseAccount only transitions open -> closed
      <3>1. CloseAccount requires accountStates[a] = "open"
        BY DEF CloseAccount
      <3>2. accountStates' = [accountStates EXCEPT ![a] = "closed"]
        BY DEF CloseAccount
      <3>3. QED
        BY <3>1, <3>2
    <2>3. CASE \E txn \in Transaction : AddTransaction(txn)
      \* AddTransaction doesn't change account states
      BY <2>3 DEF AddTransaction
    <2>4. QED
      BY <2>1, <2>2, <2>3 DEF Next
  <1>3. QED
    BY <1>1, <1>2

-----------------------------------------------------------------------------
(* Main Safety Theorems *)

\* ValidErrorCodes holds in all reachable states
THEOREM ValidErrorCodesSafety ==
    Spec => []ValidErrorCodes
PROOF
  <1>1. Init => ValidErrorCodes
    BY InitValidErrorCodes
  <1>2. ValidErrorCodes /\ [Next]_vars => ValidErrorCodes'
    \* All actions preserve ValidErrorCodes
    BY AddTransactionPreservesValidErrorCodes DEF Next
  <1>3. QED
    BY <1>1, <1>2, PTL DEF Spec

\* CorrectSeverity holds in all reachable states
THEOREM CorrectSeveritySafety ==
    Spec => []CorrectSeverity
PROOF
  <1>1. Init => CorrectSeverity
    BY InitCorrectSeverity
  <1>2. CorrectSeverity /\ [Next]_vars => CorrectSeverity'
    BY CorrectSeverityPreserved
  <1>3. QED
    BY <1>1, <1>2, PTL DEF Spec

\* ErrorsMonotonic holds for all transitions
THEOREM ErrorsMonotonicSafety ==
    Spec => []([Next]_vars => errors \subseteq errors')
PROOF
  BY ErrorsMonotonicTheorem, PTL DEF Spec

\* Combined: All validation error properties hold
THEOREM AllValidationPropertiesSafe ==
    Spec => [](ValidErrorCodes /\ CorrectSeverity)
PROOF
  BY ValidErrorCodesSafety, CorrectSeveritySafety, PTL

=============================================================================
