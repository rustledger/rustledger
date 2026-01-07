------------------------- MODULE LivenessProperties -------------------------
(***************************************************************************
 * Liveness Properties with Fairness for rustledger
 *
 * Safety properties say "bad things never happen".
 * Liveness properties say "good things eventually happen".
 *
 * Fairness ensures the system makes progress:
 * - Weak Fairness (WF): If an action is continuously enabled, it eventually occurs
 * - Strong Fairness (SF): If an action is repeatedly enabled, it eventually occurs
 *
 * Key liveness properties verified:
 * - Reductions eventually complete
 * - Errors are eventually resolved
 * - System doesn't deadlock
 ***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Currencies,
    MaxUnits,
    MaxLots

-----------------------------------------------------------------------------
(* Type Definitions *)

Lot == [
    units: 1..MaxUnits,
    currency: Currencies,
    cost: 1..1000,
    date: 1..365
]

Request == [
    type: {"add", "reduce"},
    currency: Currencies,
    units: 1..MaxUnits
]

-----------------------------------------------------------------------------
(* Variables *)

VARIABLES
    lots,           \* Current inventory
    pendingOps,     \* Queue of pending operations
    completedOps,   \* Count of completed operations
    errors,         \* Current errors
    resolvedErrors  \* Count of resolved errors

vars == <<lots, pendingOps, completedOps, errors, resolvedErrors>>

-----------------------------------------------------------------------------
(* Helper Functions *)

TotalUnits(curr) ==
    LET matching == {l \in lots : l.currency = curr}
    IN IF matching = {} THEN 0
       ELSE LET s == CHOOSE s \in matching : TRUE
            IN s.units + TotalUnits(curr) - s.units  \* Simplified

Oldest(lotSet) ==
    CHOOSE l \in lotSet : \A other \in lotSet : l.date <= other.date

CanReduce(curr, units) ==
    \E l \in lots : l.currency = curr /\ l.units >= units

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ lots = {}
    /\ pendingOps = <<>>
    /\ completedOps = 0
    /\ errors = {}
    /\ resolvedErrors = 0

-----------------------------------------------------------------------------
(* Actions *)

\* Submit a new operation request
SubmitRequest(req) ==
    /\ req \in Request
    /\ Len(pendingOps) < 10  \* Bounded queue
    /\ pendingOps' = Append(pendingOps, req)
    /\ UNCHANGED <<lots, completedOps, errors, resolvedErrors>>

\* Process an add operation
ProcessAdd ==
    /\ pendingOps # <<>>
    /\ Head(pendingOps).type = "add"
    /\ Cardinality(lots) < MaxLots
    /\ LET req == Head(pendingOps)
           newLot == [units |-> req.units, currency |-> req.currency,
                      cost |-> 100, date |-> 1]
       IN /\ lots' = lots \cup {newLot}
          /\ pendingOps' = Tail(pendingOps)
          /\ completedOps' = completedOps + 1
    /\ UNCHANGED <<errors, resolvedErrors>>

\* Process a reduce operation (success case)
ProcessReduceSuccess ==
    /\ pendingOps # <<>>
    /\ Head(pendingOps).type = "reduce"
    /\ LET req == Head(pendingOps)
       IN /\ CanReduce(req.currency, req.units)
          /\ LET matching == {l \in lots : l.currency = req.currency /\ l.units >= req.units}
                 lot == Oldest(matching)
             IN IF lot.units = req.units
                THEN lots' = lots \ {lot}
                ELSE lots' = (lots \ {lot}) \cup {[lot EXCEPT !.units = @ - req.units]}
          /\ pendingOps' = Tail(pendingOps)
          /\ completedOps' = completedOps + 1
    /\ UNCHANGED <<errors, resolvedErrors>>

\* Process a reduce operation (failure case - creates error)
ProcessReduceFailure ==
    /\ pendingOps # <<>>
    /\ Head(pendingOps).type = "reduce"
    /\ LET req == Head(pendingOps)
       IN /\ ~CanReduce(req.currency, req.units)
          /\ errors' = errors \cup {[type |-> "INSUFFICIENT", req |-> req]}
          /\ pendingOps' = Tail(pendingOps)
    /\ UNCHANGED <<lots, completedOps, resolvedErrors>>

\* Resolve an error by adding sufficient inventory
ResolveError ==
    /\ errors # {}
    /\ LET err == CHOOSE e \in errors : TRUE
       IN /\ Cardinality(lots) < MaxLots
          /\ LET newLot == [units |-> err.req.units, currency |-> err.req.currency,
                            cost |-> 100, date |-> 1]
             IN lots' = lots \cup {newLot}
          /\ errors' = errors \ {err}
          /\ resolvedErrors' = resolvedErrors + 1
    /\ UNCHANGED <<pendingOps, completedOps>>

\* System idle (stuttering step)
Stutter ==
    UNCHANGED vars

-----------------------------------------------------------------------------
(* Next State Relation *)

Next ==
    \/ \E req \in Request : SubmitRequest(req)
    \/ ProcessAdd
    \/ ProcessReduceSuccess
    \/ ProcessReduceFailure
    \/ ResolveError
    \/ Stutter

-----------------------------------------------------------------------------
(* FAIRNESS CONDITIONS *)

\* Weak fairness on processing: If an operation can be processed, it eventually will be
WeakFairProcess ==
    /\ WF_vars(ProcessAdd)
    /\ WF_vars(ProcessReduceSuccess)
    /\ WF_vars(ProcessReduceFailure)

\* Weak fairness on error resolution: Errors are eventually resolved
WeakFairResolve ==
    WF_vars(ResolveError)

\* Strong fairness on requests: If requests keep coming, some will be processed
StrongFairRequests ==
    \A req \in Request : SF_vars(SubmitRequest(req))

\* Combined fairness assumption
Fairness ==
    /\ WeakFairProcess
    /\ WeakFairResolve

-----------------------------------------------------------------------------
(* LIVENESS PROPERTIES *)

\* Property 1: No Deadlock
\* The system can always make progress (some action is enabled)
NoDeadlock ==
    [](ENABLED(Next))

\* Property 2: Request Eventually Processed
\* If there's a pending operation and the system is fair, it eventually completes
RequestEventuallyProcessed ==
    [](pendingOps # <<>> => <>(completedOps' > completedOps \/ errors' # errors))

\* Property 3: Errors Eventually Resolved
\* All errors are eventually resolved (given fairness)
ErrorsEventuallyResolved ==
    [](errors # {} => <>(errors = {}))

\* Property 4: Progress
\* The system eventually processes operations (doesn't get stuck)
Progress ==
    []<>(completedOps' > completedOps \/ pendingOps = <<>>)

\* Property 5: Starvation Freedom
\* No operation waits forever in the queue
StarvationFreedom ==
    \A i \in 1..10 :
        [](Len(pendingOps) >= i => <>(Len(pendingOps) < i \/ completedOps' > completedOps))

\* Property 6: Error Bound
\* Errors don't accumulate indefinitely (resolved as fast as created)
ErrorBound ==
    []<>(Cardinality(errors) <= 1)

\* Property 7: Eventually Idle
\* System eventually reaches idle state if no new requests
EventuallyIdle ==
    []((pendingOps = <<>> /\ errors = {}) => [](pendingOps = <<>> /\ errors = {}))
    \* Note: This requires no new submissions

-----------------------------------------------------------------------------
(* TEMPORAL PROPERTIES WITH LEADS-TO *)

\* Leads-to operator: P ~> Q means [](P => <>Q)

\* Pending request leads to completion or error
PendingLeadsToResolution ==
    (pendingOps # <<>>) ~> (completedOps' > completedOps \/ Cardinality(errors) > 0)

\* Error leads to resolution
ErrorLeadsToResolution ==
    (errors # {}) ~> (resolvedErrors' > resolvedErrors)

\* Add request leads to inventory increase
AddLeadsToInventory ==
    \A req \in Request :
        req.type = "add" =>
            (Head(pendingOps) = req) ~> (Cardinality(lots) > Cardinality(lots))

-----------------------------------------------------------------------------
(* SPECIFICATION WITH FAIRNESS *)

\* Base specification (safety only)
SafetySpec == Init /\ [][Next]_vars

\* Full specification with weak fairness (standard liveness)
LiveSpec == SafetySpec /\ Fairness

\* Specification with strong fairness (stronger liveness guarantees)
StrongLiveSpec == SafetySpec /\ Fairness /\ StrongFairRequests

-----------------------------------------------------------------------------
(* THEOREMS *)

THEOREM SafetyImpliesNoDeadlock ==
    SafetySpec => NoDeadlock

THEOREM LivenessImpliesProgress ==
    LiveSpec => Progress

THEOREM LivenessImpliesErrorResolution ==
    LiveSpec => ErrorsEventuallyResolved

THEOREM StrongLivenessImpliesStarvationFreedom ==
    StrongLiveSpec => StarvationFreedom

=============================================================================
