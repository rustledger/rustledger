--------------------------- MODULE ConcurrentAccess ---------------------------
(*
 * Concurrent Inventory Access
 *
 * Verifies:
 * - Concurrent reads are safe (no data races)
 * - Concurrent writes require synchronization
 * - Read-write conflicts are handled correctly
 * - Conservation is maintained under concurrent access
 *
 * This models concurrent access patterns in rustledger.
 *)

EXTENDS Integers

CONSTANTS
    NumReaders,     \* Number of concurrent readers
    NumWriters,     \* Number of concurrent writers
    MaxBalance      \* Maximum balance value

VARIABLES
    balance,        \* Current inventory balance
    readLock,       \* Number of active readers
    writeLock,      \* Whether write lock is held
    operations      \* Number of operations performed (bounded)

vars == <<balance, readLock, writeLock, operations>>

MaxOps == (NumReaders + NumWriters) * 3  \* Bound operations

-----------------------------------------------------------------------------
Init ==
    /\ balance = 0
    /\ readLock = 0
    /\ writeLock = FALSE
    /\ operations = 0

-----------------------------------------------------------------------------
(* Acquire read lock - can have multiple concurrent readers *)
AcquireReadLock ==
    /\ operations < MaxOps
    /\ ~writeLock                   \* No writer holding lock
    /\ readLock < NumReaders        \* Don't exceed reader limit
    /\ readLock' = readLock + 1
    /\ operations' = operations + 1
    /\ UNCHANGED <<balance, writeLock>>

(* Release read lock *)
ReleaseReadLock ==
    /\ operations < MaxOps
    /\ readLock > 0
    /\ readLock' = readLock - 1
    /\ operations' = operations + 1
    /\ UNCHANGED <<balance, writeLock>>

(* Acquire write lock - exclusive access *)
AcquireWriteLock ==
    /\ operations < MaxOps
    /\ ~writeLock                   \* No other writer
    /\ readLock = 0                 \* No active readers
    /\ writeLock' = TRUE
    /\ operations' = operations + 1
    /\ UNCHANGED <<balance, readLock>>

(* Perform write operation (add to balance) *)
WriteAdd(amount) ==
    /\ operations < MaxOps
    /\ writeLock                    \* Must hold write lock
    /\ amount > 0
    /\ balance + amount <= MaxBalance
    /\ balance' = balance + amount
    /\ operations' = operations + 1
    /\ UNCHANGED <<readLock, writeLock>>

(* Perform write operation (reduce balance) *)
WriteReduce(amount) ==
    /\ operations < MaxOps
    /\ writeLock                    \* Must hold write lock
    /\ amount > 0
    /\ balance >= amount            \* Can't go negative
    /\ balance' = balance - amount
    /\ operations' = operations + 1
    /\ UNCHANGED <<readLock, writeLock>>

(* Release write lock *)
ReleaseWriteLock ==
    /\ operations < MaxOps
    /\ writeLock
    /\ writeLock' = FALSE
    /\ operations' = operations + 1
    /\ UNCHANGED <<balance, readLock>>

Next ==
    \/ AcquireReadLock
    \/ ReleaseReadLock
    \/ AcquireWriteLock
    \/ \E amt \in 1..MaxBalance : WriteAdd(amt)
    \/ \E amt \in 1..MaxBalance : WriteReduce(amt)
    \/ ReleaseWriteLock

-----------------------------------------------------------------------------
(* INVARIANTS *)

(* No data race: readers and writers are mutually exclusive *)
NoDataRace ==
    ~(readLock > 0 /\ writeLock)

(* Balance is always non-negative *)
NonNegativeBalance ==
    balance >= 0

(* Balance is always bounded *)
BoundedBalance ==
    balance <= MaxBalance

(* Write lock is exclusive *)
ExclusiveWriteLock ==
    writeLock => (readLock = 0)

(* Read lock count is bounded *)
ReadLockBounded ==
    readLock <= NumReaders

(* Operations are bounded *)
OperationsBounded ==
    operations <= MaxOps

(* Type invariant *)
TypeOK ==
    /\ balance \in 0..MaxBalance
    /\ readLock \in 0..NumReaders
    /\ writeLock \in BOOLEAN
    /\ operations \in 0..MaxOps

Spec == Init /\ [][Next]_vars

=============================================================================
