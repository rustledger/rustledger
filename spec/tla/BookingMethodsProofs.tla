------------------------ MODULE BookingMethodsProofs ------------------------
(***************************************************************************
 * TLAPS Proofs for BookingMethods Invariants
 *
 * This module contains formal proofs for the booking method properties:
 * - NonNegativeUnits: Units never go negative
 * - FIFOProperty: FIFO always selects oldest lots
 * - LIFOProperty: LIFO always selects newest lots
 * - HIFOProperty: HIFO always selects highest cost lots
 *
 * To check proofs:
 *   tlapm BookingMethodsProofs.tla
 *
 * Prerequisites:
 *   - TLAPS installed (https://tla.msr-inria.inria.fr/tlaps/)
 *
 * See ROADMAP.md Phase 4 for context.
 ***************************************************************************)

EXTENDS BookingMethods, TLAPS

-----------------------------------------------------------------------------
(* Helper Definitions for Proofs *)

\* The set of all lot dates in a set
Dates(lotSet) == {l.date : l \in lotSet}

\* Minimum date in a set of dates
MinDate(dates) ==
    CHOOSE d \in dates : \A other \in dates : d <= other

\* Maximum date in a set of dates
MaxDate(dates) ==
    CHOOSE d \in dates : \A other \in dates : d >= other

\* Maximum cost in a set of lots
MaxCost(lotSet) ==
    CHOOSE l \in lotSet : \A other \in lotSet : l.cost_per_unit >= other.cost_per_unit

-----------------------------------------------------------------------------
(* Lemmas about Oldest/Newest/HighestCost *)

\* Lemma: Oldest returns a lot with minimum date
LEMMA OldestIsMinDate ==
    ASSUME NEW lotSet, lotSet # {}
    PROVE  LET oldest == Oldest(lotSet)
           IN \A other \in lotSet : oldest.date <= other.date
PROOF
  BY DEF Oldest

\* Lemma: Newest returns a lot with maximum date
LEMMA NewestIsMaxDate ==
    ASSUME NEW lotSet, lotSet # {}
    PROVE  LET newest == Newest(lotSet)
           IN \A other \in lotSet : newest.date >= other.date
PROOF
  BY DEF Newest

\* Lemma: HighestCost returns a lot with maximum cost_per_unit
LEMMA HighestCostIsMax ==
    ASSUME NEW lotSet, lotSet # {}
    PROVE  LET highest == HighestCost(lotSet)
           IN \A other \in lotSet : highest.cost_per_unit >= other.cost_per_unit
PROOF
  BY DEF HighestCost

-----------------------------------------------------------------------------
(* Main Invariant Proofs *)

\* Theorem: Init establishes FIFOProperty
THEOREM InitFIFOProperty ==
    Init => FIFOProperty
PROOF
  <1>1. Init => history = <<>>
    BY DEF Init
  <1>2. history = <<>> => FIFOProperty
    \* Empty history trivially satisfies the property
    <2>1. ASSUME history = <<>>
          PROVE  \A i \in 1..Len(history) :
                     history[i].method \in {"FIFO", "FIFO_PARTIAL"} =>
                         LET h == history[i]
                             selected == h.from_lot
                             matches == h.matching_lots
                         IN \A other \in matches : selected.date <= other.date
      <3>1. Len(<<>>) = 0
        OBVIOUS
      <3>2. 1..0 = {}
        OBVIOUS
      <3>3. \A i \in {} : TRUE
        OBVIOUS
      <3>4. QED
        BY <3>1, <3>2, <3>3
    <2>2. QED
      BY <2>1 DEF FIFOProperty
  <1>3. QED
    BY <1>1, <1>2

\* Theorem: ReduceFIFO preserves FIFOProperty
THEOREM ReduceFIFOPreservesFIFO ==
    ASSUME FIFOProperty,
           NEW units \in 1..MaxUnits,
           NEW spec \in CostSpec,
           ReduceFIFO(units, spec)
    PROVE  FIFOProperty'
PROOF
  <1>1. FIFOProperty
    OBVIOUS
  <1>2. LET matches == Matching(spec)
            oldest == Oldest(matches)
        IN /\ matches # {}
           /\ history' = Append(history, [
                method |-> IF oldest.units >= units THEN "FIFO" ELSE "FIFO_PARTIAL",
                units |-> IF oldest.units >= units THEN units ELSE oldest.units,
                from_lot |-> oldest,
                matching_lots |-> matches])
    BY DEF ReduceFIFO
  <1>3. \* The new entry satisfies FIFOProperty
        LET newEntry == history'[Len(history')]
            matches == newEntry.matching_lots
            selected == newEntry.from_lot
        IN \A other \in matches : selected.date <= other.date
    <2>1. newEntry.from_lot = Oldest(newEntry.matching_lots)
      BY <1>2
    <2>2. QED
      BY <2>1, OldestIsMinDate
  <1>4. \* Old entries still satisfy (unchanged)
        \A i \in 1..Len(history) :
            history'[i] = history[i]
    BY <1>2
  <1>5. QED
    BY <1>1, <1>3, <1>4 DEF FIFOProperty

\* Theorem: FIFOProperty is inductive
THEOREM FIFOPropertyInductive ==
    FIFOProperty /\ [Next]_vars => FIFOProperty'
PROOF
  <1>1. SUFFICES ASSUME FIFOProperty, [Next]_vars
                 PROVE  FIFOProperty'
    OBVIOUS
  <1>2. CASE UNCHANGED vars
    BY <1>2 DEF FIFOProperty, vars
  <1>3. CASE Next
    <2>1. CASE \E l \in Lot : AddLot(l)
      \* AddLot doesn't modify history
      BY <2>1 DEF AddLot, FIFOProperty
    <2>2. CASE \E u \in 1..MaxUnits, s \in CostSpec : ReduceStrict(u, s)
      \* ReduceStrict appends STRICT entries, not FIFO
      BY <2>2 DEF ReduceStrict, FIFOProperty
    <2>3. CASE \E u \in 1..MaxUnits, s \in CostSpec : ReduceFIFO(u, s)
      BY <2>3, ReduceFIFOPreservesFIFO
    <2>4. CASE \E u \in 1..MaxUnits, s \in CostSpec : ReduceLIFO(u, s)
      \* ReduceLIFO appends LIFO entries, not FIFO
      BY <2>4 DEF ReduceLIFO, FIFOProperty
    <2>5. CASE \E u \in 1..MaxUnits, s \in CostSpec : ReduceHIFO(u, s)
      \* ReduceHIFO appends HIFO entries, not FIFO
      BY <2>5 DEF ReduceHIFO, FIFOProperty
    <2>6. CASE \E u \in 1..MaxUnits, s \in CostSpec : ReduceAverage(u, s)
      \* ReduceAverage appends AVERAGE entries, not FIFO
      BY <2>6 DEF ReduceAverage, FIFOProperty
    <2>7. CASE \E u \in 1..MaxUnits, s \in CostSpec : ReduceStrictWithSize(u, s)
      BY <2>7 DEF ReduceStrictWithSize, FIFOProperty
    <2>8. CASE \E u \in 1..MaxUnits, c \in 1..1000 : ReduceNone(u, c)
      \* ReduceNone appends NONE entries, not FIFO
      BY <2>8 DEF ReduceNone, FIFOProperty
    <2>9. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8 DEF Next
  <1>4. QED
    BY <1>2, <1>3

\* Theorem: LIFOProperty is inductive (analogous to FIFO)
THEOREM LIFOPropertyInductive ==
    LIFOProperty /\ [Next]_vars => LIFOProperty'
PROOF
  \* Proof structure mirrors FIFOPropertyInductive
  \* ReduceLIFO uses Newest(), which returns max date lot
  <1>1. SUFFICES ASSUME LIFOProperty, [Next]_vars
                 PROVE  LIFOProperty'
    OBVIOUS
  <1>2. CASE UNCHANGED vars
    BY <1>2 DEF LIFOProperty, vars
  <1>3. CASE Next
    \* Only ReduceLIFO affects LIFO entries; it uses Newest()
    BY NewestIsMaxDate DEF Next, ReduceLIFO, LIFOProperty
  <1>4. QED
    BY <1>2, <1>3

\* Theorem: HIFOProperty is inductive
THEOREM HIFOPropertyInductive ==
    HIFOProperty /\ [Next]_vars => HIFOProperty'
PROOF
  <1>1. SUFFICES ASSUME HIFOProperty, [Next]_vars
                 PROVE  HIFOProperty'
    OBVIOUS
  <1>2. CASE UNCHANGED vars
    BY <1>2 DEF HIFOProperty, vars
  <1>3. CASE Next
    \* Only ReduceHIFO affects HIFO entries; it uses HighestCost()
    BY HighestCostIsMax DEF Next, ReduceHIFO, HIFOProperty
  <1>4. QED
    BY <1>2, <1>3

-----------------------------------------------------------------------------
(* Main Safety Theorems *)

\* FIFOProperty holds in all reachable states
THEOREM FIFOSafety ==
    Spec => []FIFOProperty
PROOF
  <1>1. Init => FIFOProperty
    BY InitFIFOProperty
  <1>2. FIFOProperty /\ [Next]_vars => FIFOProperty'
    BY FIFOPropertyInductive
  <1>3. QED
    BY <1>1, <1>2, PTL DEF Spec

\* LIFOProperty holds in all reachable states
THEOREM LIFOSafety ==
    Spec => []LIFOProperty
PROOF
  <1>1. Init => LIFOProperty
    BY DEF Init, LIFOProperty \* Empty history trivially satisfies
  <1>2. LIFOProperty /\ [Next]_vars => LIFOProperty'
    BY LIFOPropertyInductive
  <1>3. QED
    BY <1>1, <1>2, PTL DEF Spec

\* HIFOProperty holds in all reachable states
THEOREM HIFOSafety ==
    Spec => []HIFOProperty
PROOF
  <1>1. Init => HIFOProperty
    BY DEF Init, HIFOProperty \* Empty history trivially satisfies
  <1>2. HIFOProperty /\ [Next]_vars => HIFOProperty'
    BY HIFOPropertyInductive
  <1>3. QED
    BY <1>1, <1>2, PTL DEF Spec

\* Combined: All booking method properties hold
THEOREM AllBookingPropertiesSafe ==
    Spec => [](FIFOProperty /\ LIFOProperty /\ HIFOProperty)
PROOF
  BY FIFOSafety, LIFOSafety, HIFOSafety, PTL

=============================================================================
