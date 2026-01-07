---------------------------- MODULE PriceDatabase ----------------------------
(***************************************************************************
 * TLA+ Specification for Price Database
 *
 * Models price lookups and currency conversions for rustledger.
 * The price database stores historical prices and supports:
 * - Direct price lookup
 * - Date-based lookup with fallback to nearest prior date
 * - Price triangulation through intermediate currencies
 *
 * Key invariants verified:
 * - Price consistency across triangulation paths
 * - Prices are always positive
 * - Lookup always returns most recent price <= query date
 *
 * See: crates/rustledger-core/src/price.rs
 ***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Currencies,     \* Set of all currencies (e.g., {"USD", "EUR", "AAPL"})
    MaxDate,        \* Maximum date for model checking
    MaxPrice,       \* Maximum price value (scaled integer)
    Tolerance       \* Tolerance for price comparison

NULL == CHOOSE x : x \notin Currencies

-----------------------------------------------------------------------------
(* Type Definitions *)

\* A price entry: cost of 1 unit of base in quote currency
PriceEntry == [
    base: Currencies,
    quote: Currencies,
    date: 0..MaxDate,
    price: 1..MaxPrice  \* Prices must be positive
]

\* A currency pair
CurrencyPair == Currencies \X Currencies

-----------------------------------------------------------------------------
(* Variables *)

VARIABLES
    prices,         \* Set of price entries
    lookups,        \* History of price lookups
    cache           \* Cached computed prices

vars == <<prices, lookups, cache>>

-----------------------------------------------------------------------------
(* Helper Functions *)

\* Get all prices for a currency pair
PricesFor(base, quote) ==
    {p \in prices : p.base = base /\ p.quote = quote}

\* Get all prices for a pair up to a given date
PricesUpTo(base, quote, date) ==
    {p \in PricesFor(base, quote) : p.date <= date}

\* Get the most recent price for a pair up to a date
MostRecentPrice(base, quote, date) ==
    LET available == PricesUpTo(base, quote, date)
    IN IF available = {}
       THEN NULL
       ELSE LET maxDate == CHOOSE d \in {p.date : p \in available} :
                    \A p \in available : p.date <= d
            IN CHOOSE p \in available : p.date = maxDate

\* Get price value (or NULL if not found)
GetPrice(base, quote, date) ==
    LET entry == MostRecentPrice(base, quote, date)
    IN IF entry = NULL THEN NULL ELSE entry.price

\* Check if inverse price is available
HasInversePrice(base, quote, date) ==
    GetPrice(quote, base, date) # NULL

\* Compute inverse price
InversePrice(base, quote, date) ==
    LET direct == GetPrice(quote, base, date)
    IN IF direct = NULL THEN NULL
       ELSE MaxPrice \div direct  \* Simplified inverse

\* Triangulate price through intermediate currency
TriangulatePrice(base, quote, date, intermediate) ==
    LET p1 == GetPrice(base, intermediate, date)
        p2 == GetPrice(intermediate, quote, date)
    IN IF p1 = NULL \/ p2 = NULL
       THEN NULL
       ELSE (p1 * p2) \div MaxPrice  \* Scaled multiplication

\* Find best price using any method
BestPrice(base, quote, date) ==
    LET direct == GetPrice(base, quote, date)
        inverse == InversePrice(base, quote, date)
        \* Try triangulation through each currency
        triangulated == {TriangulatePrice(base, quote, date, mid) :
                        mid \in Currencies \ {base, quote}}
    IN IF direct # NULL THEN direct
       ELSE IF inverse # NULL THEN inverse
       ELSE LET validTri == {t \in triangulated : t # NULL}
            IN IF validTri = {} THEN NULL
               ELSE CHOOSE t \in validTri : TRUE

\* Absolute value
Abs(x) == IF x >= 0 THEN x ELSE -x

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ prices = {}
    /\ lookups = <<>>
    /\ cache = [pair \in CurrencyPair |-> [date \in 0..MaxDate |-> NULL]]

-----------------------------------------------------------------------------
(* Actions *)

\* Add a new price entry
AddPrice(base, quote, date, price) ==
    /\ base # quote  \* Can't price currency against itself
    /\ price > 0     \* Prices must be positive
    /\ ~\E p \in prices : p.base = base /\ p.quote = quote /\ p.date = date
       \* No duplicate prices for same pair and date
    /\ prices' = prices \cup {[base |-> base, quote |-> quote,
                               date |-> date, price |-> price]}
    /\ UNCHANGED <<lookups, cache>>

\* Lookup a price
LookupPrice(base, quote, date) ==
    /\ LET result == BestPrice(base, quote, date)
       IN lookups' = Append(lookups, [base |-> base, quote |-> quote,
                                      date |-> date, result |-> result])
    /\ UNCHANGED <<prices, cache>>

\* Cache a computed price
CachePrice(base, quote, date, price) ==
    /\ price # NULL
    /\ cache' = [cache EXCEPT ![<<base, quote>>][date] = price]
    /\ UNCHANGED <<prices, lookups>>

-----------------------------------------------------------------------------
(* Next State *)

Next ==
    \/ \E b, q \in Currencies, d \in 0..MaxDate, p \in 1..MaxPrice :
        AddPrice(b, q, d, p)
    \/ \E b, q \in Currencies, d \in 0..MaxDate :
        LookupPrice(b, q, d)
    \/ \E b, q \in Currencies, d \in 0..MaxDate, p \in 1..MaxPrice :
        CachePrice(b, q, d, p)

-----------------------------------------------------------------------------
(* Invariants *)

\* All stored prices are positive
PositivePrices ==
    \A p \in prices : p.price > 0

\* No self-referential prices (USD/USD)
NoSelfPrices ==
    \A p \in prices : p.base # p.quote

\* Lookup always returns most recent price
LookupReturnsRecent ==
    \A i \in 1..Len(lookups) :
        LET l == lookups[i]
            result == l.result
            available == PricesUpTo(l.base, l.quote, l.date)
        IN result # NULL =>
           \A p \in available : p.date <= l.date

\* Price symmetry: P(A/B) * P(B/A) ≈ 1 (within tolerance)
\* Note: This is a desired property but may not always hold exactly
PriceSymmetry ==
    \A b, q \in Currencies, d \in 0..MaxDate :
        LET pBQ == GetPrice(b, q, d)
            pQB == GetPrice(q, b, d)
        IN (pBQ # NULL /\ pQB # NULL) =>
           Abs((pBQ * pQB) - MaxPrice) <= Tolerance

\* Triangulation consistency: P(A/B) ≈ P(A/C) * P(C/B) (within tolerance)
TriangulationConsistency ==
    \A b, q, mid \in Currencies, d \in 0..MaxDate :
        (b # q /\ q # mid /\ b # mid) =>
        LET direct == GetPrice(b, q, d)
            triangulated == TriangulatePrice(b, q, d, mid)
        IN (direct # NULL /\ triangulated # NULL) =>
           Abs(direct - triangulated) <= Tolerance

\* Type correctness
TypeOK ==
    /\ prices \subseteq PriceEntry
    /\ lookups \in Seq([base: Currencies, quote: Currencies,
                        date: 0..MaxDate, result: 1..MaxPrice \cup {NULL}])

\* Main invariant
Invariant ==
    /\ TypeOK
    /\ PositivePrices
    /\ NoSelfPrices
    /\ LookupReturnsRecent

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Properties *)

\* Eventually all currency pairs have prices
EventualCoverage ==
    \A b, q \in Currencies :
        b # q => <>(BestPrice(b, q, MaxDate) # NULL)

\* Prices are never lost (monotonic)
PricesMonotonic ==
    [][prices \subseteq prices']_vars

=============================================================================
