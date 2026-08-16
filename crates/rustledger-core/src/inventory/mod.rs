//! Inventory type representing a collection of positions.
//!
//! An [`Inventory`] tracks the holdings of an account as a collection of
//! [`Position`]s. It provides methods for adding and reducing positions
//! using different booking methods (FIFO, LIFO, STRICT, NONE).

// ratchet: fxhash-only — hot path; use FxHashMap/FxHashSet, not std SipHash collections (#1237).
use imbl::Vector;
use rust_decimal::Decimal;
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;
use std::fmt;
use std::str::FromStr;

use crate::{Account, Amount, CostSpec, Currency, Position, is_subaccount_or_equal};

/// Inline storage for `BookingResult::matched`.
///
/// STRICT booking (the default) always produces exactly one matched lot
/// per posting; FIFO / LIFO frequently match a single lot too. Inline
/// cap of 1 covers the hot case with zero heap allocation while still
/// spilling to the heap for multi-lot matches.
///
/// **API surface note**: this is `pub(crate)` deliberately — we don't
/// want to commit downstream consumers to `smallvec` as part of our
/// public API contract. External code reads `BookingResult.matched` via
/// the slice deref (`.iter()`, `.len()`, indexing) which works
/// transparently. The concrete `SmallVec<[Position; 1]>` type is still
/// reachable via the field type but isn't promoted into the crate root.
pub(crate) type MatchedLots = SmallVec<[Position; 1]>;

mod booking;

/// Booking method determines how lots are matched when reducing positions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)
)]
pub enum BookingMethod {
    /// Lots must match exactly (unambiguous).
    /// If multiple lots match the cost spec, an error is raised.
    #[default]
    Strict,
    /// Like STRICT, but exact-size matches accept oldest lot.
    /// If reduction amount equals total inventory, it's considered unambiguous.
    StrictWithSize,
    /// First In, First Out. Oldest lots are reduced first.
    Fifo,
    /// Last In, First Out. Newest lots are reduced first.
    Lifo,
    /// Highest In, First Out. Highest-cost lots are reduced first.
    Hifo,
    /// Average cost booking. All lots of a currency are merged.
    Average,
    /// No cost tracking. Units are reduced without matching lots.
    None,
}

impl FromStr for BookingMethod {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_uppercase().as_str() {
            "STRICT" => Ok(Self::Strict),
            "STRICT_WITH_SIZE" => Ok(Self::StrictWithSize),
            "FIFO" => Ok(Self::Fifo),
            "LIFO" => Ok(Self::Lifo),
            "HIFO" => Ok(Self::Hifo),
            "AVERAGE" => Ok(Self::Average),
            "NONE" => Ok(Self::None),
            _ => Err(format!("unknown booking method: {s}")),
        }
    }
}

impl fmt::Display for BookingMethod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Strict => write!(f, "STRICT"),
            Self::StrictWithSize => write!(f, "STRICT_WITH_SIZE"),
            Self::Fifo => write!(f, "FIFO"),
            Self::Lifo => write!(f, "LIFO"),
            Self::Hifo => write!(f, "HIFO"),
            Self::Average => write!(f, "AVERAGE"),
            Self::None => write!(f, "NONE"),
        }
    }
}

/// Controls which positions are considered when checking whether incoming
/// units reduce (i.e. have the opposite sign of) an existing inventory.
///
/// - [`AllPositions`](ReductionScope::AllPositions): every position is
///   considered, regardless of whether it carries a cost.
/// - [`CostBearingOnly`](ReductionScope::CostBearingOnly): only positions
///   with a cost are considered.  This prevents a negative simple (no-cost)
///   position — left behind by a sell-without-cost-spec — from causing a
///   subsequent cost-bearing augmentation to be misclassified as a reduction.
///   See: issue #875, beancount#889.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ReductionScope {
    /// Consider all positions (cost-bearing and simple).
    AllPositions,
    /// Consider only positions that carry a cost.
    CostBearingOnly,
}

/// Result of a booking operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BookingResult {
    /// Positions that were matched/reduced.
    ///
    /// Backed by [`SmallVec<[Position; 1]>`](smallvec::SmallVec) so the
    /// single-match common case (always true under STRICT, common under
    /// FIFO/LIFO) doesn't touch the heap. The concrete type derefs to
    /// `[Position]`, so read-side patterns like `.iter()`,
    /// `.len()`, `.is_empty()`, and indexing work unchanged.
    ///
    /// **Breaking API change in 0.15.0**: prior versions used
    /// `Vec<Position>`. Downstream code that named the type explicitly
    /// (`let v: Vec<Position> = result.matched`) or called Vec-specific
    /// methods (`.capacity()`, `.reserve()`) needs to adapt; reading
    /// the field through the slice deref keeps working.
    pub matched: MatchedLots,
    /// The cost basis of the matched positions (for capital gains).
    pub cost_basis: Option<Amount>,
}

/// Error that can occur during booking.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BookingError {
    /// Multiple lots match but booking method requires unambiguous match.
    AmbiguousMatch {
        /// Number of lots that matched.
        num_matches: usize,
        /// The currency being reduced.
        currency: crate::Currency,
    },
    /// No lots match the cost specification.
    NoMatchingLot {
        /// The currency being reduced.
        currency: crate::Currency,
        /// The cost spec that didn't match.
        cost_spec: CostSpec,
    },
    /// Not enough units in matching lots.
    InsufficientUnits {
        /// The currency being reduced.
        currency: crate::Currency,
        /// Units requested.
        requested: Decimal,
        /// Units available.
        available: Decimal,
    },
    /// Currency mismatch between reduction and inventory.
    CurrencyMismatch {
        /// Expected currency.
        expected: crate::Currency,
        /// Got currency.
        got: crate::Currency,
    },
    /// The arithmetic left `rust_decimal`'s ~±7.9e28 range (#1863).
    ///
    /// Reported rather than clamped: `Decimal::MIN == -Decimal::MAX`, so
    /// clamped debits and credits cancel to a residual of exactly zero and an
    /// arbitrarily unbalanced ledger certifies as clean. Reported rather than
    /// panicked because ledger input must never abort the CLI.
    Overflow(OverflowError),
}

/// A `Decimal` computation whose result cannot be represented.
///
/// `rust_decimal` is a 96-bit type with a hard ~±7.9e28 magnitude ceiling and
/// its `+`/`*` panic on overflow. There is no in-range answer to substitute,
/// so the arithmetic reports instead of clamping.
///
/// Used where an operation MUTATES an inventory, so a caller that reports and
/// continues needs to know which currency was left alone. Pure leaf arithmetic
/// returns a plain `Option` instead and lets its caller supply the context:
/// [`crate::Cost::total_cost`], [`sum_account_and_subaccounts`], and
/// `rustledger_booking`'s weight ladder. The split is about who is positioned
/// to write the diagnostic, not about which failures matter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OverflowError {
    /// The currency whose running total left the range.
    pub currency: crate::Currency,
}

impl fmt::Display for OverflowError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} amount exceeds the representable range (±7.9e28); \
             split the transaction, or denominate it in larger units \
             (thousands, millions) so the number is smaller",
            self.currency
        )
    }
}

impl std::error::Error for OverflowError {}

impl From<OverflowError> for BookingError {
    fn from(e: OverflowError) -> Self {
        Self::Overflow(e)
    }
}

impl fmt::Display for BookingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AmbiguousMatch {
                num_matches,
                currency,
            } => write!(
                f,
                "Ambiguous match: {num_matches} lots match for {currency}"
            ),
            Self::NoMatchingLot {
                currency,
                cost_spec,
            } => {
                write!(f, "No matching lot for {currency} with cost {cost_spec}")
            }
            Self::InsufficientUnits {
                currency,
                requested,
                available,
            } => write!(
                f,
                "Insufficient units of {currency}: requested {requested}, available {available}"
            ),
            Self::CurrencyMismatch { expected, got } => {
                write!(f, "Currency mismatch: expected {expected}, got {got}")
            }
            Self::Overflow(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for BookingError {}

impl BookingError {
    /// Wrap this booking error with the account context that produced it.
    ///
    /// `Inventory` itself doesn't know which account it belongs to, so the
    /// raw `BookingError` carries no `account` field. The caller (booking
    /// engine, validator) knows the account and uses this constructor to
    /// produce the user-facing error.
    ///
    /// The resulting [`AccountedBookingError`] is the **single canonical
    /// rendering** of an inventory failure for user-facing output. Both the
    /// booking layer and the validator format errors via this type so the
    /// wording cannot drift between them — the failure mode that produced
    /// #748.
    #[must_use]
    pub const fn with_account(self, account: crate::Account) -> AccountedBookingError {
        AccountedBookingError {
            error: self,
            account,
        }
    }
}

/// A [`BookingError`] paired with the account that produced it.
///
/// This is the canonical user-facing inventory error type. Its `Display`
/// impl is the **single source of truth** for booking-error wording across
/// `rustledger-booking` and `rustledger-validate`. Conformance assertions
/// (e.g. pta-standards `reduction-exceeds-inventory` requires the literal
/// substring `"not enough"`) are pinned by this Display.
///
/// Construct via [`BookingError::with_account`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AccountedBookingError {
    /// The underlying inventory-level error.
    pub error: BookingError,
    /// The account whose inventory produced the error.
    pub account: crate::Account,
}

impl fmt::Display for AccountedBookingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.error {
            // The currency is already named in the inner message; the account
            // is the context this wrapper exists to add.
            BookingError::Overflow(e) => write!(f, "{}: {e}", self.account),
            BookingError::InsufficientUnits {
                requested,
                available,
                ..
            } => write!(
                f,
                "Not enough units in {}: requested {}, available {}; not enough to reduce",
                self.account, requested, available
            ),
            BookingError::NoMatchingLot { currency, .. } => {
                write!(f, "No matching lot for {} in {}", currency, self.account)
            }
            BookingError::AmbiguousMatch {
                num_matches,
                currency,
            } => write!(
                f,
                "Ambiguous lot match for {}: {} lots match in {}",
                currency, num_matches, self.account
            ),
            // Currency mismatch is semantically a specialization of
            // NoMatchingLot (there is no lot for the given currency in this
            // inventory), so we render and classify it the same way. Consumers
            // filtering on E4001 don't need to special-case CurrencyMismatch.
            //
            // This variant is defensive: no `Inventory::reduce` path in
            // `rustledger-core` currently emits it, but we still render it
            // consistently in case a future emission site is added.
            BookingError::CurrencyMismatch { got, .. } => {
                write!(f, "No matching lot for {} in {}", got, self.account)
            }
        }
    }
}

impl std::error::Error for AccountedBookingError {}
/// How an [`Inventory`] holds its positions.
///
/// The two backings exist because the two uses want opposite things, and a
/// single choice was measurably wrong for one of them:
///
/// * **Booking** mutates an inventory constantly — `add`, and a `reduce` that
///   filters, sorts and then indexes matched lots — and snapshots it only on
///   the conditional overflow-rollback path. It wants contiguous storage:
///   O(1) indexing and cache-friendly iteration.
/// * **BQL's JOURNAL running balance** is only appended to, and is CLONED
///   once per output row. It wants structural sharing: N snapshots costing
///   O(base + sum of deltas) rather than O(N x base) (#1086 — measured at
///   32.7 MB peak RSS for 2000 lots x 2000 rows; a contiguous clone per row
///   holds ~2M positions instead).
///
/// Holding everything in the persistent vector made every reduction pay RRB
/// costs: on a lot-heavy workload `imbl::Vector`'s iterator alone was ~13% of
/// all instructions, and indexed access inside `reduce_ordered` is O(log M)
/// per lookup rather than O(1). Holding everything contiguously reintroduces
/// the #1086 blow-up. So the representation follows the use.
#[derive(Debug, Clone)]
enum PositionStore {
    /// Contiguous — booking's working representation.
    Owned(Vec<Position>),
    /// Structurally shared — BQL's snapshot representation.
    Shared(Vector<Position>),
}

/// Iterator over [`PositionStore`], as a stack-allocated enum.
///
/// Deliberately NOT `Box<dyn Iterator>`: `iter` is called from `units`,
/// `merge`, `at_cost`, equality and every reduction pass, so boxing would put
/// a heap allocation and a dynamic dispatch on paths this change exists to
/// make cheaper. Copilot's catch on #2056.
enum PositionStoreIter<'a> {
    Owned(std::slice::Iter<'a, Position>),
    Shared(imbl::vector::Iter<'a, Position, imbl::shared_ptr::DefaultSharedPtr>),
}

impl<'a> Iterator for PositionStoreIter<'a> {
    type Item = &'a Position;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Owned(i) => i.next(),
            Self::Shared(i) => i.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            Self::Owned(i) => i.size_hint(),
            Self::Shared(i) => i.size_hint(),
        }
    }
}

impl Default for PositionStore {
    fn default() -> Self {
        Self::Owned(Vec::new())
    }
}

impl PositionStore {
    /// Every live position paired with the index that [`Index`] will accept
    /// for it.
    ///
    /// Today this is exactly `iter().enumerate()`, because every element of
    /// the backing store is live. It exists as its own method because that
    /// equivalence is a PROPERTY OF THE CURRENT STORAGE, not a law: the
    /// reduction paths collect indices here and hand them back through
    /// `Index`/`IndexMut`, so anything that makes the backing sparse — the
    /// tombstoned lots that would let a cost-keyed index survive removals —
    /// silently desynchronises the two unless every such site goes through
    /// one place. This is that place.
    ///
    /// [`Index`]: std::ops::Index
    fn iter_slots(&self) -> impl Iterator<Item = (usize, &Position)> {
        self.iter().enumerate()
    }

    fn iter(&self) -> PositionStoreIter<'_> {
        match self {
            Self::Owned(v) => PositionStoreIter::Owned(v.iter()),
            Self::Shared(v) => PositionStoreIter::Shared(v.iter()),
        }
    }

    fn len(&self) -> usize {
        match self {
            Self::Owned(v) => v.len(),
            Self::Shared(v) => v.len(),
        }
    }

    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn get(&self, i: usize) -> Option<&Position> {
        match self {
            Self::Owned(v) => v.get(i),
            Self::Shared(v) => v.get(i),
        }
    }

    fn push(&mut self, p: Position) {
        match self {
            Self::Owned(v) => v.push(p),
            Self::Shared(v) => v.push_back(p),
        }
    }

    fn remove(&mut self, i: usize) -> Position {
        match self {
            Self::Owned(v) => v.remove(i),
            Self::Shared(v) => v.remove(i),
        }
    }

    fn retain(&mut self, f: impl FnMut(&Position) -> bool) {
        match self {
            Self::Owned(v) => v.retain(f),
            Self::Shared(v) => v.retain(f),
        }
    }

    /// [`Self::retain`], with each position's slot index — the same index
    /// [`Self::iter_slots`] reports and [`Index`] accepts.
    ///
    /// `reduce_merge` needs this: it selects lots through `iter_slots` and
    /// then drops exactly those. Written with a plain `retain` and a counter
    /// incremented per visit, that is only correct while every element the
    /// store holds is a live position visited in order — the same dense-store
    /// assumption `iter_slots` exists to keep in one place, arriving by a
    /// second route that `iter_slots` cannot cover. A sparse store whose
    /// `retain` skips dead slots would leave the counter numbering live
    /// positions while the selection numbered real slots, and `{*}` merges
    /// would delete the wrong lots.
    ///
    /// [`Index`]: std::ops::Index
    fn retain_slots(&mut self, mut f: impl FnMut(usize, &Position) -> bool) {
        let mut slot = 0;
        self.retain(|position| {
            let keep = f(slot, position);
            slot += 1;
            keep
        });
    }

    /// Switch to contiguous storage, cloning if not already `Owned`.
    ///
    /// `reduce` calls this, which ALSO discharges the uniqueness requirement
    /// the old unconditional `self.positions.iter().cloned().collect()`
    /// existed for: mutating a structurally-SHARED `imbl::Vector` in place
    /// drives `imbl-sized-chunks`' copy-on-write into a use-after-free of the
    /// interned `Arc<str>` inside `Position`. Materializing into a fresh
    /// `Vec` leaves nothing shared to corrupt, at the same O(M) cost that
    /// copy already paid — and every subsequent access in the reduction is
    /// then contiguous instead of an RRB walk.
    fn make_owned(&mut self) {
        if let Self::Shared(v) = self {
            *self = Self::Owned(v.iter().cloned().collect());
        }
    }
}

impl std::ops::Index<usize> for PositionStore {
    type Output = Position;
    fn index(&self, i: usize) -> &Position {
        match self {
            Self::Owned(v) => &v[i],
            Self::Shared(v) => &v[i],
        }
    }
}

impl std::ops::IndexMut<usize> for PositionStore {
    fn index_mut(&mut self, i: usize) -> &mut Position {
        match self {
            Self::Owned(v) => &mut v[i],
            Self::Shared(v) => &mut v[i],
        }
    }
}

impl FromIterator<Position> for PositionStore {
    fn from_iter<I: IntoIterator<Item = Position>>(iter: I) -> Self {
        Self::Owned(iter.into_iter().collect())
    }
}

// Serialized as a plain sequence, identical for both backings — the wire
// format does not encode which representation happens to be in use, and a
// round-trip always lands in `Owned` (deserialization is followed by
// `rebuild_index`, and a freshly-loaded inventory is about to be mutated far
// more often than snapshotted).
impl Serialize for PositionStore {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_seq(self.iter())
    }
}

impl<'de> Deserialize<'de> for PositionStore {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Ok(Self::Owned(Vec::<Position>::deserialize(deserializer)?))
    }
}

/// An inventory is a collection of positions.
///
/// It tracks all positions for an account and supports booking operations
/// for adding and reducing positions.
///
/// # Examples
///
/// ```
/// use rustledger_core::{Inventory, Position, Amount, Cost, BookingMethod};
/// use rust_decimal_macros::dec;
///
/// let mut inv = Inventory::new();
///
/// // Add a simple position
/// inv.add(Position::simple(Amount::new(dec!(100), "USD")));
/// assert_eq!(inv.units("USD"), dec!(100));
///
/// // Add a position with cost
/// let cost = Cost::new(dec!(150.00), "USD");
/// inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost));
/// assert_eq!(inv.units("AAPL"), dec!(10));
/// ```
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
// Deserialization goes through `InventoryWire` so the derived caches are
// REBUILT rather than left empty.
//
// `simple_index` and `units_cache` are `#[serde(skip)]`, so a plain derive
// produced an inventory holding positions with both caches empty. `units()`
// recomputes on a miss and `add_headroom_for` refuses to answer, but `add()`
// trusted them: `units_cache.get(..).unwrap_or_default()` read 0 for an
// inventory already holding 100 USD, then wrote that back as the new total,
// while the empty `simple_index` meant a cost-less lot was appended instead of
// merged. A round-tripped 100 USD inventory answered `units("USD") == 5` after
// adding 5, with two lots where there should be one.
//
// `rebuild_index`'s own doc already claimed it ran "after ... deserialization".
// It did not — nothing called it on that path, and two comments elsewhere
// referred to it by a name (`rebuild_caches`) that never existed. Now it does.
#[serde(try_from = "InventoryWire")]
pub struct Inventory {
    /// Positions, in whichever backing suits this inventory's use — see
    /// [`PositionStore`]. Contiguous (`Owned`) by default, which is what
    /// booking wants; structurally shared (`Shared`) for the BQL running
    /// balances that are cloned once per output row.
    ///
    /// The notes below describe the SHARED backing, and are why it still
    /// exists:
    /// This is the critical property for JOURNAL-style row-per-snapshot
    /// patterns in BQL (issue #1086): N nested snapshots cost O(base + Σ
    /// deltas) memory instead of O(N · base), and the per-row clone cost
    /// drops from O(positions) to O(1).
    ///
    /// The trade is real: booking and BQL aggregator mutations pay an
    /// O(log N) tree walk vs `Vec`'s amortized O(1) push. Measured impact
    /// scales with inventory size M: +85 ns/op at M=10, +1.6 µs/op at
    /// M=100, +19 µs/op at M=500 (criterion `reduce_fifo/*`). For typical
    /// small-M ledgers the overhead is sub-millisecond per `rledger
    /// check`; the users who feel it are users with very large inventories,
    /// the same users who hit the JOURNAL OOM today.
    ///
    /// `rkyv` derives were dropped because (a) `imbl::Vector` has no `rkyv`
    /// impl and (b) no code path currently archives an `Inventory`
    /// (confirmed in the `SmallVec` experiment for #1069). Pre-1.0 break;
    /// downstream callers archiving `Inventory` directly will need to
    /// archive `Vec<Position>` themselves. Serde wire format is unchanged
    /// (sequence-typed, identical for both backings).
    positions: PositionStore,
    /// Index for O(1) lookup of simple positions (no cost) by currency.
    /// Maps currency to position index in the `positions` vector.
    /// Not serialized - rebuilt on demand.
    #[serde(skip)]
    simple_index: FxHashMap<crate::Currency, usize>,
    /// Cache of total units per currency for O(1) `units()` lookups.
    /// Updated incrementally on `add()` and `reduce()`.
    /// Not serialized - rebuilt on demand.
    #[serde(skip)]
    units_cache: FxHashMap<crate::Currency, CurrencyStats>,
}

/// Everything cached per currency: the running unit total, and the per-bucket
/// position counts that make [`Inventory::is_reduced_by`] O(1).
///
/// Deliberately ONE map rather than two. `add` already did a `get` plus an
/// `insert` on the units cache, and hanging a second map off the same key
/// added a third hash of an interned string per posting — which measured as a
/// 4% regression on the cost-spec-free `simple` profiling shape, wiping out
/// part of what the index bought on `investment`. Folded in here, the counts
/// ride along on a lookup that was already happening.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct CurrencyStats {
    /// Running total of units across every lot of this currency.
    total: Decimal,
    /// Position counts by (sign, cost-bearing) bucket.
    counts: SignCounts,
}

/// How many positions of a currency fall in each (sign, cost-bearing) bucket.
///
/// Buckets keyed on `Decimal::is_sign_positive`, which is the exact predicate
/// [`Inventory::is_reduced_by`] uses — note it answers `true` for zero, and
/// the scan it replaces counted empty positions too, so this must as well.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct SignCounts {
    /// Cost-bearing lots whose units are sign-positive.
    cost_positive: u32,
    /// Cost-bearing lots whose units are sign-negative.
    cost_negative: u32,
    /// Cost-less lots whose units are sign-positive.
    simple_positive: u32,
    /// Cost-less lots whose units are sign-negative.
    simple_negative: u32,
}

impl SignCounts {
    /// Count of positions in the bucket opposite to `units_is_positive`.
    const fn opposite(self, units_is_positive: bool, scope: ReductionScope) -> u32 {
        let (cost, simple) = if units_is_positive {
            (self.cost_negative, self.simple_negative)
        } else {
            (self.cost_positive, self.simple_positive)
        };
        match scope {
            // Saturating, not `+`: these are counts of lots and a wrap would
            // read as "no matching lot", which books a reduction as an
            // augmentation and duplicates the lot. Saturation errs the other
            // way, and `> 0` is all the caller asks.
            ReductionScope::AllPositions => cost.saturating_add(simple),
            ReductionScope::CostBearingOnly => cost,
        }
    }

    /// `delta` is `i32` rather than `i64` so it feeds `saturating_add_signed`
    /// directly. The earlier `i64` version ended in `try_into().unwrap_or(0)`,
    /// which turns a caller mistake into a silent no-op — the one outcome that
    /// leaves the counts wrong with nothing to show for it.
    fn bump(&mut self, has_cost: bool, is_positive: bool, delta: i32) {
        debug_assert!(
            delta == 1 || delta == -1,
            "counts move one lot at a time; {delta} means a caller lost track",
        );
        let slot = match (has_cost, is_positive) {
            (true, true) => &mut self.cost_positive,
            (true, false) => &mut self.cost_negative,
            (false, true) => &mut self.simple_positive,
            (false, false) => &mut self.simple_negative,
        };
        // Saturating: an under-count can only make `is_reduced_by` answer
        // "not a reduction" and fall back to augmentation, where a wrapped
        // u32 would claim billions of matching lots.
        *slot = slot.saturating_add_signed(delta);
    }
}

/// Where the positions a cache rebuild is reading came from.
///
/// Only affects whether the one-cost-less-lot-per-currency invariant is
/// ASSERTED. It is a genuine invariant of positions this type built, and a
/// `debug_assert` there earns its keep as an internal-bug tripwire — but a
/// deserialized payload is input, and input must not be able to panic us.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CacheSource {
    /// Positions this inventory produced; the invariant holds.
    Internal,
    /// Positions from outside — a deserialized payload.
    Untrusted,
}

/// Deserialization shape for [`Inventory`]: the persisted field only.
///
/// Exists so `From` can rebuild the derived caches — see the note on
/// `Inventory`. Kept private; the wire format is unchanged (a struct with a
/// `positions` sequence), so this is not a compatibility break.
#[derive(Deserialize)]
struct InventoryWire {
    // NOT `#[serde(default)]`. The derive this replaces made `positions`
    // required, so `{}` was `Err("missing field `positions`")`; defaulting it
    // would quietly accept a malformed payload as an empty inventory.
    positions: Vector<Position>,
}

impl TryFrom<InventoryWire> for Inventory {
    type Error = OverflowError;

    /// `TryFrom`, not `From`: rebuilding the caches sums a currency's positions,
    /// and that sum can overflow on a payload nobody sane wrote.
    ///
    /// `rebuild_index` accumulates with `+=`, which PANICS on `Decimal`
    /// overflow — so two `Decimal::MAX` USD lots aborted inside `Deserialize`
    /// with "Addition overflowed" rather than returning a serde error. Review
    /// catch; a deserialization boundary must not panic on its input, the same
    /// rule that applies to the parser. The rebuild now uses `checked_add` and
    /// the failure arrives as `Err`, which serde reports as a normal
    /// deserialization error.
    fn try_from(wire: InventoryWire) -> Result<Self, Self::Error> {
        let mut inv = Self {
            positions: PositionStore::Owned(wire.positions.into_iter().collect()),
            simple_index: FxHashMap::default(),
            units_cache: FxHashMap::default(),
        };
        // UNTRUSTED: the payload is input, not something this type produced, so
        // it may carry two cost-less lots for one currency — a state the
        // invariant forbids. `rebuild_index`'s `debug_assert` is there to catch
        // an internal bug; reaching it from deserialization would turn a
        // malformed document into a panic at the boundary.
        inv.try_rebuild_index_from(CacheSource::Untrusted)?;
        Ok(inv)
    }
}

impl PartialEq for Inventory {
    fn eq(&self, other: &Self) -> bool {
        // Only compare positions, not the index (which is derived data)
        self.positions.iter().eq(other.positions.iter())
    }
}

impl Eq for Inventory {}

impl Inventory {
    /// Create an empty inventory.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Iterate over all positions.
    ///
    /// Previously returned `&[Position]`; now returns an iterator
    /// because the underlying storage is a tree-based persistent
    /// vector (`imbl::Vector`) that doesn't expose a contiguous slice.
    /// Most callers already iterate — for callers that need
    /// random-access / indexed / `.len()` slice semantics, see
    /// [`Self::position_list`].
    pub fn positions(&self) -> impl Iterator<Item = &Position> + '_ {
        self.positions.iter()
    }

    /// Materialize all positions as a `Vec<&Position>` for slice-style
    /// access (indexing, `.len()`, `.first()`, `.is_empty()`).
    ///
    /// Allocates `O(N)` pointers per call. Callers that only iterate
    /// once should use [`Self::positions`] instead — this is for code
    /// paths that need slice semantics.
    #[must_use]
    pub fn position_list(&self) -> Vec<&Position> {
        self.positions.iter().collect()
    }

    /// Get mutable access to the underlying positions, contiguously.
    ///
    /// Forces the contiguous backing first, so the caller gets a real
    /// `&mut Vec<Position>` with O(1) indexing and amortized O(1) push. If
    /// the inventory was using the structurally-shared backing — the BQL
    /// snapshot representation, see [`Inventory::new_shared`] — that
    /// conversion costs O(M) once and any sharing with earlier snapshots is
    /// dropped for THIS inventory; the snapshots themselves are unaffected.
    ///
    /// (The backing enum is private, so this deliberately describes it in
    /// prose rather than linking: a public doc cannot intra-doc-link a
    /// private item, and `cargo doc -D warnings` rejects it.)
    ///
    /// **Caches are the caller's problem here.** Mutating positions through
    /// this handle leaves `units_cache` — both the running totals and the
    /// sign counts — and `simple_index` describing the OLD contents. Those
    /// drive `units()`, the reduction-vs-augmentation decision in
    /// `is_reduced_by`, and cost-less merging in `add` respectively.
    ///
    /// [`Self::compact`] rebuilds all of them, but note that it ALSO drops
    /// every empty position on the way through. If the caller deliberately
    /// left a zero-unit lot in place, compacting to refresh the caches will
    /// silently remove it — so that is a semantic change, not just a cache
    /// refresh.
    ///
    /// Debug builds catch a missed rebuild through `is_reduced_by`'s
    /// consistency assertion; release builds silently book against a stale
    /// view.
    pub fn positions_mut(&mut self) -> &mut Vec<Position> {
        self.positions.make_owned();
        match &mut self.positions {
            PositionStore::Owned(v) => v,
            PositionStore::Shared(_) => unreachable!("make_owned just ran"),
        }
    }

    /// An inventory whose positions are structurally SHARED.
    ///
    /// For accumulators that are cloned far more often than they are mutated
    /// — BQL's JOURNAL running balance, which emits one snapshot per output
    /// row. Cloning is O(1) and successive snapshots share structure, so N
    /// rows cost O(base + sum of deltas) instead of O(N x base) (#1086).
    ///
    /// Everything else should use [`Inventory::new`]: the default contiguous
    /// backing is what makes booking's `reduce` cheap, and `reduce` converts
    /// to it anyway.
    #[must_use]
    pub fn new_shared() -> Self {
        Self {
            positions: PositionStore::Shared(Vector::new()),
            ..Self::default()
        }
    }

    /// Check if inventory is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.positions.is_empty()
            || self
                .positions
                .iter()
                .all(super::position::Position::is_empty)
    }

    /// Get the number of positions (including empty ones).
    #[must_use]
    pub fn len(&self) -> usize {
        self.positions.len()
    }

    /// Get total units of a currency (ignoring cost lots).
    ///
    /// This sums all positions of the given currency regardless of cost basis.
    /// Uses an internal cache for O(1) lookups.
    #[must_use]
    pub fn units(&self, currency: &str) -> Decimal {
        // Use the cache when it is there. A miss is not a bug: the cache is
        // `#[serde(skip)]`, and while deserialization rebuilds it (the
        // `#[serde(try_from = "InventoryWire"]` on the struct), an inventory
        // built some other way may not have one yet. Recomputing is O(lots)
        // but always right.
        //
        // (This used to point callers at `rebuild_caches()`, which has never
        // existed under that name — `rebuild_index` is the real one, and
        // callers do not need it on the deserialize path any more.)
        self.units_cache.get(currency).map_or_else(
            || {
                // Fallback to computation if cache miss (e.g., after deserialization)
                self.positions
                    .iter()
                    .filter(|p| p.units.currency == currency)
                    .map(|p| p.units.number)
                    .sum()
            },
            |stats| stats.total,
        )
    }

    /// Whether every `add` of `currency` totaling at most `needed` in absolute
    /// value is guaranteed not to overflow.
    ///
    /// `add` overflows at exactly two `checked_add`s: the per-currency running
    /// total, and — for a cost-less position — the single merged lot that
    /// `simple_index` points at. Both operands are bounded here against
    /// `needed`, so a `true` answer means no sequence of adds whose magnitudes
    /// sum to `needed` can overflow either, at any intermediate step: every
    /// partial sum is bounded by the total.
    ///
    /// Conservative by construction — `false` only ever means "cannot prove
    /// it", never "will overflow". Callers use it to skip work that exists
    /// solely to recover from overflow (#1897).
    #[must_use]
    pub fn add_headroom_for(&self, currency: &str, needed: Decimal) -> bool {
        // Enforce the magnitude contract rather than trusting it. A negative
        // `needed` would make the sums below SMALLER and hand back `true` when
        // overflow is possible — and an unsound `true` here means `apply`
        // skips the snapshot it needed, so earlier postings of a failing
        // transaction cannot be rolled back. Cheap insurance on a `pub` method
        // whose failure mode is silent corruption.
        let needed = needed.abs();

        // `units_cache` and `simple_index` are `#[serde(skip)]`, so a
        // deserialized inventory carries its positions with both caches empty
        // until `rebuild_caches` runs. Reading them in that state answers
        // "plenty of room" for an inventory sitting at the ceiling — an
        // unsound `true`, which is the one direction this method must never
        // fail in. Refuse to answer instead. `units()` handles the same gap by
        // recomputing from `positions`; that is O(positions) and this is meant
        // to be O(1), so the conservative answer is the right trade here.
        if self.units_cache.is_empty() && !self.positions.is_empty() {
            return false;
        }

        let fits = |v: Decimal| {
            v.abs()
                .checked_add(needed)
                .is_some_and(|sum| sum <= Decimal::MAX)
        };

        let cached_ok = self
            .units_cache
            .get(currency)
            .map(|s| s.total)
            .is_none_or(fits);
        if !cached_ok {
            return false;
        }
        // Only a cost-less add merges, and `simple_index` names the one lot it
        // would merge into.
        self.simple_index
            .get(currency)
            .and_then(|idx| self.positions.get(*idx))
            .is_none_or(|lot| fits(lot.units.number))
    }

    /// Get all currencies in this inventory.
    #[must_use]
    pub fn currencies(&self) -> Vec<&str> {
        let mut currencies: Vec<&str> = self
            .positions
            .iter()
            .filter(|p| !p.is_empty())
            .map(|p| p.units.currency.as_str())
            .collect();
        currencies.sort_unstable();
        currencies.dedup();
        currencies
    }

    /// Check if the given units would reduce (not augment) this inventory.
    ///
    /// Returns `true` if there's a position with the same currency but opposite
    /// sign, meaning these units would reduce the inventory rather than add to it.
    ///
    /// When `has_cost_spec` is `true`, only positions **with** a cost basis are
    /// considered for reduction matching.  Simple (no-cost) positions are ignored
    /// because they live in a different "cost layer" — a sell-without-cost-spec
    /// that left a negative simple position should not cause a subsequent
    /// cost-bearing augmentation to be misclassified as a reduction.
    /// See: issue #875, beancount#889.
    ///
    /// This is used to determine whether a posting is a sale/reduction or a
    /// purchase/augmentation.
    #[must_use]
    pub fn is_reduced_by(&self, units: &Amount, scope: ReductionScope) -> bool {
        // `units_cache` is `#[serde(skip)]` like `simple_index`. An empty
        // one over non-empty positions means it has not been built yet, and
        // reading it then would answer "not a reduction" for an inventory that
        // holds matching lots — booking the posting as an augmentation and
        // silently creating a duplicate lot. Fall back to the scan, as
        // `units()` does for the same gap.
        if self.units_cache.is_empty() && !self.positions.is_empty() {
            return self.is_reduced_by_scan(units, scope);
        }

        let answer = self.units_cache.get(&units.currency).is_some_and(|stats| {
            stats
                .counts
                .opposite(units.number.is_sign_positive(), scope)
                > 0
        });

        // The index is maintained incrementally by `add` and the reduction
        // commit paths; a missed update is a wrong answer, not a slow one.
        debug_assert_eq!(
            answer,
            self.is_reduced_by_scan(units, scope),
            "the cached sign counts disagree with a scan of positions — some \
             mutation path changed a lot without maintaining them",
        );
        answer
    }

    /// The scan [`Self::is_reduced_by`] replaced, kept as the definition the
    /// index is checked against and as the fallback for an unbuilt index.
    fn is_reduced_by_scan(&self, units: &Amount, scope: ReductionScope) -> bool {
        self.positions.iter().any(|pos| {
            pos.units.currency == units.currency
                && pos.units.number.is_sign_positive() != units.number.is_sign_positive()
                && match scope {
                    ReductionScope::AllPositions => true,
                    ReductionScope::CostBearingOnly => pos.cost.is_some(),
                }
        })
    }

    /// Whether a posting of `units` carrying `cost` would REDUCE this inventory
    /// under `method` — the single source for the reduction-vs-augmentation
    /// decision shared by the booking engine (`BookingEngine::apply`) and the
    /// Late validator's inventory pass.
    ///
    /// A posting reduces only when it carries a cost spec (`cost.is_some()` —
    /// presence of the spec, which includes an empty/unresolved one like `{}`),
    /// the booking method isn't `NONE` (issue #1182 — `NONE` accumulates every
    /// posting as an augmentation, with no lot matching), and the inventory holds
    /// a cost-bearing position of the opposite sign in the same currency
    /// ([`Self::is_reduced_by`] with [`ReductionScope::CostBearingOnly`]). This
    /// gate was previously written byte-for-byte in both crates and the #1182 fix
    /// had to be applied twice.
    #[must_use]
    pub fn is_booking_reduction(
        &self,
        units: &Amount,
        cost: Option<&CostSpec>,
        method: BookingMethod,
    ) -> bool {
        method != BookingMethod::None
            && cost.is_some()
            && self.is_reduced_by(units, ReductionScope::CostBearingOnly)
    }

    /// Get the total book value (cost basis) for a currency.
    ///
    /// Returns the sum of all cost bases for positions of the given currency.
    ///
    /// # Errors
    ///
    /// [`OverflowError`] when a position's book value, or the running
    /// per-currency total, leaves `rust_decimal`'s range.
    pub fn book_value(
        &self,
        units_currency: &str,
    ) -> Result<FxHashMap<crate::Currency, Decimal>, OverflowError> {
        let mut totals: FxHashMap<crate::Currency, Decimal> = FxHashMap::default();

        for pos in self.positions.iter() {
            if pos.units.currency == units_currency {
                // NOT `pos.book_value()`: its `None` conflates "no cost" with
                // "product out of range", and skipping the latter would drop a
                // position from the total silently — the same class of bug as
                // clamping it (#1863).
                let Some(cost) = pos.cost.as_ref() else {
                    continue;
                };
                let overflow = || OverflowError {
                    currency: cost.currency.clone(),
                };
                let book = cost.total_cost(pos.units.number).ok_or_else(overflow)?;
                let slot = totals.entry(book.currency.clone()).or_default();
                *slot = slot.checked_add(book.number).ok_or_else(overflow)?;
            }
        }

        Ok(totals)
    }

    /// Add a position to the inventory.
    ///
    /// For positions without cost, this merges with existing positions
    /// of the same currency using O(1) `HashMap` lookup.
    ///
    /// For positions with cost, this adds as a new lot (O(1)).
    /// Lot aggregation for display purposes is handled separately at output time
    /// (e.g., in the query result formatter).
    ///
    /// # TLA+ Specification
    ///
    /// Implements `AddAmount` action from `Conservation.tla`:
    /// - Invariant: `inventory + totalReduced = totalAdded`
    /// - After add: `totalAdded' = totalAdded + amount`
    ///
    /// See: `spec/tla/Conservation.tla`
    ///
    /// # Errors
    ///
    /// [`OverflowError`] when the running total for this currency leaves
    /// `rust_decimal`'s ~±7.9e28 range. The inventory is left UNCHANGED — the
    /// units cache is only committed once the merge is known to fit, so a
    /// caller that reports the error and moves on does not carry a
    /// half-applied position (#1863).
    pub fn add(&mut self, position: Position) -> Result<(), OverflowError> {
        if position.is_empty() {
            return Ok(());
        }

        let overflow = || OverflowError {
            currency: position.units.currency.clone(),
        };

        // Compute both running totals BEFORE mutating anything, so an overflow
        // leaves the inventory untouched rather than half-updated.
        let cached = self
            .units_cache
            .get(&position.units.currency)
            .map(|s| s.total)
            .unwrap_or_default();
        // Python `decimal` scale semantics, not raw `checked_add` — see
        // `crate::decimal::add_python_scale`. `rust_decimal` returns the other
        // operand untouched when one side is zero, so a running total that
        // passes through zero drops its scale and everything added after it
        // renders one scale narrower. That made a coalesced balance
        // ORDER-DEPENDENT: the same postings in a different order produced
        // `1` or `1.00` for the same money.
        let new_cached = crate::decimal::checked_add_python_scale(cached, position.units.number)
            .ok_or_else(overflow)?;

        let merge_idx = position
            .cost
            .is_none()
            .then(|| self.simple_index.get(&position.units.currency).copied())
            .flatten();
        let merged_units = merge_idx
            .map(|idx| {
                // Same rule as the units cache above — these two must agree,
                // or `units()` and the position itself report different scales
                // for the same currency.
                crate::decimal::checked_add_python_scale(
                    self.positions[idx].units.number,
                    position.units.number,
                )
                .ok_or_else(overflow)
            })
            .transpose()?;

        // Bucket changes, worked out before touching the cache so the whole
        // update lands in ONE lookup below. A cost-less merge can flip the
        // lot's sign (adding -8 to a +3 lot), which moves it between buckets;
        // `is_sign_positive` answers true for zero, matching the predicate
        // `is_reduced_by` uses.
        let vacated = merge_idx.map(|idx| {
            let lot = &self.positions[idx];
            (lot.cost.is_some(), lot.units.number.is_sign_positive())
        });
        let occupied = (
            position.cost.is_some(),
            merged_units
                .unwrap_or(position.units.number)
                .is_sign_positive(),
        );

        // ONE mutable lookup for the total AND the counts. `add` runs once per
        // posting, and the units cache is keyed by an interned string whose
        // `Hash` walks its bytes — this used to be a `get` plus an `insert`,
        // and hanging the counts off a second map made it three hashes per
        // posting, which measured as a regression on ledgers that book no
        // cost specs. `get_mut` first so only a currency's first lot pays for
        // an owned key.
        if let Some(stats) = self.units_cache.get_mut(&position.units.currency) {
            stats.total = new_cached;
            if let Some((had_cost, was_positive)) = vacated {
                stats.counts.bump(had_cost, was_positive, -1);
            }
            stats.counts.bump(occupied.0, occupied.1, 1);
        } else {
            // No entry yet means no lot of this currency has ever been added,
            // so there is nothing to vacate: `merge_idx` came from
            // `simple_index`, which only names a lot that `add` already
            // counted.
            debug_assert!(
                vacated.is_none(),
                "merging into a lot whose currency has no cached entry",
            );
            let mut counts = SignCounts::default();
            counts.bump(occupied.0, occupied.1, 1);
            self.units_cache.insert(
                position.units.currency.clone(),
                CurrencyStats {
                    total: new_cached,
                    counts,
                },
            );
        }

        // For positions without cost, use index for O(1) lookup
        if position.cost.is_none() {
            if let Some(idx) = merge_idx {
                // Merge with existing position
                debug_assert!(self.positions[idx].cost.is_none());
                self.positions[idx].units.number =
                    merged_units.expect("merged_units is Some whenever merge_idx is");
                return Ok(());
            }
            // No existing position - add new one and index it
            let idx = self.positions.len();
            self.simple_index
                .insert(position.units.currency.clone(), idx);
            self.positions.push(position);
            return Ok(());
        }

        // For positions with cost, just add as a new lot.
        // This is O(1) and keeps all lots separate, matching Python beancount behavior.
        // Lot aggregation for display purposes is handled separately in query output.
        self.positions.push(position);
        Ok(())
    }

    /// Adjust `sign_index` for the position currently at `idx` by `delta`.
    ///
    /// Called with `-1` before changing or removing a lot and `+1` after, so
    /// a sign flip lands in the right bucket.
    pub(super) fn sign_index_bump(&mut self, idx: usize, delta: i32) {
        // All three call sites pass an index they just read or wrote, so this
        // is defensive only. Returning rather than panicking keeps a future
        // caller's off-by-one out of the panic path; the counts then disagree
        // with a scan, which `is_reduced_by`'s assertion reports in debug.
        debug_assert!(
            idx < self.positions.len(),
            "sign_index_bump called with out-of-range index {idx}",
        );
        let Some(position) = self.positions.get(idx) else {
            return;
        };
        // Read the two bits the bucket depends on and drop the borrow. Cloning
        // the `Position` here instead — which is what the obvious version does
        // to satisfy the borrow checker — costs an `Arc` bump per currency plus
        // the lot's label on EVERY add, and this runs on the hot path.
        let has_cost = position.cost.is_some();
        let is_positive = position.units.number.is_sign_positive();
        if let Some(stats) = self.units_cache.get_mut(&position.units.currency) {
            stats.counts.bump(has_cost, is_positive, delta);
        }
        // No entry means no lots of this currency have been counted yet, which
        // only happens before `add` records the total. `add` inserts the entry
        // before calling this, and the rebuild path fills both together.
    }

    /// Reduce positions from the inventory using the specified booking method.
    ///
    /// # Arguments
    ///
    /// * `units` - The units to reduce (negative for selling)
    /// * `cost_spec` - Optional cost specification for matching lots
    /// * `method` - The booking method to use
    ///
    /// # Returns
    ///
    /// Returns a `BookingResult` with the matched positions and cost basis,
    /// or a `BookingError` if the reduction cannot be performed.
    ///
    /// # TLA+ Specification
    ///
    /// Implements `ReduceAmount` action from `Conservation.tla`:
    /// - Invariant: `inventory + totalReduced = totalAdded`
    /// - After reduce: `totalReduced' = totalReduced + amount`
    /// - Precondition: `amount <= inventory` (else `InsufficientUnits` error)
    ///
    /// Lot selection follows these TLA+ specs based on `method`:
    /// - `Fifo`: `FIFOCorrect.tla` - Oldest lots first (`selected_date <= all other dates`)
    /// - `Lifo`: `LIFOCorrect.tla` - Newest lots first (`selected_date >= all other dates`)
    /// - `Hifo`: `HIFOCorrect.tla` - Highest cost first (`selected_cost >= all other costs`)
    ///
    /// See: `spec/tla/Conservation.tla`, `spec/tla/FIFOCorrect.tla`, etc.
    pub fn reduce(
        &mut self,
        units: &Amount,
        cost_spec: Option<&CostSpec>,
        method: BookingMethod,
    ) -> Result<BookingResult, BookingError> {
        let spec = cost_spec.cloned().unwrap_or_default();

        // Force a uniquely-owned positions Vector before any reduction mutates
        // it. `self.positions` MAY be structurally shared — BQL snapshots build
        // `Shared` stores via `Inventory::new_shared` — and every reduction
        // method below mutates it in place (via `IndexMut` / `retain`).
        //
        // The sharing comes from BQL, not from booking. Since #2056 the store
        // is a hybrid and `PositionStore::default()` is `Owned(Vec)`, so the
        // booking engine's inventories are owned and any copy of one is a
        // DEEP O(lots) copy rather than an imbl O(1) one. This comment
        // asserted the opposite until #2061, and that wrong claim is a good
        // part of why the copy went unexamined for so long — `Position::clone`
        // was growing 104x for 10x the input on the `investment` profiling
        // shape.
        //
        // `BookingEngine::book` no longer takes such a copy per transaction —
        // it previews through `try_reduce`, which computes from `&self` via
        // the `plan_*` halves in `booking.rs`, and copies only for an account
        // with more than one reducing posting in the same transaction.
        //
        // Mutating a SHARED imbl `Vector` in place drives
        // `imbl-sized-chunks`' copy-on-write into a use-after-free of the
        // interned `Arc<str>` inside `Position` — heap corruption / SIGSEGV on
        // large ledgers with many lot reductions (found by the rich-workload
        // profiler). Rebuilding from cloned positions restores a refcount-1
        // Vector with correct `Arc` refcounting, so in-place mutation below has
        // no shared chunk to corrupt.
        self.positions.make_owned();

        // {*} merge operator: merge all lots into a single weighted-average-cost
        // lot before reducing, regardless of the account's booking method.
        if spec.merge {
            return self.reduce_merge(units);
        }

        match method {
            BookingMethod::Strict => self.reduce_strict(units, &spec),
            BookingMethod::StrictWithSize => self.reduce_strict_with_size(units, &spec),
            BookingMethod::Fifo => self.reduce_fifo(units, &spec),
            BookingMethod::Lifo => self.reduce_lifo(units, &spec),
            BookingMethod::Hifo => self.reduce_hifo(units, &spec),
            BookingMethod::Average => self.reduce_average(units),
            BookingMethod::None => self.reduce_none(units),
        }
    }

    /// Remove all empty positions.
    pub fn compact(&mut self) {
        self.positions.retain(|p| !p.is_empty());
        self.rebuild_index();
    }

    /// Rebuild all caches (`simple_index` and `units_cache`) from positions.
    ///
    /// Called after operations that may invalidate them (`compact`'s retain) and
    /// on deserialization, which is what [`CacheSource`] distinguishes.
    fn rebuild_index(&mut self) {
        // Internal positions came through `add`, which already rejected any
        // sum that would overflow, so this cannot fail. Asserted rather than
        // ignored: a failure here would mean `add`'s check had a hole.
        // Call FIRST, assert on the result. Putting the call inside
        // `debug_assert!` compiles the rebuild itself out of release builds,
        // so `compact` would have left the caches stale — caught by clippy's
        // `debug_assert_with_mut_call`.
        let rebuilt = self.try_rebuild_index_from(CacheSource::Internal);
        debug_assert!(
            rebuilt.is_ok(),
            "internal positions summed past the Decimal range; `add` should \
             have rejected them",
        );
    }

    fn try_rebuild_index_from(&mut self, source: CacheSource) -> Result<(), OverflowError> {
        self.simple_index.clear();
        self.units_cache.clear();

        for (idx, pos) in self.positions.iter_slots() {
            // Update units cache for all positions. Checked, not `+=`:
            // `Decimal`'s `+` panics on overflow, and this runs over payloads.
            //
            // Must apply the SAME Python-scale rule as `add`, not a raw
            // `checked_add`. `units_cache` is `#[serde(skip)]`, so this is the
            // path that reconstructs it after a round-trip; if the two
            // disagreed, an inventory built incrementally and the same
            // inventory deserialized would report different scales for the
            // same money — measured at `1.00` built vs `1` rebuilt, across
            // three cost lots summing through zero. Pinned by
            // `a_round_trip_reports_the_same_scale_as_incremental_adds`.
            let slot = self
                .units_cache
                .entry(pos.units.currency.clone())
                .or_default();
            slot.counts
                .bump(pos.cost.is_some(), pos.units.number.is_sign_positive(), 1);
            slot.total = crate::decimal::checked_add_python_scale(slot.total, pos.units.number)
                .ok_or_else(|| OverflowError {
                    currency: pos.units.currency.clone(),
                })?;

            // Update simple_index only for positions without cost
            if pos.cost.is_none() {
                debug_assert!(
                    source == CacheSource::Untrusted
                        || !self.simple_index.contains_key(&pos.units.currency),
                    "Invariant violated: multiple simple positions for currency {}",
                    pos.units.currency
                );
                // Last-wins on a duplicate, matching the pre-existing behavior
                // of this insert. `units_cache` sums every position either way,
                // so the total stays right; only which lot a later cost-less
                // `add` merges into is affected.
                self.simple_index.insert(pos.units.currency.clone(), idx);
            }
        }
        Ok(())
    }

    /// Merge this inventory with another.
    ///
    /// # Errors
    ///
    /// [`OverflowError`] when a merged running total leaves `rust_decimal`'s
    /// range. `self` keeps the positions merged before the failure.
    pub fn merge(&mut self, other: &Self) -> Result<(), OverflowError> {
        for pos in other.positions.iter() {
            self.add(pos.clone())?;
        }
        Ok(())
    }

    /// Convert inventory to cost basis.
    ///
    /// Returns a new inventory where all positions are converted to their
    /// cost basis. Positions without cost are returned as-is.
    ///
    /// # Errors
    ///
    /// [`OverflowError`] when a `units × cost` product, or the running total
    /// of those products, leaves `rust_decimal`'s range. Note this can fire on
    /// inputs far below the ceiling — the product overflows when neither
    /// operand does.
    pub fn at_cost(&self) -> Result<Self, OverflowError> {
        let mut result = Self::new();

        for pos in self.positions.iter() {
            if pos.is_empty() {
                continue;
            }

            if let Some(cost) = &pos.cost {
                // Convert to cost basis
                let total =
                    pos.units
                        .number
                        .checked_mul(cost.number)
                        .ok_or_else(|| OverflowError {
                            currency: cost.currency.clone(),
                        })?;
                result.add(Position::simple(Amount::new(total, &cost.currency)))?;
            } else {
                // No cost, keep as-is
                result.add(pos.clone())?;
            }
        }

        Ok(result)
    }

    /// Convert inventory to units only.
    ///
    /// Returns a new inventory where all positions have their cost removed,
    /// effectively aggregating by currency only.
    ///
    /// # Errors
    ///
    /// [`OverflowError`] when stripping costs merges lots whose combined units
    /// leave `rust_decimal`'s range.
    pub fn at_units(&self) -> Result<Self, OverflowError> {
        let mut result = Self::new();

        for pos in self.positions.iter() {
            if pos.is_empty() {
                continue;
            }

            // Strip cost, keep only units
            result.add(Position::simple(pos.units.clone()))?;
        }

        Ok(result)
    }
}

/// Sum the units of `currency` across `account` AND all of its sub-accounts,
/// over a map of per-account inventories.
///
/// Beancount's `balance Assets:Bank` assertion — and the pad math that targets
/// it — includes `Assets:Bank:Checking`, `Assets:Bank:Savings`, etc. (verified
/// against `bean-check`: an assertion on a parent passes when the balance is held
/// in a sub-account). Sub-account membership uses [`is_subaccount_or_equal`], so
/// the segment-boundary rule (`Assets:BankAlias` does NOT match `Assets:Bank`)
/// is shared.
///
/// This is the single source for that sum, used by both the booking pad engine
/// and the Late balance validator. They previously computed the pad/assertion
/// difference differently — booking summed only the leaf account
/// (`Inventory::units`) while the validator summed sub-accounts — so a pad
/// targeting a non-leaf account inserted the wrong synthetic amount.
///
/// Returns `None` when the sum leaves `rust_decimal`'s range (`Decimal`'s
/// `Sum` impl panics rather than wrapping). Both callers surface that as a
/// diagnostic on the assertion/pad rather than asserting against a clamped
/// total (#1863).
pub fn sum_account_and_subaccounts<'a, I>(
    inventories: I,
    account: &str,
    currency: &Currency,
) -> Option<Decimal>
where
    I: IntoIterator<Item = (&'a Account, &'a Inventory)>,
{
    inventories
        .into_iter()
        .filter(|(inv_account, _)| is_subaccount_or_equal(inv_account.as_str(), account))
        .try_fold(Decimal::ZERO, |acc, (_, inv)| {
            acc.checked_add(inv.units(currency))
        })
}

impl fmt::Display for Inventory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty() {
            return write!(f, "(empty)");
        }

        // Sort positions alphabetically by currency, then by cost for consistency
        let mut non_empty: Vec<_> = self.positions.iter().filter(|p| !p.is_empty()).collect();
        non_empty.sort_by(|a, b| {
            // First by currency
            let cmp = a.units.currency.cmp(&b.units.currency);
            if cmp != std::cmp::Ordering::Equal {
                return cmp;
            }
            // Then by cost (if present)
            match (&a.cost, &b.cost) {
                (Some(ca), Some(cb)) => ca.number.cmp(&cb.number),
                (Some(_), None) => std::cmp::Ordering::Greater,
                (None, Some(_)) => std::cmp::Ordering::Less,
                (None, None) => std::cmp::Ordering::Equal,
            }
        });

        for (i, pos) in non_empty.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{pos}")?;
        }
        Ok(())
    }
}

impl Inventory {
    /// Build an inventory from positions.
    ///
    /// Replaces the former `FromIterator<Position>` impl, which was removed
    /// deliberately: `from_iter` cannot report failure, so it had to swallow
    /// the overflow from [`Self::add`] and hand back an inventory holding a
    /// wrong total with nothing to indicate it (#1863). A `collect()` that can
    /// silently lie is worse than no `collect()`.
    ///
    /// # Errors
    ///
    /// [`OverflowError`] when a running total leaves `rust_decimal`'s range.
    pub fn try_from_positions<I>(iter: I) -> Result<Self, OverflowError>
    where
        I: IntoIterator<Item = Position>,
    {
        let mut inv = Self::new();
        for pos in iter {
            inv.add(pos)?;
        }
        Ok(inv)
    }
}

#[cfg(test)]
mod tests {

    /// A deserialized inventory must not be reported as having headroom it
    /// does not have.
    ///
    /// The caches are `#[serde(skip)]`, so a round-trip once left `positions`
    /// populated and both caches empty. Deserialization now rebuilds them, so
    /// this passes because the cache is CORRECT rather than because
    /// `add_headroom_for` refuses to read an empty one. Both are checked: the
    /// defensive refusal stays as the second line of defense for any other way
    /// an inventory might reach that state (review catch on #1898).
    /// `new_shared` must actually produce the shared backing, and a serde
    /// round-trip must land back in `Owned`.
    ///
    /// Both are load-bearing and neither is visible from the public API: the
    /// backing is a private enum, so nothing outside this module can observe
    /// which one an inventory holds. Without this test, `new_shared` could
    /// quietly return the contiguous backing and the only symptom would be
    /// BQL's JOURNAL memory going from 31 MB back to 395 MB on a large
    /// ledger — a regression no unit test would catch. Copilot's catch on
    /// #2056.
    #[test]
    fn new_shared_is_shared_and_a_round_trip_is_owned() {
        let mut shared = Inventory::new_shared();
        assert!(
            matches!(shared.positions, PositionStore::Shared(_)),
            "new_shared must use the structurally-shared backing",
        );

        // Adding must not silently convert it — the per-row snapshot in BQL
        // adds to this inventory between every clone.
        shared
            .add(Position::simple(Amount::new(dec!(5), "USD")))
            .expect("fits");
        assert!(
            matches!(shared.positions, PositionStore::Shared(_)),
            "add must keep the shared backing; converting here would restore \
             the O(rows x lots) blow-up #1086 is about",
        );

        // ...but a reduction does convert, deliberately: it mutates heavily
        // and wants contiguous storage.
        let mut reduced = Inventory::new_shared();
        reduced
            .add(Position::simple(Amount::new(dec!(5), "USD")))
            .expect("fits");
        let _ = reduced.reduce(&Amount::new(dec!(-2), "USD"), None, BookingMethod::None);
        assert!(
            matches!(reduced.positions, PositionStore::Owned(_)),
            "reduce must switch to the contiguous backing",
        );

        // The default constructor is contiguous.
        assert!(matches!(
            Inventory::new().positions,
            PositionStore::Owned(_)
        ));

        // Serde carries a plain sequence and lands in `Owned`.
        let json = serde_json::to_string(&shared).expect("serializes");
        let back: Inventory = serde_json::from_str(&json).expect("deserializes");
        assert!(
            matches!(back.positions, PositionStore::Owned(_)),
            "a round-trip lands in the contiguous backing",
        );
        assert_eq!(back.units("USD"), dec!(5), "and preserves the positions");
    }

    #[test]
    fn a_deserialized_inventory_refuses_to_claim_headroom() {
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(Decimal::MAX, "USD")))
            .expect("one MAX position fits");
        assert!(!inv.add_headroom_for("USD", Decimal::ONE));

        let round_tripped: Inventory =
            serde_json::from_str(&serde_json::to_string(&inv).expect("serialize"))
                .expect("deserialize");

        assert!(
            !round_tripped.positions.is_empty(),
            "the positions survive the round-trip"
        );
        assert!(
            !round_tripped.units_cache.is_empty(),
            "and so do the caches now — deserialization rebuilds them"
        );

        assert!(
            !round_tripped.add_headroom_for("USD", Decimal::ONE),
            "the inventory still holds Decimal::MAX"
        );
    }

    /// A payload the type could not have produced must not panic us.
    ///
    /// Two cost-less lots for one currency violate the invariant
    /// `rebuild_index` asserts. That assert is a worthwhile internal-bug
    /// tripwire, but rebuilding on deserialization put it in reach of INPUT:
    /// this exact document panicked a debug build with "Invariant violated:
    /// multiple simple positions for currency USD". Caught reviewing the
    /// rebuild change, not present before it.
    ///
    /// Behavior matches what the plain derive did — the total is the sum, the
    /// lots are preserved — so nothing about malformed input changed except
    /// that the caches are now correct for it.
    #[test]
    fn a_payload_violating_the_lot_invariant_does_not_panic() {
        let json = r#"{"positions":[
            {"units":{"number":"100","currency":"USD"},"cost":null},
            {"units":{"number":"5","currency":"USD"},"cost":null}]}"#;
        let inv: Inventory = serde_json::from_str(json).expect("malformed input still loads");
        assert_eq!(inv.units("USD"), dec!(105), "the total sums every lot");
        assert_eq!(
            inv.positions().count(),
            2,
            "the lots are preserved as given"
        );
    }

    /// A payload whose positions sum past the `Decimal` range is an ERROR,
    /// not a panic.
    ///
    /// Rebuilding the caches sums each currency's positions, and the rebuild
    /// used `+=`, which panics on `Decimal` overflow. Running it on
    /// deserialization put that inside `Deserialize`: two `Decimal::MAX` USD
    /// lots aborted with "Addition overflowed" instead of returning a serde
    /// error — a denial of service on any embedder deserializing untrusted input. Review
    /// catch on the rebuild change; the deep review that found the
    /// `debug_assert` panic missed this second one.
    ///
    /// Two lots are needed, and the first must carry a cost: a second cost-less
    /// lot for the same currency would be a different (also-tested) malformed
    /// shape, and the sum is what is being exercised here.
    #[test]
    fn a_payload_that_overflows_the_total_is_an_error_not_a_panic() {
        let max = Decimal::MAX.to_string();
        let json = format!(
            r#"{{"positions":[
                {{"units":{{"number":"{max}","currency":"USD"}},
                  "cost":{{"number":"1","currency":"EUR","date":null,"label":null}}}},
                {{"units":{{"number":"{max}","currency":"USD"}},"cost":null}}]}}"#
        );
        let err = serde_json::from_str::<Inventory>(&json)
            .expect_err("a total past the Decimal range cannot be represented");
        // `OverflowError`'s own wording, which serde surfaces verbatim — so
        // this also pins that the error reaching the caller is the domain one
        // rather than a generic "invalid value".
        assert!(
            err.to_string().contains("exceeds the representable range"),
            "expected the USD overflow error, got: {err}",
        );
    }

    /// `positions` stays REQUIRED.
    ///
    /// The derive this replaced made it so, and routing deserialization through
    /// a wire struct is exactly the kind of change that silently relaxes it —
    /// a stray `#[serde(default)]` turns a malformed document into an empty
    /// inventory. It did, in the first draft of this change.
    #[test]
    fn a_payload_without_positions_is_rejected() {
        let err = serde_json::from_str::<Inventory>("{}")
            .expect_err("an inventory without positions is malformed");
        assert!(
            err.to_string().contains("missing field"),
            "expected a missing-field error, got: {err}",
        );
    }

    /// Mutating a deserialized inventory must not corrupt it.
    ///
    /// This is the case the rebuild exists for. `add` trusts both caches: it
    /// reads `units_cache.get(..).unwrap_or_default()` as the running total and
    /// `simple_index` as the lot to merge into. With both empty it read 0 for an
    /// inventory already holding 100 USD, wrote that back as the new total, and
    /// appended a second cost-less USD lot instead of merging — so a round-tripped
    /// 100 USD inventory answered `units("USD") == 5` after adding 5, holding two
    /// lots where the type's own invariant allows one.
    ///
    /// `units()` and `add_headroom_for` both survived that state on their own —
    /// one recomputes, the other refuses — which is exactly why it went
    /// unnoticed: the read paths were guarded and the WRITE path was not.
    #[test]
    fn adding_to_a_deserialized_inventory_keeps_the_running_total() {
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(100), "USD")))
            .expect("fits");

        let mut round_tripped: Inventory =
            serde_json::from_str(&serde_json::to_string(&inv).expect("serialize"))
                .expect("deserialize");
        assert_eq!(
            round_tripped.units("USD"),
            dec!(100),
            "the round-trip preserves the total"
        );

        round_tripped
            .add(Position::simple(Amount::new(dec!(5), "USD")))
            .expect("fits");

        assert_eq!(
            round_tripped.units("USD"),
            dec!(105),
            "add must extend the existing total, not replace it"
        );
        assert_eq!(
            round_tripped.positions().count(),
            1,
            "a cost-less add merges into the existing lot rather than appending"
        );
    }

    /// `add_headroom_for` treats `needed` as a magnitude, whatever sign it
    /// arrives with.
    ///
    /// A negative `needed` would make the internal sums smaller and return
    /// `true` where overflow is possible. `apply` would then skip the snapshot
    /// it needed, leaving a failing transaction's earlier postings applied —
    /// silent corruption. Not reachable from the in-tree caller, which sums
    /// absolute values, but this is a `pub` method (review catch on #1898).
    #[test]
    fn add_headroom_for_reads_needed_as_a_magnitude() {
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(Decimal::MAX, "USD")))
            .expect("one MAX position fits");

        assert!(
            !inv.add_headroom_for("USD", Decimal::ONE),
            "at the ceiling, there is no room for one more unit"
        );
        assert!(
            !inv.add_headroom_for("USD", -Decimal::ONE),
            "and a negatively-signed magnitude must not manufacture room"
        );
        assert_eq!(
            inv.add_headroom_for("USD", Decimal::ONE),
            inv.add_headroom_for("USD", -Decimal::ONE),
            "the sign of `needed` cannot change the answer"
        );
    }

    use super::*;
    use crate::Cost;
    use crate::NaiveDate;
    use rust_decimal_macros::dec;

    fn date(year: i32, month: u32, day: u32) -> NaiveDate {
        crate::naive_date(year, month, day).unwrap()
    }

    #[test]
    fn test_empty_inventory() {
        let inv = Inventory::new();
        assert!(inv.is_empty());
        assert_eq!(inv.len(), 0);
    }

    #[test]
    fn test_add_simple() {
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(100), "USD")))
            .expect("fixture fits in Decimal");

        assert!(!inv.is_empty());
        assert_eq!(inv.units("USD"), dec!(100));
    }

    #[test]
    fn test_add_merge_simple() {
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(100), "USD")))
            .expect("fixture fits in Decimal");
        inv.add(Position::simple(Amount::new(dec!(50), "USD")))
            .expect("fixture fits in Decimal");

        // Should merge into one position
        assert_eq!(inv.len(), 1);
        assert_eq!(inv.units("USD"), dec!(150));
    }

    #[test]
    fn test_add_with_cost_no_merge() {
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(160.00), "USD").with_date(date(2024, 1, 15));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost2))
            .expect("fixture fits in Decimal");

        // Should NOT merge - different costs
        assert_eq!(inv.len(), 2);
        assert_eq!(inv.units("AAPL"), dec!(15));
    }

    #[test]
    fn test_currencies() {
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(100), "USD")))
            .expect("fixture fits in Decimal");
        inv.add(Position::simple(Amount::new(dec!(50), "EUR")))
            .expect("fixture fits in Decimal");
        inv.add(Position::simple(Amount::new(dec!(10), "AAPL")))
            .expect("fixture fits in Decimal");

        let currencies = inv.currencies();
        assert_eq!(currencies.len(), 3);
        assert!(currencies.contains(&"USD"));
        assert!(currencies.contains(&"EUR"));
        assert!(currencies.contains(&"AAPL"));
    }

    #[test]
    fn test_reduce_strict_unique() {
        let mut inv = Inventory::new();
        let cost = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost))
            .expect("fixture fits in Decimal");

        let result = inv
            .reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Strict)
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(5));
        assert!(result.cost_basis.is_some());
        assert_eq!(result.cost_basis.unwrap().number, dec!(750.00)); // 5 * 150
    }

    #[test]
    fn test_reduce_strict_multiple_match_with_different_costs_is_ambiguous() {
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(160.00), "USD").with_date(date(2024, 1, 15));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost2))
            .expect("fixture fits in Decimal");

        // Per Python beancount: a wildcard reduction (`-3 AAPL` with no cost
        // spec) against an inventory with lots at different costs is
        // genuinely ambiguous and must error. Issue #737.
        let result = inv.reduce(&Amount::new(dec!(-3), "AAPL"), None, BookingMethod::Strict);

        assert!(
            matches!(result, Err(BookingError::AmbiguousMatch { .. })),
            "expected AmbiguousMatch, got {result:?}"
        );
        // Inventory unchanged after a failed reduction
        assert_eq!(inv.units("AAPL"), dec!(15));
    }

    #[test]
    fn test_reduce_strict_multiple_match_with_identical_costs_uses_fifo() {
        let mut inv = Inventory::new();

        // Two lots with identical cost — interchangeable, so FIFO is fine.
        let cost = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 1));

        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            cost.clone(),
        ))
        .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost))
            .expect("fixture fits in Decimal");

        let result = inv
            .reduce(&Amount::new(dec!(-3), "AAPL"), None, BookingMethod::Strict)
            .expect("identical lots should fall back to FIFO without error");

        assert_eq!(inv.units("AAPL"), dec!(12));
        assert_eq!(result.cost_basis.unwrap().number, dec!(450.00));
    }

    #[test]
    fn test_reduce_strict_multiple_match_different_dates_same_cost_uses_fifo() {
        let mut inv = Inventory::new();

        // Two lots at the same cost number but different acquisition dates.
        // The user's cost spec could not have constrained the date without
        // naming it, so the lots are interchangeable for the spec — FIFO.
        let cost1 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 15));
        let cost2 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 2, 15));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2))
            .expect("fixture fits in Decimal");

        let result = inv
            .reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Strict)
            .expect("same cost number, different dates should fall back to FIFO");

        assert_eq!(inv.units("AAPL"), dec!(15));
        // Reduced from the first (oldest) lot at 150.00 USD: 5 * 150 = 750.
        assert_eq!(result.cost_basis.unwrap().number, dec!(750.00));
    }

    #[test]
    fn test_reduce_strict_multiple_match_total_match_exception() {
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(160.00), "USD").with_date(date(2024, 1, 15));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost2))
            .expect("fixture fits in Decimal");

        // Selling exactly the entire inventory (10 + 5 = 15) is unambiguous
        // even with mixed costs — the user is liquidating the position.
        let result = inv
            .reduce(&Amount::new(dec!(-15), "AAPL"), None, BookingMethod::Strict)
            .expect("total-match exception should accept a full liquidation");

        assert_eq!(inv.units("AAPL"), dec!(0));
        // Cost basis = 10*150 + 5*160 = 1500 + 800 = 2300
        assert_eq!(result.cost_basis.unwrap().number, dec!(2300.00));
    }

    #[test]
    fn test_reduce_strict_with_spec() {
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(160.00), "USD").with_date(date(2024, 1, 15));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost2))
            .expect("fixture fits in Decimal");

        // Reducing with cost spec should work
        let spec = CostSpec::empty().with_date(date(2024, 1, 1));
        let result = inv
            .reduce(
                &Amount::new(dec!(-3), "AAPL"),
                Some(&spec),
                BookingMethod::Strict,
            )
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(12)); // 7 + 5
        assert_eq!(result.cost_basis.unwrap().number, dec!(450.00)); // 3 * 150
    }

    #[test]
    fn test_reduce_fifo() {
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 2, 1));
        let cost3 = Cost::new(dec!(200.00), "USD").with_date(date(2024, 3, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost3))
            .expect("fixture fits in Decimal");

        // FIFO should reduce from oldest (cost 100) first
        let result = inv
            .reduce(&Amount::new(dec!(-15), "AAPL"), None, BookingMethod::Fifo)
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(15));
        // Cost basis: 10 * 100 + 5 * 150 = 1000 + 750 = 1750
        assert_eq!(result.cost_basis.unwrap().number, dec!(1750.00));
    }

    #[test]
    fn test_reduce_lifo() {
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 2, 1));
        let cost3 = Cost::new(dec!(200.00), "USD").with_date(date(2024, 3, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost3))
            .expect("fixture fits in Decimal");

        // LIFO should reduce from newest (cost 200) first
        let result = inv
            .reduce(&Amount::new(dec!(-15), "AAPL"), None, BookingMethod::Lifo)
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(15));
        // Cost basis: 10 * 200 + 5 * 150 = 2000 + 750 = 2750
        assert_eq!(result.cost_basis.unwrap().number, dec!(2750.00));
    }

    #[test]
    fn test_reduce_insufficient() {
        let mut inv = Inventory::new();
        let cost = Cost::new(dec!(150.00), "USD");
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost))
            .expect("fixture fits in Decimal");

        let result = inv.reduce(&Amount::new(dec!(-15), "AAPL"), None, BookingMethod::Fifo);

        assert!(matches!(
            result,
            Err(BookingError::InsufficientUnits { .. })
        ));
    }

    #[test]
    fn test_book_value() {
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(100.00), "USD");
        let cost2 = Cost::new(dec!(150.00), "USD");

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost2))
            .expect("fixture fits in Decimal");

        let book = inv.book_value("AAPL").expect("fixture fits in Decimal");
        assert_eq!(book.get("USD"), Some(&dec!(1750.00))); // 10*100 + 5*150
    }

    #[test]
    fn test_display() {
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(100), "USD")))
            .expect("fixture fits in Decimal");

        let s = format!("{inv}");
        assert!(s.contains("100 USD"));
    }

    #[test]
    fn test_display_empty() {
        let inv = Inventory::new();
        assert_eq!(format!("{inv}"), "(empty)");
    }

    #[test]
    fn test_from_iterator() {
        let positions = vec![
            Position::simple(Amount::new(dec!(100), "USD")),
            Position::simple(Amount::new(dec!(50), "USD")),
        ];

        let inv = Inventory::try_from_positions(positions).expect("fixture fits in Decimal");
        assert_eq!(inv.units("USD"), dec!(150));
    }

    #[test]
    fn test_add_costed_positions_kept_separate() {
        // Costed positions are kept as separate lots for O(1) add performance.
        // Aggregation happens at display time (in query output).
        let mut inv = Inventory::new();

        let cost = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 1));

        // Buy 10 shares
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            cost.clone(),
        ))
        .expect("fixture fits in Decimal");
        assert_eq!(inv.len(), 1);
        assert_eq!(inv.units("AAPL"), dec!(10));

        // Sell 10 shares - kept as separate lot for tracking
        inv.add(Position::with_cost(Amount::new(dec!(-10), "AAPL"), cost))
            .expect("fixture fits in Decimal");
        assert_eq!(inv.len(), 2); // Both lots kept
        assert_eq!(inv.units("AAPL"), dec!(0)); // Net units still zero
    }

    /// A deserialized inventory must report the same scale as one built by
    /// incremental `add`s.
    ///
    /// `units_cache` is `#[serde(skip)]`, so `try_rebuild_index_from` is what
    /// reconstructs it after a round-trip. That rebuild re-sums the positions;
    /// if it used a raw `checked_add` while `add` used the Python scale rule,
    /// the two would part company the moment the running sum crossed zero —
    /// the same money reporting `1.00` from one path and `1` from the other,
    /// silently, depending only on whether it had been serialized.
    ///
    /// Needs COST-BEARING lots. Cost-less positions coalesce into a single
    /// position, and one position cannot cross zero during the rebuild, so a
    /// simpler fixture passes either way and pins nothing.
    #[test]
    fn a_round_trip_reports_the_same_scale_as_incremental_adds() {
        let mut inv = Inventory::new();
        let lots = [
            (
                dec!(2.00),
                Cost::new(dec!(10.00), "USD").with_date(date(2024, 1, 1)),
            ),
            (
                dec!(-2.00),
                Cost::new(dec!(11.00), "USD").with_date(date(2024, 1, 2)),
            ),
            (
                dec!(1),
                Cost::new(dec!(12.00), "USD").with_date(date(2024, 1, 3)),
            ),
        ];
        for (units, cost) in lots {
            inv.add(Position::with_cost(Amount::new(units, "SH"), cost))
                .expect("fixture fits in Decimal");
        }

        let built = inv.units("SH").to_string();
        assert_eq!(built, "1.00", "the incrementally-built total");

        let json = serde_json::to_string(&inv).expect("serializes");
        let round_tripped: Inventory = serde_json::from_str(&json).expect("deserializes");
        assert_eq!(
            round_tripped.units("SH").to_string(),
            built,
            "a serde round-trip must not change the reported scale",
        );
    }

    /// Coalescing must not make a balance depend on the order it was built in.
    ///
    /// `rust_decimal` returns the other operand untouched when one side is
    /// zero, so a running total that passes through zero loses its scale and
    /// every later addend renders one scale narrower. The two inventories
    /// below hold the SAME multiset of amounts in a different order.
    ///
    /// Asserts on `to_string()`, not on `Decimal` equality: `==` compares
    /// value and ignores scale (`dec!(1) == dec!(1.00)`), so a value-level
    /// assertion here would pass against the bug it is pinning.
    #[test]
    fn coalescing_is_independent_of_the_order_amounts_arrive_in() {
        // Passes through 0.00 (scale 2), then takes a scale-0 addend.
        let zero_crossing_first = [dec!(-2.00), dec!(2.00), dec!(-1)];
        // Same amounts, no zero crossing before the scale-0 addend.
        let zero_crossing_last = [dec!(-1), dec!(-2.00), dec!(2.00)];

        let build = |amounts: &[Decimal]| {
            let mut inv = Inventory::new();
            for n in amounts {
                inv.add(Position::simple(Amount::new(*n, "USD")))
                    .expect("fixture fits in Decimal");
            }
            inv
        };

        let a = build(&zero_crossing_first);
        let b = build(&zero_crossing_last);

        // The merged POSITION.
        assert_eq!(
            a.positions()
                .next()
                .expect("one position")
                .units
                .number
                .to_string(),
            "-1.00",
            "a total that passed through zero must keep the widest scale",
        );
        assert_eq!(
            b.positions()
                .next()
                .expect("one position")
                .units
                .number
                .to_string(),
            "-1.00",
        );

        // And the units CACHE, which is maintained separately and would
        // otherwise disagree with the position it summarizes.
        assert_eq!(a.units("USD").to_string(), "-1.00");
        assert_eq!(b.units("USD").to_string(), "-1.00");
    }

    #[test]
    fn test_add_costed_positions_net_units() {
        // Verify that units() correctly sums across all lots
        let mut inv = Inventory::new();

        let cost = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 1));

        // Buy 10 shares
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            cost.clone(),
        ))
        .expect("fixture fits in Decimal");

        // Sell 3 shares - kept as separate lot
        inv.add(Position::with_cost(Amount::new(dec!(-3), "AAPL"), cost))
            .expect("fixture fits in Decimal");
        assert_eq!(inv.len(), 2); // Both lots kept
        assert_eq!(inv.units("AAPL"), dec!(7)); // Net units correct
    }

    #[test]
    fn test_add_no_cancel_different_cost() {
        // Test that different costs don't cancel
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(160.00), "USD").with_date(date(2024, 1, 15));

        // Buy 10 shares at 150
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1))
            .expect("fixture fits in Decimal");

        // Sell 5 shares at 160 - should NOT cancel (different cost)
        inv.add(Position::with_cost(Amount::new(dec!(-5), "AAPL"), cost2))
            .expect("fixture fits in Decimal");

        // Should have two separate lots
        assert_eq!(inv.len(), 2);
        assert_eq!(inv.units("AAPL"), dec!(5)); // 10 - 5 = 5 total
    }

    #[test]
    fn test_add_no_cancel_same_sign() {
        // Test that same-sign positions don't merge even with same cost
        let mut inv = Inventory::new();

        let cost = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 1));

        // Buy 10 shares
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            cost.clone(),
        ))
        .expect("fixture fits in Decimal");

        // Buy 5 more shares with same cost - should NOT merge
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost))
            .expect("fixture fits in Decimal");

        // Should have two separate lots (different acquisitions)
        assert_eq!(inv.len(), 2);
        assert_eq!(inv.units("AAPL"), dec!(15));
    }

    #[test]
    fn test_merge_keeps_lots_separate() {
        // Test that merge keeps costed lots separate (aggregation at display time)
        let mut inv1 = Inventory::new();
        let mut inv2 = Inventory::new();

        let cost = Cost::new(dec!(150.00), "USD").with_date(date(2024, 1, 1));

        // inv1: buy 10 shares
        inv1.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            cost.clone(),
        ))
        .expect("fixture fits in Decimal");

        // inv2: sell 10 shares
        inv2.add(Position::with_cost(Amount::new(dec!(-10), "AAPL"), cost))
            .expect("fixture fits in Decimal");

        // Merge keeps both lots, net units is zero
        inv1.merge(&inv2).expect("fixture fits in Decimal");
        assert_eq!(inv1.len(), 2); // Both lots preserved
        assert_eq!(inv1.units("AAPL"), dec!(0)); // Net units correct
    }

    // ====================================================================
    // Phase 2: Additional Coverage Tests for Booking Methods
    // ====================================================================

    #[test]
    fn test_hifo_with_tie_breaking() {
        // When multiple lots have the same cost, HIFO should use insertion order
        let mut inv = Inventory::new();

        // Three lots with same cost but different dates
        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 2, 1));
        let cost3 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 3, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost3))
            .expect("fixture fits in Decimal");

        // HIFO with tied costs should reduce in some deterministic order
        let result = inv
            .reduce(&Amount::new(dec!(-15), "AAPL"), None, BookingMethod::Hifo)
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(15));
        // All at same cost, so 15 * 100 = 1500
        assert_eq!(result.cost_basis.unwrap().number, dec!(1500.00));
    }

    #[test]
    fn test_hifo_with_different_costs() {
        // HIFO should reduce highest cost lots first
        let mut inv = Inventory::new();

        let cost_low = Cost::new(dec!(50.00), "USD").with_date(date(2024, 1, 1));
        let cost_mid = Cost::new(dec!(100.00), "USD").with_date(date(2024, 2, 1));
        let cost_high = Cost::new(dec!(200.00), "USD").with_date(date(2024, 3, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost_low))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost_mid))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            cost_high,
        ))
        .expect("fixture fits in Decimal");

        // Reduce 15 shares - should take from highest cost (200) first
        let result = inv
            .reduce(&Amount::new(dec!(-15), "AAPL"), None, BookingMethod::Hifo)
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(15));
        // 10 * 200 + 5 * 100 = 2000 + 500 = 2500
        assert_eq!(result.cost_basis.unwrap().number, dec!(2500.00));
    }

    #[test]
    fn test_average_booking_with_pre_existing_positions() {
        let mut inv = Inventory::new();

        // Add two lots with different costs
        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(200.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2))
            .expect("fixture fits in Decimal");

        // Total: 20 shares, total cost = 10*100 + 10*200 = 3000, avg = 150/share
        // Reduce 5 shares using AVERAGE
        let result = inv
            .reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Average)
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(15));
        // Cost basis for 5 shares at average 150 = 750
        assert_eq!(result.cost_basis.unwrap().number, dec!(750.00));
    }

    #[test]
    fn test_average_booking_reduces_all() {
        let mut inv = Inventory::new();

        let cost = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost))
            .expect("fixture fits in Decimal");

        // Reduce all shares
        let result = inv
            .reduce(
                &Amount::new(dec!(-10), "AAPL"),
                None,
                BookingMethod::Average,
            )
            .unwrap();

        assert!(inv.is_empty() || inv.units("AAPL").is_zero());
        assert_eq!(result.cost_basis.unwrap().number, dec!(1000.00));
    }

    #[test]
    fn test_none_booking_augmentation() {
        // NONE booking with same-sign amounts should augment, not reduce
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(100), "USD")))
            .expect("fixture fits in Decimal");

        // Adding more (same sign) - this is an augmentation
        let result = inv
            .reduce(&Amount::new(dec!(50), "USD"), None, BookingMethod::None)
            .unwrap();

        assert_eq!(inv.units("USD"), dec!(150));
        assert!(result.matched.is_empty()); // No lots matched for augmentation
        assert!(result.cost_basis.is_none());
    }

    #[test]
    fn test_none_booking_reduction() {
        // NONE booking with opposite-sign should reduce
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(100), "USD")))
            .expect("fixture fits in Decimal");

        let result = inv
            .reduce(&Amount::new(dec!(-30), "USD"), None, BookingMethod::None)
            .unwrap();

        assert_eq!(inv.units("USD"), dec!(70));
        assert!(!result.matched.is_empty());
    }

    #[test]
    fn test_none_booking_shorts_past_zero() {
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(100), "USD")))
            .expect("fixture fits in Decimal");

        // NONE performs no booking: reducing past the balance shorts instead
        // of erroring (#1686 — previously InsufficientUnits, inconsistent
        // with the zero-balance case, NONECorrect.tla, and beancount NONE).
        let result = inv.reduce(&Amount::new(dec!(-150), "USD"), None, BookingMethod::None);

        assert!(result.is_ok(), "NONE must allow shorting: {result:?}");
        assert_eq!(inv.units("USD"), dec!(-50));
    }

    #[test]
    fn test_booking_error_no_matching_lot() {
        let mut inv = Inventory::new();

        // Add a lot with specific cost
        let cost = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost))
            .expect("fixture fits in Decimal");

        // Try to reduce with a cost spec that doesn't match
        let wrong_spec = CostSpec::empty().with_date(date(2024, 12, 31));
        let result = inv.reduce(
            &Amount::new(dec!(-5), "AAPL"),
            Some(&wrong_spec),
            BookingMethod::Strict,
        );

        assert!(matches!(result, Err(BookingError::NoMatchingLot { .. })));
    }

    #[test]
    fn test_booking_error_insufficient_units() {
        let mut inv = Inventory::new();

        let cost = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost))
            .expect("fixture fits in Decimal");

        // Try to reduce more than available
        let result = inv.reduce(&Amount::new(dec!(-20), "AAPL"), None, BookingMethod::Fifo);

        match result {
            Err(BookingError::InsufficientUnits {
                requested,
                available,
                ..
            }) => {
                assert_eq!(requested, dec!(20));
                assert_eq!(available, dec!(10));
            }
            _ => panic!("Expected InsufficientUnits error"),
        }
    }

    #[test]
    fn test_strict_with_size_exact_match() {
        let mut inv = Inventory::new();

        // Add two lots with same cost but different sizes
        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost2))
            .expect("fixture fits in Decimal");

        // Reduce exactly 5 - should match the 5-share lot
        let result = inv
            .reduce(
                &Amount::new(dec!(-5), "AAPL"),
                None,
                BookingMethod::StrictWithSize,
            )
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(10));
        assert_eq!(result.cost_basis.unwrap().number, dec!(500.00));
    }

    #[test]
    fn test_strict_with_size_total_match() {
        let mut inv = Inventory::new();

        // Add two lots
        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost2))
            .expect("fixture fits in Decimal");

        // Reduce exactly 15 (total) - should succeed via total match exception
        let result = inv
            .reduce(
                &Amount::new(dec!(-15), "AAPL"),
                None,
                BookingMethod::StrictWithSize,
            )
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(0));
        assert_eq!(result.cost_basis.unwrap().number, dec!(1500.00));
    }

    #[test]
    fn test_strict_with_size_ambiguous() {
        let mut inv = Inventory::new();

        // Add two lots of same size and cost
        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2))
            .expect("fixture fits in Decimal");

        // Reduce 7 shares - doesn't match either lot exactly, not total
        let result = inv.reduce(
            &Amount::new(dec!(-7), "AAPL"),
            None,
            BookingMethod::StrictWithSize,
        );

        assert!(matches!(result, Err(BookingError::AmbiguousMatch { .. })));
    }

    #[test]
    fn test_short_position() {
        // Test short selling (negative positions)
        let mut inv = Inventory::new();

        // Short 10 shares
        let cost = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        inv.add(Position::with_cost(Amount::new(dec!(-10), "AAPL"), cost))
            .expect("fixture fits in Decimal");

        assert_eq!(inv.units("AAPL"), dec!(-10));
        assert!(!inv.is_empty());
    }

    #[test]
    fn test_at_cost() {
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost2))
            .expect("fixture fits in Decimal");
        inv.add(Position::simple(Amount::new(dec!(100), "USD")))
            .expect("fixture fits in Decimal");

        let at_cost = inv.at_cost().expect("fixture fits in Decimal");

        // AAPL converted: 10*100 + 5*150 = 1000 + 750 = 1750 USD
        // Plus 100 USD simple position = 1850 USD total
        assert_eq!(at_cost.units("USD"), dec!(1850));
        assert_eq!(at_cost.units("AAPL"), dec!(0)); // No AAPL in cost view
    }

    #[test]
    fn test_at_units() {
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost2))
            .expect("fixture fits in Decimal");

        let at_units = inv.at_units().expect("fixture fits in Decimal");

        // All AAPL lots merged
        assert_eq!(at_units.units("AAPL"), dec!(15));
        // Should only have one position after aggregation
        assert_eq!(at_units.len(), 1);
    }

    #[test]
    fn test_add_empty_position() {
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(0), "USD")))
            .expect("fixture fits in Decimal");

        assert!(inv.is_empty());
        assert_eq!(inv.len(), 0);
    }

    #[test]
    fn test_compact() {
        let mut inv = Inventory::new();

        let cost = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost))
            .expect("fixture fits in Decimal");

        // Reduce all
        inv.reduce(&Amount::new(dec!(-10), "AAPL"), None, BookingMethod::Fifo)
            .unwrap();

        // Compact to remove empty positions
        inv.compact();
        assert!(inv.is_empty());
        assert_eq!(inv.len(), 0);
    }

    #[test]
    fn test_booking_method_from_str() {
        assert_eq!(
            BookingMethod::from_str("STRICT").unwrap(),
            BookingMethod::Strict
        );
        assert_eq!(
            BookingMethod::from_str("fifo").unwrap(),
            BookingMethod::Fifo
        );
        assert_eq!(
            BookingMethod::from_str("LIFO").unwrap(),
            BookingMethod::Lifo
        );
        assert_eq!(
            BookingMethod::from_str("Hifo").unwrap(),
            BookingMethod::Hifo
        );
        assert_eq!(
            BookingMethod::from_str("AVERAGE").unwrap(),
            BookingMethod::Average
        );
        assert_eq!(
            BookingMethod::from_str("NONE").unwrap(),
            BookingMethod::None
        );
        assert_eq!(
            BookingMethod::from_str("strict_with_size").unwrap(),
            BookingMethod::StrictWithSize
        );
        assert!(BookingMethod::from_str("INVALID").is_err());
    }

    #[test]
    fn test_booking_method_display() {
        assert_eq!(format!("{}", BookingMethod::Strict), "STRICT");
        assert_eq!(format!("{}", BookingMethod::Fifo), "FIFO");
        assert_eq!(format!("{}", BookingMethod::Lifo), "LIFO");
        assert_eq!(format!("{}", BookingMethod::Hifo), "HIFO");
        assert_eq!(format!("{}", BookingMethod::Average), "AVERAGE");
        assert_eq!(format!("{}", BookingMethod::None), "NONE");
        assert_eq!(
            format!("{}", BookingMethod::StrictWithSize),
            "STRICT_WITH_SIZE"
        );
    }

    #[test]
    fn test_booking_error_display() {
        let err = BookingError::AmbiguousMatch {
            num_matches: 3,
            currency: "AAPL".into(),
        };
        assert!(format!("{err}").contains("3 lots match"));

        let err = BookingError::NoMatchingLot {
            currency: "AAPL".into(),
            cost_spec: CostSpec::empty(),
        };
        assert!(format!("{err}").contains("No matching lot"));

        let err = BookingError::InsufficientUnits {
            currency: "AAPL".into(),
            requested: dec!(100),
            available: dec!(50),
        };
        assert!(format!("{err}").contains("requested 100"));
        assert!(format!("{err}").contains("available 50"));

        let err = BookingError::CurrencyMismatch {
            expected: "USD".into(),
            got: "EUR".into(),
        };
        assert!(format!("{err}").contains("expected USD"));
        assert!(format!("{err}").contains("got EUR"));
    }

    #[test]
    fn test_book_value_multiple_currencies() {
        let mut inv = Inventory::new();

        // Cost in USD
        let cost_usd = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost_usd))
            .expect("fixture fits in Decimal");

        // Cost in EUR
        let cost_eur = Cost::new(dec!(90.00), "EUR").with_date(date(2024, 2, 1));
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost_eur))
            .expect("fixture fits in Decimal");

        let book = inv.book_value("AAPL").expect("fixture fits in Decimal");
        assert_eq!(book.get("USD"), Some(&dec!(1000.00)));
        assert_eq!(book.get("EUR"), Some(&dec!(450.00)));
    }

    #[test]
    fn test_reduce_hifo_insufficient_units() {
        let mut inv = Inventory::new();

        let cost = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost))
            .expect("fixture fits in Decimal");

        let result = inv.reduce(&Amount::new(dec!(-20), "AAPL"), None, BookingMethod::Hifo);

        assert!(matches!(
            result,
            Err(BookingError::InsufficientUnits { .. })
        ));
    }

    #[test]
    fn test_reduce_average_insufficient_units() {
        let mut inv = Inventory::new();

        let cost = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost))
            .expect("fixture fits in Decimal");

        let result = inv.reduce(
            &Amount::new(dec!(-20), "AAPL"),
            None,
            BookingMethod::Average,
        );

        assert!(matches!(
            result,
            Err(BookingError::InsufficientUnits { .. })
        ));
    }

    #[test]
    fn test_reduce_average_empty_inventory() {
        let mut inv = Inventory::new();

        let result = inv.reduce(
            &Amount::new(dec!(-10), "AAPL"),
            None,
            BookingMethod::Average,
        );

        assert!(matches!(
            result,
            Err(BookingError::InsufficientUnits { .. })
        ));
    }

    #[test]
    fn test_reduce_merge_operator() {
        // {*} merge: two lots merged into weighted-average, then reduced
        let mut inv = Inventory::new();
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(150), "USD"),
        ))
        .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(160), "USD"),
        ))
        .expect("fixture fits in Decimal");

        let merge_spec = CostSpec::empty().with_merge();
        let result = inv
            .reduce(
                &Amount::new(dec!(-5), "AAPL"),
                Some(&merge_spec),
                BookingMethod::Strict,
            )
            .expect("merge reduction should succeed");

        // Cost basis: 5 units * 155 USD average = 775 USD
        assert_eq!(result.cost_basis, Some(Amount::new(dec!(775), "USD")));

        // Inventory should have a single merged lot with 15 remaining @ 155
        assert_eq!(inv.positions.len(), 1);
        assert_eq!(inv.positions[0].units.number, dec!(15));
        let cost = inv.positions[0].cost.as_ref().expect("should have cost");
        assert_eq!(cost.number, dec!(155));
    }

    #[test]
    fn test_reduce_merge_insufficient_units() {
        let mut inv = Inventory::new();
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(150), "USD"),
        ))
        .expect("fixture fits in Decimal");

        let merge_spec = CostSpec::empty().with_merge();
        let result = inv.reduce(
            &Amount::new(dec!(-20), "AAPL"),
            Some(&merge_spec),
            BookingMethod::Strict,
        );

        assert!(matches!(
            result,
            Err(BookingError::InsufficientUnits { .. })
        ));
    }

    #[test]
    fn test_reduce_merge_sells_all() {
        // Merge and sell entire position
        let mut inv = Inventory::new();
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(150), "USD"),
        ))
        .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(160), "USD"),
        ))
        .expect("fixture fits in Decimal");

        let merge_spec = CostSpec::empty().with_merge();
        let result = inv
            .reduce(
                &Amount::new(dec!(-20), "AAPL"),
                Some(&merge_spec),
                BookingMethod::Strict,
            )
            .expect("merge reduction should succeed");

        // Cost basis: 20 * 155 = 3100 USD
        assert_eq!(result.cost_basis, Some(Amount::new(dec!(3100), "USD")));

        // Inventory should be empty
        assert!(inv.positions.is_empty() || inv.positions.iter().all(Position::is_empty));
    }

    #[test]
    fn test_reduce_merge_single_lot() {
        // {*} with a single lot should work trivially
        let mut inv = Inventory::new();
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(150), "USD"),
        ))
        .expect("fixture fits in Decimal");

        let merge_spec = CostSpec::empty().with_merge();
        let result = inv
            .reduce(
                &Amount::new(dec!(-3), "AAPL"),
                Some(&merge_spec),
                BookingMethod::Strict,
            )
            .expect("single-lot merge should succeed");

        assert_eq!(result.cost_basis, Some(Amount::new(dec!(450), "USD")));
        assert_eq!(inv.positions.len(), 1);
        assert_eq!(inv.positions[0].units.number, dec!(7));
    }

    #[test]
    fn test_reduce_merge_three_lots() {
        // {*} with three lots at different costs
        let mut inv = Inventory::new();
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(100), "USD"),
        ))
        .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(150), "USD"),
        ))
        .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(200), "USD"),
        ))
        .expect("fixture fits in Decimal");

        // Average cost: (1000 + 1500 + 2000) / 30 = 150 USD
        let merge_spec = CostSpec::empty().with_merge();
        let result = inv
            .reduce(
                &Amount::new(dec!(-6), "AAPL"),
                Some(&merge_spec),
                BookingMethod::Strict,
            )
            .expect("three-lot merge should succeed");

        assert_eq!(result.cost_basis, Some(Amount::new(dec!(900), "USD")));
        assert_eq!(inv.positions.len(), 1);
        assert_eq!(inv.positions[0].units.number, dec!(24));
        let cost = inv.positions[0].cost.as_ref().expect("should have cost");
        assert_eq!(cost.number, dec!(150));
    }

    #[test]
    fn test_reduce_merge_mixed_cost_currencies_errors() {
        // Lots with different cost currencies cannot be merged
        let mut inv = Inventory::new();
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(150), "USD"),
        ))
        .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(130), "EUR"),
        ))
        .expect("fixture fits in Decimal");

        let merge_spec = CostSpec::empty().with_merge();
        let result = inv.reduce(
            &Amount::new(dec!(-5), "AAPL"),
            Some(&merge_spec),
            BookingMethod::Strict,
        );

        assert!(
            matches!(result, Err(BookingError::CurrencyMismatch { .. })),
            "expected CurrencyMismatch, got {result:?}"
        );
    }

    #[test]
    fn test_reduce_merge_empty_inventory() {
        let mut inv = Inventory::new();

        let merge_spec = CostSpec::empty().with_merge();
        let result = inv.reduce(
            &Amount::new(dec!(-5), "AAPL"),
            Some(&merge_spec),
            BookingMethod::Strict,
        );

        assert!(matches!(
            result,
            Err(BookingError::InsufficientUnits { .. })
        ));
    }

    #[test]
    fn test_inventory_display_sorted() {
        let mut inv = Inventory::new();

        // Add in non-alphabetical order
        inv.add(Position::simple(Amount::new(dec!(100), "USD")))
            .expect("fixture fits in Decimal");
        inv.add(Position::simple(Amount::new(dec!(50), "EUR")))
            .expect("fixture fits in Decimal");
        inv.add(Position::simple(Amount::new(dec!(10), "AAPL")))
            .expect("fixture fits in Decimal");

        let display = format!("{inv}");

        // Should be sorted alphabetically: AAPL, EUR, USD
        let aapl_pos = display.find("AAPL").unwrap();
        let eur_pos = display.find("EUR").unwrap();
        let usd_pos = display.find("USD").unwrap();

        assert!(aapl_pos < eur_pos);
        assert!(eur_pos < usd_pos);
    }

    #[test]
    fn test_inventory_with_cost_display_sorted() {
        let mut inv = Inventory::new();

        // Add same currency with different costs
        let cost_high = Cost::new(dec!(200.00), "USD").with_date(date(2024, 1, 1));
        let cost_low = Cost::new(dec!(100.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            cost_high,
        ))
        .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost_low))
            .expect("fixture fits in Decimal");

        let display = format!("{inv}");

        // Both positions should be in the output
        assert!(display.contains("AAPL"));
        assert!(display.contains("100"));
        assert!(display.contains("200"));
    }

    #[test]
    fn test_reduce_hifo_no_matching_lot() {
        let mut inv = Inventory::new();

        // No AAPL positions
        inv.add(Position::simple(Amount::new(dec!(100), "USD")))
            .expect("fixture fits in Decimal");

        let result = inv.reduce(&Amount::new(dec!(-10), "AAPL"), None, BookingMethod::Hifo);

        assert!(matches!(result, Err(BookingError::NoMatchingLot { .. })));
    }

    #[test]
    fn test_fifo_respects_dates() {
        // Ensure FIFO uses acquisition date, not insertion order
        let mut inv = Inventory::new();

        // Add newer lot first (out of order)
        let cost_new = Cost::new(dec!(200.00), "USD").with_date(date(2024, 3, 1));
        let cost_old = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost_new))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost_old))
            .expect("fixture fits in Decimal");

        // FIFO should reduce from oldest (cost 100) first
        let result = inv
            .reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Fifo)
            .unwrap();

        // Should use cost from oldest lot (100)
        assert_eq!(result.cost_basis.unwrap().number, dec!(500.00));
    }

    #[test]
    fn test_lifo_respects_dates() {
        // Ensure LIFO uses acquisition date, not insertion order
        let mut inv = Inventory::new();

        // Add older lot first
        let cost_old = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost_new = Cost::new(dec!(200.00), "USD").with_date(date(2024, 3, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost_old))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost_new))
            .expect("fixture fits in Decimal");

        // LIFO should reduce from newest (cost 200) first
        let result = inv
            .reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Lifo)
            .unwrap();

        // Should use cost from newest lot (200)
        assert_eq!(result.cost_basis.unwrap().number, dec!(1000.00));
    }

    // =========================================================================
    // Booking method coverage tests
    //
    // These tests cover gaps identified during the spring 2026 audit:
    // - STRICT_WITH_SIZE: cost spec + exact-size, multiple exact-size matches
    // - HIFO: multi-lot ordering, partial reduction, cost spec filtering
    // - AVERAGE: weighted average with different costs, partial reduction preserves cost
    // - NONE: with cost positions, short position reduction
    // =========================================================================

    // --- STRICT_WITH_SIZE ---

    #[test]
    fn test_strict_with_size_different_costs_exact_match() {
        // When lots have different costs but one matches the reduction size exactly,
        // STRICT_WITH_SIZE should pick that lot instead of raising AmbiguousMatch
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(200.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(7), "AAPL"), cost2))
            .expect("fixture fits in Decimal");

        // Reduce exactly 7 - should match the 7-share lot at cost 200
        let result = inv
            .reduce(
                &Amount::new(dec!(-7), "AAPL"),
                None,
                BookingMethod::StrictWithSize,
            )
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(10));
        assert_eq!(result.cost_basis.unwrap().number, dec!(1400.00)); // 7 * 200
    }

    #[test]
    fn test_strict_with_size_multiple_exact_matches_picks_oldest() {
        // When multiple lots have the exact same size, STRICT_WITH_SIZE should
        // pick the oldest one (first in index order)
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(200.00), "USD").with_date(date(2024, 6, 1));

        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost1))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost2))
            .expect("fixture fits in Decimal");

        // Both lots are size 5 — should pick the first (oldest) one
        let result = inv
            .reduce(
                &Amount::new(dec!(-5), "AAPL"),
                None,
                BookingMethod::StrictWithSize,
            )
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(5));
        // Should use cost from the oldest lot (100)
        assert_eq!(result.cost_basis.unwrap().number, dec!(500.00));
    }

    #[test]
    fn test_strict_with_size_with_cost_spec() {
        // Cost spec should filter lots before exact-size matching
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(200.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2))
            .expect("fixture fits in Decimal");

        // With cost spec filtering to the 200 USD lot, should find unique match
        let spec = CostSpec::empty().with_number(crate::CostNumber::PerUnit {
            value: dec!(200.00),
        });
        let result = inv
            .reduce(
                &Amount::new(dec!(-5), "AAPL"),
                Some(&spec),
                BookingMethod::StrictWithSize,
            )
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(15));
        assert_eq!(result.cost_basis.unwrap().number, dec!(1000.00)); // 5 * 200
    }

    // --- HIFO ---

    #[test]
    fn test_hifo_reduces_highest_cost_first() {
        // HIFO should reduce the highest-cost lot first, regardless of date
        let mut inv = Inventory::new();

        let cost_low = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost_mid = Cost::new(dec!(150.00), "USD").with_date(date(2024, 2, 1));
        let cost_high = Cost::new(dec!(200.00), "USD").with_date(date(2024, 3, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost_low))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost_mid))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            cost_high,
        ))
        .expect("fixture fits in Decimal");

        // Reduce 5 — should come from highest cost lot (200)
        let result = inv
            .reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Hifo)
            .unwrap();

        assert_eq!(result.cost_basis.unwrap().number, dec!(1000.00)); // 5 * 200
        assert_eq!(inv.units("AAPL"), dec!(25));
    }

    #[test]
    fn test_hifo_spans_multiple_lots() {
        // When reducing more than the highest-cost lot holds, HIFO should
        // continue to the next highest
        let mut inv = Inventory::new();

        let cost_low = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost_high = Cost::new(dec!(200.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost_low))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(5), "AAPL"), cost_high))
            .expect("fixture fits in Decimal");

        // Reduce 8: 5 from high (200) + 3 from low (100)
        let result = inv
            .reduce(&Amount::new(dec!(-8), "AAPL"), None, BookingMethod::Hifo)
            .unwrap();

        // Cost basis: 5*200 + 3*100 = 1300
        assert_eq!(result.cost_basis.unwrap().number, dec!(1300.00));
        assert_eq!(inv.units("AAPL"), dec!(2));
    }

    #[test]
    fn test_hifo_with_cost_spec_filter() {
        // Cost spec should filter lots before HIFO ordering
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(200.00), "EUR").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2))
            .expect("fixture fits in Decimal");

        // Filter to USD lots only
        let spec = CostSpec::empty().with_currency("USD");
        let result = inv
            .reduce(
                &Amount::new(dec!(-5), "AAPL"),
                Some(&spec),
                BookingMethod::Hifo,
            )
            .unwrap();

        assert_eq!(result.cost_basis.unwrap().number, dec!(500.00)); // 5 * 100 USD
    }

    #[test]
    fn test_hifo_short_position() {
        // HIFO with short positions: covering shorts should work correctly
        let mut inv = Inventory::new();

        let cost_low = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost_high = Cost::new(dec!(200.00), "USD").with_date(date(2024, 2, 1));

        // Short positions (negative units)
        inv.add(Position::with_cost(
            Amount::new(dec!(-10), "AAPL"),
            cost_low,
        ))
        .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(
            Amount::new(dec!(-10), "AAPL"),
            cost_high,
        ))
        .expect("fixture fits in Decimal");

        // Cover 5 shares (positive = reduce short position)
        // HIFO should pick the highest-cost short lot (200)
        let result = inv
            .reduce(&Amount::new(dec!(5), "AAPL"), None, BookingMethod::Hifo)
            .unwrap();

        assert_eq!(result.cost_basis.unwrap().number, dec!(1000.00)); // 5 * 200
        assert_eq!(inv.units("AAPL"), dec!(-15));
    }

    // --- AVERAGE ---

    #[test]
    fn test_average_weighted_cost() {
        // AVERAGE should compute weighted average across lots with different costs
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(200.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2))
            .expect("fixture fits in Decimal");

        // Average cost = (10*100 + 10*200) / 20 = 150
        let result = inv
            .reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Average)
            .unwrap();

        // Cost basis: 5 * 150 = 750
        assert_eq!(result.cost_basis.unwrap().number, dec!(750.00));
        assert_eq!(inv.units("AAPL"), dec!(15));
    }

    #[test]
    fn test_average_merges_into_single_position() {
        // After AVERAGE reduction, inventory should have a single simple position
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(200.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2))
            .expect("fixture fits in Decimal");

        inv.reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Average)
            .unwrap();

        // Should have exactly one AAPL position remaining
        let aapl_positions: Vec<_> = inv
            .positions
            .iter()
            .filter(|p| p.units.currency.as_ref() == "AAPL")
            .collect();
        assert_eq!(aapl_positions.len(), 1);
        assert_eq!(aapl_positions[0].units.number, dec!(15));
    }

    #[test]
    fn test_average_uneven_lots() {
        // Weighted average with unequal lot sizes
        let mut inv = Inventory::new();

        let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost2 = Cost::new(dec!(200.00), "USD").with_date(date(2024, 2, 1));

        inv.add(Position::with_cost(Amount::new(dec!(30), "AAPL"), cost1))
            .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2))
            .expect("fixture fits in Decimal");

        // Average cost = (30*100 + 10*200) / 40 = 5000/40 = 125
        let result = inv
            .reduce(
                &Amount::new(dec!(-10), "AAPL"),
                None,
                BookingMethod::Average,
            )
            .unwrap();

        assert_eq!(result.cost_basis.unwrap().number, dec!(1250.00)); // 10 * 125
    }

    // --- NONE ---

    #[test]
    fn test_none_booking_with_cost_positions() {
        // NONE booking should work even when positions have costs
        let mut inv = Inventory::new();

        let cost = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost))
            .expect("fixture fits in Decimal");

        let result = inv
            .reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::None)
            .unwrap();

        assert_eq!(inv.units("AAPL"), dec!(5));
        // NONE delegates to reduce_ordered (FIFO) internally, so cost basis is computed
        assert!(result.cost_basis.is_some());
        assert_eq!(result.cost_basis.unwrap().number, dec!(500.00));
    }

    #[test]
    fn test_none_booking_short_cover() {
        // Covering a short position with NONE booking
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(-100), "USD")))
            .expect("fixture fits in Decimal");

        // Positive amount should reduce the negative position
        let result = inv
            .reduce(&Amount::new(dec!(30), "USD"), None, BookingMethod::None)
            .unwrap();

        assert_eq!(inv.units("USD"), dec!(-70));
        assert!(!result.matched.is_empty());
    }

    #[test]
    fn test_none_booking_empty_inventory_augments() {
        // NONE booking on empty inventory should augment
        let mut inv = Inventory::new();

        let result = inv
            .reduce(&Amount::new(dec!(50), "USD"), None, BookingMethod::None)
            .unwrap();

        assert_eq!(inv.units("USD"), dec!(50));
        assert!(result.matched.is_empty()); // Augmentation, not reduction
    }

    // --- Cross-method: short positions ---

    #[test]
    fn test_fifo_short_position_cover() {
        // FIFO: cover short positions (oldest short first)
        let mut inv = Inventory::new();

        let cost_old = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost_new = Cost::new(dec!(200.00), "USD").with_date(date(2024, 3, 1));

        inv.add(Position::with_cost(
            Amount::new(dec!(-10), "AAPL"),
            cost_old,
        ))
        .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(
            Amount::new(dec!(-10), "AAPL"),
            cost_new,
        ))
        .expect("fixture fits in Decimal");

        // Cover 5 shares — FIFO should pick oldest short (cost 100)
        let result = inv
            .reduce(&Amount::new(dec!(5), "AAPL"), None, BookingMethod::Fifo)
            .unwrap();

        assert_eq!(result.cost_basis.unwrap().number, dec!(500.00)); // 5 * 100
        assert_eq!(inv.units("AAPL"), dec!(-15));
    }

    #[test]
    fn test_lifo_short_position_cover() {
        // LIFO: cover short positions (newest short first)
        let mut inv = Inventory::new();

        let cost_old = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
        let cost_new = Cost::new(dec!(200.00), "USD").with_date(date(2024, 3, 1));

        inv.add(Position::with_cost(
            Amount::new(dec!(-10), "AAPL"),
            cost_old,
        ))
        .expect("fixture fits in Decimal");
        inv.add(Position::with_cost(
            Amount::new(dec!(-10), "AAPL"),
            cost_new,
        ))
        .expect("fixture fits in Decimal");

        // Cover 5 shares — LIFO should pick newest short (cost 200)
        let result = inv
            .reduce(&Amount::new(dec!(5), "AAPL"), None, BookingMethod::Lifo)
            .unwrap();

        assert_eq!(result.cost_basis.unwrap().number, dec!(1000.00)); // 5 * 200
        assert_eq!(inv.units("AAPL"), dec!(-15));
    }

    // === AccountedBookingError Display tests ===
    //
    // These tests pin the canonical user-facing wording for every variant
    // of `AccountedBookingError`. The whole point of unifying booking-error
    // Display into `rustledger-core` (#750) is that there's a single source
    // of truth — and a single source of truth with no tests is one refactor
    // away from drifting again, which is exactly the failure mode that
    // produced #748. Any change to the Display strings below will break
    // these tests, forcing the author to consciously re-check pta-standards
    // conformance assertions and downstream user tooling.

    // =========================================================================
    // Regression test for issue #875 / beancount#889
    //
    // When a sell-without-cost-spec leaves a negative simple position in the
    // inventory, a subsequent augmentation WITH a cost spec should NOT be
    // misclassified as a reduction. `is_reduced_by` must only consider
    // cost-bearing positions when the incoming posting has a cost spec.
    // =========================================================================

    #[test]
    fn test_is_reduced_by_ignores_simple_positions_when_has_cost_spec() {
        // Regression test for issue #875 / beancount#889.
        //
        // Scenario:
        //   1. Buy 100 HOOG {1.50 EUR}  -> inventory: [100 HOOG {1.50 EUR}]
        //   2. Sell 25 HOOG @ 1.60 EUR   -> inventory: [100 HOOG {1.50 EUR}, -25 HOOG (simple)]
        //   3. Buy 50 HOOG {1.70 EUR}    -> should be augmentation, NOT reduction
        //
        // Before fix: is_reduced_by saw the -25 HOOG simple position and
        // incorrectly reported that +50 HOOG would reduce the inventory.
        let mut inv = Inventory::new();

        // Step 1: buy 100 HOOG with cost
        let cost = Cost::new(dec!(1.50), "EUR").with_date(date(2024, 1, 10));
        inv.add(Position::with_cost(Amount::new(dec!(100), "HOOG"), cost))
            .expect("fixture fits in Decimal");

        // Step 2: sell 25 HOOG without cost spec (simple position)
        inv.add(Position::simple(Amount::new(dec!(-25), "HOOG")))
            .expect("fixture fits in Decimal");

        // Step 3: check if buying 50 HOOG with cost spec would be a reduction
        let buy_units = Amount::new(dec!(50), "HOOG");

        // With has_cost_spec=true, only cost-bearing positions should be
        // considered. The 100 HOOG {1.50 EUR} is positive and so is the
        // incoming 50 HOOG -> same sign -> NOT a reduction.
        assert!(
            !inv.is_reduced_by(&buy_units, ReductionScope::CostBearingOnly),
            "augmentation with cost spec should NOT be treated as reduction \
             when only a simple (no-cost) position has opposite sign"
        );

        // With AllPositions, all positions are considered,
        // including the -25 HOOG simple position -> IS a reduction.
        assert!(
            inv.is_reduced_by(&buy_units, ReductionScope::AllPositions),
            "without cost spec filter, the -25 HOOG simple position \
             should cause is_reduced_by to return true"
        );
    }

    #[test]
    fn is_booking_reduction_gates_on_method_cost_and_sign() {
        // A cost-bearing long position.
        let mut inv = Inventory::new();
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(150), "USD").with_date(date(2024, 1, 1)),
        ))
        .expect("fixture fits in Decimal");

        let sell = Amount::new(dec!(-5), "AAPL"); // opposite sign of the held lot
        let buy = Amount::new(dec!(5), "AAPL"); // same sign
        let spec = CostSpec::empty(); // only spec *presence* (is_some) matters here

        // Opposite-sign units carrying a cost spec under a lot-matching method
        // is the one combination that reduces.
        assert!(inv.is_booking_reduction(&sell, Some(&spec), BookingMethod::Strict));
        // NONE never reduces — every posting accumulates (#1182).
        assert!(!inv.is_booking_reduction(&sell, Some(&spec), BookingMethod::None));
        // No cost spec -> augmentation.
        assert!(!inv.is_booking_reduction(&sell, None, BookingMethod::Strict));
        // Same sign as the held lot -> augmentation.
        assert!(!inv.is_booking_reduction(&buy, Some(&spec), BookingMethod::Strict));
    }

    #[test]
    fn sum_account_and_subaccounts_sums_children_not_prefix_siblings() {
        let mut bank = Inventory::new();
        bank.add(Position::simple(Amount::new(dec!(10), "USD")))
            .expect("fixture fits in Decimal");
        let mut checking = Inventory::new(); // sub-account: included
        checking
            .add(Position::simple(Amount::new(dec!(40), "USD")))
            .expect("fixture fits in Decimal");
        let mut alias = Inventory::new(); // prefix sibling: excluded
        alias
            .add(Position::simple(Amount::new(dec!(99), "USD")))
            .expect("fixture fits in Decimal");

        let mut map: FxHashMap<Account, Inventory> = FxHashMap::default();
        map.insert(Account::from("Assets:Bank"), bank);
        map.insert(Account::from("Assets:Bank:Checking"), checking);
        map.insert(Account::from("Assets:BankAlias"), alias);

        let total = sum_account_and_subaccounts(map.iter(), "Assets:Bank", &Currency::from("USD"))
            .expect("fixture fits in Decimal");
        assert_eq!(
            total,
            dec!(50),
            "parent (10) + sub-account (40), excluding the Assets:BankAlias prefix sibling"
        );
    }

    #[test]
    fn test_accounted_error_display_insufficient_units() {
        let err = BookingError::InsufficientUnits {
            currency: "AAPL".into(),
            requested: dec!(15),
            available: dec!(10),
        }
        .with_account("Assets:Stock".into());
        let rendered = format!("{err}");

        // Pinned by pta-standards `reduction-exceeds-inventory`
        // (`error_contains: ["not enough"]`). See #748 / #749.
        assert!(
            rendered.contains("not enough"),
            "must contain 'not enough' (pta-standards): {rendered}"
        );
        assert!(
            rendered.contains("Assets:Stock"),
            "must contain account name: {rendered}"
        );
        assert!(
            rendered.contains("15") && rendered.contains("10"),
            "must contain requested and available amounts: {rendered}"
        );
    }

    #[test]
    fn test_accounted_error_display_no_matching_lot() {
        let err = BookingError::NoMatchingLot {
            currency: "AAPL".into(),
            cost_spec: CostSpec::empty(),
        }
        .with_account("Assets:Stock".into());
        let rendered = format!("{err}");

        assert!(
            rendered.contains("No matching lot"),
            "must contain 'No matching lot': {rendered}"
        );
        assert!(
            rendered.contains("AAPL"),
            "must contain currency: {rendered}"
        );
        assert!(
            rendered.contains("Assets:Stock"),
            "must contain account name: {rendered}"
        );
    }

    #[test]
    fn test_accounted_error_display_ambiguous_match() {
        let err = BookingError::AmbiguousMatch {
            num_matches: 3,
            currency: "AAPL".into(),
        }
        .with_account("Assets:Stock".into());
        let rendered = format!("{err}");

        assert!(
            rendered.contains("Ambiguous"),
            "must contain 'Ambiguous': {rendered}"
        );
        assert!(
            rendered.contains("AAPL"),
            "must contain currency: {rendered}"
        );
        assert!(
            rendered.contains("Assets:Stock"),
            "must contain account name: {rendered}"
        );
        assert!(
            rendered.contains('3'),
            "must contain match count: {rendered}"
        );
    }

    #[test]
    fn test_accounted_error_display_currency_mismatch_renders_as_no_matching_lot() {
        // CurrencyMismatch is semantically a specialization of NoMatchingLot
        // (there is no lot for the given currency in this inventory) and the
        // canonical Display collapses them into the same user-facing phrasing
        // so that consumers filtering on E4001 don't need to special-case it.
        // This variant is defensive — no `Inventory::reduce` path currently
        // emits it — but we still pin its rendering in case a future emission
        // site is added.
        let err = BookingError::CurrencyMismatch {
            expected: "USD".into(),
            got: "EUR".into(),
        }
        .with_account("Assets:Cash".into());
        let rendered = format!("{err}");

        assert!(
            rendered.contains("No matching lot"),
            "CurrencyMismatch must render as 'No matching lot' for E4001 \
             consistency: {rendered}"
        );
        assert!(
            rendered.contains("EUR"),
            "must contain the mismatched (got) currency: {rendered}"
        );
        assert!(
            rendered.contains("Assets:Cash"),
            "must contain account name: {rendered}"
        );
    }

    /// `sign_index` must agree with a scan after EVERY mutation path, not
    /// just the ones a given test happens to follow with an
    /// `is_reduced_by` call.
    ///
    /// `is_reduced_by`'s own `debug_assert` compares the two on every call,
    /// which covers the whole suite — but only where something calls it.
    /// This walks the mutations that can move a lot between buckets and
    /// checks after each: a cost-less merge that flips a lot's sign by adding
    /// through zero, a reduction that takes a lot to exactly zero (removing
    /// it), and a partial reduction that leaves it. The comparison is
    /// explicit rather than leaning on the assertion, so it holds in release
    /// builds too.
    #[test]
    fn the_sign_index_tracks_every_mutation_path() {
        let usd = Amount::new(dec!(1), "USD");
        let aapl = Amount::new(dec!(1), "AAPL");
        let check = |inv: &Inventory, label: &str| {
            // The incrementally maintained counts must equal what a fresh
            // rebuild computes. This is the invariant that matters, and it is
            // strictly stronger than "the answers agree": an empty cache
            // still ANSWERS correctly, because `is_reduced_by` falls back to
            // the scan — so a path that quietly stopped maintaining the counts
            // would restore the O(lots) cost with every test still green.
            // Comparing against a rebuild catches that, and catches a broken
            // rebuild too, since the two are independent code.
            //
            // Zero-count entries are filtered from both sides: `units_cache`
            // keeps a currency's entry for its running total after the last
            // lot closes, which a rebuild has no reason to create.
            let counts_of = |inv: &Inventory| {
                inv.units_cache
                    .iter()
                    .filter(|(_, stats)| stats.counts != SignCounts::default())
                    .map(|(currency, stats)| (currency.as_str().to_string(), stats.counts))
                    .collect::<std::collections::BTreeMap<_, _>>()
            };
            let mut rebuilt = inv.clone();
            rebuilt.rebuild_index();
            assert_eq!(
                counts_of(inv),
                counts_of(&rebuilt),
                "the incrementally maintained sign counts diverged from a \
                 fresh rebuild after {label}",
            );
            for units in [&usd, &aapl] {
                for signed in [
                    units.clone(),
                    Amount::new(-units.number, units.currency.clone()),
                ] {
                    for scope in [
                        ReductionScope::AllPositions,
                        ReductionScope::CostBearingOnly,
                    ] {
                        assert_eq!(
                            inv.is_reduced_by(&signed, scope),
                            inv.is_reduced_by_scan(&signed, scope),
                            "the sign counts disagree with a scan after {label} \
                         for {signed:?} / {scope:?}",
                        );
                    }
                }
            }
        };

        let mut inv = Inventory::new();
        check(&inv, "empty");

        // Cost-less lot, then a merge that takes it negative through zero.
        inv.add(Position::simple(Amount::new(dec!(3), "USD")))
            .expect("fits");
        check(&inv, "one simple lot");
        inv.add(Position::simple(Amount::new(dec!(-8), "USD")))
            .expect("fits");
        check(&inv, "simple lot flipped negative by merge");
        inv.add(Position::simple(Amount::new(dec!(8), "USD")))
            .expect("fits");
        check(&inv, "simple lot flipped back positive");

        // Cost-bearing lots, then reductions that partially and fully drain.
        let cost = Cost::new(dec!(100), "USD");
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            cost.clone(),
        ))
        .expect("fits");
        check(&inv, "one cost-bearing lot");

        inv.reduce(
            &Amount::new(dec!(-4), "AAPL"),
            Some(&CostSpec::default()),
            BookingMethod::Fifo,
        )
        .expect("partial reduction");
        check(&inv, "partially reduced lot");

        inv.reduce(
            &Amount::new(dec!(-6), "AAPL"),
            Some(&CostSpec::default()),
            BookingMethod::Fifo,
        )
        .expect("full reduction");
        check(&inv, "fully drained lot");

        // STRICT with a single matching lot takes the OTHER commit path —
        // `commit_from_lot`, which maintains the caches incrementally instead
        // of rebuilding. A FIFO-only test leaves it completely uncovered.
        let mut strict = Inventory::new();
        strict
            .add(Position::with_cost(
                Amount::new(dec!(10), "AAPL"),
                cost.clone(),
            ))
            .expect("fits");
        check(&strict, "strict: one lot");
        strict
            .reduce(
                &Amount::new(dec!(-4), "AAPL"),
                Some(&CostSpec::default()),
                BookingMethod::Strict,
            )
            .expect("partial strict reduction");
        check(&strict, "strict: partially reduced");
        strict
            .reduce(
                &Amount::new(dec!(-6), "AAPL"),
                Some(&CostSpec::default()),
                BookingMethod::Strict,
            )
            .expect("draining strict reduction");
        check(&strict, "strict: lot drained and removed");
        assert!(
            strict.positions.is_empty(),
            "the fixture must actually remove the lot, or the removal path is \
             untested",
        );

        // A SHORT lot covered to exactly zero. This is the only shape where a
        // reduction changes a lot's bucket: `is_sign_positive` answers TRUE
        // for zero, so a negative lot reaching 0 moves from the negative
        // bucket to the positive one in the instant before it is removed.
        // Skipping the reclassify then decrements the wrong bucket and leaves
        // the index claiming a short lot that no longer exists. A long lot
        // cannot show this — it is capped at zero from above and never leaves
        // the positive bucket.
        let mut short = Inventory::new();
        short
            .add(Position::with_cost(
                Amount::new(dec!(-5), "AAPL"),
                Cost::new(dec!(100), "USD"),
            ))
            .expect("fits");
        check(&short, "short: one negative lot");
        short
            .reduce(
                &Amount::new(dec!(5), "AAPL"),
                Some(&CostSpec::default()),
                BookingMethod::Strict,
            )
            .expect("covering the short");
        check(&short, "short: covered to zero and removed");
        assert!(
            short.positions.is_empty(),
            "the short must actually close, or the bucket flip is untested",
        );

        // And a rebuild must land on the same state as the incremental path.
        // Captured from an inventory whose last mutation was `commit_from_lot`
        // (no rebuild), so the two are genuinely independent here.
        let mut incremental_inv = Inventory::new();
        incremental_inv
            .add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost))
            .expect("fits");
        incremental_inv
            .reduce(
                &Amount::new(dec!(-4), "AAPL"),
                Some(&CostSpec::default()),
                BookingMethod::Strict,
            )
            .expect("partial strict reduction");
        let incremental = incremental_inv.units_cache.clone();
        assert!(!incremental.is_empty(), "fixture holds a lot");
        incremental_inv.rebuild_index();
        assert_eq!(
            incremental, incremental_inv.units_cache,
            "the incrementally maintained index must equal a fresh rebuild",
        );
    }

    /// An inventory whose caches were never built still answers
    /// `is_reduced_by` correctly.
    ///
    /// The caches are `#[serde(skip)]`. Deserialization rebuilds them, but
    /// `positions_mut` hands out the position vector directly, so an
    /// inventory CAN hold lots with an empty cache. Reading the counts then
    /// would answer "not a reduction" for an inventory that plainly holds a
    /// matching lot — booking a sale as a purchase and duplicating the lot,
    /// which is the #875-class bug this predicate exists to prevent.
    ///
    /// So the unbuilt case falls back to the scan. This is the only test that
    /// reaches that branch: every other route into `is_reduced_by` goes
    /// through `add` or a rebuild, both of which populate the cache.
    #[test]
    fn an_unbuilt_cache_falls_back_to_the_scan_rather_than_answering_no() {
        let mut inv = Inventory::new();
        inv.positions_mut().push(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(100), "USD"),
        ));
        assert!(
            inv.units_cache.is_empty(),
            "the fixture must reach `is_reduced_by` with an unbuilt cache, or \
             it is testing the fast path instead",
        );

        assert!(
            inv.is_reduced_by(
                &Amount::new(dec!(-4), "AAPL"),
                ReductionScope::CostBearingOnly
            ),
            "a sale against a held lot must be seen as a reduction even with \
             no cache built",
        );
        assert!(
            !inv.is_reduced_by(
                &Amount::new(dec!(4), "AAPL"),
                ReductionScope::CostBearingOnly
            ),
            "a purchase in the same direction is still an augmentation",
        );

        // And once the caches are built, the answers are unchanged.
        inv.rebuild_index();
        assert!(!inv.units_cache.is_empty(), "rebuild populates the cache");
        assert!(inv.is_reduced_by(
            &Amount::new(dec!(-4), "AAPL"),
            ReductionScope::CostBearingOnly
        ));
        assert!(!inv.is_reduced_by(
            &Amount::new(dec!(4), "AAPL"),
            ReductionScope::CostBearingOnly
        ));
    }

    /// Removing a drained lot shifts every later position down one, and
    /// `simple_index` stores POSITIONS BY INDEX — so a cost-less lot sitting
    /// after the removed one must have its stored index repaired.
    ///
    /// Get this wrong and `add` merges a later cost-less deposit into the
    /// wrong lot, or indexes past the end. Nothing else in the suite covers
    /// it: it needs a cost-bearing lot and a cost-less lot in the same
    /// inventory, with the cost-bearing one removed first, and inventories in
    /// most tests hold only one kind.
    #[test]
    fn removing_a_lot_repairs_the_index_of_a_later_cost_less_lot() {
        let mut inv = Inventory::new();
        // Index 0: cost-bearing. Index 1: cost-less, so `simple_index` says 1.
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(100), "USD"),
        ))
        .expect("fits");
        inv.add(Position::simple(Amount::new(dec!(50), "USD")))
            .expect("fits");
        assert_eq!(
            inv.simple_index.get(&crate::Currency::new("USD")),
            Some(&1),
            "fixture must put the cost-less lot second, or the shift is untested",
        );

        // Drain the cost-bearing lot. STRICT takes the single-lot commit path,
        // which removes in place rather than rebuilding.
        inv.reduce(
            &Amount::new(dec!(-10), "AAPL"),
            Some(&CostSpec::default()),
            BookingMethod::Strict,
        )
        .expect("drains the lot");

        assert_eq!(
            inv.simple_index.get(&crate::Currency::new("USD")),
            Some(&0),
            "the cost-less lot moved to index 0 and the index must follow it",
        );

        // The consequence a stale index actually has: this must MERGE into the
        // existing lot, not append a second one.
        inv.add(Position::simple(Amount::new(dec!(25), "USD")))
            .expect("fits");
        assert_eq!(
            inv.positions().count(),
            1,
            "a stale simple_index appends a duplicate cost-less lot instead of \
             merging",
        );
        assert_eq!(inv.units("USD"), dec!(75));
    }

    /// Reducing a COST-LESS lot to zero removes it, and `simple_index` points
    /// at exactly that lot — so the entry must go, not just shift.
    #[test]
    fn removing_a_cost_less_lot_drops_its_index_entry() {
        let mut inv = Inventory::new();
        inv.add(Position::simple(Amount::new(dec!(50), "USD")))
            .expect("fits");
        assert_eq!(inv.simple_index.get(&crate::Currency::new("USD")), Some(&0));

        // An empty spec matches a cost-less lot (`matches_cost_spec`:
        // `(None, true) => true`), so STRICT selects it and drains it.
        inv.reduce(
            &Amount::new(dec!(-50), "USD"),
            Some(&CostSpec::default()),
            BookingMethod::Strict,
        )
        .expect("drains the cost-less lot");

        assert!(inv.positions().next().is_none(), "the lot is gone");
        assert_eq!(
            inv.simple_index.get(&crate::Currency::new("USD")),
            None,
            "a stale entry points at a removed lot; the next cost-less add \
             indexes past the end",
        );

        // The consequence: this must not panic and must create a fresh lot.
        inv.add(Position::simple(Amount::new(dec!(20), "USD")))
            .expect("fits");
        assert_eq!(inv.units("USD"), dec!(20));
    }

    /// Every index `iter_slots` yields must address, through `Index`, the very
    /// position it was yielded with.
    ///
    /// This is trivially true while the backing store is dense — `iter_slots`
    /// is `iter().enumerate()` — and it is the whole reason that method
    /// exists. The reduction paths collect indices from it and hand them back
    /// through `Index`/`IndexMut` to mutate the lot they selected. If the
    /// store ever becomes sparse (tombstoned lots, so a cost-keyed index can
    /// survive removals) and `iter_slots` keeps counting from zero instead of
    /// reporting real slots, every reduction after the first hole mutates the
    /// WRONG LOT — silently, with correct-looking totals.
    ///
    /// So this pins the contract rather than the current implementation.
    #[test]
    fn iter_slots_yields_indices_that_address_their_own_position() {
        let mut inv = Inventory::new();
        for units in [dec!(10), dec!(20), dec!(30)] {
            inv.add(Position::with_cost(
                Amount::new(units, "AAPL"),
                Cost::new(units * dec!(10), "USD"),
            ))
            .expect("fits");
        }
        // Two lots IDENTICAL by value. `add` never merges cost-bearing lots —
        // it keeps them separate to match Python — so this is an ordinary
        // inventory, and it is the shape that makes the assertion below
        // meaningful: with only distinct lots, comparing by value cannot tell
        // "the right slot" from "a slot holding an equal position".
        for _ in 0..2 {
            inv.add(Position::with_cost(
                Amount::new(dec!(7), "AAPL"),
                Cost::new(dec!(70), "USD"),
            ))
            .expect("fits");
        }
        inv.add(Position::simple(Amount::new(dec!(99), "USD")))
            .expect("fits");

        let mut seen = 0;
        for (slot, position) in inv.positions.iter_slots() {
            // Pointer identity, not `assert_eq!`. `Position: PartialEq`, so a
            // value comparison passes when a wrong index happens to land on an
            // equal lot — exactly what the duplicate pair above arranges.
            // Review catch on #2065.
            assert!(
                std::ptr::eq(std::ptr::from_ref(&inv.positions[slot]), position),
                "slot {slot} addresses a different position than the one it \
                 was yielded with",
            );
            seen += 1;
        }
        assert_eq!(
            seen,
            inv.positions().count(),
            "iter_slots must visit every live position",
        );
        assert_eq!(seen, 6, "fixture must hold six lots, two of them equal");
    }
}
