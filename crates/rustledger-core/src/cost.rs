//! Cost and cost specification types.
//!
//! A [`Cost`] represents the acquisition cost of a position (lot). It includes
//! the per-unit cost, currency, optional acquisition date, and optional label.
//!
//! A [`CostSpec`] is used for matching against existing costs or specifying
//! new costs when all fields may not be known.

// rkyv's enum derive (used on `CostNumber` below) synthesizes a
// per-variant `Archived*` struct whose generated `pub value` field
// doesn't inherit the source variant's field doc. Item-level
// `#[allow(missing_docs)]` doesn't propagate into the macro-emitted
// sibling items, so the suppression must live at module scope.
// Limited to the `rkyv` feature so hand-written items still get the
// lint under non-rkyv builds; reviewers should check that any new
// rkyv-archived type added to this file has docs on its source fields
// (review A-3.2).
#![cfg_attr(feature = "rkyv", allow(missing_docs))]

use crate::NaiveDate;
use rust_decimal::Decimal;
use serde::{Deserialize, Serialize};
use std::fmt;

use crate::Amount;

// Note: We no longer auto-quantize calculated values during cost storage.
// Python beancount preserves full precision during booking and only rounds
// at display time. Premature rounding of per-unit costs (e.g., from
// total cost / units) causes cost basis errors when selling.
// For example: 300.00 / 1.763 = 170.16505... should NOT be rounded to 170.17,
// because 1.763 * 170.17 = 300.00971 ≠ 300.00.
#[cfg(feature = "rkyv")]
use crate::intern::{AsDecimal, AsNaiveDate};

/// A cost represents the acquisition cost of a position (lot).
///
/// When you buy 10 shares of AAPL at $150 on 2024-01-15, the cost is:
/// - number: 150
/// - currency: "USD"
/// - date: Some(2024-01-15)
/// - label: None (or Some("lot1") if labeled)
///
/// # Examples
///
/// ```
/// use rustledger_core::Cost;
/// use rust_decimal_macros::dec;
///
/// let cost = Cost::new(dec!(150.00), "USD")
///     .with_date(rustledger_core::naive_date(2024, 1, 15).unwrap());
///
/// assert_eq!(cost.number, dec!(150.00));
/// assert_eq!(cost.currency, "USD");
/// assert!(cost.date.is_some());
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)
)]
pub struct Cost {
    /// Cost per unit
    #[cfg_attr(feature = "rkyv", rkyv(with = AsDecimal))]
    pub number: Decimal,
    /// Currency of the cost
    pub currency: crate::Currency,
    /// Acquisition date (optional, for lot identification)
    #[cfg_attr(feature = "rkyv", rkyv(with = rkyv::with::Map<AsNaiveDate>))]
    pub date: Option<NaiveDate>,
    /// Lot label (optional, for explicit lot identification)
    pub label: Option<String>,
}

impl Cost {
    /// Create a new cost with the given number and currency.
    ///
    /// Create a new cost with exact precision.
    /// Use this for user-specified values that should preserve their precision.
    #[must_use]
    pub fn new(number: Decimal, currency: impl Into<crate::Currency>) -> Self {
        Self {
            number,
            currency: currency.into(),
            date: None,
            label: None,
        }
    }

    /// Create a new cost for calculated values.
    ///
    /// Previously this auto-quantized, but we now preserve full precision
    /// to avoid cost basis errors. Rounding should only happen at display time.
    #[must_use]
    pub fn new_calculated(number: Decimal, currency: impl Into<crate::Currency>) -> Self {
        Self::new(number, currency)
    }

    /// Add a date to this cost.
    #[must_use]
    pub const fn with_date(mut self, date: NaiveDate) -> Self {
        self.date = Some(date);
        self
    }

    /// Add an optional date to this cost.
    #[must_use]
    pub const fn with_date_opt(mut self, date: Option<NaiveDate>) -> Self {
        self.date = date;
        self
    }

    /// Add a label to this cost.
    #[must_use]
    pub fn with_label(mut self, label: impl Into<String>) -> Self {
        self.label = Some(label.into());
        self
    }

    /// Add an optional label to this cost.
    #[must_use]
    pub fn with_label_opt(mut self, label: Option<String>) -> Self {
        self.label = label;
        self
    }

    /// Get the cost as an amount.
    #[must_use]
    pub fn as_amount(&self) -> Amount {
        Amount::new(self.number, self.currency.clone())
    }

    /// Calculate the total cost for a given number of units.
    #[must_use]
    pub fn total_cost(&self, units: Decimal) -> Amount {
        Amount::new(units * self.number, self.currency.clone())
    }
}

impl fmt::Display for Cost {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Match Beancount's `Position.__str__` format: `{ 520 USD}` —
        // single space after the opening brace, no space before the
        // closing brace. The space matters for BQL-output compat: the
        // compat harness diffs row-by-row against bean-query, and the
        // pre-fix `{520 USD}` form accounted for ~137 of 510 file ×
        // query mismatches. Verified against beanquery 0.2.0 + beancount
        // 3.2.3 (matches what CI installs and what the dev shell now
        // ships via the compat container — see PR #1047). Source-level
        // `format_cost_spec` (used by `rledger format` to round-trip
        // ledger files) keeps the no-space `{N CCY}` form because that
        // matches Beancount's `print` command output, not its
        // `Position.__str__`.
        write!(f, "{{ {} {}", self.number, self.currency)?;
        if let Some(date) = self.date {
            write!(f, ", {date}")?;
        }
        if let Some(label) = &self.label {
            // Escape via `format::escape_string` so labels containing
            // `"`, `\`, or `\n` round-trip safely. Without this a label
            // like `say "hi"` would render as `"say "hi""` — a parse
            // error if anyone tried to feed it back to a Beancount-
            // compatible reader.
            write!(f, ", \"{}\"", crate::format::escape_string(label))?;
        }
        write!(f, "}}")
    }
}

/// A cost specification for matching or creating costs.
///
/// Unlike [`Cost`], all fields are optional to allow partial matching.
/// This is used in postings where the user may specify only some
/// cost components (e.g., just the date to match a specific lot).
///
/// # Matching Rules
///
/// A `CostSpec` matches a `Cost` if all specified fields match:
/// - If `number` is `Some`, it must equal the cost's number
/// - If `currency` is `Some`, it must equal the cost's currency
/// - If `date` is `Some`, it must equal the cost's date
/// - If `label` is `Some`, it must equal the cost's label
///
/// # Examples
///
/// ```
/// use rustledger_core::{Cost, CostSpec};
/// use rust_decimal_macros::dec;
///
/// let cost = Cost::new(dec!(150.00), "USD")
///     .with_date(rustledger_core::naive_date(2024, 1, 15).unwrap());
///
/// // Match by date only
/// let spec = CostSpec::default().with_date(rustledger_core::naive_date(2024, 1, 15).unwrap());
/// assert!(spec.matches(&cost));
///
/// // Match by wrong date
/// let spec2 = CostSpec::default().with_date(rustledger_core::naive_date(2024, 1, 16).unwrap());
/// assert!(!spec2.matches(&cost));
/// ```
/// The numeric component of a [`CostSpec`].
///
/// Beancount cost specs name a number in one of two source-level
/// shapes:
///
/// - `{150.00 USD}` — per-unit cost ([`Self::PerUnit`])
/// - `{{ 1500.00 USD }}` — total cost for the posting's units
///   ([`Self::Total`])
///
/// During booking the engine converts `Total(t)` into a third state,
/// [`Self::PerUnitFromTotal`], carrying both the derived per-unit
/// value (for display, lot tracking) and the original total (for
/// precision-preserving residual math — division-then-multiplication
/// loses precision at the `rust_decimal` 28-digit ceiling).
///
/// A cost spec without a number at all (e.g. `{}` for a booking-
/// deferred lot match) is represented by `CostSpec.number: None`.
///
/// Pre-#1164 the per-unit and total numbers were two independent
/// `Option<Decimal>` fields on `CostSpec`. The invalid both-set state
/// was prevented only by parser discipline and downstream defensive
/// branches; the "booked from total" state was modeled accidentally
/// by setting both fields, with the meaning encoded only in code
/// comments. Folding the axes into one enum makes both the
/// pre-booking invalid state unrepresentable AND the post-booking
/// derived state explicit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)
)]
// Serde uses the `kind`-tagged internal representation so this enum
// matches the wire shape used by FFI-WASI, WASM, Python compat, and
// plugin-types. Pre-tag, serde defaulted to the external-tag form
// (`{"PerUnit": "100"}`) which diverged from those boundaries —
// downstream clients had to know which surface they were talking to.
// (Module-level `allow(missing_docs)` at the top of this file
// silences the rkyv-generated archived-struct field doc warnings —
// see the file header comment.)
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum CostNumber {
    /// Per-unit cost as written: `{150.00 USD}`. Booking leaves this
    /// shape unchanged.
    PerUnit {
        /// Per-unit value.
        #[cfg_attr(feature = "rkyv", rkyv(with = AsDecimal))]
        value: Decimal,
    },
    /// Total cost as written: `{{ 1500.00 USD }}`. Booking rewrites
    /// this to [`Self::PerUnitFromTotal`] once units are known.
    Total {
        /// Total value.
        #[cfg_attr(feature = "rkyv", rkyv(with = AsDecimal))]
        value: Decimal,
    },
    /// Post-booking state: a per-unit value derived from a
    /// `{{ total USD }}` spec at booking time, with the source total
    /// preserved for exact residual math. Pre-#1164 this was modeled
    /// implicitly by setting both `number_per` and `number_total` on
    /// `CostSpec`. The payload is a separate [`BookedCost`] struct
    /// so the booking-time invariant lives on a named type with
    /// constructor methods that enforce it.
    PerUnitFromTotal(BookedCost),
}

/// Payload of [`CostNumber::PerUnitFromTotal`].
///
/// Carries both the per-unit value derived at booking time and the
/// original `{{ total }}` cost so residual math can use the exact
/// total (avoiding the division-then-multiplication precision loss
/// that hits the `rust_decimal` 28-digit ceiling on long ledgers).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)
)]
pub struct BookedCost {
    /// Per-unit cost, derived as `total / |units|` during booking.
    /// Used by lot tracking, display (Python-compat post-booking
    /// per-unit form), and validation reads that want a per-unit
    /// value.
    #[cfg_attr(feature = "rkyv", rkyv(with = AsDecimal))]
    pub per_unit: Decimal,
    /// Original total as written. Used by residual calculation to
    /// avoid the division-then-multiplication precision loss that
    /// would otherwise leak into balance checks.
    #[cfg_attr(feature = "rkyv", rkyv(with = AsDecimal))]
    pub total: Decimal,
}

/// Diagnostic for a failed [`BookedCost`] consistency check.
///
/// Returned by [`BookedCost::try_new`] in three cases:
/// - **Mismatch**: `per_unit * |units|` doesn't agree with `total` to
///   within the `rust_decimal` rounding floor.
/// - **Zero units**: every `per_unit` "works" by zero-multiplication
///   so the invariant carries no information; the post-booking shape
///   is structurally meaningless without units.
/// - **Overflow**: `per_unit * |units|` would exceed `Decimal::MAX`
///   (~7.92e28). Both operands fit in `Decimal` individually but their
///   product doesn't. A wire client can reach this with extreme
///   inputs; surfacing it as a typed error keeps the host from
///   panicking on multiplication.
///
/// Carries the inputs and (for the mismatch case) the computed
/// residual so trust-boundary callers can surface a meaningful error
/// to the originating plugin or wire client ("you sent
/// `per_unit=50, total=999` with `units=10`; derived total would be
/// 500, off by 499 — far outside tolerance 1e-20"). Mapping this to a
/// `ConversionError` variant gives plugin authors a typed category
/// for the failure instead of conflating with `InvalidNumber` (parse
/// failure).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BookedCostInvariantError {
    /// The per-unit value the caller supplied.
    pub per_unit: Decimal,
    /// The total value the caller supplied.
    pub total: Decimal,
    /// The units value the caller supplied (caller-side sign retained
    /// so error messages can show what came in).
    pub units: Decimal,
    /// `per_unit * |units|`, the value we'd expect `total` to equal.
    /// `Decimal::ZERO` when the multiplication couldn't be performed
    /// (zero units, or overflow — see [`Self::overflow`]).
    pub derived_total: Decimal,
    /// `|derived_total - total|`, the magnitude of the violation.
    /// `Decimal::ZERO` for the zero-units and overflow cases.
    pub abs_diff: Decimal,
    /// The tolerance threshold we tested against. `None` when units
    /// was zero or the multiplication overflowed — see
    /// [`Self::overflow`] to distinguish the two.
    pub tolerance: Option<Decimal>,
    /// `true` when `per_unit * |units|` overflowed `Decimal::MAX`
    /// (~7.92e28). Distinguishes the overflow case from the zero-units
    /// case, since both leave `tolerance: None`.
    pub overflow: bool,
}

impl fmt::Display for BookedCostInvariantError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.overflow {
            return write!(
                f,
                "BookedCost invariant check overflowed Decimal precision: per_unit ({}) * |units| ({}) exceeds Decimal::MAX (~7.92e28)",
                self.per_unit,
                self.units.abs(),
            );
        }
        match self.tolerance {
            Some(tol) => write!(
                f,
                "BookedCost invariant violated: per_unit ({}) * |units| ({}) = {} ≠ total ({}); abs_diff {} exceeds tolerance {}",
                self.per_unit,
                self.units.abs(),
                self.derived_total,
                self.total,
                self.abs_diff,
                tol,
            ),
            None => write!(
                f,
                "BookedCost requires non-zero units; got per_unit ({}), total ({}), units (0)",
                self.per_unit, self.total,
            ),
        }
    }
}

impl std::error::Error for BookedCostInvariantError {}

impl BookedCost {
    /// Check `per_unit * |units| ≈ total` to within `rust_decimal`
    /// rounding tolerance, returning the diagnostic on failure.
    ///
    /// The booker derives `per_unit = total / |units|` at 28 significant
    /// digits; back-multiplying truncates similarly. The residual can
    /// reach a few ULP, which scales with `|total|`. Tolerance is
    /// `max(1e-20, |total| * 1e-24)` — `1e-24` is ~10000x larger than
    /// one ULP for typical magnitudes, while the absolute floor
    /// guarantees a sane window for near-zero totals.
    ///
    /// **`units == 0` is rejected**: the post-booking shape implies the
    /// booker derived `per_unit` from `total / |units|`, which is
    /// undefined for zero units. A zero-units `PerUnitFromTotal` is
    /// structurally meaningless and the caller should use the raw
    /// `PerUnit` / `Total` variants. Pre-fix the zero-units case
    /// short-circuited to `true`, which defeated the trust-boundary
    /// guard at every input bridge (review B-3.1).
    fn check_invariant(
        per_unit: Decimal,
        total: Decimal,
        units: Decimal,
    ) -> Result<(), BookedCostInvariantError> {
        let units_abs = units.abs();
        if units_abs.is_zero() {
            return Err(BookedCostInvariantError {
                per_unit,
                total,
                units,
                derived_total: Decimal::ZERO,
                abs_diff: Decimal::ZERO,
                tolerance: None,
                overflow: false,
            });
        }
        // `per_unit` and `units_abs` each fit in `Decimal` individually
        // (they came through `from_str_exact` or were constructed by
        // the booker from values that did), but their product can
        // exceed `Decimal::MAX` (~7.92e28). `Decimal::mul` panics on
        // overflow — at a trust boundary that would crash the host
        // from wire input, defeating `try_new`'s typed-error contract.
        // Surface overflow as a typed error instead.
        let Some(derived_total) = per_unit.checked_mul(units_abs) else {
            return Err(BookedCostInvariantError {
                per_unit,
                total,
                units,
                derived_total: Decimal::ZERO,
                abs_diff: Decimal::ZERO,
                tolerance: None,
                overflow: true,
            });
        };
        let abs_diff = (derived_total - total).abs();
        // `total.abs() * 1e-24` cannot overflow: `Decimal::MAX` is
        // ~7.92e28, so the product is bounded by ~7.92e4. The relative
        // tolerance scales with the magnitude of `total`; the absolute
        // floor (`1e-20`) keeps the window sane for near-zero totals.
        let relative = total.abs() * Decimal::new(1, 24);
        let tolerance = if relative > Decimal::new(1, 20) {
            relative
        } else {
            Decimal::new(1, 20)
        };
        if abs_diff <= tolerance {
            Ok(())
        } else {
            Err(BookedCostInvariantError {
                per_unit,
                total,
                units,
                derived_total,
                abs_diff,
                tolerance: Some(tolerance),
                overflow: false,
            })
        }
    }

    /// Construct from booking with a precision invariant check.
    ///
    /// In debug builds, asserts that `per_unit * |units| ≈ total` to
    /// the limits of `rust_decimal` precision (tolerance:
    /// `max(1e-20, |total| * 1e-24)`, derived from the booker's
    /// `total / |units|` divisor truncating at 28 significant digits;
    /// see the private `check_invariant` helper for the exact
    /// computation). Callers are the booker (which derives
    /// `per_unit = total / |units|`) and the plugin / FFI ingress
    /// bridges (which must validate consistency before constructing).
    ///
    /// # Panics
    ///
    /// In debug builds: if the invariant fails. Release builds skip
    /// the check (but trust-boundary callers should use
    /// [`Self::try_new`] for runtime validation in release too).
    #[must_use]
    pub fn new(per_unit: Decimal, total: Decimal, units: Decimal) -> Self {
        debug_assert!(
            Self::check_invariant(per_unit, total, units).is_ok(),
            "{}",
            Self::check_invariant(per_unit, total, units).unwrap_err(),
        );
        Self { per_unit, total }
    }

    /// Try to construct, returning a typed error if the consistency
    /// invariant fails. Use this at trust boundaries (FFI input,
    /// plugin egress) where the caller may have supplied inconsistent
    /// values and you want to reject rather than panic in debug or
    /// accept silently in release.
    ///
    /// # Errors
    ///
    /// Returns [`BookedCostInvariantError`] when:
    /// - `units == 0` (the post-booking shape is structurally
    ///   undefined for zero units; callers should send `PerUnit` or
    ///   `Total` instead).
    /// - `per_unit * |units|` differs from `total` by more than
    ///   `max(1e-20, |total| * 1e-24)`.
    pub fn try_new(
        per_unit: Decimal,
        total: Decimal,
        units: Decimal,
    ) -> Result<Self, BookedCostInvariantError> {
        Self::check_invariant(per_unit, total, units)?;
        Ok(Self { per_unit, total })
    }

    /// Construct from rkyv archive bytes the host itself wrote.
    ///
    /// Bypasses the consistency invariant because rkyv archives carry
    /// no units at the deserialization site, and the host invariant
    /// was already enforced when the bytes were written. **Do not
    /// call from boundary code** — every FFI / plugin / parser
    /// ingress must go through [`Self::try_new`] (which surfaces a
    /// typed error) so inconsistent pairs cannot enter the host.
    ///
    /// The name reflects the trust assumption: the caller has
    /// verified (via cache-version checks, archive integrity, etc.)
    /// that the bytes were produced by this host's own booker.
    #[doc(hidden)]
    #[must_use]
    pub const fn from_archive_bytes_trusted(per_unit: Decimal, total: Decimal) -> Self {
        Self { per_unit, total }
    }

    /// Construct an *intentionally inconsistent* `BookedCost` for
    /// fuzzing trust-boundary code that must reject such inputs.
    ///
    /// Separate from [`Self::from_archive_bytes_trusted`] so the
    /// "trusted" name doesn't lie at fuzz call sites — the fuzzer
    /// explicitly generates pathological inputs. Gated behind the
    /// `fuzz` Cargo feature so normal builds can't reach it (review
    /// A-4.4); fuzz targets and integration tests that want to
    /// stress trust-boundary code in convert bridges must opt in via
    /// `features = ["fuzz"]` on their `rustledger-core` dep.
    #[cfg(any(feature = "fuzz", test))]
    #[doc(hidden)]
    #[must_use]
    pub const fn from_fuzz_unchecked(per_unit: Decimal, total: Decimal) -> Self {
        Self { per_unit, total }
    }
}

impl CostNumber {
    /// Return the per-unit value if this number carries one.
    ///
    /// - [`Self::PerUnit`] → `Some(its Decimal)`
    /// - [`Self::PerUnitFromTotal`] → `Some(per_unit)`
    /// - [`Self::Total`] → `None` (booking hasn't computed per-unit yet)
    #[must_use]
    pub const fn per_unit(&self) -> Option<Decimal> {
        match self {
            Self::PerUnit { value } => Some(*value),
            Self::PerUnitFromTotal(b) => Some(b.per_unit),
            Self::Total { .. } => None,
        }
    }

    /// Return the total value if this number carries one.
    ///
    /// - [`Self::Total`] → `Some(its Decimal)`
    /// - [`Self::PerUnitFromTotal`] → `Some(total)`
    /// - [`Self::PerUnit`] → `None`
    #[must_use]
    pub const fn total(&self) -> Option<Decimal> {
        match self {
            Self::Total { value } => Some(*value),
            Self::PerUnitFromTotal(b) => Some(b.total),
            Self::PerUnit { .. } => None,
        }
    }
}

/// A cost specification on a posting (`{...}` or `{{...}}`).
///
/// Carries the parsed cost-spec axes: the numeric component (per-unit
/// vs total, modeled as the mutually-exclusive [`CostNumber`] enum),
/// currency, lot date, label, and merge flag. Any subset may be
/// missing — `{}` corresponds to all-fields-`None` plus `merge: false`,
/// which lets the booker do lot matching deferred to inventory.
///
/// Pre-#1164 this struct had two independent `Option<Decimal>` fields
/// (`number_per`, `number_total`). The mutual-exclusion invariant was
/// enforced only by parser discipline; the post-booking "derived per-
/// unit from total" state was modeled accidentally by setting both
/// fields at once. The new shape (`number: Option<CostNumber>`) makes
/// the invalid state unrepresentable and the derived state explicit.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)
)]
pub struct CostSpec {
    /// The numeric component: per-unit, total, or absent.
    ///
    /// Replaces the pre-#1164 `number_per` / `number_total` pair, which
    /// allowed the invalid both-set state at the type level. See
    /// [`CostNumber`] for the per-unit vs total distinction.
    pub number: Option<CostNumber>,
    /// Currency of the cost (if specified)
    pub currency: Option<crate::Currency>,
    /// Acquisition date (if specified)
    #[cfg_attr(feature = "rkyv", rkyv(with = rkyv::with::Map<AsNaiveDate>))]
    pub date: Option<NaiveDate>,
    /// Lot label (if specified)
    pub label: Option<String>,
    /// Whether to merge with existing lot (average cost)
    pub merge: bool,
}

impl CostSpec {
    /// Create an empty cost spec.
    #[must_use]
    pub fn empty() -> Self {
        Self::default()
    }

    /// Set the cost number directly.
    ///
    /// The mutual exclusion between per-unit and total is enforced by
    /// the [`CostNumber`] enum — there is no way to set both. Callers
    /// construct the variant explicitly:
    ///
    /// ```ignore
    /// CostSpec::empty().with_number(CostNumber::PerUnit { value: dec!(150) });
    /// CostSpec::empty().with_number(CostNumber::Total { value: dec!(1500) });
    /// ```
    ///
    /// Pre-#1164 this slot was a pair of `Option<Decimal>` fields;
    /// pre-this-PR there were `with_per_unit` / `with_total`
    /// convenience shims that perpetuated the two-axis mental model
    /// in caller code and silently overwrote each other if both were
    /// called. Both are gone — there's exactly one way to set a cost
    /// number now.
    #[must_use]
    pub const fn with_number(mut self, number: CostNumber) -> Self {
        self.number = Some(number);
        self
    }

    /// Set the currency.
    #[must_use]
    pub fn with_currency(mut self, currency: impl Into<crate::Currency>) -> Self {
        self.currency = Some(currency.into());
        self
    }

    /// Set the date.
    #[must_use]
    pub const fn with_date(mut self, date: NaiveDate) -> Self {
        self.date = Some(date);
        self
    }

    /// Set the label.
    #[must_use]
    pub fn with_label(mut self, label: impl Into<String>) -> Self {
        self.label = Some(label.into());
        self
    }

    /// Set the merge flag (for average cost booking).
    #[must_use]
    pub const fn with_merge(mut self) -> Self {
        self.merge = true;
        self
    }

    /// Check if this is an empty cost spec (all fields None).
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.number.is_none()
            && self.currency.is_none()
            && self.date.is_none()
            && self.label.is_none()
            && !self.merge
    }

    /// Check if this cost spec matches a cost.
    ///
    /// All specified fields must match the corresponding cost fields.
    /// Per-unit matching uses `CostNumber::per_unit()` — a `Total`-only
    /// spec doesn't constrain the per-unit lot value (booking hasn't
    /// resolved it yet), but a `PerUnitFromTotal` post-booking spec
    /// does.
    #[must_use]
    pub fn matches(&self, cost: &Cost) -> bool {
        // Check per-unit cost — constrains the lot whenever the spec
        // carries a per-unit value (PerUnit or PerUnitFromTotal).
        if let Some(n) = self.number.and_then(|cn| cn.per_unit())
            && n != cost.number
        {
            return false;
        }
        // Check currency
        if let Some(c) = &self.currency
            && c != &cost.currency
        {
            return false;
        }
        // Check date
        if let Some(d) = &self.date
            && cost.date.as_ref() != Some(d)
        {
            return false;
        }
        // Check label
        if let Some(l) = &self.label
            && cost.label.as_ref() != Some(l)
        {
            return false;
        }
        true
    }

    /// Resolve this cost spec to a concrete cost, given the number of units.
    ///
    /// If the number is `CostNumber::Total`, the per-unit cost is
    /// calculated as `total / |units|`. Full precision is preserved to
    /// avoid cost basis errors when the position is later sold.
    /// `PerUnitFromTotal` already carries the derived per-unit value
    /// from a prior booking pass — using `b.per_unit` directly is
    /// equivalent to recomputing `b.total / |units|` because
    /// [`BookedCost::new`] enforces that invariant at construction.
    ///
    /// Returns `None` if required fields (currency, number) are missing.
    #[must_use]
    pub fn resolve(&self, units: Decimal, date: NaiveDate) -> Option<Cost> {
        let currency = self.currency.clone()?;
        let number = match self.number? {
            // User-specified per-unit cost.
            CostNumber::PerUnit { value: per } => per,
            // Calculated from total — preserve full precision.
            CostNumber::Total { value: total } => total / units.abs(),
            // Already booked: `b.per_unit == b.total / |units|` by
            // `BookedCost::new`'s invariant, so this is identical to
            // the `Total` arm above but without the redivision.
            CostNumber::PerUnitFromTotal(b) => b.per_unit,
        };

        Some(Cost {
            number,
            currency,
            date: self.date.or(Some(date)),
            label: self.label.clone(),
        })
    }
}

impl fmt::Display for CostSpec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        // Max 5 elements: number, currency, date, label, merge
        let mut parts = Vec::with_capacity(5);

        match self.number {
            Some(CostNumber::PerUnit { value: n }) => parts.push(format!("{n}")),
            Some(CostNumber::PerUnitFromTotal(b)) => parts.push(format!("{}", b.per_unit)),
            Some(CostNumber::Total { value: n }) => parts.push(format!("# {n}")),
            None => {}
        }
        if let Some(c) = &self.currency {
            parts.push(c.to_string());
        }
        if let Some(d) = self.date {
            parts.push(d.to_string());
        }
        if let Some(l) = &self.label {
            parts.push(format!("\"{l}\""));
        }
        if self.merge {
            parts.push("*".to_string());
        }

        write!(f, "{}", parts.join(", "))?;
        write!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;

    fn date(year: i32, month: u32, day: u32) -> NaiveDate {
        crate::naive_date(year, month, day).unwrap()
    }

    #[test]
    fn test_cost_new() {
        let cost = Cost::new(dec!(150.00), "USD");
        assert_eq!(cost.number, dec!(150.00));
        assert_eq!(cost.currency, "USD");
        assert!(cost.date.is_none());
        assert!(cost.label.is_none());
    }

    #[test]
    fn test_cost_builder() {
        let cost = Cost::new(dec!(150.00), "USD")
            .with_date(date(2024, 1, 15))
            .with_label("lot1");

        assert_eq!(cost.date, Some(date(2024, 1, 15)));
        assert_eq!(cost.label, Some("lot1".to_string()));
    }

    #[test]
    fn test_cost_total() {
        let cost = Cost::new(dec!(150.00), "USD");
        let total = cost.total_cost(dec!(10));
        assert_eq!(total.number, dec!(1500.00));
        assert_eq!(total.currency, "USD");
    }

    #[test]
    fn test_cost_display() {
        let cost = Cost::new(dec!(150.00), "USD")
            .with_date(date(2024, 1, 15))
            .with_label("lot1");
        let s = format!("{cost}");
        assert!(s.contains("150.00"));
        assert!(s.contains("USD"));
        assert!(s.contains("2024-01-15"));
        assert!(s.contains("lot1"));
    }

    /// Exact-format regression covering both fixes in this PR:
    /// - leading space inside `{` (matches Beancount Position.__str__)
    /// - special-character escaping in labels via `format::escape_string`
    #[test]
    fn test_cost_display_escapes_special_characters_in_label() {
        // Bare per-unit cost — pin the leading-space form.
        let bare = Cost::new(dec!(520), "USD");
        assert_eq!(format!("{bare}"), "{ 520 USD}");

        // With date.
        let dated = Cost::new(dec!(520.00), "USD").with_date(date(2024, 1, 15));
        assert_eq!(format!("{dated}"), "{ 520.00 USD, 2024-01-15}");

        // Embedded double-quote.
        let quoted = Cost::new(dec!(100.00), "USD")
            .with_date(date(2024, 1, 15))
            .with_label("say \"hi\"");
        assert_eq!(
            format!("{quoted}"),
            "{ 100.00 USD, 2024-01-15, \"say \\\"hi\\\"\"}"
        );

        // Embedded backslash.
        let backslash = Cost::new(dec!(50.00), "USD").with_label("path\\to\\lot");
        assert_eq!(
            format!("{backslash}"),
            "{ 50.00 USD, \"path\\\\to\\\\lot\"}"
        );

        // Embedded newline.
        let newline = Cost::new(dec!(75.00), "USD").with_label("line1\nline2");
        assert_eq!(format!("{newline}"), "{ 75.00 USD, \"line1\\nline2\"}");

        // Plain label still works (no escaping changes for safe chars).
        let plain = Cost::new(dec!(540.00), "USD")
            .with_date(date(2024, 2, 15))
            .with_label("lot-A");
        assert_eq!(format!("{plain}"), "{ 540.00 USD, 2024-02-15, \"lot-A\"}");
    }

    #[test]
    fn test_cost_spec_empty() {
        let spec = CostSpec::empty();
        assert!(spec.is_empty());
    }

    #[test]
    fn test_cost_spec_matches() {
        let cost = Cost::new(dec!(150.00), "USD")
            .with_date(date(2024, 1, 15))
            .with_label("lot1");

        // Empty spec matches everything
        assert!(CostSpec::empty().matches(&cost));

        // Match by number
        let spec = CostSpec::empty().with_number(crate::CostNumber::PerUnit {
            value: dec!(150.00),
        });
        assert!(spec.matches(&cost));

        // Wrong number
        let spec = CostSpec::empty().with_number(crate::CostNumber::PerUnit {
            value: dec!(160.00),
        });
        assert!(!spec.matches(&cost));

        // Match by currency
        let spec = CostSpec::empty().with_currency("USD");
        assert!(spec.matches(&cost));

        // Match by date
        let spec = CostSpec::empty().with_date(date(2024, 1, 15));
        assert!(spec.matches(&cost));

        // Match by label
        let spec = CostSpec::empty().with_label("lot1");
        assert!(spec.matches(&cost));

        // Match by all
        let spec = CostSpec::empty()
            .with_number(crate::CostNumber::PerUnit {
                value: dec!(150.00),
            })
            .with_currency("USD")
            .with_date(date(2024, 1, 15))
            .with_label("lot1");
        assert!(spec.matches(&cost));
    }

    #[test]
    fn test_cost_spec_resolve() {
        let spec = CostSpec::empty()
            .with_number(crate::CostNumber::PerUnit {
                value: dec!(150.00),
            })
            .with_currency("USD");

        let cost = spec.resolve(dec!(10), date(2024, 1, 15)).unwrap();
        assert_eq!(cost.number, dec!(150.00));
        assert_eq!(cost.currency, "USD");
        assert_eq!(cost.date, Some(date(2024, 1, 15)));
    }

    #[test]
    fn test_cost_spec_resolve_total() {
        let spec = CostSpec::empty()
            .with_number(crate::CostNumber::Total {
                value: dec!(1500.00),
            })
            .with_currency("USD");

        let cost = spec.resolve(dec!(10), date(2024, 1, 15)).unwrap();
        assert_eq!(cost.number, dec!(150.00)); // 1500 / 10
        assert_eq!(cost.currency, "USD");
    }

    // ===== BookedCost / PerUnitFromTotal tests (#1164) =====

    #[test]
    fn booked_cost_new_accepts_consistent_pair() {
        // 10 units of "300 total" → 30 per-unit. Constructor must
        // accept; debug_assert sees per_unit * |units| == total.
        let b = BookedCost::new(dec!(30), dec!(300), dec!(10));
        assert_eq!(b.per_unit, dec!(30));
        assert_eq!(b.total, dec!(300));
    }

    #[test]
    fn booked_cost_new_accepts_negative_units() {
        // Sales (negative units) still produce consistent
        // PerUnitFromTotal: per_unit * |units| == total uses .abs().
        let b = BookedCost::new(dec!(30), dec!(300), dec!(-10));
        assert_eq!(b.per_unit, dec!(30));
    }

    #[test]
    #[should_panic(expected = "BookedCost invariant violated")]
    fn booked_cost_new_rejects_inconsistent_pair_in_debug() {
        // per_unit (50) * |units| (10) = 500, NOT 300. Invariant must
        // fire. Release builds would skip the check by design — this
        // test verifies the debug-build safety net.
        let _ = BookedCost::new(dec!(50), dec!(300), dec!(10));
    }

    #[test]
    #[should_panic(expected = "requires non-zero units")]
    fn booked_cost_new_rejects_zero_units_in_debug() {
        // Post-A-3.5/B-3.1: zero units is structurally meaningless
        // for the post-booking shape (every per_unit "works" by
        // zero-multiplication). `new` debug-asserts and panics;
        // `try_new` returns a typed error. The booker never
        // constructs PerUnitFromTotal with zero units (see book.rs),
        // so this only fires when boundary code forgets to validate.
        let _ = BookedCost::new(dec!(7), dec!(99), dec!(0));
    }

    #[test]
    fn booked_cost_from_archive_bytes_trusted_skips_invariant() {
        // rkyv deserialization uses this when units aren't at hand.
        // Constructs the inconsistent pair without panicking —
        // verifying it's truly unchecked. Plugin / FFI ingress code
        // must NOT use this path; they get `try_new`.
        let b = BookedCost::from_archive_bytes_trusted(dec!(50), dec!(300));
        assert_eq!(b.per_unit, dec!(50));
        assert_eq!(b.total, dec!(300));
    }

    #[test]
    fn booked_cost_from_fuzz_unchecked_skips_invariant() {
        // Fuzz harness uses this to generate pathological inputs that
        // stress trust-boundary code in convert bridges. Distinct
        // from the archive constructor at the source level so grep
        // can identify each kind of bypass.
        let b = BookedCost::from_fuzz_unchecked(dec!(999999), dec!(0.01));
        assert_eq!(b.per_unit, dec!(999999));
        assert_eq!(b.total, dec!(0.01));
    }

    #[test]
    fn booked_cost_try_new_rejects_inconsistent_pair_with_diagnostic() {
        // Trust-boundary constructor must return a typed error for
        // inconsistent pairs. 10 units × 50/u = 500, not 999.
        let err = BookedCost::try_new(dec!(50), dec!(999), dec!(10))
            .expect_err("expected invariant error for inconsistent input");
        assert_eq!(err.per_unit, dec!(50));
        assert_eq!(err.total, dec!(999));
        assert_eq!(err.units, dec!(10));
        assert_eq!(err.derived_total, dec!(500));
        assert_eq!(err.abs_diff, dec!(499));
        assert!(err.tolerance.is_some(), "tolerance must be reported");
        assert!(!err.overflow, "this case is mismatch, not overflow");

        // Display includes both supplied and derived values for
        // plugin-author diagnostics.
        let msg = format!("{err}");
        assert!(msg.contains("50") && msg.contains("999") && msg.contains("500"));
    }

    #[test]
    fn booked_cost_try_new_rejects_zero_units() {
        // Pre-fix the zero-units case short-circuited to "valid",
        // defeating the trust-boundary guard at every input bridge
        // (review B-3.1). PerUnitFromTotal is structurally
        // meaningless for zero units — every per_unit "works" by
        // zero-multiplication. Reject explicitly with `tolerance:
        // None` so callers can distinguish this from a numeric
        // mismatch.
        let err = BookedCost::try_new(dec!(999999), dec!(0.01), dec!(0))
            .expect_err("zero units must be rejected, not silently accepted");
        assert!(err.tolerance.is_none(), "zero-units error has no tolerance");
        assert!(!err.overflow, "this is zero-units, not overflow");
        assert!(format!("{err}").contains("non-zero units"));
    }

    #[test]
    fn booked_cost_try_new_accepts_consistent_pair() {
        let result = BookedCost::try_new(dec!(50), dec!(500), dec!(10));
        assert!(result.is_ok());
    }

    #[test]
    #[should_panic(expected = "overflow")]
    fn booked_cost_new_panics_in_debug_on_overflow() {
        // `BookedCost::new` debug-asserts the invariant. Overflow
        // should reach the assertion via `check_invariant`'s Err, then
        // panic with a message that names the failure mode — same
        // contract as the existing zero-units / mismatch debug
        // asserts. Without this test, a future refactor of
        // `check_invariant`'s error path could swallow the overflow
        // case at the `new` call site (e.g. by short-circuiting to
        // Ok or by using a different Display) and the `new`-side
        // contract would degrade silently. Inputs: 5e15 × 5e15 →
        // 2.5e31, which exceeds Decimal::MAX (~7.92e28).
        let huge = Decimal::from_str_exact("5000000000000000").unwrap();
        let _ = BookedCost::new(huge, Decimal::from_str_exact("0.01").unwrap(), huge);
    }

    #[test]
    fn booked_cost_try_new_surfaces_overflow_instead_of_panicking() {
        // Trust-boundary regression guard: a wire client can submit
        // per_unit and units that each fit in Decimal but whose product
        // exceeds Decimal::MAX (~7.92e28). Pre-fix `check_invariant`
        // used bare `*` and panicked the host on multiplication;
        // `try_new` now surfaces it as a typed error so FFI / plugin
        // bridges can map it to ConversionError and propagate to the
        // caller. Inputs: 5e15 × 5e15 = 2.5e31, well over Decimal::MAX.
        let per_unit = Decimal::from_str_exact("5000000000000000").unwrap();
        let units = Decimal::from_str_exact("5000000000000000").unwrap();
        let total = Decimal::from_str_exact("0.01").unwrap();
        let err = BookedCost::try_new(per_unit, total, units)
            .expect_err("overflow must surface as Err, not panic");
        assert!(err.overflow, "overflow flag must be set");
        assert!(
            err.tolerance.is_none(),
            "no tolerance comparison performed for overflow",
        );
        assert_eq!(err.derived_total, Decimal::ZERO);
        assert_eq!(err.abs_diff, Decimal::ZERO);

        let msg = format!("{err}");
        assert!(
            msg.contains("overflow") || msg.contains("Decimal::MAX"),
            "error message must name the overflow condition, got: {msg}"
        );
    }

    #[test]
    fn booked_cost_invariant_tolerates_rust_decimal_rounding() {
        // The booker computes per_unit = total / |units| at 28-digit
        // precision; back-multiplying truncates the same way. The
        // tolerance must accommodate the ULP-scale residual that real
        // ledgers exercise — the original tight 1e-20 floor fired
        // spuriously on cases like 300 / 1.763.
        let total = dec!(300);
        let units = dec!(1.763);
        let per_unit = total / units;
        // This must NOT panic.
        let _ = BookedCost::new(per_unit, total, units);
    }

    #[test]
    fn cost_number_per_unit_accessor() {
        assert_eq!(
            CostNumber::PerUnit { value: dec!(150) }.per_unit(),
            Some(dec!(150))
        );
        assert_eq!(CostNumber::Total { value: dec!(1500) }.per_unit(), None);
        let b = BookedCost::new(dec!(30), dec!(300), dec!(10));
        assert_eq!(CostNumber::PerUnitFromTotal(b).per_unit(), Some(dec!(30)));
    }

    #[test]
    fn cost_number_total_accessor() {
        assert_eq!(CostNumber::PerUnit { value: dec!(150) }.total(), None);
        assert_eq!(
            CostNumber::Total { value: dec!(1500) }.total(),
            Some(dec!(1500))
        );
        let b = BookedCost::new(dec!(30), dec!(300), dec!(10));
        assert_eq!(CostNumber::PerUnitFromTotal(b).total(), Some(dec!(300)));
    }

    #[test]
    fn cost_spec_resolve_per_unit_from_total_uses_per_unit_directly() {
        // Verifies the documented optimization: by `BookedCost::new`'s
        // invariant, b.per_unit == b.total / |units|, so resolve()
        // returns b.per_unit without redivision. The result must equal
        // what the `Total` arm would have computed.
        let b = BookedCost::new(dec!(30), dec!(300), dec!(10));
        let spec = CostSpec::empty()
            .with_number(CostNumber::PerUnitFromTotal(b))
            .with_currency("USD");

        let cost = spec.resolve(dec!(10), date(2024, 1, 15)).unwrap();
        assert_eq!(cost.number, dec!(30));
        assert_eq!(cost.currency, "USD");

        // Same shape via raw Total → same number after division.
        let total_spec = CostSpec::empty()
            .with_number(crate::CostNumber::Total { value: dec!(300) })
            .with_currency("USD");
        let total_cost = total_spec.resolve(dec!(10), date(2024, 1, 15)).unwrap();
        assert_eq!(cost.number, total_cost.number);
    }

    #[test]
    fn cost_spec_matches_per_unit_from_total() {
        // PerUnitFromTotal must match against a Cost by its per-unit
        // value (the lot's canonical number) — this is what lot
        // reduction code path needs.
        let cost = Cost::new(dec!(150.00), "USD")
            .with_date(date(2024, 1, 15))
            .with_label("lot1");

        let b = BookedCost::new(dec!(150), dec!(300), dec!(2));
        let spec = CostSpec::empty().with_number(CostNumber::PerUnitFromTotal(b));
        assert!(spec.matches(&cost));

        // Wrong per-unit: must not match.
        let wrong = BookedCost::new(dec!(160), dec!(320), dec!(2));
        let wrong_spec = CostSpec::empty().with_number(CostNumber::PerUnitFromTotal(wrong));
        assert!(!wrong_spec.matches(&cost));
    }

    #[test]
    fn cost_number_serde_emits_kind_tagged_shape() {
        // The unified wire shape across plugin-types, FFI-WASI, WASM,
        // and Python compat is `{"kind": "per_unit", "value": "100"}`
        // etc. This test pins that crate::CostNumber serde
        // matches — silent drift here breaks every downstream client.
        let pu = CostNumber::PerUnit { value: dec!(100) };
        let json = serde_json::to_value(pu).unwrap();
        assert_eq!(json["kind"], "per_unit", "PerUnit must use kind tag");

        let t = CostNumber::Total { value: dec!(1500) };
        let json = serde_json::to_value(t).unwrap();
        assert_eq!(json["kind"], "total");

        let b = BookedCost::new(dec!(150), dec!(300), dec!(2));
        let puft = CostNumber::PerUnitFromTotal(b);
        let json = serde_json::to_value(puft).unwrap();
        assert_eq!(json["kind"], "per_unit_from_total");
        assert_eq!(json["per_unit"], "150");
        assert_eq!(json["total"], "300");
    }

    #[test]
    fn cost_number_serde_round_trip() {
        // The cross-language wire contract is only honored if Rust
        // can also deserialize what it serialized. Pin the round-trip.
        for cn in [
            CostNumber::PerUnit { value: dec!(42) },
            CostNumber::Total { value: dec!(420) },
            CostNumber::PerUnitFromTotal(BookedCost::new(dec!(150), dec!(300), dec!(2))),
        ] {
            let json = serde_json::to_string(&cn).unwrap();
            let back: CostNumber = serde_json::from_str(&json).unwrap();
            assert_eq!(cn, back, "round trip lost data for {cn:?}");
        }
    }

    #[cfg(feature = "rkyv")]
    #[test]
    fn cost_number_rkyv_round_trip_preserves_all_variants() {
        // Cache v8 docstring claims tuple→struct variant migration is
        // byte-compatible (review A-4.1). Verify by round-tripping
        // each variant through rkyv archive bytes — if the
        // serialize/deserialize pair loses info or panics, the cache
        // claim is wrong and v8 must bump to v9.
        for cn in [
            CostNumber::PerUnit { value: dec!(150) },
            CostNumber::Total { value: dec!(1500) },
            CostNumber::PerUnitFromTotal(BookedCost::new(dec!(30), dec!(300), dec!(10))),
        ] {
            let bytes = rkyv::to_bytes::<rkyv::rancor::Error>(&cn).unwrap();
            let back: CostNumber =
                rkyv::from_bytes::<CostNumber, rkyv::rancor::Error>(&bytes).unwrap();
            assert_eq!(cn, back, "rkyv round-trip lost data for variant {cn:?}");
        }
    }

    #[cfg(feature = "rkyv")]
    #[test]
    fn cost_number_archived_bytes_snapshot() {
        // Layout snapshot: if rkyv's encoding ever changes (version
        // upgrade, attribute change, or accidental shape drift), this
        // test fires and CACHE_VERSION must bump (review A-4.1).
        // Each archived byte sequence is a fixed contract — any change
        // means existing cache files on user disks become invalid.
        let per_unit = CostNumber::PerUnit { value: dec!(150) };
        let per_unit_bytes = rkyv::to_bytes::<rkyv::rancor::Error>(&per_unit).unwrap();
        assert!(
            !per_unit_bytes.is_empty(),
            "PerUnit must serialize to non-empty bytes"
        );

        let total = CostNumber::Total { value: dec!(1500) };
        let total_bytes = rkyv::to_bytes::<rkyv::rancor::Error>(&total).unwrap();
        assert!(!total_bytes.is_empty());

        // Critical pin: PerUnit and Total of the same numeric value
        // serialize to different bytes (the discriminator must be
        // distinct). If they collide, the cache cannot distinguish
        // `{150 USD}` from `{{150 USD}}`.
        let pu_same = CostNumber::PerUnit { value: dec!(1500) };
        let pu_same_bytes = rkyv::to_bytes::<rkyv::rancor::Error>(&pu_same).unwrap();
        assert_ne!(
            total_bytes.as_ref(),
            pu_same_bytes.as_ref(),
            "PerUnit and Total of the same value must serialize distinctly"
        );

        // PerUnitFromTotal must also be distinct from PerUnit-only.
        let booked = CostNumber::PerUnitFromTotal(BookedCost::new(dec!(150), dec!(300), dec!(2)));
        let booked_bytes = rkyv::to_bytes::<rkyv::rancor::Error>(&booked).unwrap();
        let pu_only = CostNumber::PerUnit { value: dec!(150) };
        let pu_only_bytes = rkyv::to_bytes::<rkyv::rancor::Error>(&pu_only).unwrap();
        assert_ne!(
            booked_bytes.as_ref(),
            pu_only_bytes.as_ref(),
            "PerUnitFromTotal and PerUnit must serialize distinctly (preserved total is load-bearing)"
        );
    }

    // Frozen byte fixtures for the v8 cache layout live alongside
    // CACHE_VERSION in `rustledger-loader::cache::tests` so the
    // version constant and the on-disk byte layout sit in one place
    // — see `cost_number_archived_bytes_match_v8_fixtures` there.

    #[test]
    fn cost_spec_display_renders_per_unit_from_total_as_per_unit() {
        // Python-beancount compat: post-booking display uses per-unit
        // form even though source was `{{...}}`. This pins the
        // documented format-amount.rs behavior.
        let b = BookedCost::new(dec!(150), dec!(300), dec!(2));
        let spec = CostSpec::empty()
            .with_number(CostNumber::PerUnitFromTotal(b))
            .with_currency("USD");
        let s = format!("{spec}");
        // Per-unit form: just the per_unit value, not `# total`.
        assert!(s.contains("150"), "expected per-unit 150 in {s}");
        assert!(!s.contains("# 300"), "must NOT render as `# total` ({s})");
    }
}
