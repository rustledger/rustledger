//! Phantom-typed phase markers for the directive-processing pipeline.
//!
//! The loader runs directives through a strict sequence of phases:
//!
//! ```text
//! Raw → Sorted → Synthed → EarlyValidated → Booked
//!     → RegularPluginsApplied → LateValidated → Finalized
//! ```
//!
//! Phase ordering was previously enforced by code organization and
//! inline comments in `process.rs`. This module makes the ordering
//! a property of the type system: each phase transition consumes a
//! [`Directives<P>`] of one phase and produces one of the next phase
//! only. A refactor that drops a phase, swaps two phases, or calls a
//! later phase on raw input produces a type error rather than silent
//! misbehavior. See issue #1166.
//!
//! ## Phase definitions
//!
//! | Phase | Invariant after this phase |
//! |---|---|
//! | [`Raw`] | Straight from the parser. No ordering / synth / booking guarantees. |
//! | [`Sorted`] | Sorted into canonical display order `(date, priority, file_id, span.start)`. |
//! | [`Synthed`] | Synth-only plugins (`auto_accounts`, `document_discovery`) applied. |
//! | [`EarlyValidated`] | Early-phase validators ran. Account presence / lifecycle / structural errors collected. |
//! | [`Booked`] | Cost-spec interpolation done. Failed transactions partitioned out. |
//! | [`RegularPluginsApplied`] | Post-booking plugins (cost-reading) applied to the successfully-booked directives. |
//! | [`LateValidated`] | Late-phase validators ran on booked + plugin-processed directives. |
//! | [`Finalized`] | Failed transactions re-merged + re-sorted into the final display order. |
//!
//! ## Why a phantom rather than separate Vec types?
//!
//! The underlying payload is `Vec<Spanned<Directive>>` in every phase
//! — only the *invariants* differ, not the layout. Phantom-data
//! markers carry the phase at the type level without changing the
//! runtime representation. rkyv cache compatibility is preserved
//! (the wrapper is zero-sized in memory).
//!
//! ## Booking partition note
//!
//! `Directives<Booked>` carries only the successfully-booked
//! transactions. Failed ones are returned in a `FailedBookings`
//! newtype (an internal `pub(crate)` wrapper around
//! `Vec<Spanned<Directive>>`) and re-merged at [`Finalized`] (see
//! the `book` and `finalize` transitions in `process.rs`). The
//! newtype gives the out-of-band channel a name and a type — the
//! `finalize` call can't accidentally receive an arbitrary
//! `Vec<Spanned<Directive>>` (e.g. a freshly-parsed one). The
//! phantom-typed `Directives<P>` can't express "this Vec holds a
//! mix of stages," which is why the failed branch travels alongside
//! the main pipeline rather than as another phase.
//!
//! ## Open design choices documented in #1166
//!
//! - **Error state is NOT carried in the phase type.** Phase tracks
//!   ordering; errors accumulate in a separate `Vec<LedgerError>`
//!   passed through the pipeline. Including the error state in the
//!   phase would explode the variant count and impede the chain.
//! - **Only [`Finalized`] is exposed publicly.** Pipeline methods
//!   are `pub(crate)`; downstream consumers can't accidentally hold
//!   a partially-processed `Directives` because the only escape
//!   hatch is `Directives<Finalized>::into_inner()`.
//! - **Plugin trait is NOT stage-parameterized in this PR.** Plugins
//!   continue to use the `PluginPass` enum to discriminate
//!   synth-vs-regular. Making the trait phase-aware is a follow-up;
//!   the current approach catches the call-site error (calling the
//!   wrong phase function) without restructuring the plugin API.

use std::marker::PhantomData;

use rustledger_core::Directive;
use rustledger_parser::Spanned;

mod sealed {
    pub trait Sealed {}
}

/// Marker trait for pipeline phases. Sealed: only the markers in
/// this module implement it, so downstream crates can't invent new
/// phases (which would defeat the type-driven ordering).
pub trait Phase: sealed::Sealed {}

macro_rules! define_phase {
    ($name:ident, $doc:expr) => {
        #[doc = $doc]
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        pub struct $name;
        impl sealed::Sealed for $name {}
        impl Phase for $name {}
    };
}

define_phase!(
    Raw,
    "Straight from the parser — no ordering, synth, or booking guarantees."
);
define_phase!(
    Sorted,
    "Sorted by `(date, priority, file_id, span.start)` — canonical display order."
);
define_phase!(
    Synthed,
    "Synth-only plugins (`auto_accounts`, `document_discovery`) applied."
);
define_phase!(
    EarlyValidated,
    "Early validators ran; account-presence / lifecycle / structural errors collected."
);
define_phase!(
    Booked,
    "Cost-spec interpolation done; failed transactions partitioned out-of-band."
);
define_phase!(
    RegularPluginsApplied,
    "Post-booking plugins applied to successfully-booked directives."
);
define_phase!(
    LateValidated,
    "Late-phase validators ran on booked + plugin-processed directives."
);
define_phase!(
    Finalized,
    "Failed transactions re-merged + re-sorted into the final display order."
);

/// A directive collection at a specific pipeline phase.
///
/// The phase is a phantom marker — the runtime representation is the
/// same `Vec<Spanned<Directive>>` regardless of `P`. Transitions
/// between phases are the only way to advance: see the `impl`
/// blocks in `process.rs` for each phase's allowed next step.
///
/// Constructed only via [`Directives::from_parser`] (which produces
/// [`Directives<Raw>`]). Subsequent phases are reached by calling
/// the relevant transition methods in order.
#[derive(Debug)]
pub struct Directives<P: Phase> {
    inner: Vec<Spanned<Directive>>,
    _phase: PhantomData<P>,
}

impl<P: Phase> Directives<P> {
    /// **Internal**: construct a `Directives<P>` from a raw `Vec`.
    /// Phase transitions use this to advance the phantom. External
    /// callers must enter the pipeline via [`Directives::from_parser`]
    /// (which produces [`Directives<Raw>`]). Kept `const` because
    /// `from_parser` is `pub const fn` and chains through here.
    pub(crate) const fn new_unchecked(inner: Vec<Spanned<Directive>>) -> Self {
        Self {
            inner,
            _phase: PhantomData,
        }
    }

    /// Read-only borrow of the underlying directive slice.
    #[must_use]
    pub const fn as_slice(&self) -> &[Spanned<Directive>] {
        self.inner.as_slice()
    }

    /// Mutable borrow of the underlying directive vec.
    ///
    /// Pipeline transitions hand this to subsystems (booker,
    /// validator, plugin runner) that mutate in place. The phase
    /// invariant is the *next* phase's contract — mutation that
    /// breaks the invariant of the current phase is the caller's
    /// responsibility (and is normally confined to the transition
    /// function itself).
    pub(crate) const fn as_vec_mut(&mut self) -> &mut Vec<Spanned<Directive>> {
        &mut self.inner
    }

    /// Number of directives in the collection.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.inner.len()
    }

    /// Whether the collection is empty.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
}

impl Directives<Raw> {
    /// Entry point into the pipeline: wrap a parser-produced
    /// directive list as [`Directives<Raw>`]. The only public
    /// constructor — every other phase is reachable only via
    /// transitions from a prior phase.
    #[must_use]
    pub const fn from_parser(directives: Vec<Spanned<Directive>>) -> Self {
        Self::new_unchecked(directives)
    }
}

/// Transactions that failed booking, partitioned out of the main
/// pipeline by the `book` transition on [`Directives<EarlyValidated>`]
/// and re-merged at the `finalize` transition on
/// [`Directives<LateValidated>`].
///
/// Effectively `pub(crate)`: the only producer (`book`) and consumer
/// (`finalize`) are both crate-internal, and the type lives in the
/// private `mod phase` of `rustledger-loader`, so external callers
/// can't get a value of this type. Kept as a named newtype rather
/// than a bare `Vec` so `finalize` can't accidentally receive an
/// arbitrary directive list at the call site. The contents are
/// pre-booking shape: unresolved cost specs, unfilled elided slots,
/// possibly unbalanced.
#[derive(Debug)]
pub struct FailedBookings {
    inner: Vec<Spanned<Directive>>,
}

impl FailedBookings {
    /// **Internal**: construct from a raw `Vec`. The `book` transition
    /// is the only legitimate producer.
    ///
    /// `pub` only because the type lives in a private module — there's
    /// no path from the crate root to `FailedBookings::new`, so
    /// external code can't call it.
    pub const fn new(inner: Vec<Spanned<Directive>>) -> Self {
        Self { inner }
    }

    /// Consume and return the underlying directives.
    /// Used by `finalize` to merge them back into the display order.
    //
    // Not `const fn`: `self` has a destructor (the `Vec` field), and
    // E0493 forbids running destructors at compile-time. Clippy's
    // `missing_const_for_fn` knows this and correctly doesn't fire,
    // so no `#[allow]`/`#[expect]` is needed.
    pub fn into_inner(self) -> Vec<Spanned<Directive>> {
        self.inner
    }
}

impl Directives<Finalized> {
    /// Exit point: consume the finalized collection and return the
    /// underlying `Vec`. The only way to extract `Vec<Spanned<Directive>>`
    /// from the pipeline. Downstream code (`Ledger.directives`) only
    /// sees fully-processed output.
    //
    // Same rationale as above for not being `const fn`.
    #[must_use]
    pub fn into_inner(self) -> Vec<Spanned<Directive>> {
        self.inner
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn directives_raw_can_be_constructed_from_parser_output() {
        // The entry-point contract: from_parser is the only way to
        // get a `Directives<Raw>`. (Compile-fail tests for other
        // phases live as `compile_fail` doctests where appropriate;
        // here we just verify the happy path.)
        let raw = Directives::<Raw>::from_parser(Vec::new());
        assert_eq!(raw.len(), 0);
        assert!(raw.is_empty());
    }

    #[test]
    fn finalized_into_inner_returns_the_vec() {
        // Exit-point contract: into_inner consumes the wrapper and
        // returns the bare Vec. Used by the Ledger constructor.
        let finalized = Directives::<Finalized>::new_unchecked(Vec::new());
        let v = finalized.into_inner();
        assert_eq!(v.len(), 0);
    }
}
