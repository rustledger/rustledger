//! Investment-returns composition shared by every embedding of the returns
//! engine.
//!
//! [`rustledger_returns::compute_returns`] is the canonical returns math, but it
//! takes a [`PriceOracle`](rustledger_returns::PriceOracle) rather than a
//! concrete price index — so every consumer must still build a [`PriceDatabase`]
//! from the ledger, adapt it to the trait, and construct the [`Scope`]. That
//! wiring was duplicated at the CLI (`report returns`) and the component
//! (`session.returns`) composition roots, each carrying its own `PriceDbOracle`
//! copy — exactly the re-derivation the canonical-function discipline warns
//! against. This module is the single home for that composition: both surfaces
//! call [`scope_returns`] / [`scopes_returns`], so they cannot compute different
//! figures for the same ledger.
//!
//! It lives in `rustledger-query` because that crate owns [`PriceDatabase`];
//! `rustledger-returns` deliberately stays a leaf (no dependency on the price
//! index), reaching prices only through its `PriceOracle` trait.

use rustledger_core::{Directive, NaiveDate};
use rustledger_returns::{ExtractError, Returns, Scope, compute_returns, compute_returns_multi};

use crate::PriceDatabase;

/// Compute one scope's investment returns from a booked, pad-expanded stream.
///
/// Builds the price index from the same stream — so implicit transaction prices
/// and explicit `price` directives both feed the valuation — adapts it to the
/// engine's oracle, and calls [`compute_returns`]. This is the composition the
/// CLI's `report returns` and the component's `session.returns` share; keeping
/// it here is what stops those two surfaces from drifting.
///
/// # Errors
/// Propagates [`ExtractError`] from the engine: [`ExtractError::MissingPrice`]
/// when a boundary flow or the `end_date` terminal valuation cannot be priced in
/// `reporting_currency`, or [`ExtractError::UnbookedInput`] when `directives`
/// violate the booked, pad-expanded contract (a re-merged booking-failed
/// transaction) — the engine surfaces that as an `Err`, it does not panic.
pub fn scope_returns(
    directives: &[Directive],
    scope: &Scope,
    reporting_currency: &str,
    end_date: NaiveDate,
) -> Result<Returns, ExtractError> {
    let price_db = PriceDatabase::from_directives(directives);
    compute_returns(
        directives,
        scope,
        reporting_currency,
        &price_db.as_oracle(),
        end_date,
    )
}

/// Compute several scopes' returns in ONE shared realization.
///
/// Via [`compute_returns_multi`]: the booking pass is scope-independent, so the
/// price index and realization are paid once for all scopes rather than once per
/// scope. Results come back per scope in the input order.
///
/// # Errors
/// [`ExtractError::MissingPrice`] is per-scope independent: a scope whose flow or
/// terminal valuation cannot be priced fails alone, never the others. An
/// [`ExtractError::UnbookedInput`] is different — the shared booking pass is
/// contract-violating for the whole ledger, so it fails EVERY scope (a broken
/// ledger yields no returns for any scope, not a partial report). The engine
/// surfaces both as `Err`; neither panics.
#[must_use]
pub fn scopes_returns(
    directives: &[Directive],
    scopes: &[Scope],
    reporting_currency: &str,
    end_date: NaiveDate,
) -> Vec<Result<Returns, ExtractError>> {
    let price_db = PriceDatabase::from_directives(directives);
    compute_returns_multi(
        directives,
        scopes,
        reporting_currency,
        &price_db.as_oracle(),
        end_date,
    )
}
