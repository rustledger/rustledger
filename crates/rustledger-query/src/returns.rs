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

/// Compute one scope's investment returns from an interpolated, pad-expanded
/// stream (booking is not required — net units are valued at market).
///
/// Builds the price index from the same stream — so implicit transaction prices
/// and explicit `price` directives both feed the valuation — adapts it to the
/// engine's oracle, and calls [`compute_returns`]. This is the composition the
/// CLI's `report returns` and the component's `session.returns` share; keeping
/// it here is what stops those two surfaces from drifting.
///
/// The engine values **net units at market**, so a cost-basis/lot error (an
/// over-sell, an empty-cost `{}` sale with no matching lot — the common state of
/// imported brokerage data) does NOT fail the report; it nets the units, possibly
/// negative, and values at market. `rledger check` remains the validator (#1850).
///
/// # Errors
/// Propagates [`ExtractError`] from the engine: [`ExtractError::MissingPrice`]
/// when a boundary flow or the `end_date` terminal valuation cannot be priced in
/// `reporting_currency`, or [`ExtractError::UnbookedInput`] when an
/// elided/uninterpolated posting leaves a scope-relevant quantity unknown — an
/// in-scope holding, or an external boundary leg whose cash flow is unknown (the
/// one shape net-units cannot value). The engine surfaces both as an `Err`, it
/// does not panic.
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

/// Compute several scopes' returns in ONE shared accumulation.
///
/// Via [`compute_returns_multi`]: the net-units accumulation is scope-independent,
/// so the price index and the forward pass are paid once for all scopes rather
/// than once per scope. Results come back per scope in the input order.
///
/// # Errors
/// Both error kinds are **per-scope independent** — reported in the offending
/// scope's slot without affecting the others, because valuation runs per scope
/// over the shared accumulation. [`ExtractError::MissingPrice`] names a scope whose
/// flow or terminal valuation cannot be priced; [`ExtractError::UnbookedInput`]
/// names a scope with an elided/uninterpolated posting leaving a scope-relevant
/// quantity unknown (an in-scope holding, or an external boundary leg of one of
/// its transactions). A cost-basis/lot error affects no scope (net units valued at
/// market).
/// This per-scope isolation is what lets `report returns --by-group` render a
/// partial report (#1850 §4). The engine surfaces both as `Err`; neither panics.
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
