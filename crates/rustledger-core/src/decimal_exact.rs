//! Carry over-precise decimal literals (more than `rust_decimal`'s ~28 digits)
//! by **identity**, not by value.
//!
//! `Decimal` stays a 16-byte `rust_decimal::Decimal` so every hot path runs at
//! full speed. rust_decimal holds ~28–29 significant digits; Beancount (Python's
//! arbitrary-precision `Decimal`) keeps more, so a literal beyond that is rounded
//! on parse and a balance residual that depends on those digits can read zero
//! (the transaction looks balanced) where Beancount flags an imbalance.
//!
//! This module is **stateless**. It only *detects* over-precision
//! ([`overprecise_literal`]) and *reconstitutes* an exact value
//! ([`exact_to_bigdecimal`]). The exact literal is stored on the specific
//! posting that owns it, in posting metadata under [`EXACT_NUMBER_META_KEY`], so:
//! - there is no global table and no value-keyed lookup, so an over-precise
//!   literal can never leak its exact value onto an unrelated amount that merely
//!   shares its rounded value (the bug a value-keyed side table had);
//! - the exact value travels with the directive through booking and the on-disk
//!   parse cache (it is ordinary metadata, archived for free);
//! - the validator escalates to the precise residual **per transaction** (does
//!   this transaction have a posting carrying the key?), not process-globally.
//!
//! Scope: only an over-precise **posting units** literal is carried (the case
//! that affects balance residuals). Over-precise numbers in other positions
//! (cost/price/metadata) round like plain `rust_decimal` — sound (never wrong),
//! just not extended to exceed Beancount there. That's an extension point, not a
//! correctness gap.

use std::str::FromStr;

use bigdecimal::BigDecimal;
use rust_decimal::Decimal;

/// Posting-metadata key holding the exact, **unsigned** literal of an
/// over-precise units amount (the sign lives on `units.number`). Internal:
/// `__`-prefixed keys are filtered from formatted output.
pub const EXACT_NUMBER_META_KEY: &str = "__exact_number__";

/// A literal with at most this many digit characters always fits rust_decimal
/// (≤28 significant digits is guaranteed, and a ≤28-digit integer is < 2^96), so
/// the round-trip check can be skipped. 29+ digit chars *may* exceed it and are
/// checked.
const MAX_FIT_DIGITS: usize = 28;

/// If `literal` carries more precision than its rust_decimal parse (`rounded`)
/// can hold, return the exact literal verbatim. `None` when it fits — the common
/// case, gated cheaply on digit count so ordinary amounts cost only a scan.
///
/// `literal` must be the cleaned numeric text (no thousands separators).
#[must_use]
pub fn overprecise_literal(rounded: Decimal, literal: &str) -> Option<String> {
    if literal.bytes().filter(u8::is_ascii_digit).count() <= MAX_FIT_DIGITS {
        return None;
    }
    let exact = BigDecimal::from_str(literal).ok()?;
    let rounded_big = BigDecimal::from_str(&rounded.to_string()).ok()?;
    (exact != rounded_big).then(|| literal.to_string())
}

/// Reconstitute a stored exact literal as a `BigDecimal`, applying `negative`
/// (the literal is stored unsigned; the sign lives on the posting's number).
#[must_use]
pub fn exact_to_bigdecimal(literal: &str, negative: bool) -> Option<BigDecimal> {
    let v = BigDecimal::from_str(literal).ok()?;
    Some(if negative { -v } else { v })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fits_rust_decimal_returns_none() {
        for s in [
            "0",
            "1",
            "123.45",
            "0.0000000000000000000000000001", // 1e-28, fits (scale 28)
            "9999999999999999999999999999",   // 28-digit integer, fits
            "1.2345678901234567890123456789", // 28 sig digits
        ] {
            let d = Decimal::from_str(s).unwrap();
            assert_eq!(overprecise_literal(d, s), None, "{s} fits rust_decimal");
        }
    }

    #[test]
    fn over_precise_returns_exact_literal() {
        // 1 + 1e-30 (31 sig digits): rust_decimal rounds away the final 1, so
        // the detector returns the exact literal verbatim.
        let s = "1.000000000000000000000000000001";
        let d = Decimal::from_str(s).unwrap();
        assert_ne!(
            d.to_string(),
            s,
            "rust_decimal must have rounded the literal"
        );
        assert_eq!(overprecise_literal(d, s).as_deref(), Some(s));

        // A sub-1 literal whose rounded value is ZERO is still detected. Crucial:
        // the rounded value (0) is NOT a shared key — the exact literal is carried
        // per-posting — so this can't leak onto unrelated zero amounts.
        let z = "0.000000000000000000000000000001"; // 1e-30, 30 fractional places
        if let Ok(zd) = Decimal::from_str(z) {
            assert!(zd.is_zero(), "rust_decimal rounded it to 0");
            assert_eq!(overprecise_literal(zd, z).as_deref(), Some(z));
        }
    }

    #[test]
    fn sign_is_applied_on_reconstitution() {
        let s = "1.000000000000000000000000000001";
        assert_eq!(
            exact_to_bigdecimal(s, false).unwrap().to_string(),
            "1.000000000000000000000000000001"
        );
        assert_eq!(
            exact_to_bigdecimal(s, true).unwrap().to_string(),
            "-1.000000000000000000000000000001"
        );
    }
}
