//! Side channel for over-precise decimal literals.
//!
//! `Decimal` is a 16-byte [`rust_decimal::Decimal`] so every hot path runs at
//! full speed. rust_decimal holds ~29 significant digits; a literal with more
//! — which Beancount, using Python's arbitrary-precision `Decimal`, keeps
//! exactly — is rounded on parse. To *match or exceed* Beancount without taxing
//! the hot path, the exact value is stashed here, keyed by the rounded value,
//! and consulted only in the cold paths that need full precision: balance
//! residual computation and exact display.
//!
//! Hot paths — arithmetic, comparison, the 99.999% of ledgers with no
//! over-precise literal — never touch this table: the `Decimal` is unchanged,
//! and [`any_overprecise`] is a single relaxed atomic load (no lock) so callers
//! can skip per-value lookups entirely when nothing is recorded.
//!
//! ## Soundness
//!
//! - **Thread-safe.** The loader parses includes in parallel (rayon), so the
//!   table is an `RwLock` written from any thread during parse and read during
//!   validation. Over-precise literals are rare, so write contention is
//!   negligible; lookups take a shared read lock.
//! - **Collision-safe.** If two *distinct* over-precise literals round to the
//!   same `Decimal`, the key is poisoned (`None`) and both fall back to the
//!   rounded value — i.e. to plain rust_decimal behaviour, which is exactly what
//!   we'd have without this channel. So a collision can only *lose* the
//!   precision bonus, never produce a wrong value.
//! - **Append-only, self-bounding.** Entries are only added, never auto-cleared:
//!   a `clear` racing a concurrent load could wipe a live entry, and the cost of
//!   *not* clearing is trivial because over-precise literals are vanishingly
//!   rare (a handful of entries per affected file, and affected files barely
//!   exist). [`clear`] is exposed for explicit reset (tests, long-lived
//!   embedders).
//! - **Cache-aware.** A cache hit skips parsing, so an over-precise value would
//!   never be recorded. The loader therefore does **not** write the on-disk
//!   parse cache for a load containing an over-precise literal (see
//!   `rustledger`'s `loadcache`), so such files re-parse every time and the
//!   channel stays correct. Caching the exact values instead is a future option.

use std::collections::HashMap;
use std::str::FromStr;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{LazyLock, RwLock};

use bigdecimal::BigDecimal;
use rust_decimal::Decimal;

/// Rounded value → exact value. `None` marks a poisoned (collided) key.
static EXACT: LazyLock<RwLock<HashMap<Decimal, Option<BigDecimal>>>> =
    LazyLock::new(|| RwLock::new(HashMap::new()));

/// Lock-free fast path for [`any_overprecise`]: set whenever a value is
/// recorded, cleared by [`clear`]. Lets the hot validate gate skip the lock.
static PRESENT: AtomicBool = AtomicBool::new(false);

/// Number of significant digits beyond which a literal *might* exceed
/// rust_decimal and is worth the precise round-trip check. rust_decimal holds a
/// 96-bit coefficient (~29 digits), so anything with ≤29 digits is exact.
const MAX_EXACT_DIGITS: usize = 29;

/// If `literal` carries more precision than `rounded` (its rust_decimal parse)
/// can hold, record the exact value. Cheap-gated on digit count, so the common
/// case (≤29 digits — every real amount) returns immediately with no lock, no
/// allocation, no `BigDecimal`.
pub fn record_if_overprecise(rounded: Decimal, literal: &str) {
    if literal.bytes().filter(u8::is_ascii_digit).count() <= MAX_EXACT_DIGITS {
        return; // fits rust_decimal exactly — nothing to stash
    }
    let Ok(exact) = BigDecimal::from_str(literal) else {
        return;
    };
    // Only stash if rust_decimal actually lost precision.
    let rounded_big = BigDecimal::from_str(&rounded.to_string()).unwrap_or_default();
    if exact == rounded_big {
        return;
    }
    let mut table = EXACT
        .write()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    match table.get(&rounded) {
        // Same exact value already recorded — idempotent.
        Some(Some(existing)) if *existing == exact => {}
        // Distinct value already recorded (or already poisoned): collision →
        // poison so both fall back to the rounded value. Sound, never wrong.
        Some(_) => {
            table.insert(rounded, None);
        }
        None => {
            table.insert(rounded, Some(exact));
        }
    }
    PRESENT.store(true, Ordering::Relaxed);
}

/// The exact value behind a (possibly rounded) `Decimal`, if it came from an
/// over-precise literal. `None` for everything that fit rust_decimal — and the
/// overwhelmingly common case (nothing recorded) returns via the lock-free flag
/// without ever taking the lock.
#[must_use]
pub fn exact_of(rounded: Decimal) -> Option<BigDecimal> {
    if !PRESENT.load(Ordering::Relaxed) {
        return None;
    }
    let table = EXACT
        .read()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    table.get(&rounded).cloned().flatten()
}

/// Whether any over-precise literal has been recorded. A single relaxed atomic
/// load — cheap enough for the per-transaction validation gate.
#[must_use]
pub fn any_overprecise() -> bool {
    PRESENT.load(Ordering::Relaxed)
}

/// Reset the side channel. Called at the start of each load to bound memory and
/// drop stale entries.
pub fn clear() {
    EXACT
        .write()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .clear();
    PRESENT.store(false, Ordering::Relaxed);
}

#[cfg(test)]
mod tests {
    use super::*;

    // One test: the static table is process-global, so separate `#[test]`
    // functions would race on it under cargo's parallel runner. The sections run
    // sequentially here.
    #[test]
    fn side_channel_behaviour() {
        // 1. ≤29-digit literals fit rust_decimal — never recorded.
        clear();
        let d = Decimal::from_str("1.2345678901234567890123456789").unwrap(); // 29 digits
        record_if_overprecise(d, "1.2345678901234567890123456789");
        assert!(
            !any_overprecise(),
            "≤29-digit literal must not touch the table"
        );
        assert_eq!(exact_of(d), None);

        // 2. An over-precise literal is preserved exactly; clear() resets.
        clear();
        let lit = "1.234567890123456789012345678901234"; // 34 sig digits
        let rounded = Decimal::from_str(lit).unwrap(); // rounded to ~29
        record_if_overprecise(rounded, lit);
        assert!(any_overprecise());
        assert_eq!(
            exact_of(rounded).expect("recorded").to_string(),
            lit,
            "exact literal recovered, unrounded"
        );
        assert_ne!(rounded.to_string(), lit, "rust_decimal really did round it");
        clear();
        assert!(!any_overprecise(), "clear() resets the flag");
        assert_eq!(exact_of(rounded), None);

        // 3. Two distinct literals that round to the same Decimal → poisoned →
        //    both fall back to rust_decimal (None). Sound, never wrong.
        clear();
        let a = "1.000000000000000000000000000000001"; // …0001
        let b = "1.000000000000000000000000000000002"; // …0002
        let ra = Decimal::from_str(a).unwrap();
        let rb = Decimal::from_str(b).unwrap();
        assert_eq!(ra, rb, "both round to the same Decimal (precondition)");
        record_if_overprecise(ra, a);
        record_if_overprecise(rb, b);
        assert_eq!(exact_of(ra), None, "collided key falls back, never wrong");
        clear();
    }
}
