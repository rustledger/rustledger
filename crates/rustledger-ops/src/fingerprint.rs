//! Transaction fingerprinting and structural hashing.
//!
//! Provides two hashing strategies:
//!
//! - **Structural hash** — hash every field that contributes to a transaction's
//!   structural identity (flag, payee, narration, postings). Metadata is excluded.
//!   Mirrors Python beancount's `hash_entry(exclude_meta=True)`.
//!
//! - **Import fingerprint** — stable BLAKE3-based fingerprint for deduplication
//!   across import runs. Uses date + amount + normalized description text.
//!
//! The structural hash helpers use exhaustive struct destructuring so that adding
//! a field to any plugin-types struct causes a compile error here — forcing an
//! explicit decision about whether the field contributes to identity.

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::str::FromStr;

use rustledger_plugin_types::{
    AmountData, CostData, PostingData, PriceAnnotationData, TransactionData,
};

/// Sentinel bytes to discriminate `None` from `Some` in hash streams.
/// Without these, `(None, Some(x))` and `(Some(x), None)` could collide.
const ABSENT: u8 = 0;
const PRESENT: u8 = 1;

/// Compute a structural hash of a transaction.
///
/// Hashes every field that contributes to structural identity: date, flag,
/// payee, narration, tags, links, and all posting fields (account, units,
/// cost, price, flag). Metadata is deliberately excluded.
///
/// Tags and links are sorted and deduped before hashing to match beancount's
/// `frozenset` semantics.
#[must_use]
pub fn structural_hash(date: &str, txn: &TransactionData) -> u64 {
    // Destructure so any future field added to TransactionData causes a
    // compile error here.
    let TransactionData {
        flag,
        payee,
        narration,
        tags,
        links,
        metadata: _, // Intentionally excluded — matches beancount's exclude_meta=True
        postings,
    } = txn;

    let mut hasher = DefaultHasher::new();
    date.hash(&mut hasher);
    flag.hash(&mut hasher);
    payee.hash(&mut hasher);
    narration.hash(&mut hasher);

    // Tags and links are unordered sets in beancount (frozenset), so:
    // 1. Sort + dedup for stable hash regardless of parser order.
    // 2. Prefix with length so the two streams can't be swapped.
    let mut sorted_tags: Vec<&String> = tags.iter().collect();
    sorted_tags.sort();
    sorted_tags.dedup();
    sorted_tags.len().hash(&mut hasher);
    for tag in sorted_tags {
        tag.hash(&mut hasher);
    }

    let mut sorted_links: Vec<&String> = links.iter().collect();
    sorted_links.sort();
    sorted_links.dedup();
    sorted_links.len().hash(&mut hasher);
    for link in sorted_links {
        link.hash(&mut hasher);
    }

    // Prefix postings with count so the stream can't collide with set streams.
    postings.len().hash(&mut hasher);
    for posting in postings {
        hash_posting(posting, &mut hasher);
    }

    hasher.finish()
}

/// Hash a posting's structural fields.
fn hash_posting<H: Hasher>(posting: &PostingData, hasher: &mut H) {
    // Destructure for compile-time completeness checking.
    let PostingData {
        account,
        units,
        cost,
        price,
        flag,
        metadata: _, // Intentionally excluded
        span: _,     // Source location is not part of structural identity
    } = posting;

    account.hash(hasher);
    match units {
        Some(u) => {
            PRESENT.hash(hasher);
            hash_amount(u, hasher);
        }
        None => ABSENT.hash(hasher),
    }
    match cost {
        Some(c) => {
            PRESENT.hash(hasher);
            hash_cost(c, hasher);
        }
        None => ABSENT.hash(hasher),
    }
    match price {
        Some(p) => {
            PRESENT.hash(hasher);
            hash_price(p, hasher);
        }
        None => ABSENT.hash(hasher),
    }
    flag.hash(hasher);
}

/// Hash an amount's structural fields.
fn hash_amount<H: Hasher>(amount: &AmountData, hasher: &mut H) {
    let AmountData { number, currency } = amount;
    number.hash(hasher);
    currency.hash(hasher);
}

/// Hash a cost's structural fields.
fn hash_cost<H: Hasher>(cost: &CostData, hasher: &mut H) {
    use rustledger_plugin_types::CostNumberData;
    let CostData {
        number,
        currency,
        date,
        label,
        merge,
    } = cost;
    // Hash the typed number variant + payload. Pre-#1164 we hashed
    // two parallel Option<String> fields; the new shape forbids the
    // both-set state but the hash must still distinguish PerUnit from
    // Total (same number, different meaning) so we tag the variant.
    match number {
        None => 0u8.hash(hasher),
        Some(CostNumberData::PerUnit { value: s }) => {
            1u8.hash(hasher);
            s.hash(hasher);
        }
        Some(CostNumberData::Total { value: s }) => {
            2u8.hash(hasher);
            s.hash(hasher);
        }
        Some(CostNumberData::PerUnitFromTotal { per_unit, total }) => {
            // Post-booking state must hash distinctly from raw PerUnit
            // — two transactions with the same per_unit can have
            // different source totals (e.g. {{150}} vs {150}*units
            // when units rounds to the same per_unit), and the
            // fingerprint must not collapse them.
            3u8.hash(hasher);
            per_unit.hash(hasher);
            total.hash(hasher);
        }
    }
    currency.hash(hasher);
    date.hash(hasher);
    label.hash(hasher);
    merge.hash(hasher);
}

/// Hash a price annotation's structural fields.
fn hash_price<H: Hasher>(price: &PriceAnnotationData, hasher: &mut H) {
    let PriceAnnotationData {
        is_total,
        amount,
        number,
        currency,
    } = price;
    is_total.hash(hasher);
    match amount {
        Some(a) => {
            PRESENT.hash(hasher);
            hash_amount(a, hasher);
        }
        None => ABSENT.hash(hasher),
    }
    number.hash(hasher);
    currency.hash(hasher);
}

// ============================================================================
// Import fingerprint — BLAKE3-based stable fingerprint for dedup across runs
// ============================================================================

/// A stable transaction fingerprint for import deduplication.
///
/// Computed from date + amount + normalized description text using BLAKE3.
/// Stored as 128 bits (16 bytes) — sufficient for collision resistance in
/// typical ledger sizes (millions of transactions).
///
/// Unlike [`structural_hash`], this fingerprint is designed to match
/// transactions that refer to the same real-world event even if they have
/// slightly different representations (e.g., imported vs manually entered).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Fingerprint(pub [u8; 16]);

impl Fingerprint {
    /// Compute a fingerprint from transaction components.
    ///
    /// The text is normalized (lowercased, whitespace-collapsed) before hashing
    /// to handle minor formatting differences between import sources.
    #[must_use]
    pub fn compute(date: &str, amount: Option<&str>, text: &str) -> Self {
        let normalized = normalize_text(text);
        let mut hasher = blake3::Hasher::new();
        hasher.update(date.as_bytes());
        hasher.update(b"|");
        if let Some(amt) = amount {
            // Normalize amount so "50" and "50.00" produce the same fingerprint.
            let normalized_amt = rust_decimal::Decimal::from_str(amt)
                .map_or_else(|_| amt.to_string(), |d| d.normalize().to_string());
            hasher.update(normalized_amt.as_bytes());
        }
        hasher.update(b"|");
        hasher.update(normalized.as_bytes());
        let hash = hasher.finalize();
        let mut bytes = [0u8; 16];
        bytes.copy_from_slice(&hash.as_bytes()[..16]);
        Self(bytes)
    }

    /// Compute a fingerprint from a `TransactionData` and date.
    ///
    /// Uses the first posting's amount and the payee+narration as text.
    #[must_use]
    pub fn from_transaction(date: &str, txn: &TransactionData) -> Self {
        let amount = txn
            .postings
            .first()
            .and_then(|p| p.units.as_ref())
            .map(|u| u.number.as_str());

        let mut text = String::new();
        if let Some(ref payee) = txn.payee {
            text.push_str(payee);
            text.push(' ');
        }
        text.push_str(&txn.narration);

        Self::compute(date, amount, &text)
    }

    /// Encode as a hex string for storage in metadata.
    #[must_use]
    pub fn to_hex(&self) -> String {
        let mut s = String::with_capacity(32);
        for byte in &self.0 {
            use std::fmt::Write;
            // Writing to a String is infallible
            write!(s, "{byte:02x}").expect("hex write to String cannot fail");
        }
        s
    }

    /// Decode from a hex string.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the string is not exactly 32 hex characters.
    pub fn from_hex(s: &str) -> Result<Self, FingerprintError> {
        if s.len() != 32 {
            return Err(FingerprintError::InvalidLength(s.len()));
        }
        let mut bytes = [0u8; 16];
        for (i, chunk) in s.as_bytes().chunks(2).enumerate() {
            let hex_str = std::str::from_utf8(chunk).map_err(|_| FingerprintError::InvalidHex)?;
            bytes[i] = u8::from_str_radix(hex_str, 16).map_err(|_| FingerprintError::InvalidHex)?;
        }
        Ok(Self(bytes))
    }
}

impl std::fmt::Display for Fingerprint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.to_hex())
    }
}

/// Error when parsing a fingerprint from hex.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FingerprintError {
    /// Hex string was not 32 characters.
    InvalidLength(usize),
    /// Hex string contained invalid characters.
    InvalidHex,
}

impl std::fmt::Display for FingerprintError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidLength(len) => {
                write!(f, "fingerprint hex must be 32 chars, got {len}")
            }
            Self::InvalidHex => f.write_str("invalid hex in fingerprint"),
        }
    }
}

impl std::error::Error for FingerprintError {}

/// Normalize text for fingerprinting: lowercase, collapse whitespace.
fn normalize_text(text: &str) -> String {
    text.to_lowercase()
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_plugin_types::{
        AmountData, CostData, PostingData, PriceAnnotationData, TransactionData,
    };

    fn make_txn(payee: Option<&str>, narration: &str, amount: &str) -> TransactionData {
        TransactionData {
            flag: "*".to_string(),
            payee: payee.map(String::from),
            narration: narration.to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![PostingData {
                account: "Assets:Bank".to_string(),
                units: Some(AmountData {
                    number: amount.to_string(),
                    currency: "USD".to_string(),
                }),
                cost: None,
                price: None,
                flag: None,
                metadata: vec![],
                span: None,
            }],
        }
    }

    #[test]
    fn identical_transactions_produce_same_hash() {
        let txn1 = make_txn(Some("Store"), "Groceries", "-50.00");
        let txn2 = make_txn(Some("Store"), "Groceries", "-50.00");
        assert_eq!(
            structural_hash("2024-01-15", &txn1),
            structural_hash("2024-01-15", &txn2)
        );
    }

    #[test]
    fn different_dates_produce_different_hash() {
        let txn = make_txn(Some("Store"), "Groceries", "-50.00");
        assert_ne!(
            structural_hash("2024-01-15", &txn),
            structural_hash("2024-01-16", &txn)
        );
    }

    #[test]
    fn different_amounts_produce_different_hash() {
        let txn1 = make_txn(Some("Store"), "Groceries", "-50.00");
        let txn2 = make_txn(Some("Store"), "Groceries", "-51.00");
        assert_ne!(
            structural_hash("2024-01-15", &txn1),
            structural_hash("2024-01-15", &txn2)
        );
    }

    #[test]
    fn metadata_does_not_affect_hash() {
        let mut txn1 = make_txn(Some("Store"), "Groceries", "-50.00");
        let txn2 = make_txn(Some("Store"), "Groceries", "-50.00");
        txn1.metadata.push((
            "source".to_string(),
            rustledger_plugin_types::MetaValueData::String("test".to_string()),
        ));
        assert_eq!(
            structural_hash("2024-01-15", &txn1),
            structural_hash("2024-01-15", &txn2)
        );
    }

    #[test]
    fn tag_order_does_not_affect_hash() {
        let mut txn1 = make_txn(None, "Test", "100");
        txn1.tags = vec!["a".to_string(), "b".to_string()];
        let mut txn2 = make_txn(None, "Test", "100");
        txn2.tags = vec!["b".to_string(), "a".to_string()];
        assert_eq!(
            structural_hash("2024-01-15", &txn1),
            structural_hash("2024-01-15", &txn2)
        );
    }

    #[test]
    fn different_tags_produce_different_hash() {
        let mut txn1 = make_txn(None, "Test", "100");
        txn1.tags = vec!["a".to_string()];
        let mut txn2 = make_txn(None, "Test", "100");
        txn2.tags = vec!["b".to_string()];
        assert_ne!(
            structural_hash("2024-01-15", &txn1),
            structural_hash("2024-01-15", &txn2)
        );
    }

    // ===== Import fingerprint tests =====

    #[test]
    fn fingerprint_deterministic() {
        let fp1 = Fingerprint::compute("2024-01-15", Some("-50.00"), "WHOLE FOODS");
        let fp2 = Fingerprint::compute("2024-01-15", Some("-50.00"), "WHOLE FOODS");
        assert_eq!(fp1, fp2);
    }

    #[test]
    fn fingerprint_different_dates() {
        let fp1 = Fingerprint::compute("2024-01-15", Some("-50.00"), "Store");
        let fp2 = Fingerprint::compute("2024-01-16", Some("-50.00"), "Store");
        assert_ne!(fp1, fp2);
    }

    #[test]
    fn fingerprint_different_amounts() {
        let fp1 = Fingerprint::compute("2024-01-15", Some("-50.00"), "Store");
        let fp2 = Fingerprint::compute("2024-01-15", Some("-51.00"), "Store");
        assert_ne!(fp1, fp2);
    }

    #[test]
    fn fingerprint_normalizes_text() {
        // Capitalization and extra whitespace should not matter
        let fp1 = Fingerprint::compute("2024-01-15", Some("-50"), "WHOLE FOODS  MARKET");
        let fp2 = Fingerprint::compute("2024-01-15", Some("-50"), "whole foods market");
        assert_eq!(fp1, fp2);
    }

    #[test]
    fn fingerprint_from_transaction() {
        let txn = make_txn(Some("Store"), "Groceries", "-50.00");
        let fp = Fingerprint::from_transaction("2024-01-15", &txn);
        // Should match manual computation
        let expected = Fingerprint::compute("2024-01-15", Some("-50.00"), "Store Groceries");
        assert_eq!(fp, expected);
    }

    #[test]
    fn fingerprint_hex_roundtrip() {
        let fp = Fingerprint::compute("2024-01-15", Some("-50.00"), "Test");
        let hex = fp.to_hex();
        assert_eq!(hex.len(), 32);
        let fp2 = Fingerprint::from_hex(&hex).unwrap();
        assert_eq!(fp, fp2);
    }

    #[test]
    fn fingerprint_display() {
        let fp = Fingerprint::compute("2024-01-15", Some("-50.00"), "Test");
        let display = format!("{fp}");
        assert_eq!(display, fp.to_hex());
    }

    #[test]
    fn fingerprint_from_hex_invalid_length() {
        let err = Fingerprint::from_hex("abcd").unwrap_err();
        assert_eq!(err, FingerprintError::InvalidLength(4));
    }

    #[test]
    fn fingerprint_from_hex_invalid_chars() {
        let err = Fingerprint::from_hex("zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz").unwrap_err();
        assert_eq!(err, FingerprintError::InvalidHex);
    }

    // ===== Structural hash edge case tests (ported from native_plugins_test.rs) =====

    #[test]
    fn distinct_costs_produce_different_hashes() {
        use rustledger_plugin_types::CostNumberData;
        let mut txn1 = make_txn(Some("Store"), "Buy shares", "100.00");
        txn1.postings[0].cost = Some(CostData {
            number: Some(CostNumberData::PerUnit {
                value: "10.00".to_string(),
            }),
            currency: Some("USD".to_string()),
            date: None,
            label: None,
            merge: false,
        });
        let mut txn2 = make_txn(Some("Store"), "Buy shares", "100.00");
        txn2.postings[0].cost = Some(CostData {
            number: Some(CostNumberData::PerUnit {
                value: "11.00".to_string(),
            }),
            currency: Some("USD".to_string()),
            date: None,
            label: None,
            merge: false,
        });
        assert_ne!(
            structural_hash("2024-01-15", &txn1),
            structural_hash("2024-01-15", &txn2)
        );
    }

    #[test]
    fn distinct_prices_produce_different_hashes() {
        let mut txn1 = make_txn(Some("Store"), "Buy shares", "100.00");
        txn1.postings[0].price = Some(PriceAnnotationData {
            is_total: false,
            amount: Some(AmountData {
                number: "10.00".to_string(),
                currency: "USD".to_string(),
            }),
            number: None,
            currency: None,
        });
        let mut txn2 = make_txn(Some("Store"), "Buy shares", "100.00");
        txn2.postings[0].price = Some(PriceAnnotationData {
            is_total: false,
            amount: Some(AmountData {
                number: "11.00".to_string(),
                currency: "USD".to_string(),
            }),
            number: None,
            currency: None,
        });
        assert_ne!(
            structural_hash("2024-01-15", &txn1),
            structural_hash("2024-01-15", &txn2)
        );
    }

    #[test]
    fn reordered_postings_produce_different_hashes() {
        let posting_a = PostingData {
            account: "Assets:Bank".to_string(),
            units: Some(AmountData {
                number: "-50.00".to_string(),
                currency: "USD".to_string(),
            }),
            cost: None,
            price: None,
            flag: None,
            metadata: vec![],
            span: None,
        };
        let posting_b = PostingData {
            account: "Expenses:Food".to_string(),
            units: Some(AmountData {
                number: "50.00".to_string(),
                currency: "USD".to_string(),
            }),
            cost: None,
            price: None,
            flag: None,
            metadata: vec![],
            span: None,
        };

        let txn1 = TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: "Test".to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![posting_a.clone(), posting_b.clone()],
        };
        let txn2 = TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: "Test".to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![posting_b, posting_a],
        };
        assert_ne!(
            structural_hash("2024-01-15", &txn1),
            structural_hash("2024-01-15", &txn2)
        );
    }

    #[test]
    fn none_vs_empty_payee_differ() {
        let txn_none = make_txn(None, "Test", "100");
        let txn_empty = TransactionData {
            flag: "*".to_string(),
            payee: Some(String::new()),
            narration: "Test".to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![PostingData {
                account: "Assets:Bank".to_string(),
                units: Some(AmountData {
                    number: "100".to_string(),
                    currency: "USD".to_string(),
                }),
                cost: None,
                price: None,
                flag: None,
                metadata: vec![],
                span: None,
            }],
        };
        assert_ne!(
            structural_hash("2024-01-15", &txn_none),
            structural_hash("2024-01-15", &txn_empty)
        );
    }

    #[test]
    fn empty_vs_absent_tags_are_duplicates() {
        // A transaction with no tags and one with an empty tags vec should hash the same
        let txn1 = make_txn(None, "Test", "100");
        let txn2 = TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: "Test".to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![PostingData {
                account: "Assets:Bank".to_string(),
                units: Some(AmountData {
                    number: "100".to_string(),
                    currency: "USD".to_string(),
                }),
                cost: None,
                price: None,
                flag: None,
                metadata: vec![],
                span: None,
            }],
        };
        assert_eq!(
            structural_hash("2024-01-15", &txn1),
            structural_hash("2024-01-15", &txn2)
        );
    }

    #[test]
    fn distinct_posting_counts_differ() {
        let txn1 = make_txn(None, "Test", "100");
        let txn2 = TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: "Test".to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![
                PostingData {
                    account: "Assets:Bank".to_string(),
                    units: Some(AmountData {
                        number: "100".to_string(),
                        currency: "USD".to_string(),
                    }),
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
                PostingData {
                    account: "Expenses:Food".to_string(),
                    units: Some(AmountData {
                        number: "-100".to_string(),
                        currency: "USD".to_string(),
                    }),
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                },
            ],
        };
        assert_ne!(
            structural_hash("2024-01-15", &txn1),
            structural_hash("2024-01-15", &txn2)
        );
    }

    #[test]
    fn distinct_flags_differ() {
        let mut txn1 = make_txn(None, "Test", "100");
        txn1.flag = "*".to_string();
        let mut txn2 = make_txn(None, "Test", "100");
        txn2.flag = "!".to_string();
        assert_ne!(
            structural_hash("2024-01-15", &txn1),
            structural_hash("2024-01-15", &txn2)
        );
    }

    #[test]
    fn link_order_independence() {
        let mut txn1 = make_txn(None, "Test", "100");
        txn1.links = vec!["link-a".to_string(), "link-b".to_string()];
        let mut txn2 = make_txn(None, "Test", "100");
        txn2.links = vec!["link-b".to_string(), "link-a".to_string()];
        assert_eq!(
            structural_hash("2024-01-15", &txn1),
            structural_hash("2024-01-15", &txn2)
        );
    }

    #[test]
    fn duplicate_tags_are_deduped() {
        let mut txn1 = make_txn(None, "Test", "100");
        txn1.tags = vec!["a".to_string(), "a".to_string()];
        let mut txn2 = make_txn(None, "Test", "100");
        txn2.tags = vec!["a".to_string()];
        assert_eq!(
            structural_hash("2024-01-15", &txn1),
            structural_hash("2024-01-15", &txn2)
        );
    }

    #[test]
    fn posting_flag_affects_hash() {
        let mut txn1 = make_txn(None, "Test", "100");
        txn1.postings[0].flag = Some("!".to_string());
        let txn2 = make_txn(None, "Test", "100");
        assert_ne!(
            structural_hash("2024-01-15", &txn1),
            structural_hash("2024-01-15", &txn2)
        );
    }

    #[test]
    fn fingerprint_none_amount() {
        let fp1 = Fingerprint::compute("2024-01-15", None, "Store");
        let fp2 = Fingerprint::compute("2024-01-15", Some("-50.00"), "Store");
        assert_ne!(fp1, fp2);
    }

    #[test]
    fn fingerprint_normalizes_amount() {
        // "50" and "50.00" should produce the same fingerprint
        let fp1 = Fingerprint::compute("2024-01-15", Some("50"), "Store");
        let fp2 = Fingerprint::compute("2024-01-15", Some("50.00"), "Store");
        assert_eq!(fp1, fp2);
    }

    #[test]
    fn fingerprint_from_transaction_no_postings() {
        let txn = TransactionData {
            flag: "*".to_string(),
            payee: Some("Store".to_string()),
            narration: "Test".to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![],
        };
        let fp = Fingerprint::from_transaction("2024-01-15", &txn);
        // Should still compute (amount=None)
        let expected = Fingerprint::compute("2024-01-15", None, "Store Test");
        assert_eq!(fp, expected);
    }

    #[test]
    fn fingerprint_error_display() {
        let err = FingerprintError::InvalidLength(10);
        assert_eq!(err.to_string(), "fingerprint hex must be 32 chars, got 10");
        let err = FingerprintError::InvalidHex;
        assert_eq!(err.to_string(), "invalid hex in fingerprint");
    }
}
