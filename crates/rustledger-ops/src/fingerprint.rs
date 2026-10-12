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
    AmountData, BalanceData, CloseData, CommodityData, CostData, CustomData, DirectiveData,
    DirectiveWrapper, DocumentData, EventData, MetaValueData, NoteData, OpenData, PadData,
    PostingData, PriceAnnotationData, QueryData, TransactionData,
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
/// `frozenset` semantics, and the postings are hashed as a multiset, as
/// beancount sorts their hashes (#2599): the same postings in another order
/// are the same transaction.
#[must_use]
pub fn structural_hash(date: &str, txn: &TransactionData) -> u64 {
    let mut hasher = DefaultHasher::new();
    date.hash(&mut hasher);
    hash_transaction(txn, &mut hasher);
    hasher.finish()
}

/// The structural identity of a directive, as beancount's `noduplicates`
/// compares directives (#2599).
///
/// beancount's plugin calls `compare.hash_entries(entries,
/// exclude_meta=True)`. Two directives are duplicates exactly when their keys
/// are equal.
///
/// The key is the exact byte stream the `hash_*` helpers write, not a digest
/// of it, so distinct directives never compare equal. Every field beancount
/// hashes is in it, metadata is not, and lists beancount hashes element-wise
/// and sorted are compared without regard to order:
///
/// | Directive | Fields |
/// |---|---|
/// | transaction | flag, payee, narration, tags, links, postings (each: account, units, cost, price, flag) |
/// | open | account, currencies, booking |
/// | close | account |
/// | commodity | currency |
/// | pad | account, source account |
/// | balance | account, amount, tolerance |
/// | note | account, comment, tags, links |
/// | document | account, path, tags, links |
/// | event | type, description |
/// | query | name, query string |
/// | custom | type, values |
///
/// plus the date of each. A `price` has no key (`None`): beancount allows
/// duplicate prices, which a price source commonly repeats for a day the
/// market was closed.
///
/// Deliberate divergences from beancount, which hashes `str()` of each field
/// and not the directive's type: the type is part of the key (beancount
/// takes an `event "a" "b"` and a `query "a" "b"` on one date for
/// duplicates), and an absent value never equals a written one (beancount's
/// `str(None)` equals a payee written `"None"`).
#[must_use]
pub fn structural_key(directive: &DirectiveWrapper) -> Option<Vec<u8>> {
    let mut key = KeyWriter::default();
    let k = &mut key;
    match &directive.data {
        DirectiveData::Price(_) => return None,
        DirectiveData::Transaction(txn) => {
            0u8.hash(k);
            directive.date.hash(k);
            hash_transaction(txn, k);
        }
        DirectiveData::Open(OpenData {
            account,
            currencies,
            booking,
            metadata: _,
        }) => {
            1u8.hash(k);
            directive.date.hash(k);
            account.hash(k);
            // A list, not a set: sorted, but a repeat counts.
            let mut sorted: Vec<&String> = currencies.iter().collect();
            sorted.sort();
            sorted.len().hash(k);
            for currency in sorted {
                currency.hash(k);
            }
            booking.hash(k);
        }
        DirectiveData::Close(CloseData {
            account,
            metadata: _,
        }) => {
            2u8.hash(k);
            directive.date.hash(k);
            account.hash(k);
        }
        DirectiveData::Commodity(CommodityData {
            currency,
            metadata: _,
        }) => {
            3u8.hash(k);
            directive.date.hash(k);
            currency.hash(k);
        }
        DirectiveData::Pad(PadData {
            account,
            source_account,
            metadata: _,
        }) => {
            4u8.hash(k);
            directive.date.hash(k);
            account.hash(k);
            source_account.hash(k);
        }
        DirectiveData::Balance(BalanceData {
            account,
            amount,
            tolerance,
            metadata: _,
        }) => {
            5u8.hash(k);
            directive.date.hash(k);
            account.hash(k);
            hash_amount(amount, k);
            tolerance.hash(k);
        }
        DirectiveData::Note(NoteData {
            account,
            comment,
            tags,
            links,
            metadata: _,
        }) => {
            6u8.hash(k);
            directive.date.hash(k);
            account.hash(k);
            comment.hash(k);
            hash_set(tags, k);
            hash_set(links, k);
        }
        DirectiveData::Document(DocumentData {
            account,
            path,
            tags,
            links,
            metadata: _,
        }) => {
            7u8.hash(k);
            directive.date.hash(k);
            account.hash(k);
            path.hash(k);
            hash_set(tags, k);
            hash_set(links, k);
        }
        DirectiveData::Event(EventData {
            event_type,
            value,
            metadata: _,
        }) => {
            8u8.hash(k);
            directive.date.hash(k);
            event_type.hash(k);
            value.hash(k);
        }
        DirectiveData::Query(QueryData {
            name,
            query,
            metadata: _,
        }) => {
            9u8.hash(k);
            directive.date.hash(k);
            name.hash(k);
            query.hash(k);
        }
        DirectiveData::Custom(CustomData {
            custom_type,
            values,
            metadata: _,
        }) => {
            10u8.hash(k);
            directive.date.hash(k);
            custom_type.hash(k);
            // beancount hashes the values element-wise and sorted.
            hash_multiset(values.iter().map(|v| key_of(|w| hash_meta_value(v, w))), k);
        }
    }
    Some(key.0)
}

/// A [`Hasher`] that keeps the bytes written to it: an exact, collision-free
/// key built by the same code that computes [`structural_hash`]. `str`'s
/// `Hash` ends each string with `0xff`, which UTF-8 never contains, so
/// adjacent strings cannot run together.
#[derive(Default)]
struct KeyWriter(Vec<u8>);

impl Hasher for KeyWriter {
    /// Unused: the key is the bytes. `Hash` implementations only write.
    fn finish(&self) -> u64 {
        0
    }

    fn write(&mut self, bytes: &[u8]) {
        self.0.extend_from_slice(bytes);
    }
}

/// The bytes `write` puts in a fresh [`KeyWriter`].
fn key_of(write: impl FnOnce(&mut KeyWriter)) -> Vec<u8> {
    let mut key = KeyWriter::default();
    write(&mut key);
    key.0
}

/// Hash `items` (each already a key) as a multiset: count-prefixed and
/// sorted, as beancount sorts the element hashes of a list.
fn hash_multiset<H: Hasher>(items: impl Iterator<Item = Vec<u8>>, hasher: &mut H) {
    let mut items: Vec<Vec<u8>> = items.collect();
    items.sort();
    items.len().hash(hasher);
    for item in &items {
        // Length-prefixed, so no item's bytes can run into the next.
        item.len().hash(hasher);
        hasher.write(item);
    }
}

/// Hash a tag or link set: sorted, deduped (a `frozenset` in beancount) and
/// count-prefixed so two sets in a row cannot trade elements.
fn hash_set<H: Hasher>(items: &[String], hasher: &mut H) {
    let mut sorted: Vec<&String> = items.iter().collect();
    sorted.sort();
    sorted.dedup();
    sorted.len().hash(hasher);
    for item in sorted {
        item.hash(hasher);
    }
}

/// Hash a transaction's structural fields (not its date).
fn hash_transaction<H: Hasher>(txn: &TransactionData, hasher: &mut H) {
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

    flag.hash(hasher);
    payee.hash(hasher);
    narration.hash(hasher);
    hash_set(tags, hasher);
    hash_set(links, hasher);
    // A multiset: beancount sorts the postings' hashes.
    hash_multiset(
        postings.iter().map(|p| key_of(|w| hash_posting(p, w))),
        hasher,
    );
}

/// Hash a custom directive's value, with its type: beancount hashes a value
/// and its `dtype`, so the account `Assets:Bank` and the string
/// `"Assets:Bank"` differ.
fn hash_meta_value<H: Hasher>(value: &MetaValueData, hasher: &mut H) {
    match value {
        MetaValueData::String(s) => {
            0u8.hash(hasher);
            s.hash(hasher);
        }
        MetaValueData::Number(s) => {
            1u8.hash(hasher);
            s.hash(hasher);
        }
        MetaValueData::Date(s) => {
            2u8.hash(hasher);
            s.hash(hasher);
        }
        MetaValueData::Account(s) => {
            3u8.hash(hasher);
            s.hash(hasher);
        }
        MetaValueData::Currency(s) => {
            4u8.hash(hasher);
            s.hash(hasher);
        }
        MetaValueData::Tag(s) => {
            5u8.hash(hasher);
            s.hash(hasher);
        }
        MetaValueData::Link(s) => {
            6u8.hash(hasher);
            s.hash(hasher);
        }
        MetaValueData::Amount(a) => {
            7u8.hash(hasher);
            hash_amount(a, hasher);
        }
        MetaValueData::Bool(b) => {
            8u8.hash(hasher);
            b.hash(hasher);
        }
    }
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
            hash_cost(c, total_is_implied(units.as_ref(), c), hasher);
        }
        None => ABSENT.hash(hasher),
    }
    match price {
        Some(p) => {
            PRESENT.hash(hasher);
            match per_unit_price(units.as_ref(), p) {
                Some(per_unit) => hash_price(&per_unit, hasher),
                None => hash_price(p, hasher),
            }
        }
        None => ABSENT.hash(hasher),
    }
    flag.hash(hasher);
}

/// A total price (`@@`) as the per-unit price (`@`) it stands for, as
/// beancount's parser rewrites it before plugins run: `2 X @@ 10 USD` is
/// `2 X @ 5 USD`, and beancount takes the two postings for one (#2599). The
/// per-unit price has the scale Python's division gives it (`10.00 / 2` is
/// `5.00`).
///
/// `None`, leaving the price as written, when there is nothing to rewrite
/// (a per-unit or incomplete price, units without a number), and
/// when the division is not exact: `3 X @@ 10 USD` is not `3 X @ 3.33…3 USD`
/// for any number of 3s, whatever beancount's 28-digit quotient says, so
/// postings whose totals differ never match.
fn per_unit_price(
    units: Option<&AmountData>,
    price: &PriceAnnotationData,
) -> Option<PriceAnnotationData> {
    use rust_decimal::Decimal;
    use rustledger_core::decimal::{checked_div_python_scale, checked_mul_exact};
    if !price.is_total {
        return None;
    }
    let total_amount = price.amount.as_ref()?;
    let units = Decimal::from_str(&units?.number).ok()?.abs();
    let per_unit = if units.is_zero() {
        // Zero units price at zero, as beancount's parser writes them
        // (`ZERO if units.number == ZERO else ...`): `0 X @@ 10 USD` is
        // `0 X @ 0 USD`, and its weight is zero in both tools.
        Decimal::ZERO
    } else {
        let total = Decimal::from_str(&total_amount.number).ok()?;
        let per_unit = checked_div_python_scale(total, units)?;
        if checked_mul_exact(per_unit, units)? != total {
            return None;
        }
        per_unit
    };
    Some(PriceAnnotationData {
        is_total: false,
        amount: Some(AmountData {
            number: per_unit.to_string(),
            currency: total_amount.currency.clone(),
        }),
        number: None,
        currency: None,
    })
}

/// Hash an amount's structural fields.
fn hash_amount<H: Hasher>(amount: &AmountData, hasher: &mut H) {
    let AmountData { number, currency } = amount;
    number.hash(hasher);
    currency.hash(hasher);
}

/// Whether a booked `{{ total }}` cost says nothing its per-unit cost does
/// not: `2 X {{10 USD}}` books `5 USD` a unit, the lot `2 X {5 USD}` is, and
/// beancount (which keeps only the per-unit cost) takes the two postings
/// for one (#2599). A total the per-unit cost does not multiply back to
/// exactly (`3 X {{10 USD}}`) still counts, so postings whose exact totals
/// differ never match.
fn total_is_implied(units: Option<&AmountData>, cost: &CostData) -> bool {
    use rust_decimal::Decimal;
    use rustledger_plugin_types::CostNumberData;
    let Some(CostNumberData::PerUnitFromTotal { per_unit, total }) = &cost.number else {
        return false;
    };
    let parse = |s: &str| Decimal::from_str(s).ok();
    let (Some(units), Some(per_unit), Some(total)) = (
        units.and_then(|u| parse(&u.number)),
        parse(per_unit),
        parse(total),
    ) else {
        return false;
    };
    // Exact: a product `Decimal` has to round is not the total.
    rustledger_core::decimal::checked_mul_exact(per_unit, units.abs()) == Some(total)
}

/// Hash a cost's structural fields. `total_implied`: hash a booked
/// `{{ total }}` cost as its per-unit cost alone (see [`total_is_implied`]).
fn hash_cost<H: Hasher>(cost: &CostData, total_implied: bool, hasher: &mut H) {
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
        // As the per-unit cost it books, which says it all.
        Some(CostNumberData::PerUnitFromTotal { per_unit: s, .. }) if total_implied => {
            1u8.hash(hasher);
            s.hash(hasher);
        }
        Some(CostNumberData::Total { value: s }) => {
            2u8.hash(hasher);
            s.hash(hasher);
        }
        Some(CostNumberData::Compound { per_unit, total }) => {
            // Distinct tag: {5 # 10} must not collide with {5} or
            // {{10}} or a booked PerUnitFromTotal(5, 10).
            4u8.hash(hasher);
            per_unit.hash(hasher);
            total.hash(hasher);
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

    fn posting(account: &str, number: &str, price: Option<(bool, &str)>) -> PostingData {
        PostingData {
            account: account.to_string(),
            units: Some(AmountData {
                number: number.to_string(),
                currency: "HOOL".to_string(),
            }),
            cost: None,
            price: price.map(|(is_total, n)| PriceAnnotationData {
                is_total,
                amount: Some(AmountData {
                    number: n.to_string(),
                    currency: "USD".to_string(),
                }),
                number: None,
                currency: None,
            }),
            flag: None,
            metadata: vec![],
            span: None,
        }
    }

    fn txn_with(postings: Vec<PostingData>) -> TransactionData {
        TransactionData {
            postings,
            ..make_txn(None, "Test", "0")
        }
    }

    /// The postings are a multiset, as beancount sorts their hashes: the
    /// same postings in another order are the same transaction (#2599).
    #[test]
    fn posting_order_does_not_affect_hash() {
        let a = posting("Assets:A", "1", None);
        let b = posting("Assets:B", "-1", None);
        assert_eq!(
            structural_hash("2024-01-15", &txn_with(vec![a.clone(), b.clone()])),
            structural_hash("2024-01-15", &txn_with(vec![b.clone(), a.clone()]))
        );
        // A multiset, not a set: a repeated posting counts.
        assert_ne!(
            structural_hash(
                "2024-01-15",
                &txn_with(vec![a.clone(), a.clone(), b.clone()])
            ),
            structural_hash("2024-01-15", &txn_with(vec![a, b]))
        );
    }

    /// A total price is the per-unit price it stands for, as beancount's
    /// parser rewrites it: `2 HOOL @@ 10 USD` is `2 HOOL @ 5 USD`.
    #[test]
    fn total_price_hashes_as_its_per_unit_price() {
        let hash = |number, price| {
            structural_hash(
                "2024-01-15",
                &txn_with(vec![posting("Assets:A", number, Some(price))]),
            )
        };
        assert_eq!(hash("2", (true, "10")), hash("2", (false, "5")));
        assert_eq!(hash("-2", (true, "10")), hash("-2", (false, "5")));
        assert_ne!(hash("2", (true, "10")), hash("2", (false, "10")));
        // With Python's quotient scale, as beancount divides.
        assert_eq!(hash("2", (true, "10.00")), hash("2", (false, "5.00")));
        assert_eq!(hash("2.5", (true, "10")), hash("2.5", (false, "4")));
        assert_ne!(hash("2", (true, "10.00")), hash("2", (false, "5")));
        // An inexact quotient is no per-unit price: the totals differ.
        assert_ne!(
            hash("3", (true, "10")),
            hash("3", (false, "3.333333333333333333333333333"))
        );
        assert_ne!(
            hash("3", (true, "10")),
            hash("3", (false, "3.3333333333333333333333333333"))
        );
        // Zero units price at zero, as beancount's parser writes them, with
        // `ZERO`'s scale.
        assert_eq!(hash("0", (true, "10")), hash("0", (false, "0")));
        assert_ne!(hash("0", (true, "10")), hash("0", (false, "0.00")));
    }

    /// A booked `{{ total }}` cost is its per-unit cost when that says it
    /// all: `2 HOOL {{10 USD}}` books the lot `2 HOOL {5 USD}`, and beancount
    /// takes the two for one. Exact totals that differ never match.
    #[test]
    fn booked_total_cost_hashes_as_its_per_unit_when_exact() {
        use rustledger_plugin_types::CostNumberData;
        let hash = |units: &str, number: CostNumberData| {
            let mut p = posting("Assets:A", units, None);
            p.cost = Some(CostData {
                number: Some(number),
                currency: Some("USD".to_string()),
                date: Some("2024-01-15".to_string()),
                label: None,
                merge: false,
            });
            structural_hash("2024-01-15", &txn_with(vec![p]))
        };
        let per_unit = |v: &str| CostNumberData::PerUnit {
            value: v.to_string(),
        };
        let from_total = |p: &str, t: &str| CostNumberData::PerUnitFromTotal {
            per_unit: p.to_string(),
            total: t.to_string(),
        };
        assert_eq!(hash("2", from_total("5", "10")), hash("2", per_unit("5")));
        assert_eq!(hash("-2", from_total("5", "10")), hash("-2", per_unit("5")));
        // The per-unit cost keeps its scale, as everywhere else.
        assert_ne!(
            hash("2", from_total("5", "10")),
            hash("2", per_unit("5.00"))
        );
        // 3 HOOL {{10 USD}}: the per-unit cost rounds, so the total counts.
        let third = "3.3333333333333333333333333333";
        assert_ne!(
            hash("3", from_total(third, "10")),
            hash("3", per_unit(third))
        );
        assert_ne!(
            hash("3", from_total(third, "10")),
            hash("3", from_total(third, "10.000000000000000000000000001"))
        );
    }

    fn key(date: &str, data: rustledger_plugin_types::DirectiveData) -> Option<Vec<u8>> {
        structural_key(&DirectiveWrapper {
            directive_type: String::new(),
            date: date.to_string(),
            filename: None,
            lineno: None,
            data,
        })
    }

    /// A custom directive's values are compared without regard to order,
    /// as beancount sorts their hashes, and with their type: the account
    /// `Expenses:Food` is not the string `"Expenses:Food"`.
    #[test]
    fn custom_values_are_typed_and_unordered() {
        use rustledger_plugin_types::{CustomData, DirectiveData, MetaValueData};
        let custom = |values: Vec<MetaValueData>| {
            key(
                "2024-01-15",
                DirectiveData::Custom(CustomData {
                    custom_type: "budget".to_string(),
                    values,
                    metadata: vec![],
                }),
            )
        };
        let a = MetaValueData::String("a".to_string());
        let b = MetaValueData::String("b".to_string());
        assert_eq!(
            custom(vec![a.clone(), b.clone()]),
            custom(vec![b, a.clone()])
        );
        assert_ne!(custom(vec![a.clone(), a.clone()]), custom(vec![a]));
        assert_ne!(
            custom(vec![MetaValueData::Account("Expenses:Food".to_string())]),
            custom(vec![MetaValueData::String("Expenses:Food".to_string())])
        );
        assert_ne!(
            custom(vec![MetaValueData::Number("1.0".to_string())]),
            custom(vec![MetaValueData::Number("1.00".to_string())])
        );
    }

    /// An `open`'s currencies are a list beancount hashes sorted; its
    /// booking method counts. A `balance`'s amount keeps its scale, as
    /// beancount's `str(Decimal)` does, and its tolerance counts.
    #[test]
    fn open_and_balance_fields() {
        use rustledger_plugin_types::{BalanceData, DirectiveData, OpenData};
        let open = |currencies: &[&str], booking: Option<&str>| {
            key(
                "2024-01-15",
                DirectiveData::Open(OpenData {
                    account: "Assets:A".to_string(),
                    currencies: currencies.iter().map(ToString::to_string).collect(),
                    booking: booking.map(String::from),
                    metadata: vec![],
                }),
            )
        };
        assert_eq!(open(&["USD", "EUR"], None), open(&["EUR", "USD"], None));
        assert_ne!(open(&["USD"], Some("FIFO")), open(&["USD"], Some("LIFO")));
        assert_ne!(open(&["USD"], Some("FIFO")), open(&["USD"], None));
        let balance = |number: &str, tolerance: Option<&str>| {
            key(
                "2024-01-15",
                DirectiveData::Balance(BalanceData {
                    account: "Assets:A".to_string(),
                    amount: AmountData {
                        number: number.to_string(),
                        currency: "USD".to_string(),
                    },
                    tolerance: tolerance.map(String::from),
                    metadata: vec![],
                }),
            )
        };
        assert_eq!(balance("0", None), balance("0", None));
        assert_ne!(balance("0", None), balance("0.00", None));
        assert_ne!(balance("0", Some("0.01")), balance("0", None));
    }
}
