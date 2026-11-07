//! [`Metadata`]: the key-value map attached to directives and postings.
//!
//! A flat, insertion-ordered vector of entries with interned keys, not a
//! hash map. Almost every attachment holds one to three entries (an
//! importer's `uuid` / `source` / `memo`), and at that size a linear scan
//! over a few short keys is cheaper than hashing, while the storage is
//! exactly the entries: 56 bytes each. The hash map this replaced
//! (`FxHashMap<String, MetaValue>`) never allocated fewer than four
//! 64-byte buckets plus control bytes, about 276 bytes for one entry, and
//! a separate heap `String` for every key (#2835).
//!
//! Keys are [`InternedStr`]: they repeat on every directive of a ledger
//! (`filename`, `lineno`, `uuid`, ...), and the loader's cross-file dedup
//! pass (`rustledger_loader::reintern_directives`) points every equal key
//! at one `Arc<str>`, the same as it does for accounts and currencies.
//!
//! The map is behind a small `HashMap`-shaped API (`get`, `insert`,
//! `contains_key`, `remove`, `retain`, `iter`, `keys`, `values`, indexing
//! by `&str`), so readers did not have to change. Two things differ from
//! a hash map, both on purpose:
//!
//! - Iteration is in insertion order (as Python's `dict` is), so it is
//!   deterministic. Code that wants a sorted order still sorts.
//! - Lookups are linear. A map with hundreds of keys is not a shape a
//!   ledger produces; if one ever does, this is the place to add an
//!   index above a size threshold.
//!
//! Equality is order-independent, like the hash map's was: two maps with
//! the same entries in a different order are equal.

use serde::{Deserialize, Serialize};
use std::fmt;

use crate::directive::MetaValue;
#[cfg(feature = "rkyv")]
use crate::intern::AsInternedStr;
use crate::intern::InternedStr;

/// Up to this many entries, [`Metadata::insert`] grows the storage by
/// exactly one slot, so a typical map is allocated at its final size.
const SMALL: usize = 4;

/// One metadata entry, as stored. Iteration hands out `(&key, &value)`
/// pairs, so callers rarely see this type.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)
)]
struct MetaEntry {
    #[cfg_attr(feature = "rkyv", rkyv(with = AsInternedStr))]
    key: InternedStr,
    value: MetaValue,
}

/// Metadata is a key-value map attached to directives and postings.
///
/// See the [module docs](self) for the layout and why it is not a hash
/// map. Keys are unique: [`Self::insert`] replaces the value of an
/// existing key in place, keeping its position.
#[derive(Clone, Default)]
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)
)]
pub struct Metadata {
    entries: Vec<MetaEntry>,
}

impl Metadata {
    /// An empty map. Does not allocate.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// An empty map with room for `capacity` entries.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            entries: Vec::with_capacity(capacity),
        }
    }

    /// Number of entries.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether there are no entries.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    fn position(&self, key: &str) -> Option<usize> {
        self.entries.iter().position(|e| e.key.as_str() == key)
    }

    /// The value for `key`, if present.
    #[must_use]
    pub fn get(&self, key: &str) -> Option<&MetaValue> {
        self.entries
            .iter()
            .find(|e| e.key.as_str() == key)
            .map(|e| &e.value)
    }

    /// The value for `key`, mutably, if present.
    pub fn get_mut(&mut self, key: &str) -> Option<&mut MetaValue> {
        self.entries
            .iter_mut()
            .find(|e| e.key.as_str() == key)
            .map(|e| &mut e.value)
    }

    /// The stored key and value for `key`, if present.
    #[must_use]
    pub fn get_key_value(&self, key: &str) -> Option<(&InternedStr, &MetaValue)> {
        self.entries
            .iter()
            .find(|e| e.key.as_str() == key)
            .map(|e| (&e.key, &e.value))
    }

    /// Whether `key` is present.
    #[must_use]
    pub fn contains_key(&self, key: &str) -> bool {
        self.position(key).is_some()
    }

    /// Set `key` to `value`, returning the previous value if the key was
    /// already present. A replaced entry keeps its position; a new one is
    /// appended.
    pub fn insert(&mut self, key: impl Into<InternedStr>, value: MetaValue) -> Option<MetaValue> {
        let key = key.into();
        if let Some(i) = self.position(key.as_str()) {
            return Some(std::mem::replace(&mut self.entries[i].value, value));
        }
        // Grow one slot at a time while small: a `Vec`'s first push
        // reserves four slots, which for the usual one or two entries is
        // either retained waste or a shrinking `realloc` later. Past the
        // small sizes, amortized doubling keeps bulk inserts linear.
        if self.entries.len() < SMALL {
            self.entries.reserve_exact(1);
        }
        self.entries.push(MetaEntry { key, value });
        None
    }

    /// Remove `key`, returning its value if it was present. The other
    /// entries keep their order.
    pub fn remove(&mut self, key: &str) -> Option<MetaValue> {
        let i = self.position(key)?;
        Some(self.entries.remove(i).value)
    }

    /// Keep only the entries `keep` accepts, in their order.
    pub fn retain(&mut self, mut keep: impl FnMut(&InternedStr, &mut MetaValue) -> bool) {
        self.entries.retain_mut(|e| keep(&e.key, &mut e.value));
    }

    /// Remove every entry.
    pub fn clear(&mut self) {
        self.entries.clear();
    }

    /// Release spare capacity, so the map holds exactly its entries.
    pub fn shrink_to_fit(&mut self) {
        self.entries.shrink_to_fit();
    }

    /// The entries in insertion order.
    #[must_use]
    pub fn iter(&self) -> Iter<'_> {
        Iter(self.entries.iter())
    }

    /// The entries in insertion order, values mutable.
    pub fn iter_mut(&mut self) -> IterMut<'_> {
        IterMut(self.entries.iter_mut())
    }

    /// The keys in insertion order.
    pub fn keys(&self) -> impl ExactSizeIterator<Item = &InternedStr> + DoubleEndedIterator {
        self.entries.iter().map(|e| &e.key)
    }

    /// The values in insertion order.
    pub fn values(&self) -> impl ExactSizeIterator<Item = &MetaValue> + DoubleEndedIterator {
        self.entries.iter().map(|e| &e.value)
    }

    /// The values in insertion order, mutably.
    pub fn values_mut(
        &mut self,
    ) -> impl ExactSizeIterator<Item = &mut MetaValue> + DoubleEndedIterator {
        self.entries.iter_mut().map(|e| &mut e.value)
    }

    /// Every key, mutably, for re-pointing an interned key at a shared
    /// allocation (the loader's dedup pass). Replacing a key with a
    /// DIFFERENT string through this would break key uniqueness, so it is
    /// not public API.
    #[doc(hidden)]
    pub fn for_each_key_mut(&mut self, mut f: impl FnMut(&mut InternedStr)) {
        for e in &mut self.entries {
            f(&mut e.key);
        }
    }
}

impl fmt::Debug for Metadata {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Keys print as strings, as the `String` keys of the hash map did.
        f.debug_map()
            .entries(self.iter().map(|(k, v)| (k.as_str(), v)))
            .finish()
    }
}

impl PartialEq for Metadata {
    /// Order-independent, as the hash map this replaced was: same keys,
    /// each with an equal value. Keys are unique, so equal lengths plus
    /// every entry found on the other side is enough.
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len()
            && self
                .entries
                .iter()
                .all(|e| other.get(e.key.as_str()) == Some(&e.value))
    }
}

impl Eq for Metadata {}

impl std::ops::Index<&str> for Metadata {
    type Output = MetaValue;

    /// # Panics
    ///
    /// Panics if `key` is not present, like `HashMap`'s indexing.
    fn index(&self, key: &str) -> &MetaValue {
        self.get(key).expect("metadata key not present")
    }
}

impl<K: Into<InternedStr>> FromIterator<(K, MetaValue)> for Metadata {
    fn from_iter<I: IntoIterator<Item = (K, MetaValue)>>(iter: I) -> Self {
        let mut map = Self::new();
        map.extend(iter);
        map
    }
}

impl<K: Into<InternedStr>> Extend<(K, MetaValue)> for Metadata {
    /// Inserts each pair in turn, so a repeated key keeps its last value
    /// (and its first position), as with a hash map.
    fn extend<I: IntoIterator<Item = (K, MetaValue)>>(&mut self, iter: I) {
        let iter = iter.into_iter();
        self.entries.reserve(iter.size_hint().0);
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

/// Borrowing iterator over a [`Metadata`]'s entries, in insertion order.
#[derive(Debug, Clone)]
pub struct Iter<'a>(std::slice::Iter<'a, MetaEntry>);

impl<'a> Iterator for Iter<'a> {
    type Item = (&'a InternedStr, &'a MetaValue);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|e| (&e.key, &e.value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl DoubleEndedIterator for Iter<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|e| (&e.key, &e.value))
    }
}

impl ExactSizeIterator for Iter<'_> {}

/// Iterator over a [`Metadata`]'s entries with mutable values, in
/// insertion order.
#[derive(Debug)]
pub struct IterMut<'a>(std::slice::IterMut<'a, MetaEntry>);

impl<'a> Iterator for IterMut<'a> {
    type Item = (&'a InternedStr, &'a mut MetaValue);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|e| (&e.key, &mut e.value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl ExactSizeIterator for IterMut<'_> {}

/// Owning iterator over a [`Metadata`]'s entries, in insertion order.
#[derive(Debug)]
pub struct IntoIter(std::vec::IntoIter<MetaEntry>);

impl Iterator for IntoIter {
    type Item = (InternedStr, MetaValue);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|e| (e.key, e.value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl ExactSizeIterator for IntoIter {}

impl<'a> IntoIterator for &'a Metadata {
    type Item = (&'a InternedStr, &'a MetaValue);
    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Iter<'a> {
        self.iter()
    }
}

impl<'a> IntoIterator for &'a mut Metadata {
    type Item = (&'a InternedStr, &'a mut MetaValue);
    type IntoIter = IterMut<'a>;

    fn into_iter(self) -> IterMut<'a> {
        self.iter_mut()
    }
}

impl IntoIterator for Metadata {
    type Item = (InternedStr, MetaValue);
    type IntoIter = IntoIter;

    fn into_iter(self) -> IntoIter {
        IntoIter(self.entries.into_iter())
    }
}

impl Serialize for Metadata {
    /// A map, as the hash map serialized; entries in insertion order.
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_map(self.iter().map(|(k, v)| (k.as_str(), v)))
    }
}

impl<'de> Deserialize<'de> for Metadata {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct MapVisitor;

        impl<'de> serde::de::Visitor<'de> for MapVisitor {
            type Value = Metadata;

            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("a metadata map")
            }

            fn visit_map<A: serde::de::MapAccess<'de>>(
                self,
                mut access: A,
            ) -> Result<Metadata, A::Error> {
                let mut map = Metadata::with_capacity(access.size_hint().unwrap_or(0).min(64));
                while let Some((k, v)) = access.next_entry::<String, MetaValue>()? {
                    map.insert(k, v);
                }
                Ok(map)
            }
        }

        deserializer.deserialize_map(MapVisitor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(v: &str) -> MetaValue {
        MetaValue::String(v.to_string())
    }

    #[test]
    fn test_insert_replaces_in_place_and_keeps_order() {
        let mut m = Metadata::new();
        assert_eq!(m.insert("b", s("1")), None);
        assert_eq!(m.insert("a", s("2")), None);
        assert_eq!(m.insert("b", s("3")), Some(s("1")));
        let keys: Vec<&str> = m.keys().map(InternedStr::as_str).collect();
        assert_eq!(keys, ["b", "a"]);
        assert_eq!(m["b"], s("3"));
        assert_eq!(m.len(), 2);
    }

    #[test]
    fn test_remove_and_retain_keep_remaining_order() {
        let mut m: Metadata = [("a", s("1")), ("b", s("2")), ("c", s("3"))]
            .into_iter()
            .collect();
        assert_eq!(m.remove("b"), Some(s("2")));
        assert_eq!(m.remove("b"), None);
        m.insert("d", s("4"));
        m.retain(|k, _| k.as_str() != "a");
        let keys: Vec<&str> = m.keys().map(InternedStr::as_str).collect();
        assert_eq!(keys, ["c", "d"]);
        assert!(!m.contains_key("a"));
        assert!(m.contains_key("c"));
    }

    #[test]
    fn test_eq_is_order_independent() {
        let a: Metadata = [("x", s("1")), ("y", s("2"))].into_iter().collect();
        let b: Metadata = [("y", s("2")), ("x", s("1"))].into_iter().collect();
        let c: Metadata = [("y", s("2")), ("x", s("9"))].into_iter().collect();
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_ne!(a, Metadata::new());
    }

    #[test]
    fn test_from_iter_repeated_key_keeps_last_value() {
        let m: Metadata = [("k", s("1")), ("k", s("2"))].into_iter().collect();
        assert_eq!(m.len(), 1);
        assert_eq!(m.get("k"), Some(&s("2")));
    }

    #[test]
    fn test_serde_roundtrip_is_a_map_in_insertion_order() {
        let m: Metadata = [("z", s("1")), ("a", MetaValue::Bool(true))]
            .into_iter()
            .collect();
        let json = serde_json::to_string(&m).expect("serialize");
        assert!(json.starts_with("{\"z\":"), "not insertion order: {json}");
        let back: Metadata = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(back, m);
        let keys: Vec<&str> = back.keys().map(InternedStr::as_str).collect();
        assert_eq!(keys, ["z", "a"]);
    }

    #[test]
    fn test_entry_is_56_bytes() {
        // The point of the layout: an entry is a 16-byte interned key and
        // the value, nothing else. Growing either is a memory regression
        // on metadata-heavy ledgers (#2835).
        assert!(
            std::mem::size_of::<MetaEntry>() <= 56,
            "MetaEntry grew to {} bytes",
            std::mem::size_of::<MetaEntry>()
        );
        // And the map itself is one `Vec` header, no hasher or table.
        assert!(
            std::mem::size_of::<Metadata>() <= 24,
            "Metadata grew to {} bytes",
            std::mem::size_of::<Metadata>()
        );
    }

    #[test]
    fn test_insert_grows_exactly_while_small() {
        // One to four entries are allocated at their exact size: no spare
        // slots for the life of the ledger and no shrinking `realloc`. A plain
        // `Vec::push` reserves four slots on the first entry, which is what
        // this would catch (#2835).
        let mut m = Metadata::new();
        assert_eq!(m.entries.capacity(), 0, "an empty map must not allocate");
        for n in 1..=SMALL {
            m.insert(format!("k{n}"), s("v"));
            assert_eq!(
                m.entries.capacity(),
                n,
                "{n} entries should occupy exactly {n} slots"
            );
        }
        // Replacing a value never grows.
        m.insert("k1", s("w"));
        assert_eq!(m.entries.capacity(), SMALL);
        // Past the small sizes growth is amortized, so bulk inserts stay
        // linear rather than reallocating on every entry.
        for n in SMALL + 1..=64 {
            m.insert(format!("k{n}"), s("v"));
        }
        assert_eq!(m.len(), 64);
        assert!(
            m.entries.capacity() < 2 * 64,
            "growth is amortized doubling"
        );
    }

    #[test]
    fn test_meta_map_from_trims_spare_capacity() {
        // `MetaMap::from` is where a map built in bulk is attached, so it is
        // where spare slots must go.
        let mut m = Metadata::with_capacity(16);
        m.insert("a", s("1"));
        m.insert("b", s("2"));
        let attached = crate::MetaMap::from(m);
        assert_eq!(attached.as_map().entries.capacity(), 2);
    }
}
