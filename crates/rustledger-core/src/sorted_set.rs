//! [`SortedSet`]: the one representation of an entry's tags and links.
//!
//! Beancount's tags and links are sets (`frozenset`): a tag written twice, or
//! written and also pushed with `pushtag`, is one tag, and the order they were
//! written in carries no meaning. Its printer and `bean-query` both emit them
//! sorted.
//!
//! rledger used to keep them as a plain `Vec` in source order, and every path
//! that built an entry decided for itself whether to dedup (#2545): the parser
//! skipped a pushed tag already written but kept a tag written twice, plugins
//! could return anything, and consumers (`meta.hash`, fingerprints, BQL,
//! `PRINT`) saw whichever order and multiplicity the producer chose.
//!
//! `SortedSet` makes "sorted and deduplicated" a property of the TYPE. Its
//! storage is private and every way to build or change one (`from_iter`,
//! `From<Vec<_>>`, [`insert`](SortedSet::insert), [`extend`](Extend::extend),
//! serde deserialization, ...) restores the invariant, so the parser, pushtag
//! application, plugin and FFI conversions cannot produce an unsorted or
//! duplicated list even by accident. Reads go through `Deref<Target = [T]>`.
//!
//! The order is `T`'s `Ord`. For [`Tag`](crate::Tag) and
//! [`Link`](crate::Link) that is byte order of the UTF-8 text, which equals
//! Unicode code-point order, which is how Python sorts `str`.
//!
//! `rledger format` is unaffected: it rewrites the source text, not these
//! values, so the order written in a file is kept there.

use std::borrow::Borrow;
use std::ops::Deref;

/// A sorted, duplicate-free list. See the [module docs](self).
///
/// The rkyv archive stores the backing `Vec` as is. Archives are only ever
/// written from a `SortedSet`, which already holds the invariant, so reading one
/// back yields a valid set; a change to the invariant itself must bump the
/// caches' `CACHE_VERSION`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(
    feature = "rkyv",
    derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)
)]
pub struct SortedSet<T>(Vec<T>);

/// The tags of a transaction, note or document.
pub type TagSet = SortedSet<crate::Tag>;

/// The links of a transaction, note or document.
pub type LinkSet = SortedSet<crate::Link>;

impl<T> SortedSet<T> {
    /// An empty set.
    #[must_use]
    pub const fn new() -> Self {
        Self(Vec::new())
    }

    /// The elements, sorted and unique.
    #[must_use]
    pub fn as_slice(&self) -> &[T] {
        &self.0
    }

    /// Unwrap into the backing `Vec`, sorted and unique.
    #[must_use]
    pub fn into_vec(self) -> Vec<T> {
        self.0
    }
}

impl<T: Ord> SortedSet<T> {
    /// Sort and deduplicate `v`. Every constructor funnels through here.
    #[must_use]
    pub fn from_vec(mut v: Vec<T>) -> Self {
        v.sort_unstable();
        v.dedup();
        Self(v)
    }

    /// Insert `value`, keeping the set sorted. Returns `false` if it was
    /// already present (the set is then unchanged).
    pub fn insert(&mut self, value: T) -> bool {
        match self.0.binary_search(&value) {
            Ok(_) => false,
            Err(at) => {
                self.0.insert(at, value);
                true
            }
        }
    }

    /// Remove `value`. Returns `true` if it was present.
    pub fn remove<Q>(&mut self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        match self.0.binary_search_by(|e| e.borrow().cmp(value)) {
            Ok(at) => {
                self.0.remove(at);
                true
            }
            Err(_) => false,
        }
    }

    /// Whether `value` is in the set (binary search).
    #[must_use]
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.0.binary_search_by(|e| e.borrow().cmp(value)).is_ok()
    }

    /// Keep only the elements for which `f` returns `true`. Removing elements
    /// cannot break the order, so no re-sort is needed.
    pub fn retain(&mut self, f: impl FnMut(&T) -> bool) {
        self.0.retain(f);
    }

    /// Mutate every element in place, then restore the invariant.
    ///
    /// Meant for value-preserving rewrites such as the loader re-pointing each
    /// identifier at the workspace interner's `Arc`. A closure that changes
    /// values is still safe: the set is re-sorted and re-deduplicated after.
    pub fn for_each_mut(&mut self, f: impl FnMut(&mut T)) {
        self.0.iter_mut().for_each(f);
        if !self.0.is_sorted_by(|a, b| a < b) {
            self.0.sort_unstable();
            self.0.dedup();
        }
    }
}

impl<T> Default for SortedSet<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Deref for SortedSet<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        &self.0
    }
}

impl<T> AsRef<[T]> for SortedSet<T> {
    fn as_ref(&self) -> &[T] {
        &self.0
    }
}

impl<T: Ord> From<Vec<T>> for SortedSet<T> {
    fn from(v: Vec<T>) -> Self {
        Self::from_vec(v)
    }
}

impl<T: Ord, const N: usize> From<[T; N]> for SortedSet<T> {
    fn from(a: [T; N]) -> Self {
        Self::from_vec(Vec::from(a))
    }
}

impl<T> From<SortedSet<T>> for Vec<T> {
    fn from(s: SortedSet<T>) -> Self {
        s.0
    }
}

impl<T: Ord> FromIterator<T> for SortedSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self::from_vec(iter.into_iter().collect())
    }
}

impl<T: Ord> Extend<T> for SortedSet<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let before = self.0.len();
        self.0.extend(iter);
        if self.0.len() != before {
            self.0.sort_unstable();
            self.0.dedup();
        }
    }
}

impl<T> IntoIterator for SortedSet<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, T> IntoIterator for &'a SortedSet<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

/// Element-wise comparison against a plain list, in order. A list that is not
/// itself sorted and unique never equals a set.
impl<T: PartialEq<U>, U> PartialEq<Vec<U>> for SortedSet<T> {
    fn eq(&self, other: &Vec<U>) -> bool {
        self.0.as_slice() == other.as_slice()
    }
}

/// See the `PartialEq<Vec<U>>` impl.
impl<T: PartialEq<U>, U> PartialEq<[U]> for SortedSet<T> {
    fn eq(&self, other: &[U]) -> bool {
        self.0.as_slice() == other
    }
}

/// See the `PartialEq<Vec<U>>` impl.
impl<T: PartialEq<U>, U, const N: usize> PartialEq<[U; N]> for SortedSet<T> {
    fn eq(&self, other: &[U; N]) -> bool {
        self.0.as_slice() == other.as_slice()
    }
}

impl<T: serde::Serialize> serde::Serialize for SortedSet<T> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.0.serialize(serializer)
    }
}

/// Deserializes any list and normalizes it, so JSON from an older writer, a
/// plugin, or a hand-written file can never smuggle in an unsorted or
/// duplicated set.
impl<'de, T: serde::Deserialize<'de> + Ord> serde::Deserialize<'de> for SortedSet<T> {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Vec::<T>::deserialize(deserializer).map(Self::from_vec)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Tag;
    use proptest::prelude::*;

    fn is_set<T: Ord>(s: &[T]) -> bool {
        s.windows(2).all(|w| w[0] < w[1])
    }

    #[test]
    fn written_twice_is_one() {
        let s: TagSet = ["trip", "trip", "food"]
            .into_iter()
            .map(Tag::from)
            .collect();
        assert_eq!(s, ["food", "trip"]);
    }

    #[test]
    fn insert_keeps_order_and_reports_presence() {
        let mut s = TagSet::new();
        assert!(s.insert(Tag::from("b")));
        assert!(s.insert(Tag::from("a")));
        assert!(!s.insert(Tag::from("b")));
        assert_eq!(s, ["a", "b"]);
        assert!(s.contains("a"));
        assert!(s.remove("a"));
        assert!(!s.remove("a"));
        assert_eq!(s, ["b"]);
    }

    #[test]
    fn serde_normalizes_input() {
        let s: TagSet = serde_json::from_str(r#"["z","a","z"]"#).unwrap();
        assert_eq!(s, ["a", "z"]);
        assert_eq!(serde_json::to_string(&s).unwrap(), r#"["a","z"]"#);
    }

    #[test]
    fn for_each_mut_restores_invariant() {
        let mut s: SortedSet<String> = vec!["a".into(), "b".into()].into();
        // Both elements become "c": the set re-sorts and drops the duplicate.
        s.for_each_mut(|e| *e = "c".into());
        assert_eq!(s, ["c".to_string()]);
    }

    proptest! {
        /// Every constructor and mutator yields a strictly increasing list
        /// holding exactly the distinct input elements.
        #[test]
        fn every_path_yields_a_set(
            a in prop::collection::vec("[a-c]{0,2}", 0..8),
            b in prop::collection::vec("[a-c]{0,2}", 0..8),
        ) {
            let mut want: Vec<String> = a.iter().chain(&b).cloned().collect();
            want.sort();
            want.dedup();

            let collected: SortedSet<String> = a.iter().chain(&b).cloned().collect();
            prop_assert!(is_set(&collected));
            prop_assert_eq!(collected.as_slice(), want.as_slice());

            let mut inserted = SortedSet::from_vec(a.clone());
            for x in &b { inserted.insert(x.clone()); }
            prop_assert_eq!(inserted.as_slice(), want.as_slice());

            let mut extended: SortedSet<String> = a.clone().into();
            extended.extend(b.iter().cloned());
            prop_assert_eq!(extended.as_slice(), want.as_slice());

            let json = serde_json::to_string(&a.iter().chain(&b).collect::<Vec<_>>()).unwrap();
            let de: SortedSet<String> = serde_json::from_str(&json).unwrap();
            prop_assert_eq!(de.as_slice(), want.as_slice());
        }
    }
}
