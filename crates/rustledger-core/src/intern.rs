//! String interning for accounts and currencies.
//!
//! String interning reduces memory usage by storing each unique string once
//! and using references to that single copy. This is especially useful for
//! account names and currencies which appear repeatedly throughout a ledger.
//!
//! # Example
//!
//! ```
//! use rustledger_core::intern::StringInterner;
//!
//! let mut interner = StringInterner::new();
//!
//! let s1 = interner.intern("Expenses:Food");
//! let s2 = interner.intern("Expenses:Food");
//! let s3 = interner.intern("Assets:Bank");
//!
//! // s1 and s2 point to the same string
//! assert!(std::ptr::eq(s1.as_str().as_ptr(), s2.as_str().as_ptr()));
//!
//! // s3 is different
//! assert!(!std::ptr::eq(s1.as_str().as_ptr(), s3.as_str().as_ptr()));
//! ```

use std::collections::HashSet;
use std::sync::Arc;

use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// An interned string reference.
///
/// This is a thin wrapper around `Arc<str>` that provides cheap cloning
/// and comparison. Two `InternedStr` values with the same content will
/// share the same underlying memory.
#[derive(Debug, Clone, Eq)]
pub struct InternedStr(Arc<str>);

impl Serialize for InternedStr {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.0.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for InternedStr {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let s = String::deserialize(deserializer)?;
        Ok(Self::new(s))
    }
}

impl PartialOrd for InternedStr {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for InternedStr {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl InternedStr {
    /// Create a new interned string (without using an interner).
    /// Prefer using `StringInterner::intern` for deduplication.
    pub fn new(s: impl Into<Arc<str>>) -> Self {
        Self(s.into())
    }

    /// Get the string slice.
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Check if two interned strings share the same allocation.
    /// This is O(1) pointer comparison.
    pub fn ptr_eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl PartialEq for InternedStr {
    fn eq(&self, other: &Self) -> bool {
        // Fast path: pointer comparison
        if Arc::ptr_eq(&self.0, &other.0) {
            return true;
        }
        // Slow path: string comparison
        self.0 == other.0
    }
}

impl std::hash::Hash for InternedStr {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl std::fmt::Display for InternedStr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl AsRef<str> for InternedStr {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

impl std::ops::Deref for InternedStr {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<&str> for InternedStr {
    fn from(s: &str) -> Self {
        Self::new(s)
    }
}

impl From<String> for InternedStr {
    fn from(s: String) -> Self {
        Self::new(s)
    }
}

impl From<&String> for InternedStr {
    fn from(s: &String) -> Self {
        Self::new(s.as_str())
    }
}

impl From<&Self> for InternedStr {
    fn from(s: &Self) -> Self {
        s.clone()
    }
}

impl PartialEq<str> for InternedStr {
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

impl PartialEq<&str> for InternedStr {
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}

impl PartialEq<String> for InternedStr {
    fn eq(&self, other: &String) -> bool {
        self.as_str() == other
    }
}

impl Default for InternedStr {
    fn default() -> Self {
        Self::new("")
    }
}

impl std::borrow::Borrow<str> for InternedStr {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

/// A string interner that deduplicates strings.
///
/// This is useful for reducing memory usage when many strings with the
/// same content are created, such as account names and currencies in
/// a large ledger.
#[derive(Debug, Default)]
pub struct StringInterner {
    /// Set of all interned strings.
    strings: HashSet<Arc<str>>,
}

impl StringInterner {
    /// Create a new empty interner.
    pub fn new() -> Self {
        Self {
            strings: HashSet::new(),
        }
    }

    /// Create an interner with pre-allocated capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            strings: HashSet::with_capacity(capacity),
        }
    }

    /// Intern a string.
    ///
    /// If the string already exists in the interner, returns a reference
    /// to the existing copy. Otherwise, stores the string and returns
    /// a reference to the new copy.
    pub fn intern(&mut self, s: &str) -> InternedStr {
        if let Some(existing) = self.strings.get(s) {
            InternedStr(existing.clone())
        } else {
            let arc: Arc<str> = s.into();
            self.strings.insert(arc.clone());
            InternedStr(arc)
        }
    }

    /// Intern a string, taking ownership.
    pub fn intern_string(&mut self, s: String) -> InternedStr {
        if let Some(existing) = self.strings.get(s.as_str()) {
            InternedStr(existing.clone())
        } else {
            let arc: Arc<str> = s.into();
            self.strings.insert(arc.clone());
            InternedStr(arc)
        }
    }

    /// Check if a string is already interned.
    pub fn contains(&self, s: &str) -> bool {
        self.strings.contains(s)
    }

    /// Get the number of unique strings.
    pub fn len(&self) -> usize {
        self.strings.len()
    }

    /// Check if the interner is empty.
    pub fn is_empty(&self) -> bool {
        self.strings.is_empty()
    }

    /// Get an iterator over all interned strings.
    pub fn iter(&self) -> impl Iterator<Item = &str> {
        self.strings.iter().map(std::convert::AsRef::as_ref)
    }

    /// Clear all interned strings.
    pub fn clear(&mut self) {
        self.strings.clear();
    }
}

/// A specialized interner for account names.
///
/// Account names follow a specific pattern (Type:Component:Component)
/// and this interner can provide additional functionality like
/// extracting components.
#[derive(Debug, Default)]
pub struct AccountInterner {
    interner: StringInterner,
}

impl AccountInterner {
    /// Create a new account interner.
    pub fn new() -> Self {
        Self {
            interner: StringInterner::new(),
        }
    }

    /// Intern an account name.
    pub fn intern(&mut self, account: &str) -> InternedStr {
        self.interner.intern(account)
    }

    /// Get the number of unique accounts.
    pub fn len(&self) -> usize {
        self.interner.len()
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.interner.is_empty()
    }

    /// Get all interned accounts.
    pub fn accounts(&self) -> impl Iterator<Item = &str> {
        self.interner.iter()
    }

    /// Get accounts matching a prefix.
    pub fn accounts_with_prefix<'a>(&'a self, prefix: &'a str) -> impl Iterator<Item = &'a str> {
        self.interner.iter().filter(move |s| s.starts_with(prefix))
    }
}

/// A specialized interner for currency codes.
///
/// Currency codes are typically short (3-4 characters) and uppercase.
#[derive(Debug, Default)]
pub struct CurrencyInterner {
    interner: StringInterner,
}

impl CurrencyInterner {
    /// Create a new currency interner.
    pub fn new() -> Self {
        Self {
            interner: StringInterner::new(),
        }
    }

    /// Intern a currency code.
    pub fn intern(&mut self, currency: &str) -> InternedStr {
        self.interner.intern(currency)
    }

    /// Get the number of unique currencies.
    pub fn len(&self) -> usize {
        self.interner.len()
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.interner.is_empty()
    }

    /// Get all interned currencies.
    pub fn currencies(&self) -> impl Iterator<Item = &str> {
        self.interner.iter()
    }
}

/// Thread-safe string interner using a mutex.
///
/// Use this when interning strings from multiple threads.
#[derive(Debug, Default)]
pub struct SyncStringInterner {
    inner: std::sync::Mutex<StringInterner>,
}

impl SyncStringInterner {
    /// Create a new thread-safe interner.
    pub fn new() -> Self {
        Self {
            inner: std::sync::Mutex::new(StringInterner::new()),
        }
    }

    /// Intern a string (thread-safe).
    pub fn intern(&self, s: &str) -> InternedStr {
        self.inner.lock().unwrap().intern(s)
    }

    /// Get the number of unique strings.
    pub fn len(&self) -> usize {
        self.inner.lock().unwrap().len()
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.inner.lock().unwrap().is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_interned_str_equality() {
        let s1 = InternedStr::new("hello");
        let s2 = InternedStr::new("hello");
        let s3 = InternedStr::new("world");

        assert_eq!(s1, s2);
        assert_ne!(s1, s3);
        assert_eq!(s1, "hello");
        assert_eq!(s1, "hello".to_string());
    }

    #[test]
    fn test_interner_deduplication() {
        let mut interner = StringInterner::new();

        let s1 = interner.intern("Expenses:Food");
        let s2 = interner.intern("Expenses:Food");
        let s3 = interner.intern("Assets:Bank");

        // s1 and s2 should share the same allocation
        assert!(s1.ptr_eq(&s2));

        // s3 is different
        assert!(!s1.ptr_eq(&s3));

        // Only 2 unique strings
        assert_eq!(interner.len(), 2);
    }

    #[test]
    fn test_interner_contains() {
        let mut interner = StringInterner::new();

        interner.intern("hello");

        assert!(interner.contains("hello"));
        assert!(!interner.contains("world"));
    }

    #[test]
    fn test_account_interner() {
        let mut interner = AccountInterner::new();

        interner.intern("Expenses:Food:Coffee");
        interner.intern("Expenses:Food:Groceries");
        interner.intern("Assets:Bank:Checking");

        assert_eq!(interner.len(), 3);

        assert_eq!(interner.accounts_with_prefix("Expenses:").count(), 2);
    }

    #[test]
    fn test_currency_interner() {
        let mut interner = CurrencyInterner::new();

        let usd1 = interner.intern("USD");
        let usd2 = interner.intern("USD");
        let eur = interner.intern("EUR");

        assert!(usd1.ptr_eq(&usd2));
        assert!(!usd1.ptr_eq(&eur));
        assert_eq!(interner.len(), 2);
    }

    #[test]
    fn test_sync_interner() {
        use std::thread;

        let interner = std::sync::Arc::new(SyncStringInterner::new());

        let handles: Vec<_> = (0..4)
            .map(|_| {
                let interner = interner.clone();
                thread::spawn(move || {
                    for _ in 0..100 {
                        interner.intern("shared-string");
                    }
                })
            })
            .collect();

        for handle in handles {
            handle.join().unwrap();
        }

        // Should only have one unique string despite being interned 400 times
        assert_eq!(interner.len(), 1);
    }

    #[test]
    fn test_interned_str_hash() {
        use std::collections::HashMap;

        let s1 = InternedStr::new("key");
        let s2 = InternedStr::new("key");

        let mut map = HashMap::new();
        map.insert(s1, 1);

        // s2 should find the same entry as s1
        assert_eq!(map.get(&s2), Some(&1));
    }
}
