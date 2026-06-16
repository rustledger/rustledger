//! Domain-typed identifiers: [`Account`], [`Currency`], [`Tag`], [`Link`].
//!
//! These newtype wrappers around [`InternedStr`] give the type system
//! enough vocabulary to distinguish the different kinds of identifier
//! the beancount AST carries. Pre-newtype, every identifier was just
//! an `InternedStr` — passing an account where a currency was
//! expected (or vice versa) compiled fine, and the bug surfaced
//! only at runtime via wrong-but-validly-shaped string matching.
//! Now the same mistake is a type error.
//!
//! # Design
//!
//! Each newtype is a transparent wrapper:
//!
//! - `Deref<Target = str>` so calls like `account.starts_with("Assets:")`
//!   work without `.as_str()` everywhere.
//! - `AsRef<str>` and [`Borrow<str>`](std::borrow::Borrow) so `HashMap` lookups by `&str`
//!   keep working (`some_map.get("Assets:Bank")` where the map is
//!   keyed by [`Account`]).
//! - `PartialEq` against `str` / `&str` / `String` / `InternedStr` /
//!   the newtype's own type, so `account == "Assets:Bank"` keeps
//!   reading naturally without coercion.
//! - `From<&str>`, `From<String>`, `From<InternedStr>` for
//!   construction at call sites that have a string and need the
//!   typed form.
//! - `Hash` delegates to the inner `InternedStr`'s hash, so
//!   `HashMap<Account, V>` and `HashMap<InternedStr, V>` produce
//!   the same bucketing for the same underlying string.
//!
//! What you DON'T get for free is cross-newtype assignment:
//!
//! ```compile_fail
//! # use rustledger_core::{Account, Currency};
//! fn want_currency(_: Currency) {}
//! let acct = Account::from("Assets:Bank");
//! want_currency(acct); // ← type error
//! ```
//!
//! Conversions between newtypes are deliberate (`Currency::from(account.into_interned())`)
//! so the compiler can flag accidental crossings.
//!
//! # When to use which
//!
//! All four newtypes — [`Currency`], [`Account`], [`Tag`], and
//! [`Link`] — are fully plumbed through the AST, including
//! `MetaValue` variants:
//!
//! - [`Currency`]: `Commodity.currency`, `Open.currencies` entries,
//!   `Amount.currency`, `CostSpec.currency`, `Price.currency`,
//!   `IncompleteAmount::CurrencyOnly`, `MetaValue::Currency`.
//! - [`Account`]: `Open.account`, `Close.account`, `Balance.account`,
//!   `Pad.account` / `source_account`, `Note.account`,
//!   `Document.account`, `Posting.account`, `MetaValue::Account`.
//! - [`Tag`]: `Transaction.tags` entries, `pushtag`/`poptag` stack,
//!   `Document.tags`, `MetaValue::Tag`.
//! - [`Link`]: `Transaction.links` entries, `Document.links`,
//!   `MetaValue::Link`.
//!
//! The plugin wire-format type `rustledger_plugin_types::MetaValueData`
//! deliberately keeps `String` payloads — `plugin-types` is a minimal
//! WASM-compatible crate that does not depend on `rustledger-core`,
//! and plugins run without access to the workspace interner anyway.
//! The convert boundary
//! (`rustledger_plugin::convert::from_wrapper`) wraps the incoming
//! strings in fresh `Arc<str>`s; the cross-file canonicalization to
//! one `Arc<str>` per identifier string happens later in
//! `rustledger_loader::dedup::reintern_directives`, which walks both
//! AST identifier fields and `MetaValue::*` payloads inside metadata.

use crate::InternedStr;
#[cfg(feature = "rkyv")]
use crate::intern::AsInternedStr;

macro_rules! domain_newtype {
    ($name:ident, $kind:literal) => {
        #[doc = concat!("Domain-typed identifier for a ", $kind, ". See the [module docs](crate::identifiers) for rationale.")]
        #[derive(Debug, Clone, Eq)]
        #[cfg_attr(
            feature = "rkyv",
            derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)
        )]
        #[repr(transparent)]
        pub struct $name(
            #[cfg_attr(feature = "rkyv", rkyv(with = AsInternedStr))] InternedStr,
        );

        impl $name {
            /// Construct from anything that can become an `InternedStr`.
            #[must_use]
            pub fn new(s: impl Into<InternedStr>) -> Self {
                Self(s.into())
            }

            /// Borrow the underlying string slice.
            #[must_use]
            pub fn as_str(&self) -> &str {
                self.0.as_str()
            }

            /// Borrow the underlying `InternedStr`. Useful when interfacing
            /// with APIs that still take untyped interned strings.
            #[must_use]
            pub const fn as_interned(&self) -> &InternedStr {
                &self.0
            }

            /// Unwrap to the underlying `InternedStr`, discarding the
            /// domain tag. Use deliberately — this is the explicit
            /// "I'm crossing types on purpose" escape hatch.
            #[must_use]
            pub fn into_interned(self) -> InternedStr {
                self.0
            }

            /// Pointer-equality on the underlying `Arc<str>`.
            ///
            /// `true` iff both values point at the same interner allocation.
            /// Used by cross-file dedup tests to assert that the loader's
            /// re-interning pass canonicalized the storage; not a substitute
            /// for `==` (which is the byte-equality semantics callers want).
            #[must_use]
            pub fn ptr_eq(&self, other: &Self) -> bool {
                self.0.ptr_eq(&other.0)
            }

            /// Mutable access to the underlying `InternedStr`.
            /// Used by the loader's cross-file interning pass
            /// (`rustledger_loader::dedup`) to canonicalize the
            /// `Arc` after merging directives from multiple files —
            /// the value semantics don't change, but the storage is
            /// re-pointed at the workspace-wide interner's copy.
            pub const fn as_interned_mut(&mut self) -> &mut InternedStr {
                &mut self.0
            }
        }

        impl PartialEq for $name {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        impl PartialEq<str> for $name {
            fn eq(&self, other: &str) -> bool {
                self.0 == *other
            }
        }

        impl PartialEq<&str> for $name {
            fn eq(&self, other: &&str) -> bool {
                self.0 == **other
            }
        }

        impl PartialEq<String> for $name {
            fn eq(&self, other: &String) -> bool {
                self.0 == *other
            }
        }

        impl PartialEq<InternedStr> for $name {
            fn eq(&self, other: &InternedStr) -> bool {
                self.0 == *other
            }
        }

        impl PartialEq<$name> for &str {
            fn eq(&self, other: &$name) -> bool {
                other.0 == **self
            }
        }

        impl PartialEq<$name> for str {
            fn eq(&self, other: &$name) -> bool {
                other.0 == *self
            }
        }

        impl PartialEq<$name> for InternedStr {
            fn eq(&self, other: &$name) -> bool {
                *self == other.0
            }
        }

        impl std::hash::Hash for $name {
            fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
                self.0.hash(state);
            }
        }

        impl std::cmp::PartialOrd for $name {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }

        impl std::cmp::Ord for $name {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                self.0.cmp(&other.0)
            }
        }

        impl std::ops::Deref for $name {
            type Target = str;
            fn deref(&self) -> &str {
                self.0.as_str()
            }
        }

        impl AsRef<str> for $name {
            fn as_ref(&self) -> &str {
                self.0.as_str()
            }
        }

        impl std::borrow::Borrow<str> for $name {
            fn borrow(&self) -> &str {
                self.0.as_str()
            }
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::Display::fmt(&self.0, f)
            }
        }

        impl From<&str> for $name {
            fn from(s: &str) -> Self {
                Self(InternedStr::from(s))
            }
        }

        impl From<String> for $name {
            fn from(s: String) -> Self {
                Self(InternedStr::from(s))
            }
        }

        impl From<&String> for $name {
            fn from(s: &String) -> Self {
                Self(InternedStr::from(s.as_str()))
            }
        }

        impl From<InternedStr> for $name {
            fn from(s: InternedStr) -> Self {
                Self(s)
            }
        }

        impl From<&InternedStr> for $name {
            fn from(s: &InternedStr) -> Self {
                Self(s.clone())
            }
        }

        impl From<&$name> for $name {
            fn from(s: &$name) -> Self {
                s.clone()
            }
        }

        impl Default for $name {
            fn default() -> Self {
                Self(InternedStr::default())
            }
        }

        impl serde::Serialize for $name {
            fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                self.0.serialize(serializer)
            }
        }

        impl<'de> serde::Deserialize<'de> for $name {
            fn deserialize<D: serde::Deserializer<'de>>(
                deserializer: D,
            ) -> Result<Self, D::Error> {
                Ok(Self(InternedStr::deserialize(deserializer)?))
            }
        }

        // rkyv archive is `#[derive]`'d above using the field
        // attribute `#[rkyv(with = AsInternedStr)]` — same wrapper
        // pattern `Posting.account` (and every other `InternedStr`
        // field) uses. That goes through `ArchivedString` via the
        // `AsInternedStr` adapter, picking up bytecheck/CheckBytes
        // for free.
    };
}

domain_newtype!(Account, "beancount account name (e.g. `Assets:Cash:USD`)");
domain_newtype!(Currency, "currency code (e.g. `USD`, `EUR`, `AAPL`)");
domain_newtype!(Tag, "beancount tag (e.g. `#travel`)");
domain_newtype!(Link, "beancount link (e.g. `^invoice-2024-01`)");

/// Returns `true` if `child` is the same account as `parent`, or a
/// sub-account of it.
///
/// Beancount's `balance Assets:Bank` assertion (and several other
/// account-scoped operations) includes postings to `Assets:Bank` AND
/// `Assets:Bank:Checking`, `Assets:Bank:Savings`, etc. The match is
/// exact OR `parent + ":"` prefix; a name that merely starts with
/// `parent`'s string (`Assets:BankAlias`) is NOT a sub-account.
///
/// Both arguments are `&str` so callers can mix `Account`, `&str`,
/// and `String` without coercion. The function does not allocate.
///
/// Lifted from
/// `rustledger-validate::validators::balance::sum_account_and_subaccounts`
/// and `rustledger-lsp::handlers::code_lens::is_account_or_subaccount`
/// so both call sites stay aligned under one definition.
#[must_use]
pub fn is_subaccount_or_equal(child: &str, parent: &str) -> bool {
    if child == parent {
        return true;
    }
    let parent_len = parent.len();
    child.len() > parent_len && child.as_bytes()[parent_len] == b':' && child.starts_with(parent)
}

/// The five Beancount root account types, in declaration order.
///
/// The canonical root-type list for core consumers: the FFI surfaces
/// (`util.types`, `util.getAccountType`), the query account-type sort order, and
/// the LSP account-type check all reference this so they cannot drift.
/// (`rustledger-completion` keeps its own copy — it is a minimal crate that does
/// not depend on `rustledger-core`.)
///
/// These are the default English roots; the `name_*` loader options can rename
/// them per-ledger, which this constant does not model — do not use it to
/// classify accounts in a config-aware context.
pub const ACCOUNT_TYPES: [&str; 5] = ["Assets", "Liabilities", "Equity", "Income", "Expenses"];

/// The lowercased root account type for `account` — the segment before the
/// first `:` — or `"unknown"` if it is not one of [`ACCOUNT_TYPES`].
#[must_use]
pub fn account_type(account: &str) -> &'static str {
    match account.split(':').next() {
        Some("Assets") => "assets",
        Some("Liabilities") => "liabilities",
        Some("Equity") => "equity",
        Some("Income") => "income",
        Some("Expenses") => "expenses",
        _ => "unknown",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn account_type_classifies_roots_and_unknown() {
        assert_eq!(account_type("Assets:Bank:Checking"), "assets");
        assert_eq!(account_type("Liabilities:CC"), "liabilities");
        assert_eq!(account_type("Equity:Opening"), "equity");
        assert_eq!(account_type("Income:Salary"), "income");
        assert_eq!(account_type("Expenses:Food"), "expenses");
        // Bare root (no colon) still classifies.
        assert_eq!(account_type("Assets"), "assets");
        // Non-root / empty → unknown.
        assert_eq!(account_type("Frobnicate:X"), "unknown");
        assert_eq!(account_type(""), "unknown");
        // Case-sensitive, like Beancount.
        assert_eq!(account_type("assets:bank"), "unknown");
    }

    #[test]
    fn test_construction_from_str() {
        let a = Account::from("Assets:Bank");
        let c = Currency::from("USD");
        assert_eq!(a, "Assets:Bank");
        assert_eq!(c, "USD");
    }

    #[test]
    fn test_eq_against_str_in_both_directions() {
        let a = Account::from("Assets:Bank");
        assert_eq!(a, "Assets:Bank");
        assert_eq!("Assets:Bank", a);
        assert_ne!(a, "Assets:Other");
    }

    #[test]
    fn test_eq_against_self_kind() {
        let a1 = Account::from("Assets:Bank");
        let a2 = Account::from("Assets:Bank");
        let a3 = Account::from("Assets:Other");
        assert_eq!(a1, a2);
        assert_ne!(a1, a3);
    }

    #[test]
    fn test_hash_borrow_str() {
        use std::collections::HashMap;
        let mut m: HashMap<Account, u32> = HashMap::new();
        m.insert(Account::from("Assets:Bank"), 1);
        // Look up by &str via Borrow<str> impl.
        assert_eq!(m.get("Assets:Bank"), Some(&1));
        assert_eq!(m.get("Assets:Other"), None);
    }

    #[test]
    fn test_deref_str_methods() {
        let a = Account::from("Assets:Bank:Checking");
        assert!(a.starts_with("Assets:"));
        assert!(a.contains(':'));
        assert_eq!(a.len(), 20);
    }

    #[test]
    fn test_round_trip_interned() {
        let i = InternedStr::from("USD");
        let c = Currency::from(i.clone());
        assert_eq!(c.as_interned(), &i);
        assert_eq!(c.into_interned(), i);
    }

    #[test]
    fn test_different_newtypes_dont_cross() {
        // This test is structural — uncommenting either of the
        // assignment lines below MUST cause a compile error
        // (verified by the doc-comment compile_fail block on the
        // module). Here we just confirm the runtime types are
        // distinct via a function signature.
        fn want_account(_: Account) {}
        fn want_currency(_: Currency) {}
        want_account(Account::from("Assets:X"));
        want_currency(Currency::from("USD"));
    }

    #[test]
    fn test_serde_roundtrip() {
        let a = Account::from("Assets:Bank");
        let json = serde_json::to_string(&a).unwrap();
        assert_eq!(json, "\"Assets:Bank\"");
        let back: Account = serde_json::from_str(&json).unwrap();
        assert_eq!(a, back);
    }

    #[test]
    fn is_subaccount_or_equal_exact_match() {
        assert!(is_subaccount_or_equal("Assets:Bank", "Assets:Bank"));
    }

    #[test]
    fn is_subaccount_or_equal_proper_subaccount() {
        assert!(is_subaccount_or_equal(
            "Assets:Bank:Checking",
            "Assets:Bank"
        ));
        assert!(is_subaccount_or_equal(
            "Assets:Bank:Checking:Joint",
            "Assets:Bank"
        ));
    }

    #[test]
    fn is_subaccount_or_equal_prefix_without_segment_boundary_excluded() {
        // The whole point of the segment-boundary rule: a name that
        // starts with the parent's bytes but isn't followed by `:`
        // is NOT a sub-account. This is the case the validator and
        // the LSP both depend on; if the rule ever drifts, balance
        // assertions for `Assets:Bank` would silently include
        // `Assets:BankAlias` postings.
        assert!(!is_subaccount_or_equal("Assets:BankAlias", "Assets:Bank"));
        assert!(!is_subaccount_or_equal(
            "Assets:BankAlias:Checking",
            "Assets:Bank"
        ));
    }

    #[test]
    fn is_subaccount_or_equal_parent_is_prefix_substring_excluded() {
        // `Assets:Ban` is not a sub-account of `Assets:Bank` —
        // unrelated except for sharing a prefix.
        assert!(!is_subaccount_or_equal("Assets:Ban", "Assets:Bank"));
    }

    #[test]
    fn is_subaccount_or_equal_empty_inputs() {
        // Both empty: trivially equal, returns true.
        assert!(is_subaccount_or_equal("", ""));
        // Empty parent against a non-empty child: child does not
        // start with `:`, so excluded. (Beancount account names
        // never start with `:`; this is a defensive-by-construction
        // case for callers that pass garbage.)
        assert!(!is_subaccount_or_equal("Assets:Bank", ""));
        // Empty child against non-empty parent: child shorter, no
        // segment boundary possible.
        assert!(!is_subaccount_or_equal("", "Assets:Bank"));
    }

    #[test]
    fn is_subaccount_or_equal_case_sensitive() {
        // Beancount account names are case-sensitive; the helper
        // delegates to byte equality and starts_with, both of which
        // honor case.
        assert!(!is_subaccount_or_equal("Assets:bank", "Assets:Bank"));
        assert!(!is_subaccount_or_equal(
            "assets:Bank:Checking",
            "Assets:Bank"
        ));
    }
}
