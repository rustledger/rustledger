//! Serialization/deserialization support for WASM ledger caching.
//!
//! Provides binary serialization of parsed ledgers using `MessagePack`
//! (`rmp-serde`), enabling storage in browser `OPFS` or `IndexedDB` and fast
//! cache restores without re-parsing and re-booking.
//!
//! # Cache format
//!
//! Each cache blob starts with an 8-byte magic header followed by a
//! MessagePack-encoded payload struct.  The payload includes a version field
//! so that stale caches created by an older library version are detected and
//! rejected gracefully.
//!
//! # Cache invalidation
//!
//! Use [`hash_sources`] to compute a SHA-256 fingerprint of the source
//! files.  Store the fingerprint alongside the cache bytes and compare on
//! load; if the fingerprint changed, discard the cache and re-parse.
//!
//! # Example (JavaScript)
//!
//! ```javascript
//! import init, { Ledger, hashSources } from '@rustledger/wasm';
//! await init();
//!
//! const files = { "main.beancount": source };
//! const fingerprint = hashSources(Object.values(files));
//!
//! // Attempt to restore from cache
//! const stored = await loadFromIndexedDB(fingerprint);
//! let ledger;
//! if (stored) {
//!     ledger = Ledger.fromCache(stored);
//! } else {
//!     ledger = Ledger.fromFiles(files, "main.beancount");
//!     const bytes = ledger.serialize();
//!     await saveToIndexedDB(fingerprint, bytes);
//! }
//! ```

use rustledger_core::Directive;
use serde::{Deserialize, Serialize};

use crate::types::{Error, LedgerOptions};

/// Current cache format version.
///
/// Increment this constant whenever the serialized format changes so that
/// caches written by old library versions are rejected.
pub const CACHE_VERSION: u32 = 1;

/// Magic bytes prepended to every cache blob for identification.
pub const CACHE_MAGIC: &[u8; 8] = b"RLWASM\0\0";

// =============================================================================
// Payload types
// =============================================================================

/// Serializable payload for a [`super::parsed_ledger::Ledger`] cache entry.
#[derive(Debug, Serialize, Deserialize)]
pub struct LedgerCachePayload {
    /// Cache format version — used for invalidation.
    pub version: u32,
    /// Booked directives from all files.
    pub directives: Vec<Directive>,
    /// Ledger options.
    pub options: LedgerOptions,
    /// Processing errors (load, booking, validation).
    pub errors: Vec<Error>,
}

/// Serializable payload for a [`super::parsed_ledger::ParsedLedger`] cache entry.
#[derive(Debug, Serialize, Deserialize)]
pub struct ParsedLedgerCachePayload {
    /// Cache format version — used for invalidation.
    pub version: u32,
    /// Booked directives.
    pub directives: Vec<Directive>,
    /// Ledger options.
    pub options: LedgerOptions,
    /// Parse-phase errors.
    pub parse_errors: Vec<Error>,
    /// Validation-phase errors.
    pub validation_errors: Vec<Error>,
}

// =============================================================================
// Encode / decode helpers
// =============================================================================

/// Serialize `value` to `MessagePack` bytes, prepending [`CACHE_MAGIC`].
pub fn to_bytes<T: Serialize>(value: &T) -> Result<Vec<u8>, String> {
    let data =
        rmp_serde::to_vec_named(value).map_err(|e| format!("Serialization failed: {e}"))?;

    let mut result = Vec::with_capacity(CACHE_MAGIC.len() + data.len());
    result.extend_from_slice(CACHE_MAGIC);
    result.extend_from_slice(&data);
    Ok(result)
}

/// Deserialize `bytes` produced by [`to_bytes`], checking [`CACHE_MAGIC`].
pub fn from_bytes<T: for<'de> Deserialize<'de>>(bytes: &[u8]) -> Result<T, String> {
    if bytes.len() < CACHE_MAGIC.len() {
        return Err("Invalid cache: data too short".to_string());
    }

    let (magic, data) = bytes.split_at(CACHE_MAGIC.len());
    if magic != CACHE_MAGIC {
        return Err("Invalid cache: unrecognized magic bytes".to_string());
    }

    rmp_serde::from_slice(data).map_err(|e| format!("Deserialization failed: {e}"))
}

// =============================================================================
// Source fingerprinting
// =============================================================================

/// Compute a SHA-256 fingerprint of one or more source strings.
///
/// Returns the hash as a lowercase hex string.  Store this alongside cached
/// bytes and compare on the next load; if the fingerprint changed the source
/// was modified and the cache should be discarded.
///
/// Each source string is separated by a `NUL` byte before hashing so that
/// `["ab", "c"]` produces a different fingerprint from `["a", "bc"]`.
pub fn hash_sources(sources: &[&str]) -> String {
    use std::fmt::Write as _;

    use sha2::{Digest, Sha256};

    let mut hasher = Sha256::new();
    for source in sources {
        hasher.update(source.as_bytes());
        hasher.update(b"\x00");
    }
    let result = hasher.finalize();
    result
        .iter()
        .fold(String::with_capacity(64), |mut acc, b| {
            let _ = write!(acc, "{b:02x}");
            acc
        })
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{Error, LedgerOptions};
    use rustledger_core::Directive;

    fn make_payload() -> LedgerCachePayload {
        LedgerCachePayload {
            version: CACHE_VERSION,
            directives: Vec::<Directive>::new(),
            options: LedgerOptions {
                operating_currencies: vec!["USD".to_string()],
                title: Some("Test".to_string()),
            },
            errors: vec![Error::new("a warning")],
        }
    }

    #[test]
    fn test_roundtrip_empty_directives() {
        let payload = make_payload();
        let bytes = to_bytes(&payload).expect("serialize");
        assert!(bytes.starts_with(CACHE_MAGIC), "magic bytes present");

        let restored: LedgerCachePayload = from_bytes(&bytes).expect("deserialize");
        assert_eq!(restored.version, CACHE_VERSION);
        assert_eq!(restored.options.operating_currencies, ["USD"]);
        assert_eq!(restored.options.title.as_deref(), Some("Test"));
        assert_eq!(restored.errors.len(), 1);
    }

    #[test]
    fn test_bad_magic_returns_error() {
        let mut bytes = to_bytes(&make_payload()).expect("serialize");
        bytes[0] = b'X'; // corrupt the magic
        let result: Result<LedgerCachePayload, _> = from_bytes(&bytes);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("magic"));
    }

    #[test]
    fn test_too_short_returns_error() {
        let result: Result<LedgerCachePayload, _> = from_bytes(b"short");
        assert!(result.is_err());
    }

    #[test]
    fn test_hash_sources_deterministic() {
        let h1 = hash_sources(&["hello", "world"]);
        let h2 = hash_sources(&["hello", "world"]);
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_hash_sources_distinguishes_concat() {
        // "ab" + "c" must differ from "a" + "bc"
        let h1 = hash_sources(&["ab", "c"]);
        let h2 = hash_sources(&["a", "bc"]);
        assert_ne!(h1, h2);
    }

    #[test]
    fn test_hash_sources_changes_with_content() {
        let h1 = hash_sources(&["source v1"]);
        let h2 = hash_sources(&["source v2"]);
        assert_ne!(h1, h2);
    }

    #[test]
    fn test_parsed_ledger_payload_roundtrip_with_directives() {
        use crate::helpers::load_and_book;
        use crate::types::Error;

        let source = r#"
option "title" "Test Ledger"
option "operating_currency" "USD"

2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD

2024-01-15 * "Coffee Shop" "Morning coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD
"#;

        let processed = load_and_book(source);
        assert!(processed.errors.is_empty(), "no load errors expected");
        assert_eq!(processed.directives.len(), 3, "3 directives expected");

        let payload = ParsedLedgerCachePayload {
            version: CACHE_VERSION,
            directives: processed.directives.clone(),
            options: processed.options.clone(),
            parse_errors: Vec::<Error>::new(),
            validation_errors: Vec::<Error>::new(),
        };

        let bytes = to_bytes(&payload).expect("serialize");
        assert!(bytes.starts_with(CACHE_MAGIC), "magic header present");

        let restored: ParsedLedgerCachePayload = from_bytes(&bytes).expect("deserialize");
        assert_eq!(restored.version, CACHE_VERSION);
        assert_eq!(restored.directives.len(), 3, "directive count preserved");
        assert_eq!(
            restored.options.title.as_deref(),
            Some("Test Ledger"),
            "title preserved"
        );
        assert_eq!(
            restored.options.operating_currencies,
            ["USD"],
            "operating currencies preserved"
        );
    }

    #[test]
    fn test_version_mismatch_roundtrip() {
        let payload = LedgerCachePayload {
            version: 9999,
            directives: Vec::new(),
            options: LedgerOptions::default(),
            errors: Vec::new(),
        };
        let bytes = to_bytes(&payload).expect("serialize");
        // Bytes should parse fine at the msgpack level — version check is done by callers
        let restored: LedgerCachePayload = from_bytes(&bytes).expect("deserialize stale version");
        assert_eq!(restored.version, 9999);
    }
}
