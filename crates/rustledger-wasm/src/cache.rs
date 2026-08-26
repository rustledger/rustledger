//! Binary serialization for WASM ledger caching.
//!
//! Provides rkyv-based serialization of parsed ledgers, enabling storage in
//! browser OPFS or `IndexedDB` and fast cache restores.
//!
//! Restoring a [`super::parsed_ledger::Ledger`] from cache avoids all
//! re-parsing, booking, and validation. Restoring a
//! [`super::parsed_ledger::ParsedLedger`] re-parses source text to rebuild
//! editor spans, but skips the expensive booking and validation phases by
//! reusing cached directives, options, and errors.
//!
//! # Cache format
//!
//! Each cache blob starts with a 12-byte header (8-byte magic + 4-byte version)
//! followed by an rkyv-serialized payload.
//!
//! # Cache invalidation
//!
//! Use [`hash_sources`] to compute a SHA-256 fingerprint of the source files.
//! Store the fingerprint alongside the cache bytes and compare on load; if the
//! fingerprint changed, discard the cache and re-parse.

use rustledger_core::Directive;

use crate::types::{Error, LedgerOptions};

/// Current cache format version. Increment when the serialized format changes.
///
/// v2 (#1597): `Error` gained `code`/`phase`/`hint`/`file`/`end_line`/
/// `end_column`, changing its rkyv archived layout — a v1 blob must be rejected
/// and re-parsed rather than misread under the new layout.
/// v4 (#1939): arithmetic in a COST SPEC is evaluated rather than truncated to
/// its first operand, and a leading `-` is now part of the number. The archived
/// LAYOUT is unchanged, so a v3 blob would be accepted and its `Vec<Directive>`
/// deserialized happily — serving a truncated or sign-flipped cost basis on a
/// build that has the fix. This cache archives the same parsed directives as
/// the loader cache, so it needs the same bump for the same reason.
/// v5 (#1944): arithmetic is evaluated in METADATA values and BALANCE
/// TOLERANCES too. Same reasoning as v4 and the loader's v19 — the archived
/// layout does not move, so a v4 blob would be accepted and its directives
/// deserialized with the truncated tolerance still in them. Any parser change
/// that alters a VALUE has to bump both caches, not just the loader's; missing
/// this one on the previous PR is what prompted the rule.
/// v6 (#1930): account names accept any non-ASCII character inside a
/// component, so a ledger that previously failed to parse now yields
/// directives. Layout again unchanged, so a v5 blob would be accepted and the
/// cached PARSE FAILURE served on a build that can read the file.
/// v7 (#1949): trailing tags/links on most directives are now parse
/// errors, so a previously-clean file can carry errors. Same reasoning as the
/// loader's v21; both caches move when a parser change alters output.
/// v8 (#1955): metadata keys need two or more characters, so a
/// previously-clean file can carry errors. Same reasoning as the loader's
/// v22; both caches move when a parser change alters output.
/// v9 (#1954): link-valued metadata is now a parse error, so a
/// previously-clean file can carry errors. Same reasoning as the loader's v23.
/// v10 (#1958): tags/links in custom and pushmeta values are now parse
/// errors. Same reasoning as the loader's v24.
/// v11 (#2008): transaction headers beancount rejects are now parse errors.
/// Same reasoning as the loader's v25.
/// v12 (#2008): malformed cost-spec component lists likewise. Loader v26.
/// v13 (#2008): numberless cost specs archive `None`, not an invented zero.
/// Loader v27 — and unlike v11/v12 this one changes archived VALUES, so a
/// stale blob would serve the invented number rather than merely miss an error.
/// v14: a literal `-0.00` parses to an UNSIGNED zero. Loader v28 — archived
/// VALUES again, so a stale blob would serve `-0.00` where the build no longer
/// produces one.
/// v15: `Posting::cost` and `Posting::price` are boxed. Loader v29 — the first
/// entry here that changes neither the parser's output nor anything
/// loader-internal: the archived VALUES are identical, but `ArchivedPosting`
/// changed SHAPE, and a v14 blob read by this build would interpret an inline
/// `CostSpec` as a relative pointer.
pub const CACHE_VERSION: u32 = 15;

/// The `rustledger-loader` cache version this one was last reconciled with.
///
/// Both caches archive the same parsed `Vec<Directive>`. A parser change that
/// alters PARSER OUTPUT therefore invalidates both, and bumping only one leaves
/// the other serving stale directives on a build that has the fix.
///
/// That is not hypothetical: on #1942 (cost-spec arithmetic) only the loader
/// version moved, and a stale WASM blob would have kept serving a truncated
/// cost basis. It was caught in review, by a person, not by anything here.
///
/// So this pins the pair. If the assertion below fails, ask which kind of
/// change moved the loader version:
///
///   parser OUTPUT changed  -> bump `CACHE_VERSION` above too, then update
///                             this pin to match
///   archived LAYOUT changed -> bump `CACHE_VERSION` above too. Same answer as
///                             an output change and for a sharper reason: the
///                             values agree, so nothing downstream would look
///                             wrong, while the bytes are read at the wrong
///                             offsets (v15 / loader v29, boxing
///                             `Posting::cost`)
///   loader-internal only   -> only update this pin (layout of a loader-side
///                             struct moved; our archived directives did not)
///
/// The question is the point; the pin exists to force it to be asked.
/// Test-only: the pin exists to be asserted, and gating it keeps a non-test
/// build free of a constant nothing reads. The doc above stays here rather
/// than in the test module so a reader of this file meets the contract next
/// to `CACHE_VERSION`, which is the thing they came to change.
#[cfg(test)]
const LOADER_CACHE_VERSION_PIN: u32 = 30;

/// Magic bytes for [`ParsedLedgerPayload`] cache blobs.
pub const MAGIC_PARSED: &[u8; 8] = b"WLPARSED";

/// Magic bytes for [`LedgerPayload`] cache blobs.
pub const MAGIC_LEDGER: &[u8; 8] = b"WLLEDGER";

/// Header size: 8 (magic) + 4 (version).
const HEADER_SIZE: usize = 12;

// =============================================================================
// Payload types
// =============================================================================

/// Cache payload for a [`super::parsed_ledger::ParsedLedger`].
#[derive(Debug, rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)]
pub struct ParsedLedgerPayload {
    pub directives: Vec<Directive>,
    pub options: LedgerOptions,
    pub parse_errors: Vec<Error>,
    pub validation_errors: Vec<Error>,
}

/// Cache payload for a [`super::parsed_ledger::Ledger`].
#[derive(Debug, rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)]
pub struct LedgerPayload {
    pub directives: Vec<Directive>,
    pub options: LedgerOptions,
    /// Configured account-type roots as `[assets, liabilities, equity,
    /// income, expenses]` — `name_*` renames must survive the cache or
    /// `fromCache` ledgers silently misclassify in BQL (the L5 class).
    /// Plain strings rather than `rustledger_core::AccountTypes` so the
    /// rkyv derive stays local to this crate.
    pub account_type_names: Vec<String>,
    pub errors: Vec<Error>,
}

// =============================================================================
// Encode / decode
// =============================================================================

/// Validate and strip the cache header, checking the expected magic bytes.
fn strip_header(bytes: &[u8], expected_magic: [u8; 8]) -> Result<&[u8], String> {
    if bytes.len() < HEADER_SIZE {
        return Err("Invalid cache: data too short".to_string());
    }
    let (header, data) = bytes.split_at(HEADER_SIZE);
    if header[..8] != expected_magic {
        return Err("Invalid cache: wrong payload type or unrecognized magic bytes".to_string());
    }
    // `header` is exactly `HEADER_SIZE` (12) bytes — the length was checked
    // above — so bytes 8..12 are always present (no panic, no unwrap).
    let version = u32::from_le_bytes([header[8], header[9], header[10], header[11]]);
    if version != CACHE_VERSION {
        return Err(format!(
            "Cache version mismatch: expected {CACHE_VERSION}, got {version}. Re-parse the ledger."
        ));
    }
    Ok(data)
}

/// Prepend the cache header to rkyv-serialized data.
fn prepend_header(magic: [u8; 8], data: &[u8]) -> Vec<u8> {
    let mut result = Vec::with_capacity(HEADER_SIZE + data.len());
    result.extend_from_slice(&magic);
    result.extend_from_slice(&CACHE_VERSION.to_le_bytes());
    result.extend_from_slice(data);
    result
}

/// Serialize a [`ParsedLedgerPayload`] to bytes.
pub fn serialize_parsed(payload: &ParsedLedgerPayload) -> Result<Vec<u8>, String> {
    let data = rkyv::to_bytes::<rkyv::rancor::Error>(payload)
        .map_err(|e| format!("Serialization failed: {e}"))?;
    Ok(prepend_header(*MAGIC_PARSED, &data))
}

/// Deserialize a [`ParsedLedgerPayload`] from bytes.
pub fn deserialize_parsed(bytes: &[u8]) -> Result<ParsedLedgerPayload, String> {
    let data = strip_header(bytes, *MAGIC_PARSED)?;
    rkyv::from_bytes::<ParsedLedgerPayload, rkyv::rancor::Error>(data)
        .map_err(|e| format!("Deserialization failed: {e}"))
}

/// Serialize a [`LedgerPayload`] to bytes.
pub fn serialize_ledger(payload: &LedgerPayload) -> Result<Vec<u8>, String> {
    let data = rkyv::to_bytes::<rkyv::rancor::Error>(payload)
        .map_err(|e| format!("Serialization failed: {e}"))?;
    Ok(prepend_header(*MAGIC_LEDGER, &data))
}

/// Deserialize a [`LedgerPayload`] from bytes.
pub fn deserialize_ledger(bytes: &[u8]) -> Result<LedgerPayload, String> {
    let data = strip_header(bytes, *MAGIC_LEDGER)?;
    rkyv::from_bytes::<LedgerPayload, rkyv::rancor::Error>(data)
        .map_err(|e| format!("Deserialization failed: {e}"))
}

// =============================================================================
// Source fingerprinting
// =============================================================================

/// Compute a SHA-256 fingerprint of one or more source strings.
///
/// Returns the hash as a lowercase hex string. Store this alongside cached
/// bytes and compare on the next load; if the fingerprint changed, discard
/// the cache.
///
/// Sources are separated by NUL bytes so `["ab", "c"]` differs from `["a", "bc"]`.
pub fn hash_sources(sources: &[&str]) -> String {
    use sha2::{Digest, Sha256};
    use std::fmt::Write as _;

    let mut hasher = Sha256::new();
    for source in sources {
        hasher.update(source.as_bytes());
        hasher.update(b"\x00");
    }
    let result = hasher.finalize();
    result.iter().fold(String::with_capacity(64), |mut acc, b| {
        let _ = write!(acc, "{b:02x}");
        acc
    })
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {

    /// The two caches archive the same parsed directives, so they have to move
    /// together whenever PARSER OUTPUT changes.
    ///
    /// This is the guard for the failure that actually happened on #1942: the
    /// loader version was bumped, this one was not, and a stale WASM blob would
    /// have served a truncated cost basis on a fixed build. Review caught it;
    /// nothing in the test suite did.
    #[test]
    fn loader_cache_version_is_pinned() {
        assert_eq!(
            rustledger_loader::cache::CACHE_VERSION,
            LOADER_CACHE_VERSION_PIN,
            "the rustledger-loader cache version moved and this one did not. \
             If PARSER OUTPUT changed, bump CACHE_VERSION in this file too and \
             then update LOADER_CACHE_VERSION_PIN to match. If the loader \
             change was internal to the loader (its own struct layout) and our \
             archived directives are unaffected, update the pin alone. See \
             #1942, where only the loader moved and a stale blob would have \
             kept serving a truncated cost basis.",
        );
    }

    use super::*;

    #[test]
    fn test_roundtrip_ledger_payload() {
        let payload = LedgerPayload {
            directives: Vec::new(),
            options: LedgerOptions {
                operating_currencies: vec!["USD".to_string()],
                title: Some("Test".to_string()),
            },
            account_type_names: vec![
                "Assets".to_string(),
                "Liabilities".to_string(),
                "Equity".to_string(),
                "Revenue".to_string(),
                "Expenses".to_string(),
            ],
            errors: vec![Error::new("a warning")],
        };
        let bytes = serialize_ledger(&payload).expect("serialize");
        assert!(bytes.starts_with(MAGIC_LEDGER));

        let restored = deserialize_ledger(&bytes).expect("deserialize");
        assert_eq!(restored.options.operating_currencies, ["USD"]);
        assert_eq!(restored.options.title.as_deref(), Some("Test"));
        assert_eq!(restored.errors.len(), 1);
    }

    #[test]
    fn test_roundtrip_with_directives() {
        use crate::helpers::load_and_book;

        let source = r#"
option "title" "Test"
option "operating_currency" "USD"

2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD

2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD
"#;
        let processed = load_and_book(source);
        assert!(!processed.directives.is_empty());

        let payload = ParsedLedgerPayload {
            directives: processed.directives.clone(),
            options: processed.options.clone(),
            parse_errors: Vec::new(),
            validation_errors: Vec::new(),
        };

        let bytes = serialize_parsed(&payload).expect("serialize");
        let restored = deserialize_parsed(&bytes).expect("deserialize");
        assert_eq!(restored.directives.len(), processed.directives.len());
        assert_eq!(restored.options.title.as_deref(), Some("Test"));
    }

    #[test]
    fn test_bad_magic_returns_error() {
        let mut bytes = serialize_ledger(&LedgerPayload {
            directives: Vec::new(),
            options: LedgerOptions::default(),
            account_type_names: Vec::new(),
            errors: Vec::new(),
        })
        .unwrap();
        bytes[0] = b'X';
        assert!(deserialize_ledger(&bytes).unwrap_err().contains("magic"));
    }

    #[test]
    fn test_too_short_returns_error() {
        assert!(
            deserialize_ledger(b"short")
                .unwrap_err()
                .contains("too short")
        );
    }

    #[test]
    fn test_version_mismatch_returns_error() {
        let mut bytes = serialize_ledger(&LedgerPayload {
            directives: Vec::new(),
            options: LedgerOptions::default(),
            account_type_names: Vec::new(),
            errors: Vec::new(),
        })
        .unwrap();
        bytes[8..12].copy_from_slice(&99u32.to_le_bytes());
        assert!(
            deserialize_ledger(&bytes)
                .unwrap_err()
                .contains("version mismatch")
        );
    }

    #[test]
    fn test_hash_sources_deterministic() {
        let h1 = hash_sources(&["hello", "world"]);
        let h2 = hash_sources(&["hello", "world"]);
        assert_eq!(h1, h2);
        assert_eq!(h1.len(), 64);
    }

    #[test]
    fn test_hash_sources_distinguishes_concat() {
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
    fn test_cross_type_rejection() {
        // Serialized Ledger bytes should not deserialize as ParsedLedger
        let bytes = serialize_ledger(&LedgerPayload {
            directives: Vec::new(),
            options: LedgerOptions::default(),
            account_type_names: Vec::new(),
            errors: Vec::new(),
        })
        .unwrap();
        assert!(
            deserialize_parsed(&bytes).is_err(),
            "Ledger bytes should not deserialize as ParsedLedger"
        );

        // Serialized ParsedLedger bytes should not deserialize as Ledger
        let bytes = serialize_parsed(&ParsedLedgerPayload {
            directives: Vec::new(),
            options: LedgerOptions::default(),
            parse_errors: Vec::new(),
            validation_errors: Vec::new(),
        })
        .unwrap();
        assert!(
            deserialize_ledger(&bytes).is_err(),
            "ParsedLedger bytes should not deserialize as Ledger"
        );
    }
}
