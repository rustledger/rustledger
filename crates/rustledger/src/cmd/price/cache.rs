//! Disk-based price cache to reduce API calls.
//!
//! Stores fetched prices in a JSON file at `~/.cache/rledger/prices.json`.
//! Entries expire after the configured TTL (default: 30 minutes).

use std::collections::HashMap;
use std::path::PathBuf;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use rust_decimal::Decimal;
use rustledger_core::NaiveDate;
use serde::{Deserialize, Serialize};

use super::PriceResponse;

/// Maximum age before stale entries are pruned on save (7 days).
const PRUNE_AGE_SECS: u64 = 7 * 24 * 3600;

/// A disk-backed price cache.
pub struct PriceCache {
    path: PathBuf,
    ttl: Duration,
    entries: HashMap<String, CachedPrice>,
    dirty: bool,
}

/// Current cache schema. Bumped in #1801: version 1 was an unversioned
/// bare map that could hold live quotes mislabeled with historical dates
/// (#1794); those entries must never be served, so unversioned or
/// mismatched files load as empty.
const CACHE_SCHEMA_VERSION: u32 = 2;

/// The on-disk cache envelope.
#[derive(Debug, Serialize, Deserialize)]
struct CacheFile {
    version: u32,
    entries: HashMap<String, CachedPrice>,
}

/// Borrowing mirror of [`CacheFile`] for serialization — avoids deep-
/// cloning every entry on save. Field names must match `CacheFile`.
#[derive(Serialize)]
struct CacheFileRef<'a> {
    version: u32,
    entries: &'a HashMap<String, CachedPrice>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct CachedPrice {
    price: String,
    currency: String,
    date: String,
    source: String,
    cached_at: u64,
}

impl PriceCache {
    /// Load cache from disk, or create empty if not found.
    pub fn load(ttl_secs: u64) -> Self {
        Self::load_from_path(cache_file_path(), ttl_secs)
    }

    /// Load a cache from an explicit path (injectable for tests — the
    /// discard-on-mismatch behavior below must be assertable through the
    /// real load path, not a re-implemented parse).
    fn load_from_path(path: PathBuf, ttl_secs: u64) -> Self {
        let ttl = Duration::from_secs(ttl_secs);

        let (entries, discarded) = if path.exists() {
            match std::fs::read_to_string(&path) {
                // Versioned envelope: entries from other schema versions are
                // DISCARDED, not migrated. Pre-#1801 caches hold live quotes
                // stored under historical dates (the #1794 corruption); the
                // old bare-map format fails to parse as CacheFile, so those
                // poisoned entries can never be served again (deep review —
                // the cache sits ABOVE the sources, bypassing their fixes).
                // NOTE: a pre-#1801 binary sharing this file cannot read the
                // v2 envelope and will clobber it on its next fetch; that
                // downgrade path is accepted — readable-by-old-binaries
                // would mean keeping the poisoned format alive.
                Ok(contents) => match serde_json::from_str::<CacheFile>(&contents) {
                    Ok(file) if file.version == CACHE_SCHEMA_VERSION => (file.entries, false),
                    // Discarding marks the cache dirty so save() rewrites
                    // the file even when the run fetches nothing — otherwise
                    // the poisoned pre-#1801 file survives on disk for any
                    // older binary to serve again (round-2 deep review).
                    _ => (HashMap::new(), true),
                },
                Err(_) => (HashMap::new(), true),
            }
        } else {
            (HashMap::new(), false)
        };

        Self {
            path,
            ttl,
            entries,
            dirty: discarded,
        }
    }

    /// Look up a cached price. Returns `None` if missing or expired.
    ///
    /// Historical prices (with a specific date in the key) never expire.
    /// Latest prices expire after the configured TTL.
    /// This matches Python bean-price behavior.
    pub fn get(&self, key: &str) -> Option<PriceResponse> {
        let entry = self.entries.get(key)?;

        // Historical prices never expire; latest prices use TTL
        let is_latest = key.ends_with(":latest");
        if is_latest {
            let now = now_secs();
            if self.ttl.is_zero() || now.saturating_sub(entry.cached_at) > self.ttl.as_secs() {
                return None; // Expired or caching disabled
            }
        }

        let price: Decimal = entry.price.parse().ok()?;
        let date = entry.date.parse::<NaiveDate>().ok()?;

        Some(PriceResponse {
            price,
            currency: entry.currency.clone(),
            date,
            source: entry.source.clone(),
        })
    }

    /// Insert a price into the cache.
    pub fn insert(&mut self, key: &str, response: &PriceResponse) {
        self.entries.insert(
            key.to_string(),
            CachedPrice {
                price: response.price.to_string(),
                currency: response.currency.clone(),
                date: response.date.to_string(),
                source: response.source.clone(),
                cached_at: now_secs(),
            },
        );
        self.dirty = true;
    }

    /// Save cache to disk (only if modified). Prunes stale entries.
    pub fn save(&mut self) {
        if !self.dirty {
            return;
        }

        // Prune entries older than PRUNE_AGE_SECS
        let now = now_secs();
        self.entries
            .retain(|_, v| now.saturating_sub(v.cached_at) < PRUNE_AGE_SECS);

        // Ensure parent directory exists
        if let Some(parent) = self.path.parent() {
            let _ = std::fs::create_dir_all(parent);
        }

        let file = CacheFileRef {
            version: CACHE_SCHEMA_VERSION,
            entries: &self.entries,
        };
        if let Ok(json) = serde_json::to_string_pretty(&file)
            && std::fs::write(&self.path, json).is_ok()
        {
            self.dirty = false;
        }
    }

    /// Clear all cached entries and delete the cache file.
    pub fn clear(&mut self) {
        self.entries.clear();
        self.dirty = false;
        let _ = std::fs::remove_file(&self.path);
    }
}

/// Build a cache key from the request parameters.
///
/// Includes source name since different sources can return different prices
/// for the same symbol (matching Python bean-price behavior).
pub fn cache_key(source: &str, ticker: &str, currency: &str, date: Option<NaiveDate>) -> String {
    let date_part = match date {
        Some(d) => d.to_string(),
        None => "latest".to_string(),
    };
    format!("{source}:{ticker}:{currency}:{date_part}")
}

fn cache_file_path() -> PathBuf {
    dirs::cache_dir()
        .unwrap_or_else(|| PathBuf::from(".cache"))
        .join("rledger")
        .join("prices.json")
}

fn now_secs() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cache_key_with_date() {
        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();
        assert_eq!(
            cache_key("yahoo", "AAPL", "USD", Some(date)),
            "yahoo:AAPL:USD:2024-01-15"
        );
    }

    #[test]
    fn test_cache_key_without_date() {
        assert_eq!(
            cache_key("yahoo", "AAPL", "USD", None),
            "yahoo:AAPL:USD:latest"
        );
    }

    #[test]
    fn test_historical_price_never_expires() {
        let mut cache = PriceCache {
            path: PathBuf::from("/tmp/test-price-cache-hist.json"),
            ttl: Duration::from_secs(0), // TTL=0 would expire latest prices
            entries: HashMap::new(),
            dirty: false,
        };

        let response = PriceResponse {
            price: Decimal::new(15000, 2),
            currency: "USD".to_string(),
            date: rustledger_core::naive_date(2024, 1, 15).unwrap(),
            source: "yahoo".to_string(),
        };

        // Insert with a dated key (not "latest")
        cache.insert("yahoo:AAPL:USD:2024-01-15", &response);
        // Historical prices should never expire even with TTL=0
        assert!(cache.get("yahoo:AAPL:USD:2024-01-15").is_some());
    }

    #[test]
    fn test_insert_and_get() {
        let mut cache = PriceCache {
            path: PathBuf::from("/tmp/test-price-cache.json"),
            ttl: Duration::from_hours(1),
            entries: HashMap::new(),
            dirty: false,
        };

        let response = PriceResponse {
            price: Decimal::new(15000, 2), // 150.00
            currency: "USD".to_string(),
            date: rustledger_core::naive_date(2024, 1, 15).unwrap(),
            source: "yahoo".to_string(),
        };

        cache.insert("yahoo:AAPL:USD:latest", &response);
        assert!(cache.dirty);

        let cached = cache.get("yahoo:AAPL:USD:latest");
        assert!(cached.is_some());
        let cached = cached.unwrap();
        assert_eq!(cached.price, response.price);
        assert_eq!(cached.currency, "USD");
        assert_eq!(cached.source, "yahoo");
    }

    #[test]
    fn test_get_expired_returns_none() {
        let mut cache = PriceCache {
            path: PathBuf::from("/tmp/test-price-cache.json"),
            ttl: Duration::from_secs(0), // Expire immediately
            entries: HashMap::new(),
            dirty: false,
        };

        let response = PriceResponse {
            price: Decimal::new(15000, 2),
            currency: "USD".to_string(),
            date: rustledger_core::naive_date(2024, 1, 15).unwrap(),
            source: "yahoo".to_string(),
        };

        cache.insert("yahoo:AAPL:USD:latest", &response);
        // TTL is 0, so latest prices are always expired
        assert!(cache.get("yahoo:AAPL:USD:latest").is_none());
    }

    #[test]
    fn test_get_missing_returns_none() {
        let cache = PriceCache {
            path: PathBuf::from("/tmp/test-price-cache.json"),
            ttl: Duration::from_hours(1),
            entries: HashMap::new(),
            dirty: false,
        };

        assert!(cache.get("nonexistent").is_none());
    }

    #[test]
    fn test_save_and_load_round_trip() {
        let path = std::env::temp_dir().join("rustledger-test-cache-roundtrip.json");
        let _ = std::fs::remove_file(&path); // Clean up from previous runs

        let response = PriceResponse {
            price: Decimal::new(15000, 2),
            currency: "USD".to_string(),
            date: rustledger_core::naive_date(2024, 1, 15).unwrap(),
            source: "yahoo".to_string(),
        };

        // Save
        {
            let mut cache = PriceCache {
                path: path.clone(),
                ttl: Duration::from_hours(1),
                entries: HashMap::new(),
                dirty: false,
            };
            cache.insert("yahoo:AAPL:USD:latest", &response);
            cache.save();
            assert!(!cache.dirty, "dirty should be cleared after save");
        }

        // Load through the REAL load path and verify the entry survives
        // the versioned envelope round trip.
        {
            let file: CacheFile =
                serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
            assert_eq!(file.version, CACHE_SCHEMA_VERSION);
            let cache = PriceCache::load_from_path(path.clone(), 3600);
            let cached = cache.get("yahoo:AAPL:USD:latest");
            assert!(cached.is_some(), "should find cached entry after load");
            assert_eq!(cached.unwrap().price, response.price);
        }

        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_clear() {
        let mut cache = PriceCache {
            path: PathBuf::from("/tmp/test-price-cache-clear.json"),
            ttl: Duration::from_hours(1),
            entries: HashMap::new(),
            dirty: false,
        };

        let response = PriceResponse {
            price: Decimal::new(15000, 2),
            currency: "USD".to_string(),
            date: rustledger_core::naive_date(2024, 1, 15).unwrap(),
            source: "yahoo".to_string(),
        };

        cache.insert("key", &response);
        cache.clear();
        assert!(cache.entries.is_empty());
        assert!(cache.get("key").is_none());
    }

    /// A pre-#1801 cache (unversioned bare map — the format that could
    /// hold live quotes mislabeled with historical dates, #1794) must
    /// load as EMPTY through the REAL load path, never serving its
    /// poisoned entries — and the discard must mark the cache dirty so
    /// the very next `save()` destroys the poisoned file even when the
    /// run fetched nothing (round-2 deep review: the earlier version of
    /// this test asserted a re-implemented parse, which a future
    /// legacy-migration fallback inside `load()` could not trip).
    #[test]
    fn unversioned_legacy_cache_is_discarded_and_rewritten() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("prices.json");
        // The 0.21.0 on-disk shape: entries map at the top level.
        std::fs::write(
            &path,
            r#"{"yahoo:AAPL:USD:2000-01-03":{"price":"317.31","currency":"USD","date":"2000-01-03","source":"yahoo","cached_at":1700000000}}"#,
        )
        .unwrap();

        let mut cache = PriceCache::load_from_path(path.clone(), 3600);
        assert!(
            cache.get("yahoo:AAPL:USD:2000-01-03").is_none(),
            "poisoned legacy entry must never be served"
        );
        assert!(cache.entries.is_empty(), "legacy file must load as empty");
        assert!(cache.dirty, "discard must mark dirty so save() rewrites");

        cache.save();
        let rewritten: CacheFile =
            serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
        assert_eq!(rewritten.version, CACHE_SCHEMA_VERSION);
        assert!(
            rewritten.entries.is_empty(),
            "save() after a discard must replace the poisoned file with an empty v2 envelope"
        );
    }

    /// A well-formed current-version file loads its entries and is NOT
    /// dirty — the discard path above must not fire on healthy files.
    #[test]
    fn current_version_cache_loads_clean() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("prices.json");
        {
            let mut cache = PriceCache::load_from_path(path.clone(), 3600);
            assert!(!cache.dirty, "missing file is not a discard");
            cache.insert(
                "yahoo:AAPL:USD:2024-01-15",
                &PriceResponse {
                    price: Decimal::new(15000, 2),
                    currency: "USD".to_string(),
                    date: rustledger_core::naive_date(2024, 1, 15).unwrap(),
                    source: "yahoo".to_string(),
                },
            );
            cache.save();
        }
        let cache = PriceCache::load_from_path(path, 3600);
        assert!(!cache.dirty, "healthy v2 file must not be marked dirty");
        assert!(
            cache.get("yahoo:AAPL:USD:2024-01-15").is_some(),
            "entries from a healthy v2 file must be served"
        );
    }
}
