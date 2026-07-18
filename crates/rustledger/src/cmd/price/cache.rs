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
    /// The on-disk file belongs to a NEWER schema this binary cannot
    /// read. All writes are suppressed — this run simply goes uncached —
    /// so an outdated binary never destroys a newer binary's cache, not
    /// even when it fetches (round-4 deep review: the round-3 fix only
    /// protected no-fetch runs).
    readonly: bool,
}

/// Current cache schema.
///
/// Bumped in #1801: version 1 was an unversioned bare map that could
/// hold live quotes mislabeled with historical dates (#1794); those
/// entries must never be served, so unversioned or older-versioned
/// files load as empty (newer-versioned files also load as empty but
/// are left on disk for the newer binary).
///
/// Public so integration tests that pre-write cache fixtures reference
/// the real constant instead of a literal that silently goes stale on
/// the next bump (round-3 deep review).
pub const CACHE_SCHEMA_VERSION: u32 = 2;

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

        let (entries, dirty, readonly) = if path.exists() {
            match std::fs::read_to_string(&path) {
                Ok(contents) => Self::classify_contents(&contents),
                // Transient I/O error (EACCES, network home dir): leave the
                // file alone — it may be perfectly healthy (round-3 review:
                // marking dirty here let a recoverable read error destroy
                // the whole cache on save()).
                Err(_) => (HashMap::new(), false, false),
            }
        } else {
            (HashMap::new(), false, false)
        };

        Self {
            path,
            ttl,
            entries,
            dirty,
            readonly,
        }
    }

    /// Classify on-disk cache contents into `(entries, dirty, readonly)`.
    ///
    /// Entries from other schema versions are DISCARDED, not migrated,
    /// but what happens to the FILE depends on why parsing failed:
    ///
    /// - current version: served as-is.
    /// - NEWER version (parseable or not — a future envelope may change
    ///   shape entirely, so an unparsable file claiming a newer
    ///   `version` counts too): this binary is the outdated one; load
    ///   empty and go READONLY so nothing this run does — not even a
    ///   fetch — clobbers the newer binary's cache (round-4 review).
    /// - OLDER version, or the pre-#1801 unversioned bare map: poisoned —
    ///   those files hold live quotes stored under historical dates (the
    ///   #1794 corruption) and the cache sits ABOVE the source guards,
    ///   so mark dirty: `save()` rewrites the file even on a no-fetch run
    ///   (round-2 review). A pre-#1801 binary sharing the file will
    ///   still clobber it on its next fetch; that downgrade direction is
    ///   accepted — readable-by-old-binaries would keep the poisoned
    ///   format alive.
    /// - anything else (truncated write, editor damage): plain
    ///   corruption — not dirty (a no-fetch run leaves it for manual
    ///   recovery) and not readonly (a run that fetches may overwrite;
    ///   the data was unreadable anyway) (round-4 review: the old
    ///   catch-all queued these for destruction).
    fn classify_contents(contents: &str) -> (HashMap<String, CachedPrice>, bool, bool) {
        if let Ok(file) = serde_json::from_str::<CacheFile>(contents) {
            return match file.version.cmp(&CACHE_SCHEMA_VERSION) {
                std::cmp::Ordering::Equal => (file.entries, false, false),
                std::cmp::Ordering::Greater => (HashMap::new(), false, true),
                std::cmp::Ordering::Less => (HashMap::new(), true, false),
            };
        }
        // The pre-#1801 legacy shape: a bare entries map at the top level.
        if serde_json::from_str::<HashMap<String, CachedPrice>>(contents).is_ok() {
            return (HashMap::new(), true, false);
        }
        // A future envelope whose shape we can't parse but whose version
        // field is readable and newer — preserve it read-only.
        if serde_json::from_str::<serde_json::Value>(contents)
            .ok()
            .and_then(|v| v.get("version").and_then(serde_json::Value::as_u64))
            .is_some_and(|v| v > u64::from(CACHE_SCHEMA_VERSION))
        {
            return (HashMap::new(), false, true);
        }
        (HashMap::new(), false, false)
    }

    /// Look up a cached price. Returns `None` if missing or expired.
    ///
    /// SETTLED historical prices never expire — a past close is
    /// immutable. Whether an entry is settled is decided by the entry's
    /// OWN fetch time, not the live clock: a quote keyed under date D
    /// but fetched ON day D is an intraday snapshot, and it stays an
    /// intraday snapshot after midnight — promoting it to a
    /// never-expiring "settled" price would freeze it as D's price of
    /// record and serve it before any source guard runs, resurrecting
    /// the #1794 corruption through the cache (round-4 deep review;
    /// round 3's live-clock rule had exactly that hole). Only an entry
    /// fetched AFTER its keyed day ended is a real close. Latest,
    /// intraday, and future-dated entries expire with the TTL.
    pub fn get(&self, key: &str) -> Option<PriceResponse> {
        let entry = self.entries.get(key)?;

        let is_settled = !key.ends_with(":latest")
            && key
                .rsplit(':')
                .next()
                .and_then(|s| s.parse::<NaiveDate>().ok())
                .is_some_and(|key_date| {
                    civil_day_of(entry.cached_at).is_some_and(|fetched_day| key_date < fetched_day)
                });
        if !is_settled {
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
    ///
    /// A no-op when the on-disk file belongs to a newer schema — see
    /// `classify_contents` (private): this run trades caching away
    /// rather than destroy a newer binary's data.
    pub fn save(&mut self) {
        if self.readonly || !self.dirty {
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
    // The currency segment is uppercased so `-c usd` and `-c USD` share
    // one cache identity, matching `dedup_key` in price_cmd.rs (see the
    // paired comment there; round-4 deep review of #1803). The TICKER
    // stays raw: provider tickers can be case-significant (external
    // command sources define their own ticker namespace).
    format!("{source}:{ticker}:{}:{date_part}", currency.to_uppercase())
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

/// The local civil day a unix timestamp falls on. Used to decide
/// whether a dated cache entry was fetched after its keyed day ended
/// (settled) or on the day itself (intraday) — see [`PriceCache::get`].
fn civil_day_of(unix_secs: u64) -> Option<NaiveDate> {
    let ts = jiff::Timestamp::from_second(i64::try_from(unix_secs).ok()?).ok()?;
    Some(ts.to_zoned(jiff::tz::TimeZone::system()).date())
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
            readonly: false,
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
            readonly: false,
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
            readonly: false,
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
            readonly: false,
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
                readonly: false,
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
            readonly: false,
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

    /// A NEWER-versioned file (downgraded binary) loads as empty but is
    /// NOT dirty: this binary must not serve entries it can't vouch for,
    /// and must not destroy the newer binary's cache on `save()` either
    /// (round-3 deep review — the round-2 discard-marks-dirty fix made
    /// every old-binary run wipe a newer cache).
    #[test]
    fn newer_version_cache_is_ignored_but_preserved() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("prices.json");
        let future = format!(
            r#"{{"version":{},"entries":{{"yahoo:AAPL:USD:2024-01-15":{{"price":"150.00","currency":"USD","date":"2024-01-15","source":"yahoo","cached_at":1700000000}}}}}}"#,
            CACHE_SCHEMA_VERSION + 1
        );
        std::fs::write(&path, &future).unwrap();

        let mut cache = PriceCache::load_from_path(path.clone(), 3600);
        assert!(cache.entries.is_empty(), "newer schema must not be served");
        assert!(!cache.dirty, "newer schema must not be marked for rewrite");

        cache.save();
        assert_eq!(
            std::fs::read_to_string(&path).unwrap(),
            future,
            "a no-insert run must leave the newer binary's cache untouched"
        );
    }

    /// A transient read error must NOT queue the file for destruction —
    /// it may be perfectly healthy (round-3 deep review: EACCES on a
    /// network home dir wiped the whole cache on `save()`).
    #[cfg(unix)]
    #[test]
    fn unreadable_cache_is_not_marked_dirty() {
        let dir = tempfile::tempdir().unwrap();
        // A directory at the cache path: exists() is true, read fails.
        let path = dir.path().join("prices.json");
        std::fs::create_dir(&path).unwrap();

        let cache = PriceCache::load_from_path(path, 3600);
        assert!(cache.entries.is_empty());
        assert!(
            !cache.dirty,
            "a read error must leave the on-disk cache alone"
        );
    }

    /// A key dated TODAY is an intraday quote, not a settled close — it
    /// must honor the TTL instead of never expiring (round-3 deep
    /// review: the first `--date <today>` fetch froze as that day's
    /// price of record).
    #[test]
    fn today_dated_key_honors_ttl() {
        let today = jiff::Zoned::now().date();
        let mut cache = PriceCache {
            path: PathBuf::from("/tmp/test-price-cache-today.json"),
            ttl: Duration::from_secs(0), // everything TTL-subject expires
            entries: HashMap::new(),
            dirty: false,
            readonly: false,
        };
        let response = PriceResponse {
            price: Decimal::new(15000, 2),
            currency: "USD".to_string(),
            date: today,
            source: "coinbase".to_string(),
        };
        let key = format!("coinbase:BTC:USD:{today}");
        cache.insert(&key, &response);
        assert!(
            cache.get(&key).is_none(),
            "a today-dated entry must expire with the TTL"
        );
    }

    /// The newer-schema guarantee must hold through a FETCH, not only a
    /// no-fetch run: an insert marks the cache dirty, and `save()` must
    /// still refuse to clobber the newer binary's file (round-4 deep
    /// review — round 3's fix only covered the no-insert path).
    #[test]
    fn newer_version_cache_survives_an_insert_and_save() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("prices.json");
        let future = format!(
            r#"{{"version":{},"entries":{{}}}}"#,
            CACHE_SCHEMA_VERSION + 1
        );
        std::fs::write(&path, &future).unwrap();

        let mut cache = PriceCache::load_from_path(path.clone(), 3600);
        cache.insert(
            "yahoo:AAPL:USD:latest",
            &PriceResponse {
                price: Decimal::new(15000, 2),
                currency: "USD".to_string(),
                date: rustledger_core::naive_date(2024, 1, 15).unwrap(),
                source: "yahoo".to_string(),
            },
        );
        cache.save();
        assert_eq!(
            std::fs::read_to_string(&path).unwrap(),
            future,
            "a fetch in an outdated binary must not destroy the newer cache"
        );
    }

    /// An unparsable-but-newer envelope (a future schema that changed
    /// the envelope shape entirely, so the `CacheFile` parse fails) is
    /// still recognized as newer via its raw `version` field and
    /// preserved read-only (round-4 deep review — the old catch-all
    /// queued it for destruction).
    #[test]
    fn unparsable_newer_envelope_is_preserved() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("prices.json");
        let future = format!(
            r#"{{"version":{},"generations":[{{"entries":{{}}}}]}}"#,
            CACHE_SCHEMA_VERSION + 1
        );
        std::fs::write(&path, &future).unwrap();

        let mut cache = PriceCache::load_from_path(path.clone(), 3600);
        assert!(cache.entries.is_empty());
        assert!(!cache.dirty);
        cache.insert(
            "yahoo:AAPL:USD:latest",
            &PriceResponse {
                price: Decimal::new(15000, 2),
                currency: "USD".to_string(),
                date: rustledger_core::naive_date(2024, 1, 15).unwrap(),
                source: "yahoo".to_string(),
            },
        );
        cache.save();
        assert_eq!(std::fs::read_to_string(&path).unwrap(), future);
    }

    /// Plain corruption (truncated write, editor damage) is neither
    /// poisoned nor foreign: a no-fetch run must leave the file for
    /// manual recovery instead of queuing it for destruction (round-4
    /// deep review).
    #[test]
    fn corrupt_cache_is_not_marked_dirty() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("prices.json");
        let truncated = r#"{"version":2,"entries":{"yahoo:AAPL:USD:2024-01-15":{"pri"#;
        std::fs::write(&path, truncated).unwrap();

        let cache = PriceCache::load_from_path(path, 3600);
        assert!(cache.entries.is_empty());
        assert!(!cache.dirty, "corruption must not queue a rewrite");
        assert!(!cache.readonly, "a later fetch MAY overwrite corrupt junk");
    }

    /// An entry keyed under date D but FETCHED on day D is an intraday
    /// snapshot forever — crossing midnight must not promote it to a
    /// settled, never-expiring price (round-4 deep review: that
    /// promotion re-served stale intraday quotes as the historical
    /// price of record, before any source guard could run).
    #[test]
    fn entry_fetched_on_its_own_day_stays_ttl_bound() {
        // Simulate "yesterday's --date-today fetch": cached_at is 24h
        // ago, and the key date is the civil day that instant fell on.
        let cached_at = now_secs() - 24 * 3600;
        let key_date = civil_day_of(cached_at).unwrap();
        let key = format!("coinbase:BTC:USD:{key_date}");
        let mut entries = HashMap::new();
        entries.insert(
            key.clone(),
            CachedPrice {
                price: "67000.00".to_string(),
                currency: "USD".to_string(),
                date: key_date.to_string(),
                source: "coinbase".to_string(),
                cached_at,
            },
        );
        let cache = PriceCache {
            path: PathBuf::from("/tmp/test-price-cache-intraday.json"),
            ttl: Duration::from_mins(30),
            entries,
            dirty: false,
            readonly: false,
        };
        assert!(
            cache.get(&key).is_none(),
            "an intraday-fetched entry must expire with the TTL even after \
             its keyed day has passed"
        );
    }

    /// The settled exemption still applies when the entry was fetched
    /// AFTER its keyed day — a real close is immutable and never
    /// expires (pinned so the round-4 fix doesn't overshoot).
    #[test]
    fn entry_fetched_after_its_day_never_expires() {
        let cached_at = now_secs() - 24 * 3600;
        let fetch_day = civil_day_of(cached_at).unwrap();
        let key_date = fetch_day.checked_sub(jiff::Span::new().days(3)).unwrap();
        let key = format!("yahoo:AAPL:USD:{key_date}");
        let mut entries = HashMap::new();
        entries.insert(
            key.clone(),
            CachedPrice {
                price: "150.00".to_string(),
                currency: "USD".to_string(),
                date: key_date.to_string(),
                source: "yahoo".to_string(),
                cached_at,
            },
        );
        let cache = PriceCache {
            path: PathBuf::from("/tmp/test-price-cache-settled.json"),
            ttl: Duration::from_secs(0), // TTL 0 would expire anything TTL-bound
            entries,
            dirty: false,
            readonly: false,
        };
        assert!(
            cache.get(&key).is_some(),
            "a close fetched after its day ended is settled and immortal"
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
