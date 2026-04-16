//! Disk-based price cache to reduce API calls.
//!
//! Stores fetched prices in a JSON file at `~/.cache/rledger/prices.json`.
//! Entries expire after the configured TTL (default: 30 minutes).

use std::collections::HashMap;
use std::path::PathBuf;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use chrono::NaiveDate;
use rust_decimal::Decimal;
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
        let path = cache_file_path();
        let ttl = Duration::from_secs(ttl_secs);

        let entries = if path.exists() {
            match std::fs::read_to_string(&path) {
                Ok(contents) => serde_json::from_str(&contents).unwrap_or_default(),
                Err(_) => HashMap::new(),
            }
        } else {
            HashMap::new()
        };

        Self {
            path,
            ttl,
            entries,
            dirty: false,
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
        let date = NaiveDate::parse_from_str(&entry.date, "%Y-%m-%d").ok()?;

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
                date: response.date.format("%Y-%m-%d").to_string(),
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

        if let Ok(json) = serde_json::to_string_pretty(&self.entries)
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
        Some(d) => d.format("%Y-%m-%d").to_string(),
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
        let date = NaiveDate::from_ymd_opt(2024, 1, 15).unwrap();
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
            date: NaiveDate::from_ymd_opt(2024, 1, 15).unwrap(),
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
            date: NaiveDate::from_ymd_opt(2024, 1, 15).unwrap(),
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
            date: NaiveDate::from_ymd_opt(2024, 1, 15).unwrap(),
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
            date: NaiveDate::from_ymd_opt(2024, 1, 15).unwrap(),
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

        // Load and verify
        {
            let cache = PriceCache {
                path: path.clone(),
                ttl: Duration::from_hours(1),
                entries: serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap(),
                dirty: false,
            };
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
            date: NaiveDate::from_ymd_opt(2024, 1, 15).unwrap(),
            source: "yahoo".to_string(),
        };

        cache.insert("key", &response);
        cache.clear();
        assert!(cache.entries.is_empty());
        assert!(cache.get("key").is_none());
    }
}
