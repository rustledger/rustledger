//! Binary cache for parsed ledgers.
//!
//! This module provides a caching layer that can dramatically speed up
//! subsequent loads of unchanged beancount files by serializing the parsed
//! directives to a binary format using rkyv.
//!
//! # How it works
//!
//! 1. When loading a file, compute a hash of all source files
//! 2. Check if a cache file exists with a matching hash
//! 3. If yes, deserialize and return immediately (typically <1ms)
//! 4. If no, parse normally, serialize to cache, and return
//!
//! # Cache location
//!
//! Cache files are stored alongside the main ledger file with a `.cache` extension.
//! For example, `ledger.beancount` would have cache at `ledger.beancount.cache`.

use crate::Options;
use rust_decimal::Decimal;
use rustledger_core::Directive;
use rustledger_core::intern::StringInterner;
use rustledger_parser::Spanned;
use sha2::{Digest, Sha256};
use std::fs;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::str::FromStr;

/// Cached plugin information.
#[derive(Debug, Clone, rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)]
pub struct CachedPlugin {
    /// Plugin module name.
    pub name: String,
    /// Optional configuration string.
    pub config: Option<String>,
}

/// Cached options - a serializable subset of Options.
///
/// Excludes parsing-time fields like `set_options` and `warnings`.
/// These fields mirror the Options struct and inherit their meaning.
#[derive(Debug, Clone, rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)]
#[allow(missing_docs)]
pub struct CachedOptions {
    pub title: Option<String>,
    pub filename: Option<String>,
    pub operating_currency: Vec<String>,
    pub name_assets: String,
    pub name_liabilities: String,
    pub name_equity: String,
    pub name_income: String,
    pub name_expenses: String,
    pub account_rounding: Option<String>,
    pub account_previous_balances: String,
    pub account_previous_earnings: String,
    pub account_previous_conversions: String,
    pub account_current_earnings: String,
    pub account_current_conversions: Option<String>,
    pub account_unrealized_gains: Option<String>,
    pub conversion_currency: Option<String>,
    /// Stored as (currency, `tolerance_string`) pairs since Decimal needs special handling
    pub inferred_tolerance_default: Vec<(String, String)>,
    pub inferred_tolerance_multiplier: String,
    pub infer_tolerance_from_cost: bool,
    pub use_legacy_fixed_tolerances: bool,
    pub experiment_explicit_tolerances: bool,
    pub booking_method: String,
    pub render_commas: bool,
    pub allow_pipe_separator: bool,
    pub long_string_maxlines: u32,
    pub documents: Vec<String>,
    pub custom: Vec<(String, String)>,
}

impl From<&Options> for CachedOptions {
    fn from(opts: &Options) -> Self {
        Self {
            title: opts.title.clone(),
            filename: opts.filename.clone(),
            operating_currency: opts.operating_currency.clone(),
            name_assets: opts.name_assets.clone(),
            name_liabilities: opts.name_liabilities.clone(),
            name_equity: opts.name_equity.clone(),
            name_income: opts.name_income.clone(),
            name_expenses: opts.name_expenses.clone(),
            account_rounding: opts.account_rounding.clone(),
            account_previous_balances: opts.account_previous_balances.clone(),
            account_previous_earnings: opts.account_previous_earnings.clone(),
            account_previous_conversions: opts.account_previous_conversions.clone(),
            account_current_earnings: opts.account_current_earnings.clone(),
            account_current_conversions: opts.account_current_conversions.clone(),
            account_unrealized_gains: opts.account_unrealized_gains.clone(),
            conversion_currency: opts.conversion_currency.clone(),
            inferred_tolerance_default: opts
                .inferred_tolerance_default
                .iter()
                .map(|(k, v)| (k.clone(), v.to_string()))
                .collect(),
            inferred_tolerance_multiplier: opts.inferred_tolerance_multiplier.to_string(),
            infer_tolerance_from_cost: opts.infer_tolerance_from_cost,
            use_legacy_fixed_tolerances: opts.use_legacy_fixed_tolerances,
            experiment_explicit_tolerances: opts.experiment_explicit_tolerances,
            booking_method: opts.booking_method.clone(),
            render_commas: opts.render_commas,
            allow_pipe_separator: opts.allow_pipe_separator,
            long_string_maxlines: opts.long_string_maxlines,
            documents: opts.documents.clone(),
            custom: opts
                .custom
                .iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect(),
        }
    }
}

impl From<CachedOptions> for Options {
    fn from(cached: CachedOptions) -> Self {
        let mut opts = Self::new();
        opts.title = cached.title;
        opts.filename = cached.filename;
        opts.operating_currency = cached.operating_currency;
        opts.name_assets = cached.name_assets;
        opts.name_liabilities = cached.name_liabilities;
        opts.name_equity = cached.name_equity;
        opts.name_income = cached.name_income;
        opts.name_expenses = cached.name_expenses;
        opts.account_rounding = cached.account_rounding;
        opts.account_previous_balances = cached.account_previous_balances;
        opts.account_previous_earnings = cached.account_previous_earnings;
        opts.account_previous_conversions = cached.account_previous_conversions;
        opts.account_current_earnings = cached.account_current_earnings;
        opts.account_current_conversions = cached.account_current_conversions;
        opts.account_unrealized_gains = cached.account_unrealized_gains;
        opts.conversion_currency = cached.conversion_currency;
        opts.inferred_tolerance_default = cached
            .inferred_tolerance_default
            .into_iter()
            .filter_map(|(k, v)| Decimal::from_str(&v).ok().map(|d| (k, d)))
            .collect();
        opts.inferred_tolerance_multiplier =
            Decimal::from_str(&cached.inferred_tolerance_multiplier)
                .unwrap_or_else(|_| Decimal::new(5, 1));
        opts.infer_tolerance_from_cost = cached.infer_tolerance_from_cost;
        opts.use_legacy_fixed_tolerances = cached.use_legacy_fixed_tolerances;
        opts.experiment_explicit_tolerances = cached.experiment_explicit_tolerances;
        opts.booking_method = cached.booking_method;
        opts.render_commas = cached.render_commas;
        opts.allow_pipe_separator = cached.allow_pipe_separator;
        opts.long_string_maxlines = cached.long_string_maxlines;
        opts.documents = cached.documents;
        opts.custom = cached.custom.into_iter().collect();
        opts
    }
}

/// Complete cache entry containing all data needed to restore a `LoadResult`.
#[derive(Debug, Clone, rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)]
pub struct CacheEntry {
    /// All parsed directives.
    pub directives: Vec<Spanned<Directive>>,
    /// Parsed options.
    pub options: CachedOptions,
    /// Plugin declarations.
    pub plugins: Vec<CachedPlugin>,
    /// All files that were loaded (as strings, for serialization).
    pub files: Vec<String>,
}

impl CacheEntry {
    /// Get files as `PathBuf` references.
    pub fn file_paths(&self) -> Vec<PathBuf> {
        self.files.iter().map(PathBuf::from).collect()
    }
}

/// Magic bytes to identify cache files.
const CACHE_MAGIC: &[u8; 8] = b"RLEDGER\0";

/// Cache version - increment when format changes.
/// v1: Initial release with string-based Decimal/NaiveDate
/// v2: Binary Decimal (16 bytes) and `NaiveDate` (i32 days)
/// v3: Fixed account type defaults in `CachedOptions`
const CACHE_VERSION: u32 = 3;

/// Cache header stored at the start of cache files.
#[derive(Debug, Clone)]
struct CacheHeader {
    /// Magic bytes for identification.
    magic: [u8; 8],
    /// Cache format version.
    version: u32,
    /// SHA-256 hash of source files.
    hash: [u8; 32],
    /// Length of the serialized data.
    data_len: u64,
}

impl CacheHeader {
    const SIZE: usize = 8 + 4 + 32 + 8;

    fn to_bytes(&self) -> [u8; Self::SIZE] {
        let mut buf = [0u8; Self::SIZE];
        buf[0..8].copy_from_slice(&self.magic);
        buf[8..12].copy_from_slice(&self.version.to_le_bytes());
        buf[12..44].copy_from_slice(&self.hash);
        buf[44..52].copy_from_slice(&self.data_len.to_le_bytes());
        buf
    }

    fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() < Self::SIZE {
            return None;
        }

        let mut magic = [0u8; 8];
        magic.copy_from_slice(&bytes[0..8]);

        let version = u32::from_le_bytes(bytes[8..12].try_into().ok()?);

        let mut hash = [0u8; 32];
        hash.copy_from_slice(&bytes[12..44]);

        let data_len = u64::from_le_bytes(bytes[44..52].try_into().ok()?);

        Some(Self {
            magic,
            version,
            hash,
            data_len,
        })
    }
}

/// Compute a hash of the given files and their modification times.
fn compute_hash(files: &[&Path]) -> [u8; 32] {
    let mut hasher = Sha256::new();

    for file in files {
        // Hash the file path
        hasher.update(file.to_string_lossy().as_bytes());

        // Hash the modification time
        if let Ok(metadata) = fs::metadata(file) {
            if let Ok(mtime) = metadata.modified() {
                if let Ok(duration) = mtime.duration_since(std::time::UNIX_EPOCH) {
                    hasher.update(duration.as_secs().to_le_bytes());
                    hasher.update(duration.subsec_nanos().to_le_bytes());
                }
            }
            // Hash the file size
            hasher.update(metadata.len().to_le_bytes());
        }
    }

    hasher.finalize().into()
}

/// Get the cache file path for a given source file.
fn cache_path(source: &Path) -> std::path::PathBuf {
    let mut path = source.to_path_buf();
    let name = path.file_name().map_or_else(
        || "ledger.cache".to_string(),
        |n| format!("{}.cache", n.to_string_lossy()),
    );
    path.set_file_name(name);
    path
}

/// Try to load a cache entry from disk.
///
/// Returns `Some(CacheEntry)` if cache is valid and file hashes match,
/// `None` if cache is missing, invalid, or outdated.
pub fn load_cache_entry(main_file: &Path) -> Option<CacheEntry> {
    let cache_file = cache_path(main_file);
    let mut file = fs::File::open(&cache_file).ok()?;

    // Read header
    let mut header_bytes = [0u8; CacheHeader::SIZE];
    file.read_exact(&mut header_bytes).ok()?;
    let header = CacheHeader::from_bytes(&header_bytes)?;

    // Validate magic and version
    if header.magic != *CACHE_MAGIC {
        return None;
    }
    if header.version != CACHE_VERSION {
        return None;
    }

    // Read data
    let mut data = vec![0u8; header.data_len as usize];
    file.read_exact(&mut data).ok()?;

    // Deserialize
    let entry: CacheEntry = rkyv::from_bytes::<CacheEntry, rkyv::rancor::Error>(&data).ok()?;

    // Validate hash against the files stored in the cache
    let file_paths = entry.file_paths();
    let file_refs: Vec<&Path> = file_paths.iter().map(PathBuf::as_path).collect();
    let expected_hash = compute_hash(&file_refs);
    if header.hash != expected_hash {
        return None;
    }

    Some(entry)
}

/// Save a cache entry to disk.
pub fn save_cache_entry(main_file: &Path, entry: &CacheEntry) -> Result<(), std::io::Error> {
    let cache_file = cache_path(main_file);

    // Compute hash from the files in the entry
    let file_paths = entry.file_paths();
    let file_refs: Vec<&Path> = file_paths.iter().map(PathBuf::as_path).collect();
    let hash = compute_hash(&file_refs);

    // Serialize
    let data = rkyv::to_bytes::<rkyv::rancor::Error>(entry)
        .map(|v| v.to_vec())
        .map_err(|e| std::io::Error::other(e.to_string()))?;

    // Write header + data
    let header = CacheHeader {
        magic: *CACHE_MAGIC,
        version: CACHE_VERSION,
        hash,
        data_len: data.len() as u64,
    };

    let mut file = fs::File::create(&cache_file)?;
    file.write_all(&header.to_bytes())?;
    file.write_all(&data)?;

    Ok(())
}

/// Serialize directives to bytes using rkyv (for benchmarking).
#[cfg(test)]
fn serialize_directives(directives: &Vec<Spanned<Directive>>) -> Result<Vec<u8>, std::io::Error> {
    rkyv::to_bytes::<rkyv::rancor::Error>(directives)
        .map(|v| v.to_vec())
        .map_err(|e| std::io::Error::other(e.to_string()))
}

/// Deserialize directives from bytes using rkyv (for benchmarking).
#[cfg(test)]
fn deserialize_directives(data: &[u8]) -> Option<Vec<Spanned<Directive>>> {
    rkyv::from_bytes::<Vec<Spanned<Directive>>, rkyv::rancor::Error>(data).ok()
}

/// Invalidate the cache for a file.
pub fn invalidate_cache(main_file: &Path) {
    let cache_file = cache_path(main_file);
    let _ = fs::remove_file(cache_file);
}

/// Re-intern all strings in directives to deduplicate memory.
///
/// After deserializing from cache, strings are not interned (each is a separate
/// allocation). This function walks through all directives and re-interns account
/// names and currencies using a shared `StringInterner`, deduplicating identical
/// strings to save memory.
///
/// Returns the number of strings that were deduplicated (i.e., strings that
/// were found to already exist in the interner).
pub fn reintern_directives(directives: &mut [Spanned<Directive>]) -> usize {
    use rustledger_core::intern::InternedStr;
    use rustledger_core::{IncompleteAmount, PriceAnnotation};

    // Intern a single string (defined before use to satisfy clippy)
    fn do_intern(s: &mut InternedStr, interner: &mut StringInterner) -> bool {
        let already_exists = interner.contains(s.as_str());
        *s = interner.intern(s.as_str());
        already_exists
    }

    let mut interner = StringInterner::with_capacity(1024);
    let mut dedup_count = 0;

    for spanned in directives.iter_mut() {
        match &mut spanned.value {
            Directive::Transaction(txn) => {
                for posting in &mut txn.postings {
                    if do_intern(&mut posting.account, &mut interner) {
                        dedup_count += 1;
                    }
                    // Units
                    if let Some(ref mut units) = posting.units {
                        match units {
                            IncompleteAmount::Complete(amt) => {
                                if do_intern(&mut amt.currency, &mut interner) {
                                    dedup_count += 1;
                                }
                            }
                            IncompleteAmount::CurrencyOnly(cur) => {
                                if do_intern(cur, &mut interner) {
                                    dedup_count += 1;
                                }
                            }
                            IncompleteAmount::NumberOnly(_) => {}
                        }
                    }
                    // Cost spec
                    if let Some(ref mut cost) = posting.cost {
                        if let Some(ref mut cur) = cost.currency {
                            if do_intern(cur, &mut interner) {
                                dedup_count += 1;
                            }
                        }
                    }
                    // Price annotation
                    if let Some(ref mut price) = posting.price {
                        match price {
                            PriceAnnotation::Unit(amt) | PriceAnnotation::Total(amt) => {
                                if do_intern(&mut amt.currency, &mut interner) {
                                    dedup_count += 1;
                                }
                            }
                            PriceAnnotation::UnitIncomplete(inc)
                            | PriceAnnotation::TotalIncomplete(inc) => match inc {
                                IncompleteAmount::Complete(amt) => {
                                    if do_intern(&mut amt.currency, &mut interner) {
                                        dedup_count += 1;
                                    }
                                }
                                IncompleteAmount::CurrencyOnly(cur) => {
                                    if do_intern(cur, &mut interner) {
                                        dedup_count += 1;
                                    }
                                }
                                IncompleteAmount::NumberOnly(_) => {}
                            },
                            PriceAnnotation::UnitEmpty | PriceAnnotation::TotalEmpty => {}
                        }
                    }
                }
            }
            Directive::Balance(bal) => {
                if do_intern(&mut bal.account, &mut interner) {
                    dedup_count += 1;
                }
                if do_intern(&mut bal.amount.currency, &mut interner) {
                    dedup_count += 1;
                }
            }
            Directive::Open(open) => {
                if do_intern(&mut open.account, &mut interner) {
                    dedup_count += 1;
                }
                for cur in &mut open.currencies {
                    if do_intern(cur, &mut interner) {
                        dedup_count += 1;
                    }
                }
            }
            Directive::Close(close) => {
                if do_intern(&mut close.account, &mut interner) {
                    dedup_count += 1;
                }
            }
            Directive::Commodity(comm) => {
                if do_intern(&mut comm.currency, &mut interner) {
                    dedup_count += 1;
                }
            }
            Directive::Pad(pad) => {
                if do_intern(&mut pad.account, &mut interner) {
                    dedup_count += 1;
                }
                if do_intern(&mut pad.source_account, &mut interner) {
                    dedup_count += 1;
                }
            }
            Directive::Note(note) => {
                if do_intern(&mut note.account, &mut interner) {
                    dedup_count += 1;
                }
            }
            Directive::Document(doc) => {
                if do_intern(&mut doc.account, &mut interner) {
                    dedup_count += 1;
                }
            }
            Directive::Price(price) => {
                if do_intern(&mut price.currency, &mut interner) {
                    dedup_count += 1;
                }
                if do_intern(&mut price.amount.currency, &mut interner) {
                    dedup_count += 1;
                }
            }
            Directive::Event(_) | Directive::Query(_) | Directive::Custom(_) => {
                // These don't contain InternedStr fields
            }
        }
    }

    dedup_count
}

#[cfg(test)]
mod tests {
    use super::*;
    use chrono::NaiveDate;
    use rust_decimal_macros::dec;
    use rustledger_core::{Amount, Posting, Transaction};
    use rustledger_parser::Span;

    #[test]
    fn test_cache_header_roundtrip() {
        let header = CacheHeader {
            magic: *CACHE_MAGIC,
            version: CACHE_VERSION,
            hash: [42u8; 32],
            data_len: 12345,
        };

        let bytes = header.to_bytes();
        let parsed = CacheHeader::from_bytes(&bytes).unwrap();

        assert_eq!(parsed.magic, header.magic);
        assert_eq!(parsed.version, header.version);
        assert_eq!(parsed.hash, header.hash);
        assert_eq!(parsed.data_len, header.data_len);
    }

    #[test]
    fn test_compute_hash_deterministic() {
        let files: Vec<&Path> = vec![];
        let hash1 = compute_hash(&files);
        let hash2 = compute_hash(&files);
        assert_eq!(hash1, hash2);
    }

    #[test]
    fn test_serialize_deserialize_roundtrip() {
        let date = NaiveDate::from_ymd_opt(2024, 1, 15).unwrap();

        let txn = Transaction::new(date, "Test transaction")
            .with_payee("Test Payee")
            .with_posting(Posting::new(
                "Expenses:Test",
                Amount::new(dec!(100.00), "USD"),
            ))
            .with_posting(Posting::auto("Assets:Checking"));

        let directives = vec![Spanned::new(Directive::Transaction(txn), Span::new(0, 100))];

        // Serialize
        let serialized = serialize_directives(&directives).expect("serialization failed");

        // Deserialize
        let deserialized = deserialize_directives(&serialized).expect("deserialization failed");

        // Verify roundtrip
        assert_eq!(directives.len(), deserialized.len());
        let orig_txn = directives[0].value.as_transaction().unwrap();
        let deser_txn = deserialized[0].value.as_transaction().unwrap();

        assert_eq!(orig_txn.date, deser_txn.date);
        assert_eq!(orig_txn.payee, deser_txn.payee);
        assert_eq!(orig_txn.narration, deser_txn.narration);
        assert_eq!(orig_txn.postings.len(), deser_txn.postings.len());

        // Check first posting
        assert_eq!(orig_txn.postings[0].account, deser_txn.postings[0].account);
        assert_eq!(orig_txn.postings[0].units, deser_txn.postings[0].units);
    }

    #[test]
    #[ignore = "manual benchmark - run with: cargo test -p rustledger-loader --release -- --ignored --nocapture"]
    fn bench_cache_performance() {
        // Generate test directives
        let date = NaiveDate::from_ymd_opt(2024, 1, 15).unwrap();
        let mut directives = Vec::with_capacity(10000);

        for i in 0..10000 {
            let txn = Transaction::new(date, format!("Transaction {i}"))
                .with_payee("Store")
                .with_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(25.00), "USD"),
                ))
                .with_posting(Posting::auto("Assets:Checking"));

            directives.push(Spanned::new(Directive::Transaction(txn), Span::new(0, 100)));
        }

        println!("\n=== Cache Benchmark (10,000 directives) ===");

        // Benchmark serialization
        let start = std::time::Instant::now();
        let serialized = serialize_directives(&directives).unwrap();
        let serialize_time = start.elapsed();
        println!(
            "Serialize: {:?} ({:.2} MB)",
            serialize_time,
            serialized.len() as f64 / 1_000_000.0
        );

        // Benchmark deserialization
        let start = std::time::Instant::now();
        let deserialized = deserialize_directives(&serialized).unwrap();
        let deserialize_time = start.elapsed();
        println!("Deserialize: {deserialize_time:?}");

        assert_eq!(directives.len(), deserialized.len());

        println!(
            "\nSpeedup potential: If parsing takes 100ms, cache load would be {:.1}x faster",
            100.0 / deserialize_time.as_millis() as f64
        );
    }

    #[test]
    fn test_cache_path() {
        let source = Path::new("/tmp/ledger.beancount");
        let cache = cache_path(source);
        assert_eq!(cache, Path::new("/tmp/ledger.beancount.cache"));

        let source2 = Path::new("relative/path/my.beancount");
        let cache2 = cache_path(source2);
        assert_eq!(cache2, Path::new("relative/path/my.beancount.cache"));
    }

    #[test]
    fn test_save_load_cache_entry_roundtrip() {
        use std::io::Write;

        // Create a temp directory
        let temp_dir = std::env::temp_dir().join("rustledger_cache_test");
        let _ = fs::create_dir_all(&temp_dir);

        // Create a temp beancount file
        let beancount_file = temp_dir.join("test.beancount");
        let mut f = fs::File::create(&beancount_file).unwrap();
        writeln!(f, "2024-01-01 open Assets:Test").unwrap();
        drop(f);

        // Create a cache entry
        let date = NaiveDate::from_ymd_opt(2024, 1, 15).unwrap();
        let txn = Transaction::new(date, "Test").with_posting(Posting::auto("Assets:Test"));
        let directives = vec![Spanned::new(Directive::Transaction(txn), Span::new(0, 50))];

        let entry = CacheEntry {
            directives,
            options: CachedOptions::from(&Options::new()),
            plugins: vec![CachedPlugin {
                name: "test_plugin".to_string(),
                config: Some("config".to_string()),
            }],
            files: vec![beancount_file.to_string_lossy().to_string()],
        };

        // Save cache
        save_cache_entry(&beancount_file, &entry).expect("save failed");

        // Load cache
        let loaded = load_cache_entry(&beancount_file).expect("load failed");

        // Verify
        assert_eq!(loaded.directives.len(), entry.directives.len());
        assert_eq!(loaded.plugins.len(), 1);
        assert_eq!(loaded.plugins[0].name, "test_plugin");
        assert_eq!(loaded.plugins[0].config, Some("config".to_string()));
        assert_eq!(loaded.files.len(), 1);

        // Cleanup
        let _ = fs::remove_file(&beancount_file);
        let _ = fs::remove_file(cache_path(&beancount_file));
        let _ = fs::remove_dir(&temp_dir);
    }

    #[test]
    fn test_invalidate_cache() {
        use std::io::Write;

        let temp_dir = std::env::temp_dir().join("rustledger_invalidate_test");
        let _ = fs::create_dir_all(&temp_dir);

        let beancount_file = temp_dir.join("test.beancount");
        let mut f = fs::File::create(&beancount_file).unwrap();
        writeln!(f, "2024-01-01 open Assets:Test").unwrap();
        drop(f);

        // Create and save a cache
        let entry = CacheEntry {
            directives: vec![],
            options: CachedOptions::from(&Options::new()),
            plugins: vec![],
            files: vec![beancount_file.to_string_lossy().to_string()],
        };
        save_cache_entry(&beancount_file, &entry).unwrap();

        // Verify cache exists
        assert!(cache_path(&beancount_file).exists());

        // Invalidate
        invalidate_cache(&beancount_file);

        // Verify cache is gone
        assert!(!cache_path(&beancount_file).exists());

        // Cleanup
        let _ = fs::remove_file(&beancount_file);
        let _ = fs::remove_dir(&temp_dir);
    }

    #[test]
    fn test_load_cache_missing_file() {
        let missing = Path::new("/nonexistent/path/to/file.beancount");
        assert!(load_cache_entry(missing).is_none());
    }

    #[test]
    fn test_load_cache_invalid_magic() {
        use std::io::Write;

        let temp_dir = std::env::temp_dir().join("rustledger_magic_test");
        let _ = fs::create_dir_all(&temp_dir);

        let cache_file = temp_dir.join("test.beancount.cache");
        let mut f = fs::File::create(&cache_file).unwrap();
        // Write invalid magic
        f.write_all(b"INVALID\0").unwrap();
        f.write_all(&[0u8; CacheHeader::SIZE - 8]).unwrap();
        drop(f);

        let beancount_file = temp_dir.join("test.beancount");
        assert!(load_cache_entry(&beancount_file).is_none());

        // Cleanup
        let _ = fs::remove_file(&cache_file);
        let _ = fs::remove_dir(&temp_dir);
    }

    #[test]
    fn test_reintern_directives_deduplication() {
        let date = NaiveDate::from_ymd_opt(2024, 1, 15).unwrap();

        // Create multiple transactions with the same account
        let mut directives = vec![];
        for i in 0..5 {
            let txn = Transaction::new(date, format!("Txn {i}"))
                .with_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(10.00), "USD"),
                ))
                .with_posting(Posting::auto("Assets:Checking"));
            directives.push(Spanned::new(Directive::Transaction(txn), Span::new(0, 50)));
        }

        // Re-intern should deduplicate the repeated account names and currencies
        let dedup_count = reintern_directives(&mut directives);

        // We should have deduplicated:
        // - "Expenses:Food" appears 5 times but only first is new (4 dedup)
        // - "USD" appears 5 times but only first is new (4 dedup)
        // - "Assets:Checking" appears 5 times but only first is new (4 dedup)
        // Total: 12 deduplications
        assert_eq!(dedup_count, 12);
    }

    #[test]
    fn test_cached_options_roundtrip() {
        let mut opts = Options::new();
        opts.title = Some("Test Ledger".to_string());
        opts.operating_currency = vec!["USD".to_string(), "EUR".to_string()];
        opts.render_commas = true;

        let cached = CachedOptions::from(&opts);
        let restored: Options = cached.into();

        assert_eq!(restored.title, Some("Test Ledger".to_string()));
        assert_eq!(restored.operating_currency, vec!["USD", "EUR"]);
        assert!(restored.render_commas);
    }

    #[test]
    fn test_cache_entry_file_paths() {
        let entry = CacheEntry {
            directives: vec![],
            options: CachedOptions::from(&Options::new()),
            plugins: vec![],
            files: vec![
                "/path/to/ledger.beancount".to_string(),
                "/path/to/include.beancount".to_string(),
            ],
        };

        let paths = entry.file_paths();
        assert_eq!(paths.len(), 2);
        assert_eq!(paths[0], PathBuf::from("/path/to/ledger.beancount"));
        assert_eq!(paths[1], PathBuf::from("/path/to/include.beancount"));
    }

    #[test]
    fn test_reintern_balance_directive() {
        use rustledger_core::Balance;

        let date = NaiveDate::from_ymd_opt(2024, 1, 15).unwrap();
        let balance = Balance::new(date, "Assets:Checking", Amount::new(dec!(1000.00), "USD"));

        let mut directives = vec![
            Spanned::new(Directive::Balance(balance.clone()), Span::new(0, 50)),
            Spanned::new(Directive::Balance(balance), Span::new(51, 100)),
        ];

        let dedup_count = reintern_directives(&mut directives);
        // Second occurrence of "Assets:Checking" and "USD" should be deduplicated
        assert_eq!(dedup_count, 2);
    }

    #[test]
    fn test_reintern_open_close_directives() {
        use rustledger_core::{Close, Open};

        let date = NaiveDate::from_ymd_opt(2024, 1, 15).unwrap();
        let open = Open::new(date, "Assets:Checking");
        let close = Close::new(date, "Assets:Checking");

        let mut directives = vec![
            Spanned::new(Directive::Open(open), Span::new(0, 50)),
            Spanned::new(Directive::Close(close), Span::new(51, 100)),
        ];

        let dedup_count = reintern_directives(&mut directives);
        // Second "Assets:Checking" should be deduplicated
        assert_eq!(dedup_count, 1);
    }
}
