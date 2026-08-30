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
//! By default, cache files are stored alongside the main ledger as a hidden
//! dotfile: `ledger.beancount` → `.ledger.beancount.cache`. This matches Python
//! beancount's `.{filename}.picklecache` convention.
//!
//! Two environment variables control the location, both compatible with
//! Python beancount and honored at the loader level (so any consumer of
//! [`load_cache_entry`] / [`save_cache_entry`] gets the kill switch for free):
//!
//! - `BEANCOUNT_DISABLE_LOAD_CACHE`: when set (even to an empty value),
//!   [`load_cache_entry`] returns `None` and [`save_cache_entry`] is a no-op.
//! - `BEANCOUNT_LOAD_CACHE_FILENAME`: a path pattern that may contain
//!   `{filename}` (replaced with the source basename). Relative paths resolve
//!   against the source directory; absolute paths are used as-is. If the
//!   target directory doesn't exist, [`save_cache_entry`] creates it.

use crate::Options;
use blake3::Hasher;
use rust_decimal::Decimal;
use rustledger_core::Directive;
use rustledger_parser::Spanned;
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
    /// Whether the `python:` prefix was used to force Python execution.
    pub force_python: bool,
}

/// Cached options - a serializable subset of Options.
///
/// Excludes transient parsing-time fields like `warnings`, but DOES
/// persist `set_options`: it is load-bearing downstream, because
/// `resolve_effective_booking_method` gates on
/// `set_options.contains("booking_method")` to decide whether the
/// file-level `option "booking_method"` wins over the API default.
/// Dropping it across the cache round-trip silently re-books FIFO/LIFO
/// ledgers as STRICT on a cache hit (#1340).
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
    pub use_precise_interpolation: bool,
    pub booking_method: String,
    pub render_commas: bool,
    /// `option "display_precision" "USD:0.0001"` overrides (the digit count is
    /// the example number's decimal scale, so `0.0001` → 4), stored as
    /// (currency, digits) pairs. Dropping this on a cache hit silently reverted
    /// number formatting to inferred precision (the bug this field fixes).
    pub display_precision: Vec<(String, u32)>,
    pub allow_pipe_separator: bool,
    pub long_string_maxlines: u32,
    pub documents: Vec<String>,
    pub plugin_processing_mode: String,
    pub custom: Vec<(String, String)>,
    /// Names of options the source explicitly set (e.g.
    /// `"booking_method"`). Restored so downstream resolution that
    /// distinguishes "file set this" from "inherited default" behaves
    /// identically on a cache hit. See the struct-level note (#1340).
    pub set_options: Vec<String>,
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
            use_precise_interpolation: opts.use_precise_interpolation,
            booking_method: opts.booking_method.clone(),
            render_commas: opts.render_commas,
            display_precision: opts
                .display_precision
                .iter()
                .map(|(k, v)| (k.clone(), *v))
                .collect(),
            allow_pipe_separator: opts.allow_pipe_separator,
            long_string_maxlines: opts.long_string_maxlines,
            documents: opts.documents.clone(),
            plugin_processing_mode: opts.plugin_processing_mode.clone(),
            custom: opts
                .custom
                .iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect(),
            set_options: opts.set_options.iter().cloned().collect(),
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
        opts.use_precise_interpolation = cached.use_precise_interpolation;
        opts.booking_method = cached.booking_method;
        opts.render_commas = cached.render_commas;
        opts.display_precision = cached.display_precision.into_iter().collect();
        opts.allow_pipe_separator = cached.allow_pipe_separator;
        opts.long_string_maxlines = cached.long_string_maxlines;
        opts.documents = cached.documents;
        opts.plugin_processing_mode = cached.plugin_processing_mode;
        opts.custom = cached.custom.into_iter().collect();
        opts.set_options = cached.set_options.into_iter().collect();
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

    /// Reconstruct a [`LoadResult`](crate::LoadResult) equivalent to a
    /// fresh parse of the cached source.
    ///
    /// Re-reads each cached source file for the source map (so error
    /// reporting still has text), converts the cached plugin
    /// declarations back (their span / `file_id` are not meaningful
    /// from cache), and — crucially — rebuilds the display context from
    /// the cached directives + options via the same inference a fresh
    /// load uses, so a cache-hit `LoadResult` formats numbers
    /// identically to an uncached one. Reconstructing it as an empty
    /// `DisplayContext` (as the per-command CLI code used to) would
    /// silently change per-currency display precision for any consumer
    /// that reads it.
    ///
    /// `errors` is empty by construction: the cache is only written for
    /// error-free, warning-free loads.
    ///
    /// Strings are NOT re-interned here; a caller that wants the memory
    /// dedup should call [`crate::reintern_directives`] on
    /// `self.directives` first (it needs `&mut`).
    #[must_use]
    pub fn into_load_result(self) -> crate::LoadResult {
        let mut source_map = crate::SourceMap::new();
        for path in self.file_paths() {
            // Read bytes + lossy UTF-8 to match `DiskFileSystem::read`
            // (the uncached loader path). `read_to_string` would error
            // and silently skip a non-UTF8 source file, leaving the
            // cache-hit source map missing text the uncached run has -
            // an error-reporting parity gap.
            //
            // Structured exactly as `DiskFileSystem::read` rather than as
            // `from_utf8_lossy(&bytes).into_owned()`, which is the same
            // operation by a much slower route: it validates through
            // `Utf8Chunks` a byte at a time instead of the word-at-a-time
            // check `String::from_utf8` runs, and then copies the whole file
            // even when every byte was already valid. `String::from_utf8`
            // takes the `Vec` by value and keeps the allocation. Only a
            // genuinely non-UTF-8 file pays for the lossy rebuild, and that
            // branch produces the identical string.
            if let Ok(bytes) = fs::read(&path) {
                let content = match String::from_utf8(bytes) {
                    Ok(s) => s,
                    Err(e) => String::from_utf8_lossy(e.as_bytes()).into_owned(),
                };
                source_map.add_file(path, content.into());
            }
        }

        let plugins: Vec<crate::Plugin> = self
            .plugins
            .iter()
            .map(|p| crate::Plugin {
                name: p.name.clone(),
                config: p.config.clone(),
                span: rustledger_parser::Span::ZERO,
                file_id: 0,
                force_python: p.force_python,
            })
            .collect();

        let options: Options = self.options.into();
        let display_context = crate::build_display_context(&self.directives, &options);

        crate::LoadResult {
            directives: self.directives,
            options,
            plugins,
            source_map,
            errors: Vec::new(),
            display_context,
        }
    }
}

/// Magic bytes to identify cache files.
const CACHE_MAGIC: &[u8; 8] = b"RLEDGER\0";

/// Cache version - increment when format changes.
///
/// v1: Initial release with string-based Decimal/NaiveDate
/// v2: Binary Decimal (16 bytes) and `NaiveDate` (i32 days)
/// v3: Fixed account type defaults in `CachedOptions`
/// v4: Hash algorithm switched from SHA-256 to BLAKE3 — same 32-byte
///     output so the header layout is unchanged, but old hashes won't
///     match new files. Bumping the version short-circuits stale
///     caches at the header check instead of paying the rkyv
///     deserialize cost only to fail the hash compare.
/// v5: `Transaction.postings: Vec<Posting>` became
///     `Vec<Spanned<Posting>>` (#1151). The inner posting bytes
///     gained a `Span + file_id` per entry, so old cache files
///     would rkyv-deserialize into the new type as junk. Header
///     check forces a rebuild instead.
/// v6: The #1163 newtype slices (#1169 `Currency`, #1171 `Account`,
///     #1172 `Tag`, #1173 `Link`, #1174 `MetaValue`) swapped variant
///     payload types from `InternedStr`/`String` to typed newtypes.
///     The archived layout coincidentally matches `AsInternedStr`
///     in most cases, but `MetaValue::{Account,Currency,Tag,Link}`
///     and `Transaction.tags`/`links` (plus the parallel `Document`
///     fields) changed their archive wrappers. Bumping the version
///     forces regeneration so we don't risk rkyv reading old bytes
///     into a structurally-different `ArchivedMetaValue`.
/// v7: `PriceAnnotation` refactored from 6-variant enum to
///     `{ kind: PriceKind, amount: Option<IncompleteAmount> }`
///     (#1167). Old cache bytes for the enum's discriminant would
///     deserialize as nonsense in the new struct layout.
/// v8: `CostSpec.{number_per,number_total}: Option<Decimal>` collapsed
///     into `CostSpec.number: Option<CostNumber>` where `CostNumber` is
///     a 3-variant enum (`PerUnit`, `Total`, `PerUnitFromTotal`)
///     (#1164). The archived layout is structurally different
///     (`Option<Decimal>` + `Option<Decimal>` → `Option<discriminant +
///     payload>`); reading v7 bytes into the v8 layout would produce
///     garbage cost numbers. Bumping forces regeneration.
///     Subsequent #1164 follow-up commits converted `CostNumber`'s
///     variants from tuple form (`PerUnit(Decimal)`) to struct form
///     (`PerUnit { value: Decimal }`) so serde could apply
///     `tag = "kind"` for cross-boundary wire unification. The rkyv-
///     archived layout for a single-field struct variant is byte-
///     identical to the tuple variant (both pack `Archived<Decimal>`
///     positionally) — verified against rkyv 0.8.16 — so this change
///     does NOT require a separate version bump. If a future rkyv
///     version changes that encoding, OR if `CostNumber` gains
///     additional fields, bump `CACHE_VERSION` to the next value.
/// v13: `CostNumber` gained the `Compound { per_unit, total }` variant
///     (#1700) and the parser now emits it for `{a # b}` cost specs —
///     exactly the "gains additional fields" case the v12 note calls
///     out. Without the bump, a cache written by a pre-#1700 binary
///     serves the old misparse (`Total{b}` / `PerUnit{b}`) to fixed
///     binaries, resurrecting the bug for any previously-loaded ledger.
/// v14: green compound-cost conversion now retries past unparsable
///     pre-/post-hash NUMBER tokens like red (#1713); inputs with garbage
///     around `{a # b}` parse to different `CostNumber` values than v13
///     cached them as.
/// v15: EOF now terminates a line in the parser's error-recovery walkers, so a
///     malformed FINAL line without a trailing newline emits its diagnostic
///     (#1884). Previously such a file parsed to zero errors and `rledger
///     check` exited 0 on it. The cached `errors` differ, and a cache written
///     by a pre-fix binary would serve the silent-pass result to a fixed one —
///     resurrecting exactly the bug for every ledger already in the cache,
///     which is the worst case since the symptom is "no error reported".
/// v16: a sign separated from its operand is no longer dropped. `- 7.50 USD`
///     (valid beancount) parsed as **+7.50**, and `-,123.00 USD` (malformed)
///     parsed as **+123.00** with no diagnostic, because the sign landed
///     outside the `AMOUNT` node where nothing read it. Cached postings from a
///     pre-fix binary therefore hold the WRONG SIGN, and the malformed case
///     also holds an empty `errors` list. Serving either to a fixed binary
///     reproduces the original bug on every ledger already in the cache — and
///     a flipped sign is silent, so nothing downstream would flag it.
/// v17: `balance` / `price` values are no longer read as "the first NUMBER
///     token". Parenthesized arithmetic evaluated to the leading operand
///     (`(1 + 5) / 2.1 USD` asserted against **1**, not 2.857…), and a split
///     numeral did the same (`1,23,4.50 USD` -> **1**, a thousandfold error).
///     Cached directives from a pre-fix binary therefore hold those wrong
///     VALUES, and the malformed cases also hold an empty `errors` list — both
///     silent, so nothing downstream would flag them.
/// v9: `CachedOptions` gained a `set_options: Vec<String>` field
///     (#1340). It was previously dropped, so a cache hit lost the
///     record of which options the file explicitly set — making
///     `resolve_effective_booking_method` re-book FIFO/LIFO ledgers as
///     STRICT. The new trailing field changes the archived layout, so
///     old bytes must be regenerated.
/// v10: String literals are now escape-decoded at parse (`\"`->`"`, etc.);
///     the stored narration/payee/meta/etc. bytes differ from the old raw
///     form, so a cache hit would serve stale, still-escaped strings.
/// v11: `MetaValue` gained an `Int(i64)` variant (appended last). Integer
///     metadata literals (`key: 42`) now archive as `Int` rather than
///     `Number`, and the new discriminant changes the enum's archived
///     layout, so old bytes must be regenerated.
/// v12: `CachedOptions` gained `display_precision`, `use_precise_interpolation`,
///     and `plugin_processing_mode` — previously dropped, so a cache hit
///     silently ignored `option "display_precision" "USD:0.0001"` (formatting
///     fell back to inferred precision) and the other two settings. New fields
///     change the archived layout, so old bytes must be regenerated.
/// v18: arithmetic in a COST SPEC is now evaluated rather than truncated to
///     its first operand (#1939). `{10.00 * 3 USD}` previously archived a
///     cost of `10.00`; it now archives `30.00`. The layout is unchanged, so
///     nothing here would REJECT the old bytes — which is exactly why the
///     bump is required: a stale cache would keep serving the truncated cost
///     basis, and the file would keep failing to balance, on a build that has
///     the fix. Verified by hitting precisely that during development.
/// v19: arithmetic is now evaluated in METADATA values and BALANCE
///     TOLERANCES as well as cost specs (#1944). `key: 2 * 3` archives 6 not
///     2, and `~ 0.005 * 2` archives 0.010 not 0.005. Values again, not
///     layout — and again the reason the bump is mandatory: a stale cache
///     would keep serving the truncated tolerance and keep rejecting a file
///     the fixed build accepts.
/// v20: account names accept any NON-ASCII character inside a component
///     (#1930). A ledger that previously failed to parse now yields
///     directives, and one that parsed may gain account names it did not
///     have. Layout unchanged, so old bytes would be accepted and a cached
///     PARSE FAILURE served on a build that can read the file.
/// v21: a `#tag` / `^link` on a directive that does not take one is now a
///     parse error (#1949). A file that previously loaded clean can now carry
///     errors, so a stale cache would serve the old clean parse on a build
///     that objects.
/// v22: a metadata key now needs at least two characters, as in beancount
///     (#1955). A file using `k: 42` previously loaded clean and now carries a
///     parse error, so a stale cache would serve the old clean parse on a
///     build that objects.
/// v23: a `^link` is no longer accepted as a metadata VALUE (#1954), so a
///     file using `ref: ^x` moves from clean to erroring. A stale cache would
///     serve the old clean parse.
/// v24: tags and links are no longer accepted as `custom` / `pushmeta`
///     values (#1958), so a file using them moves from clean to erroring and
///     a stale cache would serve the old clean parse.
/// v25: transaction headers beancount's grammar rejects are now parse errors
///     (#2008) - a third header string, a string after a tag/link, or junk
///     after the narration. Same reasoning as v24: those files move from
///     clean to erroring, and this was observed for real - the first
///     `rledger check` run against the fixtures after the change reported
///     only the old downstream `E1001`s, because the cache still held the
///     permissive parse.
/// v26: malformed cost-spec component lists are now parse errors (#2008 cases
///     1 and 2) - an empty comma-delimited component, or a token after a
///     component is already complete. Same clean-to-erroring move as v25, and
///     a separate version because a cache written between the two lands is
///     stale for this change even though it carries v25.
/// v27: a cost spec with no number the author wrote now archives `number:
///     None` instead of an invented zero (#2008). `{ # CCY}` used to become
///     `Compound { per_unit: 0, total: 0 }`, and a malformed spec had a number
///     scraped out of it. Both changed the ARCHIVED `CostSpec`, so a stale cache
///     would serve the invented number to a build that no longer produces one.
///
/// v28: a literal `-0.00` now parses to an UNSIGNED zero (matching
///     beancount, whose parser yields `Decimal('0.00')`), where the green
///     path's bare `-n` previously archived a signed zero. That is parser
///     OUTPUT, so a stale cache would keep serving `-0.00` from a build that
///     no longer produces one.
///
/// v29: `Posting::cost` and `Posting::price` are boxed. rkyv mirrors the
///     in-memory layout, so `ArchivedPosting` changed shape — a v28 file read
///     as v29 would interpret an inline `CostSpec` as a relative pointer.
///     This is a layout change rather than a content change, so unlike the
///     entries above nothing about the ledger's meaning moved.
///
///   v30: options declared in an INCLUDED file are no longer applied unless
///     they accumulate across includes (#2151). `Options` is part of the
///     cached payload, so a v29 cache replays the old resolution and
///     resurrects the behavior: a sub-ledger's `booking_method` still
///     changing lot selection, a sub-ledger's `inferred_tolerance_default`
///     still letting an unbalanced transaction pass. Caught exactly that way
///     while testing the fix -- the matrices kept diverging until the stale
///     caches were cleared.
///
/// v31: `Note` gained `tags` and `links` (#2160). The parser always accepted
///     them on a note header and threw them away; now it keeps them, so the
///     archived layout has two more fields. Without the bump a cache written
///     by an older binary deserializes into the new struct and every note
///     comes back with no tags -- the exact bug, resurrected from disk.
///
/// v32: a blank line before a `note` or `document` no longer eats its tags
///     and links (#2160 review). Parser OUTPUT, not layout: the archived
///     shape is v31's, but a v31 cache holds the empty tag lists the old
///     parser produced, and this build would serve them as fact.
///
/// Public so `rustledger-wasm` can pin its own cache version against this one.
/// Both caches archive the same `Vec<Directive>`, so a parser change that
/// alters PARSER OUTPUT has to bump both — and on #1942 only this one was
/// bumped, which review caught rather than any test. See
/// `loader_cache_version_is_pinned` in `rustledger-wasm/src/cache.rs`.
pub const CACHE_VERSION: u32 = 32;

/// Cache header stored at the start of cache files.
#[derive(Debug, Clone)]
struct CacheHeader {
    /// Magic bytes for identification.
    magic: [u8; 8],
    /// Cache format version.
    version: u32,
    /// BLAKE3 hash of source files (path + mtime + size).
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
///
/// Files whose metadata cannot be read (e.g., deleted between load and cache)
/// contribute only their path to the hash. This is intentional — the resulting
/// hash mismatch will cause a cache miss on next load.
fn compute_hash(files: &[&Path]) -> [u8; 32] {
    let mut hasher = Hasher::new();

    for file in files {
        // Hash the file path
        hasher.update(file.to_string_lossy().as_bytes());

        // Hash the modification time (skip silently if inaccessible)
        if let Ok(metadata) = fs::metadata(file) {
            if let Ok(mtime) = metadata.modified()
                && let Ok(duration) = mtime.duration_since(std::time::UNIX_EPOCH)
            {
                hasher.update(&duration.as_secs().to_le_bytes());
                hasher.update(&duration.subsec_nanos().to_le_bytes());
            }
            // Hash the file size
            hasher.update(&metadata.len().to_le_bytes());
        }
    }

    *hasher.finalize().as_bytes()
}

/// Environment variable that overrides the default cache filename pattern.
///
/// The value is a path that may contain `{filename}` as a placeholder for the
/// source file's basename. Relative paths are resolved against the source
/// file's directory; absolute paths are used as-is. Mirrors Python beancount's
/// `BEANCOUNT_LOAD_CACHE_FILENAME`.
pub const CACHE_FILENAME_ENV: &str = "BEANCOUNT_LOAD_CACHE_FILENAME";

/// Environment variable that disables the binary cache entirely when set.
///
/// Mirrors Python beancount's `BEANCOUNT_DISABLE_LOAD_CACHE`.
pub const DISABLE_CACHE_ENV: &str = "BEANCOUNT_DISABLE_LOAD_CACHE";

/// Returns the cache file path for a given source file.
///
/// Resolution order:
/// 1. If `BEANCOUNT_LOAD_CACHE_FILENAME` is set, substitute `{filename}` with
///    the source basename and resolve relative paths against the source dir.
/// 2. Otherwise, default to a hidden dotfile alongside the source via
///    [`default_cache_path`]: `path/to/main.beancount` →
///    `path/to/.main.beancount.cache`.
///
/// The dotfile prefix matches Python beancount's `.{filename}.picklecache`
/// convention, so the cache stays out of the way of `ls` and most file
/// explorers without breaking from the established beancount ecosystem
/// behavior. See issue #939.
///
/// This function reads process env. Tests that need a deterministic path
/// regardless of the caller's environment should use [`default_cache_path`]
/// directly.
pub fn cache_path(source: &Path) -> PathBuf {
    if let Ok(pattern) = std::env::var(CACHE_FILENAME_ENV)
        && !pattern.is_empty()
    {
        return resolve_cache_pattern(source, &pattern);
    }
    default_cache_path(source)
}

/// Returns the default cache file path (no env-var lookup).
///
/// Use this when you need a path that is independent of process env, e.g.
/// in tests that mustn't be perturbed by a developer's
/// `BEANCOUNT_LOAD_CACHE_FILENAME`.
#[must_use]
pub fn default_cache_path(source: &Path) -> PathBuf {
    let mut path = source.to_path_buf();
    let name = path.file_name().map_or_else(
        || ".ledger.cache".to_string(),
        |n| format!(".{}.cache", n.to_string_lossy()),
    );
    path.set_file_name(name);
    path
}

/// Resolve a `BEANCOUNT_LOAD_CACHE_FILENAME` pattern against a source path.
///
/// The `"{filename}"` token below is a literal user-facing substitution
/// placeholder (matching Python beancount), not a `format!` argument — hence
/// the explicit allow.
#[allow(clippy::literal_string_with_formatting_args)]
fn resolve_cache_pattern(source: &Path, pattern: &str) -> PathBuf {
    let filename = source.file_name().map_or_else(
        || "ledger".to_string(),
        |n| n.to_string_lossy().into_owned(),
    );
    let resolved = pattern.replace("{filename}", &filename);
    let p = PathBuf::from(&resolved);
    if p.is_absolute() {
        return p;
    }
    source.parent().map_or(p.clone(), |parent| parent.join(&p))
}

/// Returns the legacy (pre-#939) cache path: `<source>.cache` alongside source.
///
/// Used by `save_cache_entry` to opportunistically clean up stale cache files
/// from earlier rustledger versions. Not part of the lookup path.
fn legacy_cache_path(source: &Path) -> PathBuf {
    let mut path = source.to_path_buf();
    let name = path.file_name().map_or_else(
        || "ledger.cache".to_string(),
        |n| format!("{}.cache", n.to_string_lossy()),
    );
    path.set_file_name(name);
    path
}

/// Returns true if `BEANCOUNT_DISABLE_LOAD_CACHE` is set in the environment.
///
/// Mere presence disables — value is ignored, including empty string. Matches
/// Python beancount's `os.getenv("BEANCOUNT_DISABLE_LOAD_CACHE") is None`
/// check.
#[must_use]
pub fn cache_disabled_by_env() -> bool {
    std::env::var_os(DISABLE_CACHE_ENV).is_some()
}

/// Try to load a cache entry from disk.
///
/// Returns `Some(CacheEntry)` if cache is valid and file hashes match,
/// `None` if cache is missing, invalid, outdated, or
/// `BEANCOUNT_DISABLE_LOAD_CACHE` is set.
pub fn load_cache_entry(main_file: &Path) -> Option<CacheEntry> {
    if cache_disabled_by_env() {
        return None;
    }
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
    // Intern while deserializing rather than deduplicating afterwards.
    // rkyv's deserializer carries no interner, so `AsInternedStr` handed
    // every occurrence its own `Arc<str>` — 40,015 of them on a
    // 10,000-transaction ledger holding a few dozen distinct strings — and
    // the caller then walked every directive again through
    // `reintern_directives` to collapse them. The scope establishes the same
    // postcondition (equal strings share a pointer) on the way in, so the
    // second walk is redundant on this path; see `load_result_cached`.
    //
    // The guard drops at the end of this function, including on the `?`
    // paths below, so nothing outlives the load.
    let entry: CacheEntry = {
        let _intern = rustledger_core::intern::InternScope::new();
        rkyv::from_bytes::<CacheEntry, rkyv::rancor::Error>(&data).ok()?
    };

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
///
/// No-op (returns Ok) when `BEANCOUNT_DISABLE_LOAD_CACHE` is set.
pub fn save_cache_entry(main_file: &Path, entry: &CacheEntry) -> Result<(), std::io::Error> {
    if cache_disabled_by_env() {
        return Ok(());
    }
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

    // Custom BEANCOUNT_LOAD_CACHE_FILENAME patterns can point at a directory
    // that doesn't exist yet (e.g. ~/.cache/rledger/foo.cache on a fresh
    // install). Create the parent eagerly so caching isn't silently disabled.
    if let Some(parent) = cache_file.parent()
        && !parent.as_os_str().is_empty()
    {
        fs::create_dir_all(parent)?;
    }

    let mut file = fs::File::create(&cache_file)?;
    file.write_all(&header.to_bytes())?;
    file.write_all(&data)?;

    // One-shot cleanup of pre-#939 visible cache files. Only attempt when the
    // legacy path differs from the new path (i.e., we're not using a custom
    // pattern that happens to land on the old name) and silently ignore
    // failures — leaving the file is harmless, just untidy.
    let legacy = legacy_cache_path(main_file);
    if legacy != cache_file && legacy.exists() {
        let _ = fs::remove_file(&legacy);
    }

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
///
/// Removes both the current cache file and any legacy pre-#939
/// `<file>.cache` sidecar so a subsequent load can't pick up stale data.
pub fn invalidate_cache(main_file: &Path) {
    let cache_file = cache_path(main_file);
    let _ = fs::remove_file(&cache_file);

    let legacy = legacy_cache_path(main_file);
    if legacy != cache_file {
        let _ = fs::remove_file(&legacy);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dedup::reintern_directives;
    use rust_decimal_macros::dec;
    use rustledger_core::{Amount, IncompleteAmount, Posting, Transaction};
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
        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();

        let txn = Transaction::new(date, "Test transaction")
            .with_payee("Test Payee")
            .with_synthesized_posting(Posting::new(
                "Expenses:Test",
                Amount::new(dec!(100.00), "USD"),
            ))
            .with_synthesized_posting(Posting::auto("Assets:Checking"));

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
        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();
        let mut directives = Vec::with_capacity(10000);

        for i in 0..10000 {
            let txn = Transaction::new(date, format!("Transaction {i}"))
                .with_payee("Store")
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(25.00), "USD"),
                ))
                .with_synthesized_posting(Posting::auto("Assets:Checking"));

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

    // Note: end-to-end coverage of `cache_path()` (including the
    // `BEANCOUNT_LOAD_CACHE_FILENAME` env var) lives in
    // `tests/cache_env_var_test.rs`, which can mutate process env without
    // tripping the crate's `forbid(unsafe_code)`. The tests below cover the
    // pure pattern-resolution logic and the legacy-path helper.

    /// Fail fast if a developer has set the cache env vars locally — the
    /// roundtrip tests in this module call `save_cache_entry`/`invalidate_cache`
    /// which read process env, and a custom pattern would silently redirect
    /// writes elsewhere (or fail in surprising ways). CI runs with a clean env.
    fn assert_clean_cache_env() {
        for var in [CACHE_FILENAME_ENV, DISABLE_CACHE_ENV] {
            assert!(
                std::env::var_os(var).is_none(),
                "unset {var} before running this test"
            );
        }
    }

    #[test]
    fn test_resolve_cache_pattern_relative_with_substitution() {
        let source = Path::new("/home/user/finances/main.beancount");
        let resolved = resolve_cache_pattern(source, ".cache/{filename}.bin");
        assert_eq!(
            resolved,
            Path::new("/home/user/finances/.cache/main.beancount.bin")
        );
    }

    #[test]
    fn test_resolve_cache_pattern_absolute() {
        let source = Path::new("/home/user/main.beancount");
        let resolved = resolve_cache_pattern(source, "/var/cache/rledger/{filename}.cache");
        assert_eq!(
            resolved,
            Path::new("/var/cache/rledger/main.beancount.cache")
        );
    }

    #[test]
    fn test_resolve_cache_pattern_no_substitution() {
        // Pattern without {filename} is used verbatim.
        let source = Path::new("/home/user/main.beancount");
        let resolved = resolve_cache_pattern(source, "fixed.cache");
        assert_eq!(resolved, Path::new("/home/user/fixed.cache"));
    }

    #[test]
    fn test_legacy_cache_path() {
        let source = Path::new("/tmp/ledger.beancount");
        assert_eq!(
            legacy_cache_path(source),
            Path::new("/tmp/ledger.beancount.cache")
        );
    }

    #[test]
    fn test_save_load_cache_entry_roundtrip() {
        use std::io::Write;

        assert_clean_cache_env();

        // Create a temp directory
        let temp_dir = std::env::temp_dir().join("rustledger_cache_test");
        let _ = fs::create_dir_all(&temp_dir);

        // Create a temp beancount file
        let beancount_file = temp_dir.join("test.beancount");
        let mut f = fs::File::create(&beancount_file).unwrap();
        writeln!(f, "2024-01-01 open Assets:Test").unwrap();
        drop(f);

        // Create a cache entry
        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();
        let txn =
            Transaction::new(date, "Test").with_synthesized_posting(Posting::auto("Assets:Test"));
        let directives = vec![Spanned::new(Directive::Transaction(txn), Span::new(0, 50))];

        let entry = CacheEntry {
            directives,
            options: CachedOptions::from(&Options::new()),
            plugins: vec![CachedPlugin {
                name: "test_plugin".to_string(),
                config: Some("config".to_string()),
                force_python: false,
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

        assert_clean_cache_env();

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
    fn test_invalidate_cache_removes_legacy_sidecar() {
        // invalidate_cache should remove both the new dotfile cache and any
        // pre-#939 visible cache file alongside the source.
        assert_clean_cache_env();

        let temp_dir = std::env::temp_dir().join("rustledger_invalidate_legacy_test");
        let _ = fs::create_dir_all(&temp_dir);

        let beancount_file = temp_dir.join("legacy.beancount");
        // Synthesize a leftover legacy cache file (no need to be valid — we're
        // only testing that invalidate removes it).
        let legacy = legacy_cache_path(&beancount_file);
        fs::write(&legacy, b"stale").unwrap();
        assert!(legacy.exists());

        invalidate_cache(&beancount_file);
        assert!(
            !legacy.exists(),
            "invalidate_cache should remove the legacy sidecar file"
        );

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

        assert_clean_cache_env();

        let temp_dir = std::env::temp_dir().join("rustledger_magic_test");
        let _ = fs::create_dir_all(&temp_dir);

        let beancount_file = temp_dir.join("test.beancount");
        // Write a malformed cache file at the path load_cache_entry will look up.
        let cache_file = cache_path(&beancount_file);
        let mut f = fs::File::create(&cache_file).unwrap();
        // Write invalid magic
        f.write_all(b"INVALID\0").unwrap();
        f.write_all(&[0u8; CacheHeader::SIZE - 8]).unwrap();
        drop(f);

        assert!(load_cache_entry(&beancount_file).is_none());

        // Cleanup
        let _ = fs::remove_file(&cache_file);
        let _ = fs::remove_dir(&temp_dir);
    }

    /// Bumping `CACHE_VERSION` must short-circuit at the header so we
    /// never feed an older payload to rkyv with the newer schema. Writes
    /// a header with the correct magic but `version = CACHE_VERSION - 1`
    /// (e.g., v4 from before #1151's `Vec<Spanned<Posting>>` shape
    /// change) and asserts the loader refuses it.
    #[test]
    fn test_load_cache_rejects_older_version() {
        use std::io::Write;

        assert_clean_cache_env();

        let temp_dir = std::env::temp_dir().join("rustledger_old_version_test");
        let _ = fs::create_dir_all(&temp_dir);

        let beancount_file = temp_dir.join("test.beancount");
        let cache_file = cache_path(&beancount_file);
        let mut f = fs::File::create(&cache_file).unwrap();

        // Valid magic + previous CACHE_VERSION. The version check at
        // `load_cache_header` should refuse before any payload is
        // touched, no matter what the tail bytes look like.
        let stale_version: u32 = CACHE_VERSION.checked_sub(1).expect("CACHE_VERSION >= 1");
        f.write_all(CACHE_MAGIC).unwrap();
        f.write_all(&stale_version.to_le_bytes()).unwrap();
        f.write_all(&[0u8; CacheHeader::SIZE - 8 - 4]).unwrap();
        drop(f);

        assert!(
            load_cache_entry(&beancount_file).is_none(),
            "loader must reject cache files with an older CACHE_VERSION"
        );

        let _ = fs::remove_file(&cache_file);
        let _ = fs::remove_dir(&temp_dir);
    }

    /// Frozen byte fixtures for the v8 cache layout of
    /// [`rustledger_core::CostNumber`].
    ///
    /// The intra-build distinctness test in `rustledger-core::cost`
    /// (`cost_number_archived_bytes_snapshot`) only catches drift
    /// where variants collide with each other. It would NOT catch a
    /// uniform encoding shift (e.g. a future rkyv minor bump that
    /// changes how `Archived<Decimal>` packs, or an accidental
    /// attribute change). When that happens every variant moves
    /// together so distinctness still holds, but user caches on disk
    /// silently fail to deserialize as garbage in the new layout.
    ///
    /// Capturing the exact bytes here pins the on-disk contract:
    /// any drift trips this test, forcing the developer to either
    /// (a) revert the encoding change, or (b) bump
    /// [`CACHE_VERSION`] so old cache files are short-circuited at
    /// the header check. The companion `cache_version_matches_v8`
    /// assertion below fires if a developer regenerates the fixtures
    /// without bumping the version constant in the same commit.
    ///
    /// **If this test fails** and you intend the new encoding to be
    /// the contract going forward: regenerate the fixtures by
    /// printing `rkyv::to_bytes(&cn)` for each variant, bump
    /// `CACHE_VERSION` to `9`, and update both the fixtures and the
    /// `cache_version_matches_v8` constant below in the same commit.
    ///
    /// Gated to little-endian targets — `rkyv::to_bytes` uses native
    /// endianness, so the hardcoded bytes are valid for `x86_64` /
    /// `aarch64` but would spuriously fail on big-endian platforms
    /// (`s390x`, `ppc64be`). `CACHE_VERSION`'s purpose is same-machine
    /// read guarding, so non-portable bytes aren't a real defect,
    /// just a test-portability footnote.
    #[cfg(target_endian = "little")]
    #[test]
    fn cost_number_archived_bytes_match_v8_fixtures() {
        use rust_decimal_macros::dec;
        use rustledger_core::{BookedCost, CostNumber};

        // Tripwire: regenerating the byte fixtures below without
        // bumping CACHE_VERSION leaves users with rotten caches. The
        // assertion fires when CACHE_VERSION advances past 8, forcing
        // the developer to also update the fixtures (or remove this
        // tripwire if v9's contract is identical to v8 for CostNumber
        // — which is unusual but possible).
        // v9 (#1340), v10 (string escape-decoding), v11 (`MetaValue::Int`), and
        // v12 (`CachedOptions` field-parity) all bumped CACHE_VERSION without
        // touching the `CostNumber` archived layout these fixtures pin, so the
        // byte arrays below are still valid and only FIXTURE_VERSION moves.
        // v13 (#1700) ADDS `CostNumber::Compound` at the END of the enum:
        // existing discriminants and payload encodings are unchanged (the
        // arrays below still pin them), and a fixture for the new variant
        // joins them.
        // v15 (#1884) changes WHICH parse errors are emitted, not how anything
        // is archived, so the byte arrays below still pin the same encoding —
        // only the fixture version moves. The assertions after this one prove
        // that rather than assume it.
        // v19 (#1944) does the same for metadata values and balance
        // tolerances: values move, `CostNumber`'s archived layout does not.
        // v20 (#1930) widens the account-name character set; no archived
        // layout moves, only which inputs produce directives at all.
        // v18 (#1939) changes the cost-spec NUMBER a parse produces
        // (`{10.00 * 3 USD}` archives 30.00, not 10.00). That is a value, not a
        // layout: the `CostNumber` discriminants and payload encodings the byte
        // arrays below pin are untouched, and those assertions prove it rather
        // than take this comment's word for it.
        // v25 (#2008) is another v15: transaction headers beancount rejects now
        // produce a parse error. That changes WHICH errors are emitted, not how
        // a `CostNumber` is archived, so the byte arrays are still valid.
        // v30 (#2151) is the same shape again: options declared in an included
        // file stop being applied. That changes which OPTIONS a load resolves,
        // not how a `CostNumber` is archived, so the byte arrays below are
        // untouched and only FIXTURE_VERSION moves.
        // v31 (#2160) is the FIRST bump in this list that genuinely moves an
        // archived layout: `Note` gained `tags` and `links`. The byte arrays
        // below are still valid, but for a different reason than v25/v30 --
        // not "no layout moved" but "the layout that moved is not this one".
        // They pin `CostNumber` discriminants and payload encodings, which
        // `Note` does not participate in. A future bump that touches
        // `CostNumber` itself has to regenerate them.
        // v32 is a v25/v30 again: a blank line before a `note` or `document`
        // stops eating its tags. That changes which TAGS a parse yields, not
        // how a `CostNumber` is archived, so the byte arrays below hold.
        const FIXTURE_VERSION: u32 = 32;
        assert_eq!(
            CACHE_VERSION, FIXTURE_VERSION,
            "CACHE_VERSION advanced past the fixture version; regenerate \
             the byte fixtures in this test and update FIXTURE_VERSION, \
             or remove the tripwire if v{CACHE_VERSION}'s CostNumber \
             encoding is byte-identical to the fixtures.",
        );

        let cases: &[(&str, CostNumber, &[u8])] = &[
            (
                "PerUnit { value: 150 }",
                CostNumber::PerUnit { value: dec!(150) },
                &[
                    0, 0, 0, 0, 0, 150, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0,
                ],
            ),
            (
                "Compound { per_unit: 5, total: 10 }",
                CostNumber::Compound {
                    per_unit: dec!(5),
                    total: dec!(10),
                },
                &[
                    3, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0,
                ],
            ),
            (
                "Total { value: 1500 }",
                CostNumber::Total { value: dec!(1500) },
                &[
                    1, 0, 0, 0, 0, 220, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0,
                ],
            ),
            (
                "PerUnitFromTotal { per_unit: 150, total: 300 }",
                CostNumber::PerUnitFromTotal(BookedCost::new(dec!(150), dec!(300), dec!(2))),
                &[
                    2, 0, 0, 0, 0, 150, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 44, 1, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0,
                ],
            ),
        ];
        let mut mismatches = Vec::new();
        for (name, cn, expected) in cases {
            let bytes = rkyv::to_bytes::<rkyv::rancor::Error>(cn).unwrap();
            if bytes.as_ref() != *expected {
                mismatches.push(format!("  `{name}` → {:?}", bytes.as_ref()));
            }
        }
        assert!(
            mismatches.is_empty(),
            "rkyv layout drifted from v8 fixtures — bump CACHE_VERSION and \
             update the fixtures in this test if intentional. Actual bytes:\n{}",
            mismatches.join("\n"),
        );
    }

    /// Layout-hash tripwire for [`rustledger_core::MetaValue`] — generalizes the
    /// `CostNumber` frozen-byte fixtures above to the metadata value type the
    /// cache also archives.
    ///
    /// The `CostNumber` fixtures only catch drift in cost numbers. A `MetaValue`
    /// variant reorder, or an rkyv encoding shift in how `InternedStr` / `String`
    /// / `Decimal` / `Amount` pack, changes the on-disk metadata bytes while
    /// `CostNumber` stays byte-identical — and `MetaValue::Int` (v11) was
    /// previously guarded only by a code comment, not a test. This hashes the
    /// archived bytes of one of every `MetaValue` variant (declaration order,
    /// length-prefixed) and pins the digest. Any archived-layout drift trips this,
    /// forcing the developer to bump `CACHE_VERSION` (so stale on-disk caches
    /// short-circuit at the header check) and regenerate the hash.
    ///
    /// Little-endian only, like the `CostNumber` fixtures — `rkyv::to_bytes` uses
    /// native endianness, and `CACHE_VERSION` guards same-machine reads.
    #[cfg(target_endian = "little")]
    #[test]
    fn meta_value_archived_layout_hash_matches() {
        use rustledger_core::{Account, Currency, Link, MetaValue, Tag};

        // Tripwire: regenerating the hash without bumping CACHE_VERSION leaves
        // users with rotten metadata caches.
        // v13 (#1700) added a CostNumber variant; MetaValue's archived
        // layout is untouched, so per the tripwire contract only the
        // fixture version moves.
        // v15 (#1884) is a parser-diagnostics change with no layout impact —
        // same reasoning, and the hash assertion below is what verifies it.
        // v18 (#1939) evaluates arithmetic in a cost spec; `MetaValue` is not
        // involved at all, so the hash below must be unchanged — and is.
        // v19 (#1944) DOES touch metadata, but only which VALUE a given source
        // text produces (`2 * 3` -> Int(6) rather than Int(2)). The variants
        // and their archived encodings are untouched, so the hash below must
        // still match — and the assertion, not this comment, is what proves it.
        // v20 (#1930) is an account-name lexer change; `MetaValue` is
        // untouched and the hash below must still match.
        // v28 is the negative-zero parse rule: a literal `-0.00` now archives
        // an UNSIGNED zero. Like v19 that changes which VALUE a source text
        // produces, not the variants or their encodings, so the hash below
        // must still match — and the assertion, not this comment, proves it.
        // v30 (#2151) changes which options an included file contributes,
        // not how a `MetaValue` is archived; the hash below is unchanged.
        // v31 (#2160) adds `tags` and `links` to `Note`. That moves `Note`'s
        // archived layout, not `MetaValue`'s -- the two new fields are
        // `Vec<Tag>` and `Vec<Link>`, neither of which is a `MetaValue` -- so
        // the hash below is unchanged and the assertion proves it.
        // v32 keeps a note's/document's tags across a preceding blank line.
        // Tags and links are not `MetaValue`s, so the hash below is unchanged.
        const FIXTURE_VERSION: u32 = 32;
        const META_VALUE_LAYOUT_HASH: &str =
            "43e3c258fe376cede6a6c2c975100bcf67ddda0ab84b21566b123c01e0a54b25";
        assert_eq!(
            CACHE_VERSION, FIXTURE_VERSION,
            "CACHE_VERSION advanced past the MetaValue layout-hash fixture; if the \
             MetaValue archived layout changed, bump CACHE_VERSION and regenerate \
             META_VALUE_LAYOUT_HASH below in the same commit, else just bump \
             FIXTURE_VERSION.",
        );

        // One value of every variant in declaration order. Each is archived alone
        // (no metadata map), so the bytes are deterministic.
        let variants: &[MetaValue] = &[
            MetaValue::String("USD".to_string()),
            MetaValue::Account(Account::from("Assets:Bank")),
            MetaValue::Currency(Currency::from("USD")),
            MetaValue::Tag(Tag::from("t")),
            MetaValue::Link(Link::from("t")),
            MetaValue::Date(rustledger_core::naive_date(2024, 1, 15).unwrap()),
            MetaValue::Number(dec!(42)),
            MetaValue::Bool(true),
            MetaValue::Amount(Amount::new(dec!(10), "USD")),
            MetaValue::None,
            MetaValue::Int(42),
        ];

        let mut hasher = Hasher::new();
        for mv in variants {
            let bytes = rkyv::to_bytes::<rkyv::rancor::Error>(mv).unwrap();
            // Length-prefix so a byte moving across a variant boundary can't be
            // masked by a compensating change in the neighbor.
            hasher.update(&(bytes.len() as u64).to_le_bytes());
            hasher.update(&bytes);
        }
        let digest = hasher.finalize().to_hex();

        assert_eq!(
            digest.as_str(),
            META_VALUE_LAYOUT_HASH,
            "MetaValue archived layout changed. If intentional, bump CACHE_VERSION \
             and set META_VALUE_LAYOUT_HASH to: {digest}",
        );
    }

    #[test]
    fn test_reintern_directives_deduplication() {
        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();

        // Create multiple transactions with the same account
        let mut directives = vec![];
        for i in 0..5 {
            let txn = Transaction::new(date, format!("Txn {i}"))
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(10.00), "USD"),
                ))
                .with_synthesized_posting(Posting::auto("Assets:Checking"));
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

    /// The property `load_result_cached` relies on when it skips
    /// `reintern_directives`: deserializing under an `InternScope` leaves
    /// equal strings sharing one `Arc`, which is exactly what that pass
    /// exists to guarantee.
    ///
    /// Asserts the NEGATIVE half first. Without the scope every occurrence
    /// gets its own `Arc`, so if the scope ever stopped working this test
    /// would still be checking something real rather than passing because
    /// `ptr_eq` happened to hold for another reason.
    #[test]
    fn cache_hit_directives_share_one_arc_per_distinct_string() {
        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();
        let mut directives = vec![];
        for _ in 0..5 {
            // Every field the same, so each of the four categories below has
            // five occurrences of one string to share.
            let txn = Transaction::new(date, "SAME-NARRATION")
                .with_payee("SAME-PAYEE")
                .with_synthesized_posting(Posting::new(
                    "Expenses:Food",
                    Amount::new(dec!(10.00), "USD"),
                ))
                .with_synthesized_posting(Posting::auto("Assets:Checking"));
            directives.push(Spanned::new(Directive::Transaction(txn), Span::new(0, 50)));
        }

        let bytes =
            rkyv::to_bytes::<rkyv::rancor::Error>(&directives).expect("directives serialize");

        // All four categories of `InternedStr` a transaction carries, because
        // `reintern_directives` covers all of them and skipping it is only
        // sound if the scope does too. `account` reaches `AsInternedStr`
        // through the `Account` newtype and `currency` through `Amount`,
        // neither of which names the wrapper at the field, so covering one
        // does not imply covering the others.
        let pairs = |ds: &[Spanned<Directive>]| {
            let pick = |d: &Spanned<Directive>| match &d.value {
                Directive::Transaction(t) => {
                    let currency = match &t.postings[0].units {
                        Some(IncompleteAmount::Complete(a)) => a.currency.clone(),
                        other => panic!("expected complete units, got {other:?}"),
                    };
                    (
                        t.postings[0].account.clone(),
                        currency,
                        t.payee.clone().expect("payee"),
                        t.narration.clone(),
                    )
                }
                other => panic!("expected a transaction, got {other:?}"),
            };
            (pick(&ds[0]), pick(&ds[4]))
        };

        let plain: Vec<Spanned<Directive>> =
            rkyv::from_bytes::<Vec<Spanned<Directive>>, rkyv::rancor::Error>(&bytes)
                .expect("deserialize without a scope");
        let (x, y) = pairs(&plain);
        assert_eq!(x.0.as_str(), y.0.as_str());
        assert!(
            !x.0.ptr_eq(&y.0) && !x.1.ptr_eq(&y.1) && !x.2.ptr_eq(&y.2) && !x.3.ptr_eq(&y.3),
            "without an InternScope each occurrence should get its own Arc - \
             if this now holds, the positive assertions below prove nothing"
        );

        let scoped: Vec<Spanned<Directive>> = {
            let _intern = rustledger_core::intern::InternScope::new();
            rkyv::from_bytes::<Vec<Spanned<Directive>>, rkyv::rancor::Error>(&bytes)
                .expect("deserialize under a scope")
        };
        let (x, y) = pairs(&scoped);
        for (label, shared) in [
            ("account", x.0.ptr_eq(&y.0)),
            ("currency", x.1.ptr_eq(&y.1)),
            ("payee", x.2.ptr_eq(&y.2)),
            ("narration", x.3.ptr_eq(&y.3)),
        ] {
            assert!(
                shared,
                "under an InternScope {label} must share one Arc, which is \
                 what lets the cache-hit path skip reintern_directives"
            );
        }
    }

    /// Deserialize `bytes` (optionally under a scope) and return the account
    /// of the first transaction. Interning only happens inside
    /// `AsInternedStr::deserialize_with`, so a scope test that builds an
    /// `InternedStr` directly proves nothing — `InternedStr::new` does not
    /// consult the scope at all.
    fn first_account(bytes: &[u8]) -> rustledger_core::Account {
        let ds = rkyv::from_bytes::<Vec<Spanned<Directive>>, rkyv::rancor::Error>(bytes)
            .expect("deserialize");
        match &ds[0].value {
            Directive::Transaction(t) => t.postings[0].account.clone(),
            other => panic!("expected a transaction, got {other:?}"),
        }
    }

    /// The table must not outlive its guard, or a long-running host would
    /// accumulate every string it ever deserialized.
    #[test]
    fn the_intern_scope_stops_interning_once_the_guard_drops() {
        let bytes = one_txn_archive();
        let inside = {
            let _intern = rustledger_core::intern::InternScope::new();
            let a = first_account(&bytes);
            // Same scope, second deserialization: shares.
            assert!(first_account(&bytes).ptr_eq(&a));
            a
        };
        // The guard has dropped, so a fresh deserialization cannot reach the
        // table that produced `inside`.
        let after = first_account(&bytes);
        assert_eq!(inside.as_str(), after.as_str());
        assert!(
            !inside.ptr_eq(&after),
            "the table must be gone once the guard drops"
        );
    }

    /// An inner scope must not pull the table out from under an outer one
    /// when it drops. `InternScope::new` returns a guard either way, so
    /// without the `installed` flag the inner `Drop` would clear the table
    /// and silently stop interning for the rest of the outer scope — which
    /// no assertion about a single scope would notice.
    #[test]
    fn a_nested_intern_scope_leaves_the_outer_one_interning() {
        let bytes = one_txn_archive();
        let outer = rustledger_core::intern::InternScope::new();
        let first = first_account(&bytes);
        {
            let _inner = rustledger_core::intern::InternScope::new();
            assert!(
                first_account(&bytes).ptr_eq(&first),
                "the inner scope should adopt the outer table, not replace it"
            );
        }
        assert!(
            first_account(&bytes).ptr_eq(&first),
            "the outer scope must still be interning after the inner guard drops"
        );
        drop(outer);
        assert!(!first_account(&bytes).ptr_eq(&first));
    }

    /// One archived transaction, for the scope tests above.
    fn one_txn_archive() -> rkyv::util::AlignedVec {
        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();
        let txn = Transaction::new(date, "N")
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(10.00), "USD"),
            ))
            .with_synthesized_posting(Posting::auto("Assets:Checking"));
        let ds = vec![Spanned::new(Directive::Transaction(txn), Span::new(0, 50))];
        rkyv::to_bytes::<rkyv::rancor::Error>(&ds).expect("serialize")
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

    /// Structural guard (fitness function): populate EVERY non-transient
    /// `Options` field with a non-default value, round-trip through
    /// `CachedOptions`, and assert nothing was dropped. A new `Options` field
    /// that `CachedOptions` forgets to carry fails here — the bug class that
    /// silently dropped `display_precision` / `use_precise_interpolation` /
    /// `plugin_processing_mode` (and `set_options` before #1340).
    ///
    /// `warnings` is intentionally transient (re-derived, not cached), so it is
    /// left default on both sides. **When you add a field to `Options`, set it
    /// here too.**
    #[test]
    fn cached_options_field_parity() {
        use rust_decimal_macros::dec;

        let mut opts = Options::new();
        opts.title = Some("T".into());
        opts.filename = Some("f.beancount".into());
        opts.operating_currency = vec!["USD".into(), "EUR".into()];
        opts.name_assets = "A".into();
        opts.name_liabilities = "L".into();
        opts.name_equity = "Q".into();
        opts.name_income = "I".into();
        opts.name_expenses = "X".into();
        opts.account_rounding = Some("Equity:Round".into());
        opts.account_previous_balances = "Opening".into();
        opts.account_previous_earnings = "Earn".into();
        opts.account_previous_conversions = "Conv".into();
        opts.account_current_earnings = "CurEarn".into();
        opts.account_current_conversions = Some("CurConv".into());
        opts.account_unrealized_gains = Some("Unreal".into());
        opts.conversion_currency = Some("NOTHING".into());
        opts.inferred_tolerance_default =
            std::iter::once(("USD".to_string(), dec!(0.005))).collect();
        opts.inferred_tolerance_multiplier = dec!(1.5);
        opts.infer_tolerance_from_cost = true;
        opts.use_legacy_fixed_tolerances = true;
        opts.experiment_explicit_tolerances = true;
        opts.use_precise_interpolation = true;
        opts.booking_method = "FIFO".into();
        opts.render_commas = true;
        opts.display_precision = [("USD".to_string(), 4u32), ("JPY".to_string(), 0)]
            .into_iter()
            .collect();
        opts.allow_pipe_separator = true;
        opts.long_string_maxlines = 99;
        opts.documents = vec!["docs".into()];
        opts.plugin_processing_mode = "raw".into();
        opts.custom = std::iter::once(("k".to_string(), "v".to_string())).collect();
        opts.set_options = std::iter::once("booking_method".to_string()).collect();
        // `warnings` left default (transient — not cached).

        let restored: Options = CachedOptions::from(&opts).into();
        assert_eq!(
            restored, opts,
            "a CachedOptions field was dropped on the cache round-trip"
        );
    }

    /// Regression for #1340: `set_options` must survive the cache
    /// round-trip. It gates `resolve_effective_booking_method`, so
    /// dropping it makes a cache hit re-book FIFO/LIFO ledgers as
    /// STRICT (the file-level `option "booking_method"` is ignored).
    #[test]
    fn test_cached_options_preserves_set_options_for_booking_method() {
        let mut opts = Options::new();
        // `set()` is what a parsed `option "booking_method" "FIFO"`
        // calls — it records both the value AND the set-membership.
        opts.set("booking_method", "FIFO");
        assert!(opts.set_options.contains("booking_method"));

        let cached = CachedOptions::from(&opts);
        let restored: Options = cached.into();

        assert_eq!(restored.booking_method, "FIFO");
        assert!(
            restored.set_options.contains("booking_method"),
            "set_options dropped across cache round-trip — booking method \
             resolution would fall back to the STRICT default on a cache hit"
        );
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

        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();
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

        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();
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
