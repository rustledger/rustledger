//! BQL Query Executor.
//!
//! Executes parsed BQL queries against a set of Beancount directives.

mod functions;
mod types;

use types::AccountInfo;
pub use types::{
    Interval, IntervalUnit, PostingContext, QueryResult, Row, SourceLocation, Table, Value,
    WindowContext,
};

use parking_lot::RwLock;

use rustc_hash::FxHashMap;

use regex::{Regex, RegexBuilder};
use rust_decimal::Decimal;
use rustledger_core::{Amount, Directive, Inventory, NaiveDate, Position};
#[cfg(test)]
use rustledger_core::{MetaValue, Transaction};
use rustledger_loader::SourceMap;
use rustledger_parser::Spanned;
use std::sync::Arc;

use crate::ast::{Expr, FromClause, FunctionCall, Query, SelectQuery, Target};
use crate::error::QueryError;

/// Compute a posting's `weight` — the cost-converted amount used for
/// transaction balancing.
///
/// Both the arithmetic and the cost-beats-price ladder come from
/// [`rustledger_booking::posting_weight`], shared with the budget report's
/// actual-spend accrual, so those two cannot drift from each other.
///
/// It is NOT the balance validator's rule and must not be described as one.
/// `posting_weight`'s own docs spell out where it diverges from
/// `calculate_residual`'s `residual_weight` (a cost number carrying no
/// currency, and a bare `{}` refusing to fall through to a price). Claiming
/// the two cannot drift would send someone chasing a `weight`-vs-`rledger
/// check` disagreement into "aligning" the residual — which is issue #1026
/// re-introduced, flipping E3001 for every ledger holding a bare-cost-plus-
/// price posting. `currency_accounts` re-derives the ladder on the DTO types
/// and differs deliberately as well; see its own comments.
/// Notably `{{total}}`/`PerUnitFromTotal` specs take the preserved total
/// (sign following units) rather than recomputing `units × per_unit`, which
/// for a non-terminating per-unit division would be off in the last of
/// `rust_decimal`'s 28 digits (#1106/#1113), and `@@` credit-side postings
/// flip sign (issue #1052).
///
/// Returns `Value::Null` for postings without resolved units. Used by
/// both [`Executor::build_postings_table`] (the `#postings` table
/// builder) and [`Executor::evaluate_column`] (the default-FROM column
/// accessor) so the two paths can't drift again.
/// The BQL-facing rendering of a `Decimal` overflow (#1863).
///
/// A query cell has no error code, so this carries the currency in the message
/// instead — the same information `E4004` puts in its context field.
fn overflow_err(currency: &rustledger_core::Currency) -> QueryError {
    QueryError::Evaluation(format!(
        "{currency} amount exceeds the representable range (±7.9e28); \
         split the transaction, or denominate it in larger units \
         (thousands, millions) so the number is smaller"
    ))
}

/// `units x per-unit cost`, with the scale the multiplication invents stripped
/// (#1963).
///
/// ONE implementation, because `WEIGHT()` reaches this arithmetic down two
/// paths — a bare `Position` and every position inside an `Inventory` — and the
/// first fix for #1963 patched only the first. The two then disagreed with each
/// other as well as with the column: `WEIGHT(position)` gave `100` where
/// `WEIGHT(SUM(position))` still gave `100.00000000000000000000000000`.
///
/// Why the arithmetic is re-derived here at all, why the strip is conditional,
/// and what it still does not recover are documented at the `WEIGHT` arm.
fn position_cost_total(units: &Amount, cost: &rustledger_core::Cost) -> Result<Amount, QueryError> {
    /// Past any scale a cost is plausibly WRITTEN with. A heuristic, not an
    /// invariant - see the `WEIGHT` arm.
    const ARTIFACT_SCALE: u32 = 12;

    // `checked_mul`, matching the `COST` arm. A saturating or wrapping product
    // would certify a weight that never existed - the unsoundness #1863
    // removed from the residual path.
    let raw = units
        .number
        .checked_mul(cost.number)
        .ok_or_else(|| overflow_err(&cost.currency))?;
    let total = if raw.scale() > ARTIFACT_SCALE {
        raw.normalize()
    } else {
        raw
    };
    Ok(Amount::new(total, cost.currency.clone()))
}

pub(super) fn compute_posting_weight(posting: &rustledger_core::Posting) -> Value {
    rustledger_booking::posting_weight(posting).map_or(Value::Null, Value::Amount)
}

/// Query executor.
pub struct Executor<'a> {
    /// All directives to query over.
    directives: &'a [Directive],
    /// Spanned directives (optional, for source location support).
    spanned_directives: Option<&'a [Spanned<Directive>]>,
    /// Price database for `VALUE()` conversions.
    price_db: crate::price::PriceDatabase,
    /// Target currency for `VALUE()` conversions.
    target_currency: Option<String>,
    /// Query date for price lookups (defaults to today).
    query_date: rustledger_core::NaiveDate,
    /// Config-aware account-type classifier (honors `name_*` renames).
    /// `POSSIGN` and `ACCOUNT_SORTKEY` must classify against this — hardcoded
    /// roots diverge from beanquery on renamed ledgers (L5). Defaults to
    /// the standard five; hosts with a loaded `Ledger` set it via
    /// [`Executor::set_account_types`].
    account_types: rustledger_core::AccountTypes,
    /// Cache for compiled regex patterns (`RwLock` for thread-safe parallel execution).
    // `Arc<Regex>`, not `Regex`: the `~`/`!~` operators look the regex up per
    // row, and cloning a `Regex` gives the clone a fresh, empty lazy-DFA cache
    // pool — so every row rebuilt the DFA from scratch (`Lazy::init_cache` was
    // ~18% of a regex-filter query). Cloning the `Arc` shares the one regex (and
    // its cache), so the DFA is built once per query, not once per row.
    regex_cache: RwLock<FxHashMap<String, Option<Arc<Regex>>>>,
    /// Account info cache from Open/Close directives.
    account_info: FxHashMap<String, AccountInfo>,
    /// Metadata of each `commodity` directive, keyed by currency.
    /// Backs `COMMODITY_META` / `CURRENCY_META`, which beanquery answers from
    /// the commodity directive rather than from any posting (#2153).
    commodity_meta: FxHashMap<String, rustledger_core::Metadata>,
    /// Source locations for directives (indexed by directive index).
    source_locations: Option<Vec<SourceLocation>>,
    /// The source map, kept so per-posting source locations (the `lineno` /
    /// `filename` / `location` columns on posting rows) can be resolved from
    /// each posting's own span, not just the enclosing directive's.
    source_map: Option<&'a SourceMap>,
    /// In-memory tables created by CREATE TABLE.
    tables: FxHashMap<String, Table>,
}

// Sub-modules for focused functionality
mod aggregation;
mod evaluation;
mod execution;
mod operators;
mod sort;
mod system_tables;
mod window;

/// Default column names for `SELECT *` wildcard expansion.
/// This must match the order of values pushed in `evaluate_row()`.
pub const WILDCARD_COLUMNS: &[&str] =
    &["date", "flag", "payee", "narration", "account", "position"];

/// Result of [`Executor::scan_postings`]: the per-posting contexts plus the
/// final per-account running balances. `account_balances` is only meaningful
/// when the scan was asked for it (`needs_account_balance`); it honors the same
/// `FROM` window (`open_on`/`close_on`) as the rest of the scan, so consumers
/// like `BALANCES` get the windowed per-account totals for free.
pub(crate) struct PostingScan<'a> {
    pub(crate) postings: Vec<PostingContext<'a>>,
    pub(crate) account_balances: FxHashMap<rustledger_core::Account, Inventory>,
}

impl<'a> Executor<'a> {
    /// Create a new executor with the given directives.
    pub fn new(directives: &'a [Directive]) -> Self {
        let price_db = crate::price::PriceDatabase::from_directives(directives);

        // Build account info cache from Open/Close directives
        let mut account_info: FxHashMap<String, AccountInfo> = FxHashMap::default();
        let mut commodity_meta: FxHashMap<String, rustledger_core::Metadata> = FxHashMap::default();
        for directive in directives {
            match directive {
                Directive::Open(open) => {
                    let account = open.account.to_string();
                    let info = account_info.entry(account).or_default();
                    info.open_date = Some(open.date);
                    info.open_meta.clone_from(&open.meta);
                    info.booking.clone_from(&open.booking);
                }
                Directive::Close(close) => {
                    let account = close.account.to_string();
                    let info = account_info.entry(account).or_default();
                    info.close_date = Some(close.date);
                }
                Directive::Commodity(commodity) => {
                    // Last declaration wins, matching bean-query: a ledger
                    // that declares `commodity USD` twice resolves to the
                    // later directive's metadata. `or_insert_with` here kept
                    // the FIRST and disagreed.
                    commodity_meta.insert(commodity.currency.to_string(), commodity.meta.clone());
                }
                _ => {}
            }
        }

        Self {
            directives,
            spanned_directives: None,
            price_db,
            target_currency: None,
            query_date: jiff::Zoned::now().date(),
            account_types: rustledger_core::AccountTypes::default(),
            regex_cache: RwLock::new(FxHashMap::default()),
            account_info,
            commodity_meta,
            source_locations: None,
            source_map: None,
            tables: FxHashMap::default(),
        }
    }

    /// Set the config-aware account types (from the loaded ledger's
    /// `name_*` options) so `POSSIGN` / `ACCOUNT_SORTKEY` classify renamed
    /// roots the way beanquery does.
    pub fn set_account_types(&mut self, account_types: rustledger_core::AccountTypes) {
        self.account_types = account_types;
    }

    /// Create a new executor with source location support.
    ///
    /// This constructor accepts spanned directives and a source map, enabling
    /// the `filename`, `lineno`, and `location` columns in queries.
    pub fn new_with_sources(
        spanned_directives: &'a [Spanned<Directive>],
        source_map: &'a SourceMap,
    ) -> Self {
        // Build price database from spanned directives — two passes
        // (mirrors `PriceDatabase::from_directives`).
        // Pass 1: explicit Price directives.
        // Pass 2: implicit prices from transactions, gated on the
        // `(base, quote, date)` tuples already added by pass 1 so the
        // plugin's output (which lands as explicit Price directives in
        // pass 1) isn't duplicated by pass 2's transaction walk
        // (issue #1006).
        let mut price_db = crate::price::PriceDatabase::new();
        for spanned in spanned_directives {
            if let Directive::Price(p) = &spanned.value {
                price_db.add_price(p);
            }
        }
        let explicit = price_db.snapshot_keys();
        for spanned in spanned_directives {
            if let Directive::Transaction(txn) = &spanned.value {
                price_db.add_implicit_prices_from_transaction(txn, &explicit);
            }
        }
        price_db.sort_prices();

        // Build source locations
        let source_locations: Vec<SourceLocation> = spanned_directives
            .iter()
            .map(|spanned| {
                let file = source_map.get(spanned.file_id as usize);
                let (line, _col) = file.map_or((0, 0), |f| f.line_col(spanned.span.start));
                SourceLocation {
                    filename: file.map_or_else(String::new, |f| f.path.display().to_string()),
                    lineno: line,
                }
            })
            .collect();

        // Build account info cache from Open/Close directives
        let mut account_info: FxHashMap<String, AccountInfo> = FxHashMap::default();
        let mut commodity_meta: FxHashMap<String, rustledger_core::Metadata> = FxHashMap::default();
        for spanned in spanned_directives {
            match &spanned.value {
                Directive::Open(open) => {
                    let account = open.account.to_string();
                    let info = account_info.entry(account).or_default();
                    info.open_date = Some(open.date);
                    info.open_meta.clone_from(&open.meta);
                    info.booking.clone_from(&open.booking);
                }
                Directive::Close(close) => {
                    let account = close.account.to_string();
                    let info = account_info.entry(account).or_default();
                    info.close_date = Some(close.date);
                }
                Directive::Commodity(commodity) => {
                    // Last declaration wins, matching bean-query: a ledger
                    // that declares `commodity USD` twice resolves to the
                    // later directive's metadata. `or_insert_with` here kept
                    // the FIRST and disagreed.
                    commodity_meta.insert(commodity.currency.to_string(), commodity.meta.clone());
                }
                _ => {}
            }
        }

        Self {
            directives: &[], // Empty - we use spanned_directives instead
            spanned_directives: Some(spanned_directives),
            price_db,
            target_currency: None,
            query_date: jiff::Zoned::now().date(),
            account_types: rustledger_core::AccountTypes::default(),
            regex_cache: RwLock::new(FxHashMap::default()),
            account_info,
            commodity_meta,
            source_locations: Some(source_locations),
            source_map: Some(source_map),
            tables: FxHashMap::default(),
        }
    }

    /// Get the source location for a directive by index.
    fn get_source_location(&self, directive_index: usize) -> Option<&SourceLocation> {
        self.source_locations
            .as_ref()
            .and_then(|locs| locs.get(directive_index))
    }

    /// Resolve a (file + line) source location from a span's start offset.
    /// Returns `None` for synthesized spans (pad/booking-generated, which carry
    /// no real source) or when no source map is available.
    pub(super) fn span_source_location(
        &self,
        file_id: u16,
        span_start: usize,
    ) -> Option<SourceLocation> {
        if file_id == rustledger_core::SYNTHESIZED_FILE_ID {
            return None;
        }
        let file = self.source_map?.get(file_id as usize)?;
        let (line, _) = file.line_col(span_start);
        Some(SourceLocation {
            filename: file.path.display().to_string(),
            lineno: line,
        })
    }

    /// Resolve a posting's OWN source location from its span, rather than the
    /// enclosing transaction's. Matches beanquery, which reports each posting's
    /// own line; callers fall back to the directive location when this is
    /// `None` (synthesized posting / no source map).
    fn posting_source_location(&self, ctx: &PostingContext) -> Option<SourceLocation> {
        let posting = ctx.transaction.postings.get(ctx.posting_index)?;
        self.span_source_location(posting.file_id, posting.span.start)
    }

    /// Resolve the source location for a posting row's `filename`/`lineno`/
    /// `location` columns: prefer the posting's own location, falling back to
    /// the enclosing directive's (for synthesized postings or when no source
    /// map is present).
    pub(super) fn resolved_source_location(&self, ctx: &PostingContext) -> Option<SourceLocation> {
        self.posting_source_location(ctx).or_else(|| {
            ctx.directive_index
                .and_then(|idx| self.get_source_location(idx).cloned())
        })
    }

    /// The directives to iterate over, regardless of which constructor built
    /// the `Executor`.
    ///
    /// The source-location-aware constructor ([`Self::new_with_sources`], used
    /// by the CLI and LSP) stores directives in `spanned_directives` and leaves
    /// `directives` **empty**. Any command that walks directives MUST go through
    /// here — iterating `self.directives` directly silently yields an empty
    /// result under that constructor. That exact omission regressed `JOURNAL`
    /// (issue: BQL compat 93%→77%), after `SELECT`, `PRINT`, and `BALANCES` each
    /// had to be fixed the same way. Routing every generic walk through one
    /// accessor keeps the next command from re-introducing the bug.
    pub(super) fn resolved_directives(&self) -> impl Iterator<Item = &'a Directive> {
        // The two sources are mutually exclusive (see the constructors):
        // `new_with_sources` leaves `directives` empty and fills
        // `spanned_directives`; `new` leaves `spanned_directives` None. Chaining
        // them therefore yields exactly the populated source — with no
        // allocation, unlike collecting into a `Vec`.
        self.spanned_directives
            .unwrap_or(&[])
            .iter()
            .map(|s| &s.value)
            .chain(self.directives.iter())
    }

    /// Get or compile a regex pattern from the cache.
    ///
    /// Returns `Some(Arc<Regex>)` if the pattern is valid, `None` if it's invalid.
    /// Invalid patterns are cached as `None` to avoid repeated compilation attempts.
    fn get_or_compile_regex(&self, pattern: &str) -> Option<Arc<Regex>> {
        // Fast path: check read lock first
        {
            // parking_lot's RwLock does not poison, so the read guard is
            // returned directly (this matches the previous std behavior,
            // which recovered from poisoning via into_inner()).
            let cache = self.regex_cache.read();
            if let Some(cached) = cache.get(pattern) {
                return cached.clone();
            }
        }
        // Slow path: compile and insert with write lock
        // Use case-insensitive matching to match Python beancount behavior
        let compiled = RegexBuilder::new(pattern)
            .case_insensitive(true)
            .build()
            .ok()
            .map(Arc::new);
        let mut cache = self.regex_cache.write();
        // Double-check in case another thread inserted while we waited
        if let Some(cached) = cache.get(pattern) {
            return cached.clone();
        }
        cache.insert(pattern.to_string(), compiled.clone());
        compiled
    }

    /// Get or compile a regex pattern, returning an error if invalid.
    /// Does any posting on this entry have an account matching `pattern`?
    ///
    /// ONE implementation for both spellings of `HAS_ACCOUNT`: the FROM
    /// predicate in `evaluate_from_filter` and the projection arm in
    /// `evaluate_function`. They answer the same question about the same
    /// entry, so a second copy is a divergence waiting to happen -- the
    /// two already differed in their error text before this was extracted.
    fn entry_has_account(
        &self,
        txn: &rustledger_core::Transaction,
        pattern: &str,
    ) -> Result<bool, QueryError> {
        let regex = self.require_regex(pattern)?;
        Ok(txn.postings.iter().any(|p| regex.is_match(&p.account)))
    }

    fn require_regex(&self, pattern: &str) -> Result<Arc<Regex>, QueryError> {
        self.get_or_compile_regex(pattern)
            .ok_or_else(|| QueryError::Type(format!("invalid regex: {pattern}")))
    }

    /// Set the target currency for `VALUE()` conversions.
    pub fn set_target_currency(&mut self, currency: impl Into<String>) {
        self.target_currency = Some(currency.into());
    }

    /// Execute a query and return the results.
    ///
    /// # Errors
    ///
    /// Returns [`QueryError`] in the following cases:
    ///
    /// - [`QueryError::UnknownColumn`] - A referenced column name doesn't exist
    /// - [`QueryError::UnknownFunction`] - An unknown function is called
    /// - [`QueryError::InvalidArguments`] - Function called with wrong arguments
    /// - [`QueryError::Type`] - Type mismatch in expression (e.g., comparing string to number)
    /// - [`QueryError::Aggregation`] - Error in aggregate function (SUM, COUNT, etc.)
    /// - [`QueryError::Evaluation`] - General expression evaluation error
    pub fn execute(&mut self, query: &Query) -> Result<QueryResult, QueryError> {
        match query {
            Query::Select(select) => self.execute_select(select),
            Query::Journal(journal) => self.execute_journal(journal),
            Query::Balances(balances) => self.execute_balances(balances),
            Query::Print(print) => self.execute_print(print),
            Query::CreateTable(create) => self.execute_create_table(create),
            Query::Insert(insert) => self.execute_insert(insert),
        }
    }

    /// Compute per-account inventories for a `BALANCES` query.
    ///
    /// Returns a fresh map rather than mutating shared state on `self` so that
    /// sequential queries on the same `Executor` produce independent results.
    /// See issue #958 for the bug that motivated this signature: a previous
    /// implementation accumulated into `self.balances` without clearing,
    /// causing a second `BALANCES` call to double-count and a `BALANCES FROM
    /// year=2024` followed by `BALANCES FROM year=2025` to return a confused
    /// union of both filters.
    fn build_balances_with_filter(
        &self,
        from: Option<&FromClause>,
    ) -> Result<FxHashMap<rustledger_core::Account, Inventory>, QueryError> {
        // Delegate to the shared posting scan so BALANCES uses the SAME cost
        // resolution AND the SAME `FROM` window (`open_on` / `close_on`) as the
        // default SELECT path. `scan_postings`' per-account `account_balances`
        // (requested via `needs_account_balance = true`) is exactly the windowed
        // per-account total BALANCES wants. Previously this re-iterated postings
        // and applied only `from.filter`, silently ignoring `OPEN ON`/`CLOSE ON`.
        //
        // `needs_balance = false` (no cumulative needed); `where_clause = None`
        // — `BALANCES` applies its own `WHERE` to the result afterward, and
        // `account_balances` is WHERE-independent by construction anyway.
        Ok(self
            .scan_postings(
                from,
                None,
                ScanNeeds {
                    balance: false,
                    account_balance: true,
                    where_reads_balance: false,
                    where_reads_account_balance: false,
                    output_reads_account_balance: true,
                },
                false,
            )?
            .account_balances)
    }

    /// Collect postings matching the FROM and WHERE clauses.
    fn collect_postings(&self, query: &SelectQuery) -> Result<Vec<PostingContext<'a>>, QueryError> {
        let from = query.from.as_ref();
        let where_clause = query.where_clause.as_ref();

        // Both `balance` (cumulative, WHERE-filtered) and `account_balance`
        // (per-account, raw) are running-state columns. Each PostingContext
        // built below carries snapshots — and `cumulative_balance` grows
        // monotonically across the iteration, so cloning it per posting on
        // a 100k-posting ledger was the runaway-allocation regression in
        // issue #1080.
        //
        // Gate the clones on whether the query actually references the
        // columns anywhere (SELECT / WHERE / ORDER BY / HAVING / GROUP BY /
        // FROM filter). Queries that don't touch them (the common case —
        // `SELECT account WHERE account ~ "^Assets"` references neither)
        // skip the entire state-tracking + clone path. Pre-fix, the only
        // gate was `where_clause.is_some()` for the pre-WHERE snapshot,
        // which fired even when the WHERE didn't read balance.
        let needs_balance = query_references_column(query, "balance");
        let needs_account_balance = query_references_column(query, "account_balance");

        // Tighter gate for the *pre-WHERE* `balance` clone — only
        // required when the WHERE clause itself reads `balance`. For
        // queries like `SELECT balance FROM #postings` (`balance` in
        // SELECT, no WHERE-time read), the pre-snapshot is never
        // observed; we skip the extra clone and let the post-WHERE
        // refresh fill `ctx.balance`. Caught by Copilot review on
        // PR #1085. `account_balance` now gets the same treatment, for the
        // same reason but with a different mechanism: it is not REFRESHED
        // post-WHERE (the eager update above already made it the running
        // total), so instead of a late refresh it is simply filled late —
        // after the filter, for rows that survive. See #2086.
        let where_reads_balance =
            where_clause.is_some_and(|w| expr_references_column(w, "balance"));
        // Same distinction for `account_balance`: referenced ANYWHERE decides
        // whether the column is materialized at all, referenced by the WHERE
        // decides whether it has to exist before the filter runs.
        let where_reads_account_balance =
            where_clause.is_some_and(|w| expr_references_column(w, "account_balance"));
        // And whether anything AFTER the filter reads it. A snapshot the WHERE
        // needed but nothing else does must be released once the filter is
        // done, or it keeps the engine's `Arc` shared and forces that account
        // to copy on its next mutation — the copy this exists to avoid.
        let output_reads_account_balance = output_references_column(query, "account_balance");

        Ok(self
            .scan_postings(
                from,
                where_clause,
                ScanNeeds {
                    balance: needs_balance,
                    account_balance: needs_account_balance,
                    where_reads_balance,
                    where_reads_account_balance,
                    output_reads_account_balance,
                },
                true,
            )?
            .postings)
    }

    /// The single posting-source scan, shared by the default `SELECT` path
    /// ([`Self::collect_postings`]) and the `#postings` table
    /// ([`Self::build_postings_table`]).
    ///
    /// Iterates the resolved directives in order, applies the optional `FROM` and
    /// posting-level `WHERE` filters, accumulates the running cumulative `balance`
    /// (over `WHERE`-passed postings) and the per-account `account_balance`, and
    /// yields one [`PostingContext`] per surviving posting. The `needs_*` flags
    /// gate the per-posting Inventory clones (issue #1080); pass them all `true`
    /// with no filter to materialize the full unfiltered table.
    ///
    /// `collect_contexts` controls whether the per-posting [`PostingContext`]
    /// stream is built at all. Callers that only consume `account_balances` (the
    /// `BALANCES` command) pass `false` to skip materializing — and immediately
    /// discarding — a context per posting; the returned `postings` is then empty.
    // Four independent, individually-documented scan toggles on one internal hot
    // path; a flags struct would add per-call construction churn here without
    // changing the boolean nature of the configuration.
    #[allow(clippy::fn_params_excessive_bools)]
    fn scan_postings(
        &self,
        from: Option<&FromClause>,
        where_clause: Option<&Expr>,
        needs: ScanNeeds,
        collect_contexts: bool,
    ) -> Result<PostingScan<'a>, QueryError> {
        let ScanNeeds {
            balance: needs_balance,
            account_balance: needs_account_balance,
            where_reads_balance,
            where_reads_account_balance,
            output_reads_account_balance,
        } = needs;
        let mut postings = Vec::new();
        // Per-account running balance — accumulates every posting the FROM clause
        // keeps (plus the pre-`open_on` carry-in below), independent of the WHERE
        // filter, so `account_balance` always reflects the account's true ledger
        // balance at the point of the posting.
        // Realize through the BOOKING ENGINE, not a bare inventory map.
        //
        // This used to be `FxHashMap<Account, Inventory>` accumulated with
        // `Inventory::add` — unconditionally, with no reduction branch at all.
        // For FIFO/LIFO that looks right by coincidence: booking has already
        // resolved a reduction's cost, so its lot key matches an existing lot
        // and `add` nets it. Under AVERAGE it does not, because the reduction
        // is booked at the MERGED average cost — a key belonging to no
        // augmentation — so it survived as a dangling negative position and
        // BALANCES reported `10 {200}  10 {150}  -5 {175}` for an account
        // holding 15 (#1985).
        //
        // `replay_posting` is the same decision `report balances` realizes
        // through, which is the point: two realizations of one ledger is the
        // duplication registry's realization family, and this was the drift.
        let mut engine = rustledger_booking::BookingEngine::new();
        // Single cumulative running balance across WHERE-filtered postings in
        // iteration order. This is the bean-query `balance` semantic: a snapshot
        // of "everything selected so far" rather than a per-account view.
        // SHARED backing: cloned once per output row below. A contiguous
        // copy per row is what #1086 is about — 2000 lots x 2000 rows holds
        // ~2M positions at once (measured 395 MB vs 31 MB).
        let mut cumulative_balance: Inventory = Inventory::new_shared();

        // Create an iterator over (directive_index, directive) pairs
        // Handle both spanned and unspanned directives
        let directive_iter: Vec<(usize, &Directive)> =
            self.resolved_directives().enumerate().collect();
        // Register from the vec just built rather than walking the directive
        // stream a second time — Copilot's catch. `register_account_methods`
        // only reads `Open` directives, so the order is irrelevant and this is
        // the same registration, one pass earlier.
        engine.register_account_methods(directive_iter.iter().map(|(_, d)| *d));

        // Resolve a posting to a Position that preserves cost basis when present.
        // The single cost-resolve lives in `Position::from_posting`, shared with
        // every other balance accumulator in this crate so lot details can't be
        // dropped by a divergent copy.
        let resolve_position = |posting: &rustledger_core::Posting, txn_date: NaiveDate| {
            posting
                .amount()
                .map(|units| Position::from_posting(units, posting.cost.as_deref(), txn_date))
        };

        for (directive_index, directive) in directive_iter {
            if let Directive::Transaction(txn) = directive {
                // Check FROM clause (transaction-level filter)
                if let Some(from) = from {
                    // Apply date filters
                    if let Some(open_date) = from.open_on
                        && txn.date < open_date
                    {
                        // Update per-account balances but don't include in results
                        // and don't touch the cumulative balance — these postings
                        // didn't make it past the FROM filter.
                        if needs_account_balance {
                            for posting in &txn.postings {
                                engine
                                    .replay_posting(posting, txn.date)
                                    .map_err(|e| QueryError::Evaluation(e.to_string()))?;
                            }
                        }
                        continue;
                    }
                    // `close on D` is exclusive (matches bean-query): the books
                    // are closed AT D, so a transaction stamped exactly on D is
                    // not part of the closing period. Combined with `open on D`
                    // being inclusive, the resulting range is `[open, close)`.
                    if let Some(close_date) = from.close_on
                        && txn.date >= close_date
                    {
                        continue;
                    }
                    // Apply filter expression
                    if let Some(filter) = &from.filter
                        && !self.evaluate_from_filter(filter, txn)?
                    {
                        continue;
                    }
                }

                for (i, posting) in txn.postings.iter().enumerate() {
                    // Update the account-level running balance regardless of
                    // whether this posting passes WHERE — `account_balance`
                    // should always reflect the underlying ledger truth.
                    // Skip the update entirely when the query doesn't read
                    // account_balance (saves the `.clone()` + map probe per
                    // posting; `Inventory::add` allocates internally so the
                    // saving compounds across a long run).
                    // Only `needs_balance` reads this now. Before #1985 the
                    // per-account accumulation used it too, so it was
                    // unconditional; `replay_posting` resolves the position
                    // itself, so computing it here for a query that reads
                    // neither column was a `Position::from_posting` per
                    // posting for nothing. Copilot's catch.
                    let resolved = needs_balance
                        .then(|| resolve_position(posting, txn.date))
                        .flatten();
                    if needs_account_balance {
                        engine
                            .replay_posting(posting, txn.date)
                            .map_err(|e| QueryError::Evaluation(e.to_string()))?;
                    }

                    // Callers that only want the per-account totals (BALANCES, via
                    // `build_balances_with_filter`) pass `collect_contexts = false`:
                    // `account_balances` is already updated above, so skip building
                    // and pushing a `PostingContext` (and its per-posting Inventory
                    // clone) for every posting — a large-ledger CPU/memory win that
                    // avoids materializing a stream BALANCES would just discard.
                    if !collect_contexts {
                        continue;
                    }

                    // Build the context with both balance views. The cumulative
                    // snapshot is the running total *before* this posting; we
                    // update it after WHERE passes so postings rejected by WHERE
                    // don't pollute the cumulative. Cloning the cumulative
                    // `Inventory` is the hot allocation — it grows monotonically
                    // across the iteration, so a 22k-posting WHERE-filtered
                    // query was producing ~3 clones × thousands of positions per
                    // posting (issue #1080 — multi-GB WASM heap growth).
                    //
                    // `balance` and `account_balance` have asymmetric pre/post
                    // semantics so they gate differently:
                    //
                    // * `balance` is refreshed post-WHERE below — its pre-WHERE
                    //   slot only matters when the WHERE clause itself reads
                    //   the column. For `SELECT balance FROM #postings` (no
                    //   WHERE-time read), we skip the pre-WHERE clone entirely
                    //   and let the post-WHERE refresh fill it. Saves one
                    //   clone-per-posting versus the gating logic
                    //   in the first cut of this fix (Copilot review on PR #1085).
                    //
                    // * `account_balance` is NOT refreshed post-WHERE —
                    //   account_balances is updated *before* this block, so
                    //   the value here is already the post-update running
                    //   total. We populate it eagerly when `needs_account_balance`
                    //   so SELECT / ORDER BY / HAVING / etc. can read it.
                    let mut ctx = PostingContext {
                        transaction: txn,
                        posting_index: i,
                        balance: if where_reads_balance {
                            Some(cumulative_balance.clone())
                        } else {
                            None
                        },
                        // Snapshotting the account's inventory used to copy
                        // every lot, for EVERY posting the FROM clause kept,
                        // including the ones WHERE was about to reject. That is
                        // O(rows x lots) — 0.11s / 0.39s / 3.31s for 1k / 2k /
                        // 6k transactions, quadratic (#2086).
                        //
                        // Same treatment `balance` got in #1085: the pre-WHERE
                        // copy is only observable when the WHERE clause itself
                        // reads the column. Otherwise it is filled in below,
                        // for surviving rows only. Nothing mutates the engine
                        // between here and there, so the deferred value is the
                        // same one.
                        account_balance: if needs_account_balance && where_reads_account_balance {
                            engine.inventory_snapshot(&posting.account)
                        } else {
                            None
                        },
                        directive_index: Some(directive_index),
                    };

                    // Check WHERE clause (posting-level filter)
                    if let Some(where_expr) = where_clause
                        && !self.evaluate_predicate(where_expr, &ctx)?
                    {
                        continue;
                    }

                    // WHERE passed: contribute this posting to the cumulative
                    // balance and refresh the snapshot in ctx so SELECT sees
                    // the post-update value. Both steps are no-ops when the
                    // query doesn't read `balance`.
                    if needs_balance {
                        if let Some(pos) = resolved {
                            cumulative_balance
                                .add(pos)
                                .map_err(|e| QueryError::Evaluation(e.to_string()))?;
                        }
                        ctx.balance = Some(cumulative_balance.clone());
                    }
                    // The deferred half of the gate above: this row survived, so
                    // it is one of the few that will actually be read.
                    if output_reads_account_balance {
                        if ctx.account_balance.is_none() {
                            ctx.account_balance = engine.inventory_snapshot(&posting.account);
                        }
                    } else {
                        // The filter has had its look. Dropping the snapshot
                        // here returns the engine's `Arc` to unique ownership,
                        // so the next posting on this account mutates in place
                        // instead of copying every lot (#2086).
                        ctx.account_balance = None;
                    }
                    postings.push(ctx);
                }
            }
        }

        Ok(PostingScan {
            postings,
            account_balances: engine.into_inventories(),
        })
    }
    /// Is this call `WEIGHT(position)` over the posting COLUMN?
    ///
    /// Deliberately narrow. `WEIGHT(<anything else>)` — a literal, an
    /// expression, `SUM(position)` — keeps going to the shared value registry,
    /// so this reintroduces exactly one lazy-path arm rather than un-collapsing
    /// the dual dispatch the registry exists to prevent.
    fn is_position_column(func: &FunctionCall) -> bool {
        matches!(
            func.args.as_slice(),
            [Expr::Column(c)] if c.eq_ignore_ascii_case("position")
        )
    }

    fn evaluate_function(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        let name = func.name.to_uppercase();
        match name.as_str() {
            // Metadata functions read the row's `PostingContext`, so they stay
            // on the lazy path rather than routing through the value registry.
            "META" | "ENTRY_META" | "ANY_META" | "POSTING_META" => {
                self.eval_meta_function(&name, func, ctx)
            }
            // COALESCE short-circuits on its raw argument expressions and must
            // NOT pre-evaluate every argument, so it stays on the lazy path.
            "COALESCE" => self.eval_coalesce(func, ctx),
            // `WEIGHT(position)` needs the POSTING, not the evaluated argument,
            // for the same reason the META family does: the value registry has
            // already lost what the answer depends on.
            //
            // The canonical weight ladder in `rustledger_booking::posting_weight`
            // is cost, then PRICE, then units. A `Value::Position` carries units
            // and cost and no price at all, so the eager path could implement
            // only two of the three rungs and silently returned the units for a
            // priced posting — `10 EUR @ 1.10 USD` gave `10 EUR` where the
            // `weight` column gives `11.00 USD`. A different number in a
            // different currency, so summing WEIGHT() over a ledger with priced
            // postings produced a currency-mixed total (#1966).
            //
            // Routing to the same helper the `weight` COLUMN uses makes the two
            // spellings one computation rather than two implementations that
            // agree by inspection. It also closes the residual scale gap from
            // #1963 — the column's exact `100.00` instead of a re-derived `100`.
            "WEIGHT" if Self::is_position_column(func) => Ok(compute_posting_weight(
                &ctx.transaction.postings[ctx.posting_index],
            )),
            // `HAS_ACCOUNT(regex)` asks about the whole ENTRY, so like the META
            // family it needs the row's transaction rather than the evaluated
            // argument list. It was already implemented for the FROM clause in
            // `evaluate_from_filter`; without this arm the same name resolved
            // there and raised `UnknownFunction` in a projection (#2153).
            "HAS_ACCOUNT" => {
                let args = func
                    .args
                    .iter()
                    .map(|a| self.evaluate_expr(a, ctx))
                    .collect::<Result<Vec<_>, _>>()?;
                if args.len() != 1 {
                    return Err(QueryError::InvalidArguments(
                        "HAS_ACCOUNT".to_string(),
                        "expected 1 argument".to_string(),
                    ));
                }
                let Value::String(pattern) = &args[0] else {
                    return match &args[0] {
                        Value::Null => Ok(Value::Null),
                        _ => Err(QueryError::Type(
                            "HAS_ACCOUNT expects a string pattern".to_string(),
                        )),
                    };
                };
                Ok(Value::Boolean(
                    self.entry_has_account(ctx.transaction, pattern)?,
                ))
            }
            // Aggregates evaluate to Null per row; real aggregation happens in
            // the aggregation pass.
            "SUM" | "COUNT" | "MIN" | "MAX" | "FIRST" | "LAST" | "AVG" => Ok(Value::Null),
            // Every other function: evaluate the arguments, then dispatch through
            // the single value-based registry shared with `#postings`, aggregates,
            // and subqueries. Unknown names fall through to its `UnknownFunction`
            // arm. This is the collapse of the formerly-duplicated lazy dispatch
            // onto `evaluate_function_on_values` (dual-eval-path unification).
            _ => {
                let args = func
                    .args
                    .iter()
                    .map(|a| self.evaluate_expr(a, ctx))
                    .collect::<Result<Vec<_>, _>>()?;
                self.evaluate_function_on_values(&name, &args)
            }
        }
    }

    /// Evaluate a function with pre-evaluated arguments (for subquery context).
    fn evaluate_function_on_values(&self, name: &str, args: &[Value]) -> Result<Value, QueryError> {
        let name_upper = name.to_uppercase();
        match name_upper.as_str() {
            // Date functions
            "TODAY" => {
                // Takes no arguments; reject extras to match the lazy path.
                Self::require_args_count(&name_upper, args, 0)?;
                Ok(Value::Date(jiff::Zoned::now().date()))
            }
            "YEAR" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Date(d) => Ok(Value::Integer(d.year().into())),
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type("YEAR expects a date".to_string())),
                }
            }
            "MONTH" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Date(d) => Ok(Value::Integer(d.month().into())),
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type("MONTH expects a date".to_string())),
                }
            }
            "DAY" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Date(d) => Ok(Value::Integer(d.day().into())),
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type("DAY expects a date".to_string())),
                }
            }
            // String functions
            "LENGTH" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    // Count Unicode characters, not UTF-8 bytes (matches beanquery).
                    Value::String(s) => Ok(Value::Integer(s.chars().count() as i64)),
                    Value::StringSet(s) => Ok(Value::Integer(s.len() as i64)),
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "LENGTH expects a string or set".to_string(),
                    )),
                }
            }
            "UPPER" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::String(s) => Ok(Value::String(s.to_uppercase())),
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type("UPPER expects a string".to_string())),
                }
            }
            "LOWER" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::String(s) => Ok(Value::String(s.to_lowercase())),
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type("LOWER expects a string".to_string())),
                }
            }
            "TRIM" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::String(s) => Ok(Value::String(s.trim().to_string())),
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type("TRIM expects a string".to_string())),
                }
            }
            // Math functions
            "ABS" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Number(n) => Ok(Value::Number(n.abs())),
                    Value::Integer(i) => Ok(Value::Integer(i.abs())),
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type("ABS expects a number".to_string())),
                }
            }
            "ROUND" => Self::round_on_values(args),
            // Utility functions
            "COALESCE" => {
                for arg in args {
                    if !matches!(arg, Value::Null) {
                        return Ok(arg.clone());
                    }
                }
                Ok(Value::Null)
            }
            // Position/Amount functions
            "NUMBER" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Amount(a) => Ok(Value::Number(a.number)),
                    Value::Position(p) => Ok(Value::Number(p.units.number)),
                    Value::Number(n) => Ok(Value::Number(*n)),
                    Value::Integer(i) => Ok(Value::Number(Decimal::from(*i))),
                    Value::Inventory(inv) => {
                        // For inventory, only return a number if all positions share the same
                        // currency. Summing across different currencies is not meaningful.
                        // Single pass: track the first currency and running total, bail out
                        // to Null on any currency mismatch.
                        let mut iter = inv.positions();
                        let Some(first) = iter.next() else {
                            return Ok(Value::Number(Decimal::ZERO));
                        };
                        let first_currency = &first.units.currency;
                        let mut total = first.units.number;
                        for pos in iter {
                            if &pos.units.currency != first_currency {
                                return Ok(Value::Null);
                            }
                            // Python scale rule, same as SUM — see
                            // `rustledger_core::add_python_scale`. This walks
                            // a multi-lot inventory (cost-bearing lots are not
                            // coalesced), so it is a real accumulation and
                            // gets the same rule rather than a second
                            // convention.
                            //
                            // Scope note, so this is not mistaken for a fix of
                            // the visible symptom: no ledger is known that
                            // makes THIS loop's own zero-crossing observable —
                            // booking rejects the reductions that would build
                            // one. The `0` vs `0.00` that `NUMBER(SUM(position))`
                            // does show on a single-currency ledger comes from
                            // further upstream, where `Inventory::add`
                            // coalesces same-key lots with a plain
                            // `checked_add` and drops the scale there. Fixing
                            // that is a `rustledger-core` change read by every
                            // balance surface (reports, FFI, BQL) and wants its
                            // own compat sweep.
                            total = rustledger_core::add_python_scale(total, pos.units.number);
                        }
                        Ok(Value::Number(total))
                    }
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "NUMBER expects an amount, position, or inventory".to_string(),
                    )),
                }
            }
            "CURRENCY" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Amount(a) => Ok(Value::String(a.currency.to_string())),
                    Value::Position(p) => Ok(Value::String(p.units.currency.to_string())),
                    Value::Inventory(inv) => {
                        // Return the currency of the first position, or Null if empty
                        if let Some(pos) = inv.positions().next() {
                            Ok(Value::String(pos.units.currency.to_string()))
                        } else {
                            Ok(Value::Null)
                        }
                    }
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "CURRENCY expects an amount or position".to_string(),
                    )),
                }
            }
            "UNITS" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Position(p) => Ok(Value::Amount(p.units.clone())),
                    Value::Amount(a) => Ok(Value::Amount(a.clone())),
                    Value::Inventory(inv) => {
                        // Return inventory with just units (no cost info)
                        let mut units_inv = Inventory::new();
                        for pos in inv.positions() {
                            units_inv
                                .add(Position::simple(pos.units.clone()))
                                .map_err(|e| QueryError::Evaluation(e.to_string()))?;
                        }
                        Ok(Value::Inventory(std::sync::Arc::new(units_inv)))
                    }
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "UNITS expects a position or inventory".to_string(),
                    )),
                }
            }
            "COST" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Position(p) => {
                        if let Some(cost) = &p.cost {
                            // Preserve sign: buys give positive cost, sells give negative
                            let total = p
                                .units
                                .number
                                .checked_mul(cost.number)
                                .ok_or_else(|| overflow_err(&cost.currency))?;
                            Ok(Value::Amount(Amount::new(total, cost.currency.clone())))
                        } else {
                            Ok(Value::Amount(p.units.clone()))
                        }
                    }
                    Value::Amount(a) => Ok(Value::Amount(a.clone())),
                    Value::Inventory(inv) => {
                        let mut total = Decimal::ZERO;
                        let mut currency: Option<rustledger_core::Currency> = None;
                        for pos in inv.positions() {
                            if let Some(cost) = &pos.cost {
                                total = pos
                                    .units
                                    .number
                                    .checked_mul(cost.number)
                                    .and_then(|v| total.checked_add(v))
                                    .ok_or_else(|| overflow_err(&cost.currency))?;
                                if currency.is_none() {
                                    currency = Some(cost.currency.clone());
                                }
                            } else {
                                total = total
                                    .checked_add(pos.units.number)
                                    .ok_or_else(|| overflow_err(&pos.units.currency))?;
                                if currency.is_none() {
                                    currency = Some(pos.units.currency.clone());
                                }
                            }
                        }
                        if let Some(curr) = currency {
                            Ok(Value::Amount(Amount::new(total, curr)))
                        } else {
                            Ok(Value::Null)
                        }
                    }
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "COST expects a position or inventory".to_string(),
                    )),
                }
            }
            "VALUE" => {
                // Use shared VALUE implementation for consistent behavior.
                // See `eval_value` on PositionFunctions for the full signature
                // contract (DATE vs. currency-string dispatch).
                if args.is_empty() || args.len() > 2 {
                    return Err(QueryError::InvalidArguments(
                        "VALUE".to_string(),
                        "expected 1-2 arguments".to_string(),
                    ));
                }
                let (explicit_currency, at_date) = if args.len() == 2 {
                    match &args[1] {
                        Value::Date(d) => (None, Some(*d)),
                        Value::String(s) => (Some(s.as_str()), None),
                        Value::Null => {
                            return Err(QueryError::Type(
                                concat!(
                                    "VALUE: second argument evaluated to NULL; ",
                                    "expected a date or currency string ",
                                    "(this often means an aggregate expression couldn't ",
                                    "evaluate against an empty group — see issue #902)",
                                )
                                .to_string(),
                            ));
                        }
                        _ => {
                            return Err(QueryError::Type(
                                "VALUE second argument must be a date or currency string"
                                    .to_string(),
                            ));
                        }
                    }
                } else {
                    (None, None)
                };
                self.convert_to_market_value(&args[0], explicit_currency, at_date)
            }
            // Math functions
            "SAFEDIV" => {
                Self::require_args_count(&name_upper, args, 2)?;
                let (dividend, divisor) = (&args[0], &args[1]);
                match (dividend, divisor) {
                    // NULL propagates.
                    (Value::Null, _) | (_, Value::Null) => Ok(Value::Null),
                    // Any numeric pair: coerce to Decimal and divide. A zero
                    // divisor yields 0 (the "safe" in SAFEDIV) — matching
                    // beanquery and the per-row `eval_safediv` path, which used to
                    // disagree (this path returned NULL on a zero divisor).
                    _ => {
                        let to_dec = |v: &Value| match v {
                            Value::Number(n) => Some(*n),
                            Value::Integer(i) => Some(Decimal::from(*i)),
                            _ => None,
                        };
                        match (to_dec(dividend), to_dec(divisor)) {
                            (Some(a), Some(b)) => Ok(Value::Number(if b.is_zero() {
                                Decimal::ZERO
                            } else {
                                a / b
                            })),
                            _ => Err(QueryError::Type(
                                "SAFEDIV expects numeric arguments".to_string(),
                            )),
                        }
                    }
                }
            }
            "NEG" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Number(n) => Ok(Value::Number(-n)),
                    Value::Integer(i) => Ok(Value::Integer(-i)),
                    Value::Amount(a) => {
                        Ok(Value::Amount(Amount::new(-a.number, a.currency.clone())))
                    }
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "NEG expects a number or amount".to_string(),
                    )),
                }
            }
            // Account functions
            "ACCOUNT_SORTKEY" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::String(s) => {
                        let type_index = self.account_type_index(s);
                        Ok(Value::String(format!("{type_index}-{s}")))
                    }
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "ACCOUNT_SORTKEY expects an account string".to_string(),
                    )),
                }
            }
            "PARENT" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::String(s) => {
                        if let Some(idx) = s.rfind(':') {
                            Ok(Value::String(s[..idx].to_string()))
                        } else {
                            Ok(Value::Null)
                        }
                    }
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "PARENT expects an account string".to_string(),
                    )),
                }
            }
            "LEAF" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::String(s) => {
                        if let Some(idx) = s.rfind(':') {
                            Ok(Value::String(s[idx + 1..].to_string()))
                        } else {
                            Ok(Value::String(s.clone()))
                        }
                    }
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "LEAF expects an account string".to_string(),
                    )),
                }
            }
            "ROOT" => {
                if args.is_empty() || args.len() > 2 {
                    return Err(QueryError::InvalidArguments(
                        "ROOT".to_string(),
                        "expected 1 or 2 arguments".to_string(),
                    ));
                }
                let n = if args.len() == 2 {
                    let raw = match &args[1] {
                        Value::Integer(i) => *i,
                        _ => {
                            return Err(QueryError::Type(
                                "ROOT second arg must be integer".to_string(),
                            ));
                        }
                    };
                    // Reject negatives explicitly — `i as usize` would silently
                    // turn -1 into `usize::MAX` and return the whole account.
                    // Mirrors the lazy `eval_root` guard so both paths agree.
                    usize::try_from(raw).map_err(|_| {
                        QueryError::Type(format!(
                            "ROOT second arg must be a non-negative integer, got {raw}"
                        ))
                    })?
                } else {
                    1
                };
                match &args[0] {
                    Value::String(s) => {
                        let parts: Vec<&str> = s.split(':').collect();
                        if n >= parts.len() {
                            Ok(Value::String(s.clone()))
                        } else {
                            Ok(Value::String(parts[..n].join(":")))
                        }
                    }
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "ROOT expects an account string".to_string(),
                    )),
                }
            }
            // ONLY function: extract single-currency amount from inventory
            "ONLY" => {
                Self::require_args_count(&name_upper, args, 2)?;
                let currency = match &args[0] {
                    Value::String(s) => s.clone(),
                    // NULL propagates (beanquery parity): `first(cost_currency)`
                    // is NULL for groups without costs, and fava's Holdings
                    // by_currency query feeds exactly that into only() — see
                    // #1699. The second-argument match below already
                    // propagates; the asymmetry was the bug.
                    Value::Null => return Ok(Value::Null),
                    _ => {
                        return Err(QueryError::Type(
                            "ONLY: first argument must be a currency string".to_string(),
                        ));
                    }
                };
                match &args[1] {
                    Value::Inventory(inv) => {
                        let total = inv.units(&currency);
                        if total.is_zero() {
                            Ok(Value::Null)
                        } else {
                            Ok(Value::Amount(Amount::new(total, &currency)))
                        }
                    }
                    Value::Position(p) => {
                        if p.units.currency.as_str() == currency {
                            Ok(Value::Amount(p.units.clone()))
                        } else {
                            Ok(Value::Null)
                        }
                    }
                    Value::Amount(a) => {
                        if a.currency.as_str() == currency {
                            Ok(Value::Amount(a.clone()))
                        } else {
                            Ok(Value::Null)
                        }
                    }
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "ONLY: second argument must be an inventory, position, or amount"
                            .to_string(),
                    )),
                }
            }
            // GETPRICE function - needs price database
            "GETPRICE" => {
                if args.len() < 2 || args.len() > 3 {
                    return Err(QueryError::InvalidArguments(
                        "GETPRICE".to_string(),
                        "expected 2 or 3 arguments".to_string(),
                    ));
                }
                // Handle NULL arguments gracefully
                let base = match &args[0] {
                    Value::String(s) => s.clone(),
                    Value::Null => return Ok(Value::Null),
                    _ => {
                        return Err(QueryError::Type(
                            "GETPRICE: first argument must be a currency string".to_string(),
                        ));
                    }
                };
                let quote = match &args[1] {
                    Value::String(s) => s.clone(),
                    Value::Null => return Ok(Value::Null),
                    _ => {
                        return Err(QueryError::Type(
                            "GETPRICE: second argument must be a currency string".to_string(),
                        ));
                    }
                };
                let date = if args.len() == 3 {
                    match &args[2] {
                        Value::Date(d) => *d,
                        Value::Null => self.query_date,
                        _ => self.query_date,
                    }
                } else {
                    self.query_date
                };
                match self.price_db.get_price(&base, &quote, date) {
                    Some(price) => Ok(Value::Number(price)),
                    None => Ok(Value::Null),
                }
            }
            // Inventory functions
            "EMPTY" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Inventory(inv) => Ok(Value::Boolean(inv.is_empty())),
                    Value::Null => Ok(Value::Boolean(true)),
                    _ => Err(QueryError::Type("EMPTY expects an inventory".to_string())),
                }
            }
            "FILTER_CURRENCY" => {
                Self::require_args_count(&name_upper, args, 2)?;
                let currency = match &args[1] {
                    Value::String(s) => s.clone(),
                    Value::Null => return Ok(Value::Null),
                    _ => {
                        return Err(QueryError::Type(
                            "FILTER_CURRENCY expects (inventory, string)".to_string(),
                        ));
                    }
                };
                match &args[0] {
                    Value::Inventory(inv) => {
                        let filtered: Vec<Position> = inv
                            .positions()
                            .filter(|p| p.units.currency.as_str() == currency)
                            .cloned()
                            .collect();
                        let mut new_inv = Inventory::new();
                        for pos in filtered {
                            new_inv
                                .add(pos)
                                .map_err(|e| QueryError::Evaluation(e.to_string()))?;
                        }
                        Ok(Value::Inventory(std::sync::Arc::new(new_inv)))
                    }
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "FILTER_CURRENCY expects (inventory, string)".to_string(),
                    )),
                }
            }
            "POSSIGN" => {
                Self::require_args_count(&name_upper, args, 2)?;
                let account_str = match &args[1] {
                    Value::String(s) => s.clone(),
                    Value::Null => return Ok(Value::Null),
                    _ => {
                        return Err(QueryError::Type(
                            "POSSIGN expects (amount, account_string)".to_string(),
                        ));
                    }
                };
                // Configured credit-normal set (honors `name_*` renames) —
                // beanquery flips for a renamed Income root too (L5).
                let is_credit_normal = self.account_types.is_credit_normal(&account_str);
                match &args[0] {
                    Value::Amount(a) => {
                        let mut amt = a.clone();
                        if is_credit_normal {
                            amt.number = -amt.number;
                        }
                        Ok(Value::Amount(amt))
                    }
                    Value::Number(n) => {
                        let adjusted = if is_credit_normal { -n } else { *n };
                        Ok(Value::Number(adjusted))
                    }
                    // Mirror the lazy `POSSIGN`: an integer amount is treated as
                    // a number and sign-adjusted.
                    Value::Integer(i) => {
                        let n = Decimal::from(*i);
                        let adjusted = if is_credit_normal { -n } else { n };
                        Ok(Value::Number(adjusted))
                    }
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "POSSIGN expects (amount, account_string)".to_string(),
                    )),
                }
            }
            // CONVERT function - convert amounts/positions/inventories to target currency
            "CONVERT" => {
                if args.len() < 2 || args.len() > 3 {
                    return Err(QueryError::InvalidArguments(
                        "CONVERT".to_string(),
                        "expected 2 or 3 arguments: (value, currency[, date])".to_string(),
                    ));
                }

                let target_currency = match &args[1] {
                    Value::String(s) => s.clone(),
                    Value::Null => {
                        return Err(QueryError::Type(
                            concat!(
                                "CONVERT: second argument evaluated to NULL; ",
                                "expected a currency string ",
                                "(this often means an aggregate expression couldn't ",
                                "evaluate against an empty group — see issue #902)",
                            )
                            .to_string(),
                        ));
                    }
                    _ => {
                        return Err(QueryError::Type(
                            "CONVERT: second argument must be a currency string".to_string(),
                        ));
                    }
                };

                // Optional date argument
                let date: Option<rustledger_core::NaiveDate> = if args.len() == 3 {
                    match &args[2] {
                        Value::Date(d) => Some(*d),
                        Value::Null => None, // NULL date uses latest price
                        _ => {
                            return Err(QueryError::Type(
                                "CONVERT: third argument must be a date".to_string(),
                            ));
                        }
                    }
                } else {
                    None
                };

                // Helper closure to convert an amount
                let convert_amount = |amt: &Amount| -> Option<Amount> {
                    if let Some(d) = date {
                        self.price_db.convert(amt, &target_currency, d)
                    } else {
                        self.price_db.convert_latest(amt, &target_currency)
                    }
                };

                match &args[0] {
                    Value::Position(p) => {
                        if p.units.currency == target_currency {
                            Ok(Value::Amount(p.units.clone()))
                        } else if let Some(converted) = convert_amount(&p.units) {
                            Ok(Value::Amount(converted))
                        } else {
                            Ok(Value::Amount(p.units.clone()))
                        }
                    }
                    Value::Amount(a) => {
                        if a.currency == target_currency {
                            Ok(Value::Amount(a.clone()))
                        } else if let Some(converted) = convert_amount(a) {
                            Ok(Value::Amount(converted))
                        } else {
                            Ok(Value::Amount(a.clone()))
                        }
                    }
                    Value::Inventory(inv) => {
                        // Convert each position, keeping originals when no conversion available
                        // (matches Python beancount behavior)
                        let mut result = Inventory::default();
                        for pos in inv.positions() {
                            if pos.units.currency == target_currency {
                                result
                                    .add(Position::simple(pos.units.clone()))
                                    .map_err(|e| QueryError::Evaluation(e.to_string()))?;
                            } else if let Some(converted) = convert_amount(&pos.units) {
                                result
                                    .add(Position::simple(converted))
                                    .map_err(|e| QueryError::Evaluation(e.to_string()))?;
                            } else {
                                // No conversion available - keep original (Python beancount behavior)
                                result
                                    .add(Position::simple(pos.units.clone()))
                                    .map_err(|e| QueryError::Evaluation(e.to_string()))?;
                            }
                        }
                        // If result has single currency matching target, return as Amount
                        // If result is empty, return zero in target currency (issue #586)
                        let positions: Vec<&Position> = result.positions().collect();
                        if positions.is_empty() {
                            Ok(Value::Amount(Amount::new(Decimal::ZERO, &target_currency)))
                        } else if positions.len() == 1
                            && positions[0].units.currency == target_currency
                        {
                            Ok(Value::Amount(positions[0].units.clone()))
                        } else {
                            Ok(Value::Inventory(std::sync::Arc::new(result)))
                        }
                    }
                    Value::Number(n) => Ok(Value::Amount(Amount::new(*n, &target_currency))),
                    Value::String(s) => {
                        // String input is a rustledger extension (issue #1179),
                        // not present in Python beancount. Lets users write
                        // ad-hoc currency conversions like
                        // `SELECT CONVERT('100 USD', 'EUR')` without anchoring
                        // them to a posting. Strict parser (see
                        // `Amount::from_str`): malformed input surfaces as a
                        // typed `QueryError` rather than a silent zero or a
                        // panic.
                        let amt: Amount = s.parse().map_err(|e| {
                            QueryError::Type(format!(
                                "CONVERT: first argument {e} (e.g. \"100 USD\")"
                            ))
                        })?;
                        if amt.currency == target_currency {
                            Ok(Value::Amount(amt))
                        } else if let Some(converted) = convert_amount(&amt) {
                            Ok(Value::Amount(converted))
                        } else {
                            // Match the `Value::Amount` arm: no price available
                            // → return original unchanged.
                            Ok(Value::Amount(amt))
                        }
                    }
                    Value::Null => {
                        // For null values (e.g., empty sum), return zero in target currency
                        // This matches Python beancount behavior for empty balances (issue #586)
                        Ok(Value::Amount(Amount::new(Decimal::ZERO, &target_currency)))
                    }
                    _ => Err(QueryError::Type(
                        "CONVERT expects a position, amount, inventory, number, or amount-string"
                            .to_string(),
                    )),
                }
            }
            // Type casting functions - use shared helpers
            "STR" => {
                Self::require_args_count(&name_upper, args, 1)?;
                Self::value_to_str(&args[0])
            }
            "INT" => {
                Self::require_args_count(&name_upper, args, 1)?;
                Self::value_to_int(&args[0])
            }
            "DECIMAL" => {
                Self::require_args_count(&name_upper, args, 1)?;
                Self::value_to_decimal(&args[0])
            }
            "BOOL" => {
                Self::require_args_count(&name_upper, args, 1)?;
                Self::value_to_bool(&args[0])
            }
            // Date functions for wrapping aggregates: QUARTER(MAX(date))
            "QUARTER" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    // beanquery returns a `YYYY-Qn` string, not an integer.
                    // Through the canonical, like `DATE_TRUNC('QUARTER', …)`
                    // and `DATE_PART('QUARTER', …)`. This was the last inline
                    // copy of the formula: a configurable fiscal-year quarter
                    // offset would have moved those two and left this one
                    // labeling each bucket a quarter off from the rows beside
                    // it, with no test failing.
                    Value::Date(d) => Ok(Value::String(format!(
                        "{:04}-Q{}",
                        d.year(),
                        rustledger_core::quarter_index0(u32::from(d.month().unsigned_abs())) + 1
                    ))),
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type("QUARTER expects a date".to_string())),
                }
            }
            "WEEKDAY" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Date(d) => Ok(Value::String(
                        functions::weekday_abbrev(d.weekday().to_monday_zero_offset() as u32)
                            .to_string(),
                    )),
                    _ => Err(QueryError::Type("WEEKDAY expects a date".to_string())),
                }
            }
            "YMONTH" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Date(d) => {
                        Ok(Value::String(format!("{:04}-{:02}", d.year(), d.month())))
                    }
                    _ => Err(QueryError::Type("YMONTH expects a date".to_string())),
                }
            }
            // String functions for wrapping aggregates
            "SUBSTR" | "SUBSTRING" => {
                if args.len() < 2 || args.len() > 3 {
                    return Err(QueryError::InvalidArguments(
                        name_upper,
                        "expected 2 or 3 arguments".to_string(),
                    ));
                }
                // Python slice semantics s[start:end] — see `py_slice` /
                // `eval_substr`. arg3 is the END index, not a length.
                match (&args[0], &args[1], args.get(2)) {
                    (Value::String(s), Value::Integer(start), None) => Ok(Value::String(
                        functions::string::py_slice(&s.chars().collect::<Vec<_>>(), *start, None),
                    )),
                    (Value::String(s), Value::Integer(start), Some(Value::Integer(end))) => {
                        Ok(Value::String(functions::string::py_slice(
                            &s.chars().collect::<Vec<_>>(),
                            *start,
                            Some(*end),
                        )))
                    }
                    _ => Err(QueryError::Type(
                        "SUBSTR expects (string, int, [int])".to_string(),
                    )),
                }
            }
            "STARTSWITH" => {
                Self::require_args_count(&name_upper, args, 2)?;
                match (&args[0], &args[1]) {
                    (Value::String(s), Value::String(prefix)) => {
                        Ok(Value::Boolean(s.starts_with(prefix.as_str())))
                    }
                    _ => Err(QueryError::Type(
                        "STARTSWITH expects two strings".to_string(),
                    )),
                }
            }
            "ENDSWITH" => {
                Self::require_args_count(&name_upper, args, 2)?;
                match (&args[0], &args[1]) {
                    (Value::String(s), Value::String(suffix)) => {
                        Ok(Value::Boolean(s.ends_with(suffix.as_str())))
                    }
                    _ => Err(QueryError::Type("ENDSWITH expects two strings".to_string())),
                }
            }
            "MAXWIDTH" => Self::maxwidth_on_values(args),
            // Account function used in GROUP BY
            "ACCOUNT_DEPTH" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::String(s) => Ok(Value::Integer(s.matches(':').count() as i64 + 1)),
                    _ => Err(QueryError::Type(
                        "ACCOUNT_DEPTH expects an account string".to_string(),
                    )),
                }
            }
            // Position/amount getters
            "GETITEM" | "GET" => {
                Self::require_args_count(&name_upper, args, 2)?;
                match (&args[0], &args[1]) {
                    // Container lookups delegate to the CANONICAL
                    // `getitem_lookup`, shared with `[...]` subscript
                    // expressions so the two spellings cannot drift
                    // (#1800 review).
                    (container, Value::String(key)) => Self::getitem_lookup(container, key),
                    (Value::Null, _) => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "GETITEM expects (inventory, string), (metadata, string), or (object, string)"
                            .to_string(),
                    )),
                }
            }
            "WEIGHT" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Position(p) => {
                        if let Some(cost) = &p.cost {
                            // `units x per-unit`, normalized (#1963).
                            //
                            // This CANNOT call `rustledger_booking::posting_weight`
                            // like the `weight` COLUMN does: that takes a
                            // `Posting`, whose `CostSpec` still carries the
                            // preserved total for `Total`/`PerUnitFromTotal`,
                            // while a `Position`'s cost is already resolved to a
                            // per-unit `Decimal`. The total is gone by the time
                            // this function sees it, and `evaluate_function_on_values`
                            // receives only `Value`s — no posting to recover it from.
                            //
                            // Recomputing therefore reintroduces exactly the
                            // division-then-multiplication the canonical exists to
                            // avoid (#1106/#1113). `3 HOOL {{100.00 USD}}` resolves
                            // to a per-unit of 33.333..., and multiplying back gave
                            // `100.00000000000000000000000000` where the column
                            // gives `100.00` — the same value with 26 digits of
                            // scale invented by the multiplication.
                            //
                            // The mitigation is deliberately narrow. Normalizing
                            // unconditionally was tried first and is WORSE: it also
                            // strips MEANINGFUL trailing zeros, turning the ordinary
                            // `2 HOOL {5.25 USD}` weight from `10.50` into `10.5`
                            // and regressing the common case to paper over the rare
                            // one. So the strip applies only when the scale is
                            // already past anything a cost is plausibly WRITTEN
                            // with. That is a heuristic, not an invariant:
                            // `rust_decimal` accepts literals out to 28 places, so
                            // a user could author a 13-place cost and see its
                            // weight normalized. No real currency is quoted that
                            // finely, and the alternative — touching every weight —
                            // is the regression described above.
                            //
                            // It does NOT recover the original scale: this yields
                            // `100` where the column yields `100.00`. For
                            // `WEIGHT(position)` that no longer matters — #1966
                            // routes the position COLUMN to the canonical on the
                            // lazy path, where the `Posting` is still in hand, so
                            // it gets the column's exact `100.00`. This arm is
                            // now reached only by arguments the canonical cannot
                            // serve: an `Inventory` from `SUM(position)`, or a
                            // `Position` built by an expression. Neither carries
                            // a price, so the price rung of the weight ladder is
                            // genuinely unavailable here and cost-or-units is the
                            // best answer possible.
                            //
                            // `WEIGHT()` is a rustledger extension — beanquery has
                            // no `weight(position)` function — so there is no
                            // reference implementation to match here, only the
                            // column to stay consistent with.
                            Ok(Value::Amount(position_cost_total(&p.units, cost)?))
                        } else {
                            Ok(Value::Amount(p.units.clone()))
                        }
                    }
                    Value::Amount(a) => Ok(Value::Amount(a.clone())),
                    Value::Inventory(inv) => {
                        let mut result = Inventory::new();
                        for pos in inv.positions() {
                            if let Some(cost) = &pos.cost {
                                result
                                    .add(Position::simple(position_cost_total(&pos.units, cost)?))
                                    .map_err(|e| QueryError::Evaluation(e.to_string()))?;
                            } else {
                                result
                                    .add(Position::simple(pos.units.clone()))
                                    .map_err(|e| QueryError::Evaluation(e.to_string()))?;
                            }
                        }
                        Ok(Value::Inventory(std::sync::Arc::new(result)))
                    }
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "WEIGHT expects a position, amount, or inventory".to_string(),
                    )),
                }
            }
            "DATE" => Self::date_construct_on_values(args),
            "DATE_ADD" => Self::date_add_on_values(args),
            "DATE_TRUNC" => Self::date_trunc_on_values(args),
            "DATE_PART" => Self::date_part_on_values(args),
            "PARSE_DATE" => Self::parse_date_on_values(args),
            "DATE_BIN" => Self::date_bin_on_values(args),
            "INTERVAL" => Self::interval_on_values(args),
            // Date: DATE_DIFF for wrapping aggregates like DATE_DIFF(MAX(date), MIN(date))
            "DATE_DIFF" => {
                Self::require_args_count(&name_upper, args, 2)?;
                match (&args[0], &args[1]) {
                    (Value::Date(d1), Value::Date(d2)) => Ok(Value::Integer(i64::from(
                        d1.since(*d2).unwrap_or_default().get_days(),
                    ))),
                    _ => Err(QueryError::Type("DATE_DIFF expects two dates".to_string())),
                }
            }
            // String: regex functions for wrapping aggregates
            "GREP" => {
                Self::require_args_count(&name_upper, args, 2)?;
                match (&args[0], &args[1]) {
                    (Value::String(pattern), Value::String(s)) => {
                        let re = regex::Regex::new(pattern).map_err(|e| {
                            QueryError::Type(format!("GREP: invalid regex '{pattern}': {e}"))
                        })?;
                        match re.find(s) {
                            Some(m) => Ok(Value::String(m.as_str().to_string())),
                            None => Ok(Value::Null),
                        }
                    }
                    // Null args → Null (e.g., narration is Null for non-transaction entries)
                    (Value::Null, _) | (_, Value::Null) => Ok(Value::Null),
                    _ => Err(QueryError::Type("GREP expects two strings".to_string())),
                }
            }
            "GREPN" => {
                Self::require_args_count(&name_upper, args, 3)?;
                let n = match &args[2] {
                    Value::Integer(i) => (*i).max(0) as usize,
                    Value::Number(n) => {
                        use rust_decimal::prelude::ToPrimitive;
                        n.to_usize().unwrap_or(0)
                    }
                    _ => {
                        return Err(QueryError::Type(
                            "GREPN: third argument must be an integer".to_string(),
                        ));
                    }
                };
                match (&args[0], &args[1]) {
                    (Value::String(pattern), Value::String(s)) => {
                        let re = regex::Regex::new(pattern).map_err(|e| {
                            QueryError::Type(format!("GREPN: invalid regex '{pattern}': {e}"))
                        })?;
                        match re.captures(s) {
                            Some(caps) => match caps.get(n) {
                                Some(m) => Ok(Value::String(m.as_str().to_string())),
                                None => Ok(Value::Null),
                            },
                            None => Ok(Value::Null),
                        }
                    }
                    (Value::Null, _) | (_, Value::Null) => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "GREPN expects (pattern, string, int)".to_string(),
                    )),
                }
            }
            "SUBST" => {
                Self::require_args_count(&name_upper, args, 3)?;
                match (&args[0], &args[1], &args[2]) {
                    (Value::String(pattern), Value::String(replacement), Value::String(s)) => {
                        let re = regex::Regex::new(pattern).map_err(|e| {
                            QueryError::Type(format!("SUBST: invalid regex '{pattern}': {e}"))
                        })?;
                        Ok(Value::String(
                            re.replace_all(s, replacement.as_str()).to_string(),
                        ))
                    }
                    _ => Err(QueryError::Type(
                        "SUBST expects (pattern, replacement, string)".to_string(),
                    )),
                }
            }
            "SPLITCOMP" => {
                Self::require_args_count(&name_upper, args, 3)?;
                let n = match &args[2] {
                    Value::Integer(i) => (*i).max(0) as usize,
                    Value::Number(n) => {
                        use rust_decimal::prelude::ToPrimitive;
                        n.to_usize().unwrap_or(0)
                    }
                    _ => {
                        return Err(QueryError::Type(
                            "SPLITCOMP: third argument must be an integer".to_string(),
                        ));
                    }
                };
                match (&args[0], &args[1]) {
                    (Value::String(s), Value::String(delim)) => {
                        let parts: Vec<&str> = s.split(delim.as_str()).collect();
                        match parts.get(n) {
                            Some(part) => Ok(Value::String((*part).to_string())),
                            None => Ok(Value::Null),
                        }
                    }
                    _ => Err(QueryError::Type(
                        "SPLITCOMP expects (string, delimiter, int)".to_string(),
                    )),
                }
            }
            "JOINSTR" => {
                // Mirror the former lazy `eval_joinstr`: require >=1 argument,
                // SKIP nulls, and stringify every other non-String/Set arg via
                // `value_to_string`, joining with ", " (a comma+space).
                if args.is_empty() {
                    return Err(QueryError::InvalidArguments(
                        "JOINSTR".to_string(),
                        "expected at least 1 argument".to_string(),
                    ));
                }
                let mut parts = Vec::new();
                for v in args {
                    match v {
                        Value::String(s) => parts.push(s.clone()),
                        Value::StringSet(ss) => parts.extend(ss.iter().cloned()),
                        Value::Null => {}
                        other => parts.push(Self::value_to_string(other)),
                    }
                }
                Ok(Value::String(parts.join(", ")))
            }
            // Account metadata functions — look up open/close info
            "OPEN_DATE" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::String(account) => Ok(self
                        .account_info
                        .get(account.as_str())
                        .and_then(|info| info.open_date)
                        .map_or(Value::Null, Value::Date)),
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "OPEN_DATE expects an account string".to_string(),
                    )),
                }
            }
            "CLOSE_DATE" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::String(account) => Ok(self
                        .account_info
                        .get(account.as_str())
                        .and_then(|info| info.close_date)
                        .map_or(Value::Null, Value::Date)),
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "CLOSE_DATE expects an account string".to_string(),
                    )),
                }
            }
            "OPEN_META" => {
                Self::require_args_count(&name_upper, args, 2)?;
                match (&args[0], &args[1]) {
                    (Value::String(account), Value::String(key)) => Ok(self
                        .account_info
                        .get(account.as_str())
                        .and_then(|info| info.open_meta.get(key))
                        .map_or(Value::Null, |mv| Self::meta_value_to_value(Some(mv)))),
                    (Value::Null, _) | (_, Value::Null) => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "OPEN_META expects (account_string, key_string)".to_string(),
                    )),
                }
            }
            // Metadata access — returns Null in evaluate_function_on_values
            // because metadata is accessed via row context in eval_meta_on_table_row.
            // This branch handles edge cases where META is called outside table context.
            "META" | "ENTRY_META" | "ANY_META" | "POSTING_META" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::String(_) | Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(format!(
                        "{name_upper}: argument must be a string key"
                    ))),
                }
            }
            // The currency of an amount. bean-query types this strictly as
            // `commodity(Amount) -> str` and rejects a position, so
            // `commodity(position)` is an error on both sides; the idiomatic
            // spellings are `commodity(units(position))` and
            // `commodity(cost(position))`, both of which yield an Amount.
            "COMMODITY" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Amount(amount) => Ok(Value::String(amount.currency.to_string())),
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type("COMMODITY expects an amount".to_string())),
                }
            }
            // `CURRENCY_META` is beanquery's own alias for `COMMODITY_META`;
            // both resolve against the `commodity` directive. One argument
            // returns the whole metadata map, two return a single key, so a
            // ledger with no matching directive yields Null either way.
            "COMMODITY_META" | "CURRENCY_META" => {
                if args.is_empty() || args.len() > 2 {
                    return Err(QueryError::InvalidArguments(
                        name_upper.clone(),
                        "expected 1 or 2 arguments".to_string(),
                    ));
                }
                let Value::String(currency) = &args[0] else {
                    return match &args[0] {
                        Value::Null => Ok(Value::Null),
                        _ => Err(QueryError::Type(format!(
                            "{name_upper} expects a currency string"
                        ))),
                    };
                };
                let Some(meta) = self.commodity_meta.get(currency.as_str()) else {
                    return Ok(Value::Null);
                };
                if args.len() == 1 {
                    return Ok(Value::Metadata(Box::new(meta.clone())));
                }
                match &args[1] {
                    Value::String(key) => Ok(Self::meta_value_to_value(meta.get(key.as_str()))),
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(format!(
                        "{name_upper}: key must be a string"
                    ))),
                }
            }
            // First element of a string set matching a regex. The set is
            // scanned in its stored order, which for `tags`/`links` is the
            // order the directive declares them, so the answer is stable
            // rather than dependent on set iteration.
            "FINDFIRST" => {
                Self::require_args_count(&name_upper, args, 2)?;
                let (Value::String(pattern), haystack) = (&args[0], &args[1]) else {
                    return match (&args[0], &args[1]) {
                        (Value::Null, _) => Ok(Value::Null),
                        _ => Err(QueryError::Type(
                            "FINDFIRST expects (regex_string, string_set)".to_string(),
                        )),
                    };
                };
                // Borrowed scan: only the matching element is cloned, so a hit
                // on the first tag does not copy the whole set.
                let candidates: &[String] = match haystack {
                    Value::StringSet(items) => items,
                    Value::String(single) => std::slice::from_ref(single),
                    Value::Null => return Ok(Value::Null),
                    _ => {
                        return Err(QueryError::Type(
                            "FINDFIRST expects a string set as its second argument".to_string(),
                        ));
                    }
                };
                let regex = self.require_regex(pattern)?;
                Ok(candidates
                    .iter()
                    .find(|c| regex.is_match(c))
                    .map_or(Value::Null, |c| Value::String(c.clone())))
            }
            // Truncate a date to the first of its month. beanquery returns a
            // date here, not a string, so `yearmonth(date)` stays orderable
            // and comparable against other dates.
            "YEARMONTH" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Date(date) => Ok(Value::Date(
                        rustledger_core::CalendarPeriod::Month.start_of(*date),
                    )),
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type("YEARMONTH expects a date".to_string())),
                }
            }
            // Aggregate functions return Null when evaluated on a single row
            "SUM" | "COUNT" | "MIN" | "MAX" | "FIRST" | "LAST" | "AVG" => Ok(Value::Null),
            _ => Err(QueryError::UnknownFunction(name.to_string())),
        }
    }

    /// Convert a `Metadata` map to a `Value::Object` for table storage.
    fn metadata_to_value(meta: &rustledger_core::Metadata) -> Value {
        // An empty map, NOT Null. bean-query returns `{}` for a directive
        // with no metadata and renders Null as an empty CSV field, so the
        // two are distinguishable there: `meta IS NULL` is false where we
        // used to make it true (#2162).
        // Alphabetical, deliberately NOT bean-query's order. bean-query emits
        // `filename`/`lineno` first and then the user's keys in declaration
        // order; we cannot reproduce either half. `Metadata` is an
        // `FxHashMap`, so declaration order is already lost at parse time,
        // and `Value::Object` is a `BTreeMap`, so the query layer cannot
        // impose an order even if it knew one. Matching would mean an
        // order-preserving map in `rustledger-core`: a new dependency
        // (`indexmap` is not one today) and a changed rkyv layout, since
        // `Metadata` is part of the archived cache payload and rkyv is a
        // default feature -- so a `CACHE_VERSION` bump too. All to change the
        // order keys print in. Measured and declined in #2168.
        //
        // `meta.hash` is NOT at risk, contrary to an earlier draft of this
        // comment: `rustledger-ffi-wasi::hash` sorts the keys itself before
        // hashing, precisely because `Metadata` is a hash map, so the digest
        // is already independent of iteration order.
        //
        // The sort is also what makes `SELECT meta` deterministic at all,
        // given the hash-map source. Same shape as the `#prices` ordering
        // in #2163.
        let map: std::collections::BTreeMap<String, Value> = meta
            .iter()
            .map(|(k, v)| (k.clone(), Self::meta_value_to_value(Some(v))))
            .collect();
        Value::Object(Box::new(map))
    }

    /// Helper to require a specific number of arguments (for pre-evaluated args).
    fn require_args_count(name: &str, args: &[Value], expected: usize) -> Result<(), QueryError> {
        if args.len() != expected {
            return Err(QueryError::InvalidArguments(
                name.to_string(),
                format!("expected {} argument(s), got {}", expected, args.len()),
            ));
        }
        Ok(())
    }

    /// Helper to require a specific number of arguments.
    fn require_args(name: &str, func: &FunctionCall, expected: usize) -> Result<(), QueryError> {
        if func.args.len() != expected {
            return Err(QueryError::InvalidArguments(
                name.to_string(),
                format!("expected {expected} argument(s)"),
            ));
        }
        Ok(())
    }

    /// Convert a value to its market value.
    ///
    /// Shared `VALUE()` implementation used by both expression evaluation and
    /// the aggregate/subquery path in `evaluate_function_on_values`.
    ///
    /// # Arguments
    /// * `val` - The value to convert (`Position`, `Amount`, `Inventory`, or `Null`).
    /// * `explicit_currency` - Optional explicit target currency. When `None`,
    ///   the currency is inferred from the position's cost basis (Python
    ///   beancount compatibility) or falls back to the executor's
    ///   `target_currency` setting.
    /// * `at_date` - Optional valuation date. When `Some`, prices are looked up
    ///   with "on or before" semantics via [`price::PriceDatabase::convert`];
    ///   when `None`, the latest available price is used via
    ///   [`price::PriceDatabase::convert_latest`] (matches Python's
    ///   `value(position)` with `date=None`, which may use a future-dated price).
    ///
    /// # Returns
    /// - `Value::Amount` when conversion succeeds, or when the input is a
    ///   single `Position`/`Amount` that can't be priced (raw units returned).
    /// - `Value::Inventory` when no target currency can be determined and the
    ///   input is an `Inventory`.
    /// - `Value::Null` when the input is null.
    ///
    /// # Inventory caveat
    ///
    /// For `Value::Inventory` inputs with a determined target currency, this
    /// function returns a single `Value::Amount` summed in the target currency.
    /// Positions within the inventory that cannot be priced at `at_date` (or
    /// have no latest price) are silently dropped from the sum. This differs
    /// from Python beancount's `inventory.reduce(get_value, ...)`, which
    /// preserves unpriced positions as raw units in the resulting inventory.
    /// Reconciling this is tracked as a separate follow-up and is out of scope
    /// for #892.
    pub(crate) fn convert_to_market_value(
        &self,
        val: &Value,
        explicit_currency: Option<&str>,
        at_date: Option<NaiveDate>,
    ) -> Result<Value, QueryError> {
        // Column-type stability (#1701): the one-argument form infers the
        // target currency PER ROW (cost currency, else executor default), so
        // an Amount-vs-Inventory return that depends on the row's data makes
        // the column type unstable — the FFI layer declares the type from one
        // row and other rows then contradict it. The rule:
        //   - explicit currency (two-arg form): target is constant across the
        //     query -> Amount for every row (existing behavior, stable);
        //   - one-arg form over an Inventory: ALWAYS return an Inventory
        //     (beanquery parity: value(inventory) is inventory-typed), whether
        //     or not a target currency could be inferred for this row.
        let inventory_stays_inventory = explicit_currency.is_none();
        // Determine target currency:
        // 1. Explicit argument takes precedence
        // 2. Infer from position's cost currency (beancount compatibility)
        // 3. Fall back to executor's target_currency setting
        let target_currency = if let Some(currency) = explicit_currency {
            currency.to_string()
        } else {
            // Try to infer from cost currency
            let inferred = match val {
                Value::Position(p) => p.cost.as_ref().map(|c| c.currency.to_string()),
                Value::Inventory(inv) => inv
                    .positions()
                    .find_map(|p| p.cost.as_ref().map(|c| c.currency.to_string())),
                _ => None,
            };

            match inferred.or_else(|| self.target_currency.clone()) {
                Some(c) => c,
                None => {
                    // No currency can be determined — return value as-is
                    // (matches Python beancount behavior for positions without cost).
                    // Note: `at_date` is ignored here because there is nothing to
                    // convert without a target currency.
                    return match val {
                        Value::Position(p) => Ok(Value::Amount(p.units.clone())),
                        Value::Amount(a) => Ok(Value::Amount(a.clone())),
                        Value::Inventory(inv) => Ok(Value::Inventory(inv.clone())),
                        Value::Null => Ok(Value::Null),
                        _ => Err(QueryError::Type(
                            "VALUE expects a position, amount, or inventory".to_string(),
                        )),
                    };
                }
            }
        };

        // Price lookup matches Python beancount's semantics:
        // - When `at_date` is None, use the latest price (which may be future-dated).
        // - When `at_date` is Some, use the most recent price on or before that date;
        //   if no such price exists, the conversion silently returns the raw units.
        let convert_one = |amount: &Amount| -> Option<Amount> {
            match at_date {
                Some(d) => self.price_db.convert(amount, &target_currency, d),
                None => self.price_db.convert_latest(amount, &target_currency),
            }
        };

        match val {
            Value::Position(p) => {
                if p.units.currency == target_currency {
                    Ok(Value::Amount(p.units.clone()))
                } else if let Some(converted) = convert_one(&p.units) {
                    Ok(Value::Amount(converted))
                } else {
                    Ok(Value::Amount(p.units.clone()))
                }
            }
            Value::Amount(a) => {
                if a.currency == target_currency {
                    Ok(Value::Amount(a.clone()))
                } else if let Some(converted) = convert_one(a) {
                    Ok(Value::Amount(converted))
                } else {
                    Ok(Value::Amount(a.clone()))
                }
            }
            Value::Inventory(inv) => {
                if inventory_stays_inventory {
                    // Convert per position; a position with no available price
                    // keeps its raw units (matching the Position/Amount arms
                    // above and beanquery, which never drops positions).
                    let mut out = rustledger_core::Inventory::new();
                    for pos in inv.positions() {
                        let units = if pos.units.currency == target_currency {
                            pos.units.clone()
                        } else if let Some(converted) = convert_one(&pos.units) {
                            converted
                        } else {
                            pos.units.clone()
                        };
                        out.add(rustledger_core::Position::simple(units))
                            .map_err(|e| QueryError::Evaluation(e.to_string()))?;
                    }
                    return Ok(Value::Inventory(std::sync::Arc::new(out)));
                }
                // Two-arg form: collapse to a single Amount in the explicit
                // target currency. NOTE (pre-existing beanquery divergence,
                // out of #1701's scope): positions with no available price are
                // dropped from the total here; beanquery would keep them as
                // their original units in an Inventory result.
                let mut total = Decimal::ZERO;
                for pos in inv.positions() {
                    if pos.units.currency == target_currency {
                        total += pos.units.number;
                    } else if let Some(converted) = convert_one(&pos.units) {
                        total += converted.number;
                    }
                }
                Ok(Value::Amount(Amount::new(total, &target_currency)))
            }
            Value::Null => Ok(Value::Null),
            _ => Err(QueryError::Type(
                "VALUE expects a position, amount, or inventory".to_string(),
            )),
        }
    }

    /// Check if an expression is a window function.
    pub(super) const fn is_window_expr(expr: &Expr) -> bool {
        matches!(expr, Expr::Window(_))
    }

    /// Resolve column names from targets.
    fn resolve_column_names(&self, targets: &[Target]) -> Result<Vec<String>, QueryError> {
        let mut names = Vec::new();
        for (i, target) in targets.iter().enumerate() {
            if matches!(target.expr, Expr::Wildcard) {
                // Check wildcard BEFORE alias to catch `SELECT * AS alias` edge case
                if target.alias.is_some() {
                    return Err(QueryError::Evaluation(
                        "Cannot alias wildcard (*) - it expands to multiple columns".to_string(),
                    ));
                }
                // Expand wildcard using shared constant (must match evaluate_row expansion)
                names.extend(WILDCARD_COLUMNS.iter().map(|s| (*s).to_string()));
            } else if let Some(alias) = &target.alias {
                // bean-query lowercases the alias too: `AS LatestDate`
                // heads the result `latestdate` (#2164).
                names.push(alias.to_lowercase());
            } else {
                names.push(self.expr_to_name(&target.expr, i));
            }
        }
        Ok(names)
    }

    /// Convert an expression to a column name.
    fn expr_to_name(&self, expr: &Expr, index: usize) -> String {
        match expr {
            Expr::Wildcard => "*".to_string(),
            // bean-query lowercases a bare column reference to the column's
            // own name: `SELECT DATE` heads the result `date`. Scripts that
            // read our CSV by header name otherwise miss the field (#2164).
            Expr::Column(name) => name.to_lowercase(),
            // ...but renders a function target from its source text, case
            // intact: `sum(NUMBER)` stays `sum(NUMBER)`. We emitted just the
            // function name, dropping the arguments, so `SELECT count(date)`
            // headed `count` where bean-query heads `count(date)`.
            Expr::Function(_) => expr.to_string(),
            // Window functions keep the bare name, deliberately NOT the source
            // text the `Function` arm above uses. They are a rustledger
            // extension -- bean-query has no `OVER` -- so there is no rule to
            // match, and `ROW_NUMBER() OVER (PARTITION BY account ORDER BY
            // date)` as a column header helps nobody. Alias it if you want a
            // different name; `AS rn` works.
            Expr::Window(wf) => wf.name.clone(),
            // Postfix accesses name themselves by their source spelling so
            // ORDER BY / PIVOT BY string resolution finds the target (a
            // bare "colN" broke `SELECT entry.narration ORDER BY
            // entry.narration`, #1800 review).
            Expr::Attribute { .. } | Expr::Subscript { .. } => expr.to_string(),
            // Literals and binary/unary expressions still head as `colN`.
            // bean-query names them by printing the expression with MINIMAL
            // parentheses -- `number + 1 * 2` gains none, `(number + 1) * 2`
            // keeps the ones precedence requires, `((number))` collapses to
            // `number`. Our `Display` parenthesizes every binary node, so
            // `expr.to_string()` here yields `(number + 1)` and still would
            // not match. Matching needs a precedence-aware printer, and
            // `Display` is shared with hidden-column naming and error
            // messages, so it cannot simply be changed. Tracked in #2171.
            _ => format!("col{index}"),
        }
    }

    /// Get a built-in system table by name.
    ///
    /// Built-in tables are virtual tables that provide access to ledger data:
    /// - `#prices` / `prices`: Price directives from the ledger
    /// - `#balances` / `balances`: Balance assertion directives from the ledger
    /// - `#commodities` / `commodities`: Commodity directives from the ledger
    /// - `#events` / `events`: Event directives from the ledger
    /// - `#notes` / `notes`: Note directives from the ledger
    /// - `#documents` / `documents`: Document directives from the ledger
    /// - `#accounts` / `accounts`: Open/Close directives paired by account
    /// - `#transactions` / `transactions`: Transaction directives from the ledger
    /// - `#entries` / `entries`: All directives with source location info
    /// - `#postings` / `postings`: All postings from transactions
    ///
    /// Both `#`-prefixed and non-prefixed names are supported for Python beancount
    /// compatibility (issue #632).
    ///
    /// Returns `None` if the table name is not a recognized built-in table.
    pub(super) fn get_builtin_table(&self, table_name: &str, query: &SelectQuery) -> Option<Table> {
        // Normalize table name: strip # prefix if present for Python beancount compatibility.
        // Both "#transactions" (rustledger) and "transactions" (beancount) work.
        // Using strip_prefix avoids allocation in the common case.
        let upper = table_name.to_uppercase();
        let normalized = upper.strip_prefix('#').unwrap_or(&upper);

        match normalized {
            "PRICES" => Some(self.build_prices_table()),
            "BALANCES" => Some(self.build_balances_table()),
            "COMMODITIES" => Some(self.build_commodities_table()),
            "EVENTS" => Some(self.build_events_table()),
            "NOTES" => Some(self.build_notes_table()),
            "DOCUMENTS" => Some(self.build_documents_table()),
            "ACCOUNTS" => Some(self.build_accounts_table()),
            "TRANSACTIONS" => Some(self.build_transactions_table()),
            "ENTRIES" => Some(self.build_entries_table()),
            "POSTINGS" => Some(self.build_postings_table(query)),
            _ => None,
        }
    }
}

/// Walk an [`Expr`] tree, returning `true` if any [`Expr::Column`]
/// references the given column name (case-insensitive).
///
/// Used to decide whether [`Executor::collect_postings`] needs to
/// materialize the per-posting `balance` / `account_balance` snapshots
/// — they're expensive (cumulative `Inventory` clones per posting,
/// the runaway cost in #1080) so we skip the work when no part of the
/// query reads them.
fn expr_references_column(expr: &Expr, name: &str) -> bool {
    match expr {
        Expr::Column(col) => col.eq_ignore_ascii_case(name),
        Expr::Attribute { operand, .. } | Expr::Subscript { operand, .. } => {
            expr_references_column(operand, name)
        }
        Expr::Function(call) => call.args.iter().any(|a| expr_references_column(a, name)),
        Expr::Window(call) => {
            // Function args + the OVER clause's PARTITION BY / ORDER BY
            // expressions all need to be walked — a window function like
            // `SUM(amount) OVER (PARTITION BY balance)` references
            // `balance` in the partition-by, not the function args.
            // Caught by Copilot review on PR #1085.
            call.args.iter().any(|a| expr_references_column(a, name))
                || call
                    .over
                    .partition_by
                    .as_ref()
                    .is_some_and(|ps| ps.iter().any(|p| expr_references_column(p, name)))
                || call
                    .over
                    .order_by
                    .as_ref()
                    .is_some_and(|os| os.iter().any(|o| expr_references_column(&o.expr, name)))
        }
        Expr::BinaryOp(op) => {
            expr_references_column(&op.left, name) || expr_references_column(&op.right, name)
        }
        Expr::UnaryOp(op) => expr_references_column(&op.operand, name),
        Expr::Paren(inner) => expr_references_column(inner, name),
        Expr::Between { value, low, high } => {
            expr_references_column(value, name)
                || expr_references_column(low, name)
                || expr_references_column(high, name)
        }
        Expr::Set(items) => items.iter().any(|i| expr_references_column(i, name)),
        Expr::Wildcard | Expr::Literal(_) => false,
    }
}

/// Which of the expensive per-posting values a scan has to produce.
///
/// Each one is a copy the scan can skip when nothing reads it, and *when* it
/// is read decides how long it must be kept: a value the filter reads can be
/// released once the filter has run, while one the output reads has to survive
/// until the row is rendered. Passed as a struct because six booleans in a row
/// at a call site say nothing about which is which.
#[derive(Debug, Clone, Copy)]
struct ScanNeeds {
    /// The cumulative `balance` column is read somewhere.
    balance: bool,
    /// The `account_balance` column is read somewhere.
    account_balance: bool,
    /// The WHERE clause itself reads `balance`, so it must exist pre-filter.
    where_reads_balance: bool,
    /// The WHERE clause itself reads `account_balance`.
    where_reads_account_balance: bool,
    /// Something other than the WHERE reads `account_balance`, so the snapshot
    /// has to outlive the filter.
    output_reads_account_balance: bool,
}

/// Return `true` if any part of a `SelectQuery` OTHER than its `WHERE` clause
/// references the given column.
///
/// The distinction matters for values that are expensive to keep: a column the
/// filter reads and nothing else can be released as soon as the filter has run,
/// while one the output reads has to survive until the row is rendered.
fn output_references_column(query: &SelectQuery, name: &str) -> bool {
    query
        .targets
        .iter()
        .any(|t| expr_references_column(&t.expr, name))
        || query
            .group_by
            .as_ref()
            .is_some_and(|g| g.iter().any(|e| expr_references_column(e, name)))
        || query
            .having
            .as_ref()
            .is_some_and(|h| expr_references_column(h, name))
        || query
            .pivot_by
            .as_ref()
            .is_some_and(|p| p.iter().any(|e| expr_references_column(e, name)))
        || query
            .order_by
            .as_ref()
            .is_some_and(|o| o.iter().any(|s| expr_references_column(&s.expr, name)))
}

/// Return `true` if any part of a `SelectQuery` references the given
/// column. Walks SELECT targets, WHERE, GROUP BY, HAVING, PIVOT BY,
/// ORDER BY, and the FROM filter expression. A subquery in FROM is
/// treated as opaque — its inner references don't surface to the
/// outer query's posting iterator.
fn query_references_column(query: &SelectQuery, name: &str) -> bool {
    if query
        .targets
        .iter()
        .any(|t| expr_references_column(&t.expr, name))
    {
        return true;
    }
    if let Some(w) = &query.where_clause
        && expr_references_column(w, name)
    {
        return true;
    }
    if let Some(g) = &query.group_by
        && g.iter().any(|e| expr_references_column(e, name))
    {
        return true;
    }
    if let Some(h) = &query.having
        && expr_references_column(h, name)
    {
        return true;
    }
    if let Some(p) = &query.pivot_by
        && p.iter().any(|e| expr_references_column(e, name))
    {
        return true;
    }
    if let Some(o) = &query.order_by
        && o.iter().any(|s| expr_references_column(&s.expr, name))
    {
        return true;
    }
    if let Some(from) = &query.from
        && let Some(f) = &from.filter
        && expr_references_column(f, name)
    {
        return true;
    }
    false
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod dual_eval_parity;
