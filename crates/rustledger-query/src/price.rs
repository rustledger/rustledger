//! Price database for currency conversions.
//!
//! This module provides a price database that stores historical prices
//! and allows looking up prices for currency conversions.

use rust_decimal::Decimal;
use rustc_hash::FxHashMap as HashMap;
use rustledger_core::{Amount, Directive, NaiveDate, Price as PriceDirective, Transaction};

/// A price entry.
///
/// Marked `#[non_exhaustive]` so future provenance/metadata fields can
/// be added without breaking downstream struct-literal construction.
/// Internal construction in this module isn't restricted.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct PriceEntry {
    /// Date of the price.
    pub date: NaiveDate,
    /// Price amount.
    pub price: Decimal,
    /// Quote currency.
    pub currency: rustledger_core::Currency,
    /// `true` if sourced from an explicit `Price` directive (or a
    /// plugin-emitted one — same shape after plugin runs); `false` if
    /// derived from a transaction posting in the executor's pass-2
    /// fallback. The `#prices` BQL table filters to `explicit: true`
    /// to match `bean-query`, which only surfaces explicit Price
    /// directives. Internal price lookups (`get_price`, `getprice()`
    /// BQL function) still see all entries — that preserves the
    /// rustledger UX extension where `VALUE()` works without the
    /// `implicit_prices` plugin being declared (issues #567, #593).
    pub explicit: bool,
}

/// Database of currency prices.
///
/// Two structures with distinct jobs, mirroring Python beancount's
/// split between Price *directives* and the *price map* built from
/// them:
///
/// - `prices` — the raw provenance store: every entry as declared (or
///   extracted from a transaction), with its `explicit` flag. Feeds
///   the `#prices` BQL table, `len()`, and the two-pass dedup gating
///   (#1006). Never mirrored or deduplicated.
/// - `lookup` — the conversion index every price lookup reads, built
///   from the raw entries by a faithful port of beancount's
///   `build_price_map` merge (see `rebuild_lookup`). Both
///   directions of every pair are materialized, so lookups pick the
///   most recent rate *regardless of which direction it was written
///   in* (issue #1759 — an older direct rate must not shadow a newer
///   inverse one).
#[derive(Debug, Default)]
pub struct PriceDatabase {
    /// Prices indexed by base currency.
    /// Each base currency maps to a list of price entries sorted by date.
    prices: HashMap<rustledger_core::Currency, Vec<PriceEntry>>,
    /// Every raw entry in insertion (ledger) order. The lookup-index
    /// build consumes this instead of `prices`: beancount's merge
    /// tie-breaks depend on Python dict insertion order, which a hash
    /// map cannot preserve.
    raw_seq: Vec<RawPrice>,
    /// The conversion index: base → quote → date-sorted rates, one
    /// rate per date, both directions of every pair present. Rebuilt
    /// by [`Self::sort_prices`].
    lookup: HashMap<
        rustledger_core::Currency,
        HashMap<rustledger_core::Currency, Vec<(NaiveDate, Decimal)>>,
    >,
}

/// One raw price observation in ledger order — input to the
/// conversion-index build.
#[derive(Debug, Clone)]
struct RawPrice {
    base: rustledger_core::Currency,
    quote: rustledger_core::Currency,
    date: NaiveDate,
    rate: Decimal,
}

/// The [`PriceDatabase`] → [`PriceOracle`](rustledger_returns::PriceOracle)
/// adapter returned by [`PriceDatabase::as_oracle`].
///
/// A pure pass-through to [`PriceDatabase::convert`] — the codebase's single
/// such adapter (the CLI's `report returns`, the component's `session.returns`,
/// and the shared `crate::returns` helpers all reach the returns engine through
/// it).
pub struct PriceDbOracle<'a>(&'a PriceDatabase);

impl rustledger_returns::PriceOracle for PriceDbOracle<'_> {
    fn convert(&self, amount: &Amount, to_currency: &str, date: NaiveDate) -> Option<Amount> {
        self.0.convert(amount, to_currency, date)
    }
}

impl PriceDatabase {
    /// Create a new empty price database.
    pub fn new() -> Self {
        Self {
            prices: HashMap::default(),
            raw_seq: Vec::new(),
            lookup: HashMap::default(),
        }
    }

    /// Build a price database from directives.
    ///
    /// Two passes:
    /// 1. **Explicit `Price` directives** — added unconditionally.
    /// 2. **Implicit prices from transaction postings** — added only
    ///    for `(base, quote, date)` tuples that don't already have an
    ///    explicit Price entry from pass 1.
    ///
    /// The two-pass design fixes issue #1006: when the user enables
    /// the `implicit_prices` plugin, it emits `Price` directives for
    /// each priced posting; pass 1 picks those up. Pre-fix, pass 2
    /// would then ALSO walk the same transactions and re-emit the
    /// same implicit prices, doubling every entry. Now pass 2 sees
    /// the explicit entry already exists and skips, so the plugin's
    /// output is the single source of truth.
    ///
    /// When the plugin is NOT enabled (the rustledger-extension case
    /// from #567 / #593 — `VALUE()` should work on implicit-priced
    /// transactions automatically), pass 1 adds nothing for those
    /// dates and pass 2 fills them in. Net effect: implicit prices
    /// are reachable from BQL without requiring the user to wire up
    /// a plugin, but never doubled when the plugin IS wired up.
    ///
    /// **Behavior note**: an explicit `Price` directive *suppresses*
    /// any divergent transaction-derived implicit price on the same
    /// `(base, quote, date)`. This is intentional — explicit Price is
    /// authoritative — but a behavior change vs pre-#1015, where a
    /// user-written `2024-01-15 price ABC 1.40 EUR` plus a transaction
    /// emitting ABC@EUR with a different value on the same date would
    /// have stored both. Now only the explicit value survives. In
    /// practice this only surfaces with hand-authored conflicts.
    ///
    /// **Provenance tagging** (issue #1048): each entry stores
    /// `explicit: bool`. Pass-1 entries are `true`, pass-2
    /// transaction-derived entries are `false`. The `#prices` BQL
    /// table filters to `explicit: true` via `iter_explicit_entries`
    /// to match `bean-query`, which only surfaces real `Price`
    /// directives. Internal `get_price` / `convert` lookups see
    /// both kinds — that's how `VALUE()` keeps working without the
    /// `implicit_prices` plugin being declared.
    pub fn from_directives(directives: &[Directive]) -> Self {
        let mut db = Self::new();

        // Pass 1: explicit Price directives.
        for directive in directives {
            if let Directive::Price(price) = directive {
                db.add_price(price);
            }
        }

        // Snapshot the explicit `(base, quote, date)` tuples — pass 2
        // skips any transaction-derived price that would land on one
        // of these (the plugin already filled it in via pass 1).
        let explicit = db.snapshot_keys();

        // Pass 2: implicit prices from transactions, gated on the
        // explicit set.
        for directive in directives {
            if let Directive::Transaction(txn) = directive {
                db.add_implicit_prices_from_transaction(txn, &explicit);
            }
        }

        // Sort all price lists by date
        db.sort_prices();

        db
    }

    /// Sort all price entries by date and rebuild the conversion
    /// index.
    ///
    /// Call this after adding prices to ensure lookups work correctly.
    pub fn sort_prices(&mut self) {
        for entries in self.prices.values_mut() {
            entries.sort_by_key(|e| e.date);
        }
        self.rebuild_lookup();
    }

    /// Rebuild the conversion index from the raw entries.
    ///
    /// A faithful port of Python beancount's `build_price_map` merge
    /// (`beancount/core/prices.py`), whose observable semantics are
    /// emergent from the build order and cannot be reproduced by
    /// per-lookup rules (issue #1759):
    ///
    /// 1. Group raw entries per `(base, quote)` pair, preserving
    ///    first-seen pair order and per-pair entry order (Python
    ///    dicts are insertion-ordered; the tie-breaks below depend
    ///    on it).
    /// 2. When both directions of a pair exist, invert the one with
    ///    fewer rates and merge it into the other ("swallow"). Zero
    ///    rates are dropped on inversion (zero-cost postings, e.g.
    ///    gifted options). On equal counts Python removes
    ///    `(quote, base)`, keeping whichever direction is reached
    ///    first in insertion order.
    /// 3. Sort each pair's list by date (stable, so same-date order
    ///    stays originals-then-inverted) and collapse to one rate per
    ///    date keeping the LAST — Python's
    ///    `sorted_uniquify(..., last=True)`.
    /// 4. Materialize the inverse of every surviving pair, so the
    ///    index is direction-blind at lookup time.
    fn rebuild_lookup(&mut self) {
        type Pair = (rustledger_core::Currency, rustledger_core::Currency);

        // Step 1: group per pair in insertion order.
        let mut order: Vec<Pair> = Vec::new();
        let mut index: HashMap<Pair, usize> = HashMap::default();
        let mut lists: Vec<Option<Vec<(NaiveDate, Decimal)>>> = Vec::new();
        for raw in &self.raw_seq {
            let key = (raw.base.clone(), raw.quote.clone());
            let i = *index.entry(key.clone()).or_insert_with(|| {
                order.push(key);
                lists.push(Some(Vec::new()));
                lists.len() - 1
            });
            if let Some(list) = &mut lists[i] {
                list.push((raw.date, raw.rate));
            }
        }

        // Step 2: swallow the direction with fewer rates.
        for i in 0..order.len() {
            let inv_key = (order[i].1.clone(), order[i].0.clone());
            let Some(&j) = index.get(&inv_key) else {
                continue;
            };
            if lists[i].is_none() || lists[j].is_none() {
                // Already swallowed when its inverse was visited —
                // matches Python's second visit being a no-op.
                continue;
            }
            let len_i = lists[i].as_ref().map_or(0, Vec::len);
            let len_j = lists[j].as_ref().map_or(0, Vec::len);
            let (keep, remove) = if len_i < len_j { (j, i) } else { (i, j) };
            let removed = lists[remove].take().unwrap_or_default();
            if let Some(target) = lists[keep].as_mut() {
                target.extend(
                    removed
                        .iter()
                        .filter(|(_, rate)| !rate.is_zero())
                        .map(|&(d, rate)| (d, Decimal::ONE / rate)),
                );
            }
        }

        // Step 3: stable date sort + one rate per date (last wins).
        let mut merged: Vec<(Pair, Vec<(NaiveDate, Decimal)>)> = Vec::new();
        for (i, key) in order.into_iter().enumerate() {
            let Some(mut list) = lists[i].take() else {
                continue;
            };
            list.sort_by_key(|entry| entry.0);
            let mut deduped: Vec<(NaiveDate, Decimal)> = Vec::with_capacity(list.len());
            for (d, rate) in list {
                match deduped.last_mut() {
                    Some(last) if last.0 == d => last.1 = rate,
                    _ => deduped.push((d, rate)),
                }
            }
            merged.push((key, deduped));
        }

        // Step 4: materialize all inverses. After step 2 at most one
        // direction per pair survives, so these inserts cannot
        // collide with a surviving forward list.
        self.lookup = HashMap::default();
        for ((base, quote), list) in merged {
            let inverted: Vec<(NaiveDate, Decimal)> = list
                .iter()
                .filter(|(_, rate)| !rate.is_zero())
                .map(|&(d, rate)| (d, Decimal::ONE / rate))
                .collect();
            self.lookup
                .entry(quote.clone())
                .or_default()
                .insert(base.clone(), inverted);
            self.lookup.entry(base).or_default().insert(quote, list);
        }
    }

    /// Add a price directive to the database.
    ///
    /// Marks the entry as `explicit: true` — these entries surface in
    /// the `#prices` BQL table.
    pub fn add_price(&mut self, price: &PriceDirective) {
        let entry = PriceEntry {
            date: price.date,
            price: price.amount.number,
            currency: price.amount.currency.clone(),
            explicit: true,
        };

        self.raw_seq.push(RawPrice {
            base: price.currency.clone(),
            quote: price.amount.currency.clone(),
            date: price.date,
            rate: price.amount.number,
        });
        self.prices
            .entry(price.currency.clone())
            .or_default()
            .push(entry);
    }

    /// Snapshot every `(base, quote, date)` tuple currently in the
    /// database. **Internal helper for the two-pass build only** —
    /// the result reflects whatever is in the DB at the moment of the
    /// call; it is "explicit" only because callers invoke it after
    /// pass 1 (which adds explicit `Price` directives) and before
    /// pass 2 (which adds transaction-derived implicit prices). See
    /// [`from_directives`] for the protocol.
    pub(crate) fn snapshot_keys(
        &self,
    ) -> std::collections::HashSet<(
        rustledger_core::Currency,
        rustledger_core::Currency,
        NaiveDate,
    )> {
        self.prices
            .iter()
            .flat_map(|(base, entries)| {
                let base = base.clone();
                entries
                    .iter()
                    .map(move |e| (base.clone(), e.currency.clone(), e.date))
            })
            .collect()
    }

    /// Add implicit prices from a transaction's postings, skipping
    /// any `(base, quote, date)` tuple already present in `explicit`.
    ///
    /// Delegates per-posting price math to
    /// [`rustledger_core::extract_per_unit_price`] — the same helper
    /// used by the native `implicit_prices` plugin
    /// (`rustledger_plugin::native::plugins::implicit_prices`), so the
    /// numeric output of both paths stays in sync (issue #992 was the
    /// pre-shared-helper version where they drifted on `@@` handling).
    ///
    /// The `explicit` parameter is the set of `(base, quote, date)`
    /// tuples already supplied by explicit `Price` directives. When
    /// the `implicit_prices` plugin runs, it emits Price directives
    /// for each priced posting, populating this set; pass 2 then
    /// skips those tuples to avoid the duplication described in
    /// issue #1006.
    pub(crate) fn add_implicit_prices_from_transaction(
        &mut self,
        txn: &Transaction,
        explicit: &std::collections::HashSet<(
            rustledger_core::Currency,
            rustledger_core::Currency,
            NaiveDate,
        )>,
    ) {
        for posting in &txn.postings {
            let Some(units) = posting.amount() else {
                continue;
            };

            // Build the helper's annotation descriptor only when both
            // an amount and currency are available; the helper pairs
            // the returned per-unit value with the matching currency
            // by construction.
            let annotation = posting.price.as_deref().and_then(|annotation| {
                let amount = annotation.amount()?;
                Some((
                    !annotation.is_unit(),
                    amount.number,
                    amount.currency.clone(),
                ))
            });
            let cost = posting.cost.as_deref().and_then(|c| {
                let currency = c.currency.clone()?;
                Some((c.number, currency))
            });

            let Some((per_unit, quote)) =
                rustledger_core::extract_per_unit_price(units.number, annotation, cost)
            else {
                continue;
            };

            // Skip if an explicit Price directive already covers this
            // (base, quote, date) tuple — the plugin's emission is
            // authoritative and pass 2 must not duplicate.
            if explicit.contains(&(units.currency.clone(), quote.clone(), txn.date)) {
                continue;
            }

            self.add_implicit_price(txn.date, &units.currency, per_unit, &quote);
        }
    }

    /// Add an implicit price entry.
    ///
    /// Marks the entry as `explicit: false` — internal lookups still
    /// see it, but the `#prices` BQL table hides it (matches
    /// bean-query, which only shows explicit Price directives).
    fn add_implicit_price(
        &mut self,
        date: NaiveDate,
        base_currency: &rustledger_core::Currency,
        price: Decimal,
        quote_currency: &rustledger_core::Currency,
    ) {
        let entry = PriceEntry {
            date,
            price,
            currency: quote_currency.clone(),
            explicit: false,
        };

        self.raw_seq.push(RawPrice {
            base: base_currency.clone(),
            quote: quote_currency.clone(),
            date,
            rate: price,
        });
        self.prices
            .entry(base_currency.clone())
            .or_default()
            .push(entry);
    }

    /// Get the price of a currency on or before a given date.
    ///
    /// Returns the most recent rate for the pair from the conversion
    /// index — which holds both directions of every pair, so a rate
    /// declared as `quote → base` is found (inverted) exactly like a
    /// direct one, with date recency deciding between them (#1759).
    /// Falls back to a chained lookup (A→B→C) when the pair has no
    /// rates at all.
    pub fn get_price(&self, base: &str, quote: &str, date: NaiveDate) -> Option<Decimal> {
        // Same currency = price of 1
        if base == quote {
            return Some(Decimal::ONE);
        }

        if let Some(rate) = self.lookup_rate_at(base, quote, date) {
            return Some(rate);
        }

        // Try chained lookup (A→B→C where B is an intermediate currency)
        self.get_chained_price(base, quote, date)
    }

    /// Most recent rate for the pair on or before `date`, from the
    /// conversion index.
    fn lookup_rate_at(&self, base: &str, quote: &str, date: NaiveDate) -> Option<Decimal> {
        let list = self.lookup.get(base)?.get(quote)?;
        let idx = list.partition_point(|entry| entry.0 <= date);
        (idx > 0).then(|| list[idx - 1].1)
    }

    /// Most recent (date, rate) for the pair on or before `date`.
    ///
    /// Same lookup as [`Self::lookup_rate_at`], returning the date too. The
    /// chained path ranking needs it: how good a chain is depends on when its
    /// legs were quoted, not only on what they were quoted at.
    fn lookup_dated_at(
        &self,
        base: &str,
        quote: &str,
        date: NaiveDate,
    ) -> Option<(NaiveDate, Decimal)> {
        let list = self.lookup.get(base)?.get(quote)?;
        let idx = list.partition_point(|entry| entry.0 <= date);
        (idx > 0).then(|| list[idx - 1])
    }

    /// Latest (date, rate) for the pair.
    fn lookup_dated_latest(&self, base: &str, quote: &str) -> Option<(NaiveDate, Decimal)> {
        self.lookup.get(base)?.get(quote)?.last().copied()
    }

    /// Latest rate for the pair, from the conversion index.
    fn lookup_rate_latest(&self, base: &str, quote: &str) -> Option<Decimal> {
        self.lookup
            .get(base)?
            .get(quote)?
            .last()
            .map(|entry| entry.1)
    }

    /// Try to find a price through an intermediate currency.
    /// For A→C, try to find A→B and B→C for some intermediate B.
    ///
    /// This is a rustledger extension — beancount's price map has no
    /// transitive lookups, and answers an unreachable pair by leaving the
    /// amount unconverted. One hop only; both legs read the bidirectional
    /// index, so no per-leg inverse handling is needed.
    ///
    /// Path selection and the stale-chain policy are described on
    /// [`Self::best_chain`], which both chained lookups share.
    fn get_chained_price(&self, base: &str, quote: &str, date: NaiveDate) -> Option<Decimal> {
        self.best_chain(base, quote, |b, q| self.lookup_dated_at(b, q, date))
    }

    /// Shared body of both chained lookups.
    ///
    /// Both legs are dated the same way the caller asks for, so a leg that is
    /// merely NEWER than the other is fine: valuing a 07-10 stock close with
    /// an 07-11 exchange rate is ordinary, and refusing it would be stricter
    /// than any comparable tool.
    ///
    /// Paths are ranked by the evidence behind them rather than by spelling.
    /// A chain is only as current as its OLDEST leg -- multiplying a 2010
    /// `A -> B` by a 2024 `B -> C` yields a figure that looks 2024-dated but
    /// rests on 2010 data -- so the path whose oldest leg is most recent wins,
    /// then the one whose legs sit closest together, then the currency name so
    /// the order stays total and stable.
    ///
    /// This replaced a purely alphabetical tie-break. That rule reached only
    /// two pairs in the whole corpus, but it reached them for no reason: the
    /// real case is BTC to CNY routed via USD or USDT, where the answers
    /// differ by 68% purely because one route's quotes stop 16 months
    /// earlier, and `USD` happened to sort ahead of `USDT`.
    ///
    /// This does not make a stale chain unavailable, and deliberately so: a
    /// stale DIRECT price is returned without complaint too, so refusing only
    /// the chained case would be an inconsistent rule rather than a stricter
    /// one. Staleness as such is #2152.
    fn best_chain<F>(&self, base: &str, quote: &str, first_leg: F) -> Option<Decimal>
    where
        F: Fn(&str, &str) -> Option<(NaiveDate, Decimal)>,
    {
        let inner = self.lookup.get(base)?;
        let mut intermediates: Vec<&rustledger_core::Currency> = inner.keys().collect();
        intermediates.sort_unstable_by_key(|c| c.as_str());

        let mut best: Option<(std::cmp::Reverse<NaiveDate>, i64, &str, Decimal)> = None;
        for intermediate in intermediates {
            if intermediate.as_str() == quote {
                continue; // Already tried direct
            }
            let Some((leg1_date, rate1)) = first_leg(base, intermediate.as_str()) else {
                continue;
            };
            let Some((leg2_date, rate2)) = first_leg(intermediate.as_str(), quote) else {
                continue;
            };
            // The chain is only as current as its oldest leg.
            let effective = leg1_date.min(leg2_date);
            let gap = i64::from((leg1_date - leg2_date).get_days().abs());
            let candidate = (
                std::cmp::Reverse(effective),
                gap,
                intermediate.as_str(),
                rate1 * rate2,
            );
            let better = best.as_ref().is_none_or(|current| {
                (candidate.0, candidate.1, candidate.2) < (current.0, current.1, current.2)
            });
            if better {
                best = Some(candidate);
            }
        }
        best.map(|(_, _, _, rate)| rate)
    }

    /// Get the latest price of a currency (most recent date).
    ///
    /// Same direction-blind semantics as [`Self::get_price`], using
    /// each pair's most recent rate.
    pub fn get_latest_price(&self, base: &str, quote: &str) -> Option<Decimal> {
        // Same currency = price of 1
        if base == quote {
            return Some(Decimal::ONE);
        }

        if let Some(rate) = self.lookup_rate_latest(base, quote) {
            return Some(rate);
        }

        // Try chained lookup (A→B→C where B is an intermediate currency)
        self.get_chained_latest_price(base, quote)
    }

    /// Latest-rate variant of [`Self::get_chained_price`].
    fn get_chained_latest_price(&self, base: &str, quote: &str) -> Option<Decimal> {
        self.best_chain(base, quote, |b, q| self.lookup_dated_latest(b, q))
    }

    /// Convert an amount to a target currency.
    ///
    /// Returns the converted amount, or `None` if no price is available — or
    /// if the converted value would leave `rust_decimal`'s range (#1863).
    /// Both callers already keep the raw units when this returns `None`, which
    /// is the right answer for an unrepresentable conversion too: showing the
    /// original amount is honest, showing a clamped one is not.
    pub fn convert(&self, amount: &Amount, to_currency: &str, date: NaiveDate) -> Option<Amount> {
        if amount.currency == to_currency {
            return Some(amount.clone());
        }

        self.get_price(&amount.currency, to_currency, date)
            .and_then(|price| amount.number.checked_mul(price))
            .map(|n| Amount::new(n, to_currency))
    }

    /// Adapt this price index to the returns engine's
    /// [`PriceOracle`](rustledger_returns::PriceOracle) trait.
    ///
    /// The single `PriceDatabase` → `PriceOracle` bridge in the codebase, so
    /// `rustledger-returns` stays a leaf (it reaches prices only through the
    /// trait) and no consumer re-derives the adapter. Used by
    /// [`crate::returns::scope_returns`] / [`crate::returns::scopes_returns`] and
    /// the CLI/component returns paths.
    #[must_use]
    pub const fn as_oracle(&self) -> PriceDbOracle<'_> {
        PriceDbOracle(self)
    }

    /// Convert an amount using the latest available price.
    ///
    /// `None` on no price OR on an unrepresentable product — see
    /// [`Self::convert`] for why those share a return value.
    pub fn convert_latest(&self, amount: &Amount, to_currency: &str) -> Option<Amount> {
        if amount.currency == to_currency {
            return Some(amount.clone());
        }

        self.get_latest_price(&amount.currency, to_currency)
            .and_then(|price| amount.number.checked_mul(price))
            .map(|n| Amount::new(n, to_currency))
    }

    /// Get all currencies that have prices defined.
    pub fn currencies(&self) -> impl Iterator<Item = &str> {
        self.prices.keys().map(rustledger_core::Currency::as_str)
    }

    /// Check if a currency has any prices defined.
    pub fn has_prices(&self, currency: &str) -> bool {
        self.prices.contains_key(currency)
    }

    /// Get the number of price entries.
    pub fn len(&self) -> usize {
        self.prices.values().map(Vec::len).sum()
    }

    /// Check if the database is empty.
    pub fn is_empty(&self) -> bool {
        self.prices.is_empty()
    }

    /// Iterate over explicit price entries only — those sourced from
    /// `Price` directives (either user-written or plugin-emitted).
    /// Excludes transaction-derived entries added by the executor's
    /// pass-2 fallback. Used by the `#prices` BQL table to match
    /// `bean-query`'s behavior.
    ///
    /// For internal price *lookups* (e.g. `VALUE()`, `getprice()`),
    /// use `get_price` / `convert` / `convert_latest` — those walk
    /// the underlying entries without filtering, which preserves the
    /// rustledger UX extension where implicit prices are usable for
    /// conversion without declaring the `implicit_prices` plugin.
    pub fn iter_explicit_entries(&self) -> impl Iterator<Item = (&str, NaiveDate, Decimal, &str)> {
        self.prices.iter().flat_map(|(base, entries)| {
            entries
                .iter()
                .filter(|e| e.explicit)
                .map(move |e| (base.as_str(), e.date, e.price, e.currency.as_str()))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;

    fn date(y: i32, m: u32, d: u32) -> NaiveDate {
        rustledger_core::naive_date(y, m, d).unwrap()
    }

    #[test]
    fn test_price_lookup() {
        let mut db = PriceDatabase::new();

        // Add some prices
        db.add_price(&PriceDirective {
            date: date(2024, 1, 1),
            currency: "AAPL".into(),
            amount: Amount::new(dec!(150.00), "USD"),
            meta: Default::default(),
        });

        db.add_price(&PriceDirective {
            date: date(2024, 6, 1),
            currency: "AAPL".into(),
            amount: Amount::new(dec!(180.00), "USD"),
            meta: Default::default(),
        });

        // Sort after adding
        db.sort_prices();

        // Lookup on exact date
        assert_eq!(
            db.get_price("AAPL", "USD", date(2024, 1, 1)),
            Some(dec!(150.00))
        );

        // Lookup on later date gets most recent
        assert_eq!(
            db.get_price("AAPL", "USD", date(2024, 6, 15)),
            Some(dec!(180.00))
        );

        // Lookup between dates gets earlier price
        assert_eq!(
            db.get_price("AAPL", "USD", date(2024, 3, 15)),
            Some(dec!(150.00))
        );

        // Lookup before any price returns None
        assert_eq!(db.get_price("AAPL", "USD", date(2023, 12, 31)), None);
    }

    #[test]
    fn test_inverse_price() {
        let mut db = PriceDatabase::new();

        // Add USD in terms of EUR
        db.add_price(&PriceDirective {
            date: date(2024, 1, 1),
            currency: "USD".into(),
            amount: Amount::new(dec!(0.92), "EUR"),
            meta: Default::default(),
        });

        // Sort
        db.sort_prices();

        // Can lookup USD->EUR
        assert_eq!(
            db.get_price("USD", "EUR", date(2024, 1, 1)),
            Some(dec!(0.92))
        );

        // Can lookup EUR->USD via inverse
        let inverse = db.get_price("EUR", "USD", date(2024, 1, 1)).unwrap();
        // 1/0.92 ≈ 1.087
        assert!(inverse > dec!(1.08) && inverse < dec!(1.09));
    }

    #[test]
    fn test_convert() {
        let mut db = PriceDatabase::new();

        db.add_price(&PriceDirective {
            date: date(2024, 1, 1),
            currency: "AAPL".into(),
            amount: Amount::new(dec!(150.00), "USD"),
            meta: Default::default(),
        });

        db.sort_prices();

        let shares = Amount::new(dec!(10), "AAPL");
        let usd = db.convert(&shares, "USD", date(2024, 1, 1)).unwrap();

        assert_eq!(usd.number, dec!(1500.00));
        assert_eq!(usd.currency, "USD");
    }

    #[test]
    fn test_same_currency_convert() {
        let db = PriceDatabase::new();
        let amount = Amount::new(dec!(100), "USD");

        let result = db.convert(&amount, "USD", date(2024, 1, 1)).unwrap();
        assert_eq!(result.number, dec!(100));
        assert_eq!(result.currency, "USD");
    }

    #[test]
    fn test_from_directives() {
        let directives = vec![
            Directive::Price(PriceDirective {
                date: date(2024, 1, 1),
                currency: "AAPL".into(),
                amount: Amount::new(dec!(150.00), "USD"),
                meta: Default::default(),
            }),
            Directive::Price(PriceDirective {
                date: date(2024, 1, 1),
                currency: "EUR".into(),
                amount: Amount::new(dec!(1.10), "USD"),
                meta: Default::default(),
            }),
        ];

        let db = PriceDatabase::from_directives(&directives);

        assert_eq!(db.len(), 2);
        assert!(db.has_prices("AAPL"));
        assert!(db.has_prices("EUR"));
    }

    #[test]
    fn test_chained_price_lookup() {
        let mut db = PriceDatabase::new();

        // Add AAPL -> USD price
        db.add_price(&PriceDirective {
            date: date(2024, 1, 1),
            currency: "AAPL".into(),
            amount: Amount::new(dec!(150.00), "USD"),
            meta: Default::default(),
        });

        // Add USD -> EUR price
        db.add_price(&PriceDirective {
            date: date(2024, 1, 1),
            currency: "USD".into(),
            amount: Amount::new(dec!(0.92), "EUR"),
            meta: Default::default(),
        });

        // Sort
        db.sort_prices();

        // Direct lookup AAPL -> USD works
        assert_eq!(
            db.get_price("AAPL", "USD", date(2024, 1, 1)),
            Some(dec!(150.00))
        );

        // Direct lookup USD -> EUR works
        assert_eq!(
            db.get_price("USD", "EUR", date(2024, 1, 1)),
            Some(dec!(0.92))
        );

        // Chained lookup AAPL -> EUR should work (AAPL -> USD -> EUR)
        // 150 USD * 0.92 EUR/USD = 138 EUR
        let chained = db.get_price("AAPL", "EUR", date(2024, 1, 1)).unwrap();
        assert_eq!(chained, dec!(138.00));
    }

    #[test]
    fn test_chained_price_with_inverse() {
        let mut db = PriceDatabase::new();

        // Add BTC -> USD price
        db.add_price(&PriceDirective {
            date: date(2024, 1, 1),
            currency: "BTC".into(),
            amount: Amount::new(dec!(40000.00), "USD"),
            meta: Default::default(),
        });

        // Add EUR -> USD price (inverse of what we need for USD -> EUR)
        db.add_price(&PriceDirective {
            date: date(2024, 1, 1),
            currency: "EUR".into(),
            amount: Amount::new(dec!(1.10), "USD"),
            meta: Default::default(),
        });

        // Sort
        db.sort_prices();

        // BTC -> EUR should work via BTC -> USD -> EUR
        // BTC -> USD = 40000
        // USD -> EUR = 1/1.10 ≈ 0.909
        // BTC -> EUR = 40000 / 1.10 ≈ 36363.63
        let chained = db.get_price("BTC", "EUR", date(2024, 1, 1)).unwrap();
        // 40000 / 1.10 = 36363.636363...
        assert!(chained > dec!(36363) && chained < dec!(36364));
    }

    /// When several one-hop paths exist, the best-supported one wins, and it
    /// is the same one every run.
    ///
    /// The three tests around this one each build a single chain, so nothing
    /// pinned the multi-path behavior: the ranking could have been dropped in
    /// a refactor and they would all still pass (#2152).
    ///
    /// Two properties, in order of what matters. First, a chain is only as
    /// current as its OLDEST leg, so the path resting on more recent data
    /// wins even when the other sorts first alphabetically -- this is the case
    /// that used to go the wrong way. Second, when the evidence is equally
    /// good the currency name breaks the tie, which is what keeps the answer
    /// repeatable rather than dependent on hash-map order.
    #[test]
    fn chained_price_prefers_the_better_supported_path() {
        // AAAA sorts first but its data stops in 2019; ZZZZ sorts last and is
        // current. Modeled on ledger_prices.beancount, where the real BTC to
        // CNY pair has exactly this shape and the two answers differ by 68%.
        let stale_vs_fresh = || {
            let mut db = PriceDatabase::new();
            db.add_price(&price(date(2019, 7, 16), "XCOIN", dec!(10757.30), "AAAA"));
            db.add_price(&price(date(2019, 7, 16), "AAAA", dec!(6.95), "CNY"));
            db.add_price(&price(date(2020, 11, 24), "XCOIN", dec!(19107.45), "ZZZZ"));
            db.add_price(&price(date(2020, 11, 24), "ZZZZ", dec!(6.5868), "CNY"));
            db.sort_prices();
            db
        };
        let db = stale_vs_fresh();
        assert_eq!(
            db.get_latest_price("XCOIN", "CNY"),
            Some(dec!(19107.45) * dec!(6.5868)),
            "the path with the more recent oldest-leg must win, not the one that sorts first",
        );
        assert_eq!(
            db.get_price("XCOIN", "CNY", date(2021, 1, 1)),
            Some(dec!(19107.45) * dec!(6.5868)),
            "the as-of variant must rank paths the same way the latest variant does",
        );

        // Equally-supported paths: same dates on both, so the name decides and
        // keeps the answer stable. Rebuilt repeatedly because the underlying
        // map is a hash map, and insertion-order luck shows up across
        // constructions rather than within one run.
        let equally_good = || {
            let mut db = PriceDatabase::new();
            db.add_price(&price(date(2024, 1, 5), "XCOIN", dec!(2.00), "AAA"));
            db.add_price(&price(date(2024, 1, 5), "AAA", dec!(10.00), "USD"));
            db.add_price(&price(date(2024, 1, 5), "XCOIN", dec!(5.00), "MMM"));
            db.add_price(&price(date(2024, 1, 5), "MMM", dec!(10.00), "USD"));
            db.sort_prices();
            db
        };
        for _ in 0..8 {
            let db = equally_good();
            assert_eq!(
                db.get_price("XCOIN", "USD", date(2024, 6, 1)),
                Some(dec!(20.00))
            );
            assert_eq!(db.get_latest_price("XCOIN", "USD"), Some(dec!(20.00)));
        }
    }

    #[test]
    fn test_chained_price_no_path() {
        let mut db = PriceDatabase::new();

        // Add AAPL -> USD price
        db.add_price(&PriceDirective {
            date: date(2024, 1, 1),
            currency: "AAPL".into(),
            amount: Amount::new(dec!(150.00), "USD"),
            meta: Default::default(),
        });

        // Add GBP -> EUR price (disconnected from USD)
        db.add_price(&PriceDirective {
            date: date(2024, 1, 1),
            currency: "GBP".into(),
            amount: Amount::new(dec!(1.17), "EUR"),
            meta: Default::default(),
        });

        // Sort
        db.sort_prices();

        // No path from AAPL to GBP
        assert_eq!(db.get_price("AAPL", "GBP", date(2024, 1, 1)), None);
    }

    // ============================================================================
    // Implicit-price extraction tests
    // ============================================================================
    //
    // `from_directives` does TWO passes:
    //   1. Add explicit `Price` directives.
    //   2. Walk Transaction postings; extract implicit prices ONLY for
    //      `(base, quote, date)` tuples not already covered by pass 1.
    //
    // This preserves the rustledger extension from #567 / #593 (BQL
    // `VALUE()` works on implicit-priced transactions automatically,
    // without requiring the `implicit_prices` plugin) AND fixes the
    // duplication from #1006 (when the plugin IS enabled, its emitted
    // Price directives suppress the same-tuple BQL extraction).

    /// Transaction with `@` annotation, no plugin → BQL extracts the
    /// implicit price (no explicit Price directive to suppress it).
    /// Preserves the #567/#593 rustledger-extension behavior.
    #[test]
    fn test_implicit_price_from_annotation() {
        use rustledger_core::{CostSpec, Posting, PriceAnnotation, Transaction};

        let txn = Transaction::new(date(2024, 1, 15), "Sell stock")
            .with_synthesized_posting(
                Posting::new("Assets:Stocks", Amount::new(dec!(-5), "ABC"))
                    .with_cost(
                        CostSpec::default()
                            .with_number(rustledger_core::CostNumber::PerUnit { value: dec!(1.25) })
                            .with_currency("EUR"),
                    )
                    .with_price(PriceAnnotation::unit(Amount::new(dec!(1.40), "EUR"))),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(7.00), "EUR")));

        let db = PriceDatabase::from_directives(&[Directive::Transaction(txn)]);
        assert_eq!(
            db.get_price("ABC", "EUR", date(2024, 1, 15)),
            Some(dec!(1.40))
        );
    }

    /// Cost spec only, no annotation → cost-derived implicit price.
    #[test]
    fn test_implicit_price_from_cost_only() {
        use rustledger_core::{CostSpec, Posting, Transaction};

        let txn = Transaction::new(date(2024, 1, 10), "Buy stock")
            .with_synthesized_posting(
                Posting::new("Assets:Stocks", Amount::new(dec!(10), "XYZ")).with_cost(
                    CostSpec::default()
                        .with_number(rustledger_core::CostNumber::PerUnit { value: dec!(50.00) })
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-500), "USD")));

        let db = PriceDatabase::from_directives(&[Directive::Transaction(txn)]);
        assert_eq!(
            db.get_price("XYZ", "USD", date(2024, 1, 10)),
            Some(dec!(50.00))
        );
    }

    /// `@@` total annotation — divided by units. Pins the #992 fix
    /// is preserved end-to-end through the BQL extraction path.
    #[test]
    fn test_implicit_price_from_total_annotation() {
        use rustledger_core::{Posting, PriceAnnotation, Transaction};

        let txn = Transaction::new(date(2024, 1, 15), "Sell")
            .with_synthesized_posting(
                Posting::new("Assets:Stocks", Amount::new(dec!(-10), "ABC"))
                    .with_price(PriceAnnotation::total(Amount::new(dec!(1500), "USD"))),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(1500), "USD")));

        let db = PriceDatabase::from_directives(&[Directive::Transaction(txn)]);
        // 1500 USD / 10 = 150 USD per unit
        assert_eq!(
            db.get_price("ABC", "USD", date(2024, 1, 15)),
            Some(dec!(150))
        );
    }

    /// Both annotation and cost present — annotation wins.
    #[test]
    fn test_implicit_price_annotation_takes_priority_over_cost() {
        use rustledger_core::{CostSpec, Posting, PriceAnnotation, Transaction};

        let txn = Transaction::new(date(2024, 1, 15), "Sell")
            .with_synthesized_posting(
                Posting::new("Assets:Stocks", Amount::new(dec!(-5), "ABC"))
                    .with_cost(
                        CostSpec::default()
                            .with_number(rustledger_core::CostNumber::PerUnit { value: dec!(1.25) })
                            .with_currency("EUR"),
                    )
                    .with_price(PriceAnnotation::unit(Amount::new(dec!(1.40), "EUR"))),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(7.00), "EUR")));

        let db = PriceDatabase::from_directives(&[Directive::Transaction(txn)]);
        assert_eq!(
            db.get_price("ABC", "EUR", date(2024, 1, 15)),
            Some(dec!(1.40))
        );
    }

    /// Zero-units `@@` falls through to cost — regression for the
    /// currency-pairing fix in #997 on the BQL path.
    #[test]
    fn test_implicit_price_zero_units_total_annotation_uses_cost_currency() {
        use rustledger_core::{CostSpec, Posting, PriceAnnotation, Transaction};

        let txn = Transaction::new(date(2024, 1, 15), "Close position").with_synthesized_posting(
            Posting::new("Assets:Stocks", Amount::new(dec!(0), "ABC"))
                .with_cost(
                    CostSpec::default()
                        .with_number(rustledger_core::CostNumber::PerUnit { value: dec!(50) })
                        .with_currency("USD"),
                )
                .with_price(PriceAnnotation::total(Amount::new(dec!(100), "EUR"))),
        );

        let db = PriceDatabase::from_directives(&[Directive::Transaction(txn)]);
        assert_eq!(
            db.get_price("ABC", "USD", date(2024, 1, 15)),
            Some(dec!(50))
        );
        // ABC→EUR has no path; the (50, EUR) bug from #997 stays fixed.
        assert_eq!(db.get_price("ABC", "EUR", date(2024, 1, 15)), None);
    }

    /// Combined explicit + implicit on different dates: explicit
    /// price for an earlier date, implicit price (from transaction)
    /// for the later date. Both reachable.
    #[test]
    fn test_implicit_price_combined_with_explicit() {
        use rustledger_core::{CostSpec, Posting, PriceAnnotation, Transaction};

        let explicit = PriceDirective {
            date: date(2024, 1, 10),
            currency: "ABC".into(),
            amount: Amount::new(dec!(1.30), "EUR"),
            meta: Default::default(),
        };
        let txn = Transaction::new(date(2024, 1, 15), "Sell")
            .with_synthesized_posting(
                Posting::new("Assets:Stocks", Amount::new(dec!(-5), "ABC"))
                    .with_cost(
                        CostSpec::default()
                            .with_number(rustledger_core::CostNumber::PerUnit { value: dec!(1.25) })
                            .with_currency("EUR"),
                    )
                    .with_price(PriceAnnotation::unit(Amount::new(dec!(1.40), "EUR"))),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(7.00), "EUR")));

        let directives = vec![Directive::Price(explicit), Directive::Transaction(txn)];
        let db = PriceDatabase::from_directives(&directives);
        assert_eq!(
            db.get_price("ABC", "EUR", date(2024, 1, 10)),
            Some(dec!(1.30))
        );
        assert_eq!(db.get_latest_price("ABC", "EUR"), Some(dec!(1.40)));
    }

    // ============================================================================
    // Issue #1006 regression — duplication when plugin runs
    // ============================================================================

    /// Plugin-emitted Price directive on the same `(base, quote, date)`
    /// as a transaction's implicit price → exactly ONE entry in the DB.
    /// Pre-fix this would have doubled (the BQL pass would re-extract
    /// the same price the plugin already emitted).
    #[test]
    fn test_plugin_emitted_price_suppresses_bql_extraction_for_same_tuple() {
        use rustledger_core::{CostSpec, Posting, PriceAnnotation, Transaction};

        let directives = vec![
            // Simulates `implicit_prices` plugin output.
            Directive::Price(PriceDirective {
                date: date(2024, 1, 15),
                currency: "ABC".into(),
                amount: Amount::new(dec!(1.40), "EUR"),
                meta: Default::default(),
            }),
            // The original transaction the plugin derived from — still
            // in the directive list, since plugins append rather than
            // replace.
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Sell stock")
                    .with_synthesized_posting(
                        Posting::new("Assets:Stocks", Amount::new(dec!(-5), "ABC"))
                            .with_cost(
                                CostSpec::default()
                                    .with_number(rustledger_core::CostNumber::PerUnit {
                                        value: dec!(1.25),
                                    })
                                    .with_currency("EUR"),
                            )
                            .with_price(PriceAnnotation::unit(Amount::new(dec!(1.40), "EUR"))),
                    )
                    .with_synthesized_posting(Posting::new(
                        "Assets:Cash",
                        Amount::new(dec!(7.00), "EUR"),
                    )),
            ),
        ];
        let db = PriceDatabase::from_directives(&directives);

        assert_eq!(
            db.len(),
            1,
            "exactly one ABC→EUR entry; pre-fix this would be 2 (plugin + BQL)"
        );
        assert_eq!(
            db.get_price("ABC", "EUR", date(2024, 1, 15)),
            Some(dec!(1.40))
        );
    }

    /// Two separate transactions on the same date emitting the same
    /// implicit price — both legitimate, both should remain. Pre-fix
    /// these were already kept (no dedup at insert) — verify the
    /// new two-pass design preserves that.
    #[test]
    fn test_two_transactions_same_date_same_price_both_kept() {
        use rustledger_core::{CostSpec, Posting, Transaction};

        let directives = vec![
            Directive::Transaction(
                Transaction::new(date(2017, 12, 15), "Sale 1")
                    .with_synthesized_posting(
                        Posting::new("Assets:Stock", Amount::new(dec!(-10), "BAM")).with_cost(
                            CostSpec::default()
                                .with_number(rustledger_core::CostNumber::PerUnit {
                                    value: dec!(0.5113),
                                })
                                .with_currency("EUR"),
                        ),
                    )
                    .with_synthesized_posting(Posting::new(
                        "Assets:Cash",
                        Amount::new(dec!(5.113), "EUR"),
                    )),
            ),
            Directive::Transaction(
                Transaction::new(date(2017, 12, 15), "Sale 2")
                    .with_synthesized_posting(
                        Posting::new("Assets:Stock", Amount::new(dec!(-20), "BAM")).with_cost(
                            CostSpec::default()
                                .with_number(rustledger_core::CostNumber::PerUnit {
                                    value: dec!(0.5113),
                                })
                                .with_currency("EUR"),
                        ),
                    )
                    .with_synthesized_posting(Posting::new(
                        "Assets:Cash",
                        Amount::new(dec!(10.226), "EUR"),
                    )),
            ),
        ];
        let db = PriceDatabase::from_directives(&directives);

        // Both transactions emit BAM→EUR at 0.5113 on the same date.
        // No explicit Price suppresses pass 2 → both kept (BQL extracts
        // both since neither is in `explicit`).
        assert_eq!(
            db.len(),
            2,
            "two distinct transactions both emit implicit prices on the same date"
        );
    }

    /// The actual 2017-12-15 case from issue #1006: the
    /// `implicit_prices` plugin runs and emits one Price directive per
    /// priced posting (NOT one per unique tuple). When two distinct
    /// transactions on the same date emit the same `(base, quote)`
    /// pair, the plugin produces two Price directives — pass 1 keeps
    /// both, pass 2 skips both transactions (the tuple is in
    /// `explicit`). Net: two entries, matching what `bean-query`
    /// shows for that date. Pins the plugin+multi-txn interaction
    /// that the original PR's tests left implicit.
    #[test]
    fn test_plugin_emits_per_posting_two_txns_same_tuple_both_kept() {
        use rustledger_core::{CostSpec, Posting, Transaction};

        let directives = vec![
            // Plugin output: one Price per priced posting. Two
            // postings on the same date with the same (base, quote)
            // → two Price directives at the same tuple.
            Directive::Price(PriceDirective {
                date: date(2017, 12, 15),
                currency: "BAM".into(),
                amount: Amount::new(dec!(0.5113), "EUR"),
                meta: Default::default(),
            }),
            Directive::Price(PriceDirective {
                date: date(2017, 12, 15),
                currency: "BAM".into(),
                amount: Amount::new(dec!(0.5113), "EUR"),
                meta: Default::default(),
            }),
            // The original transactions the plugin derived from.
            // Pass 2 must skip both (the (BAM, EUR, 2017-12-15) tuple
            // is already in `explicit` from pass 1's first add).
            Directive::Transaction(
                Transaction::new(date(2017, 12, 15), "Sale 1")
                    .with_synthesized_posting(
                        Posting::new("Assets:Stock", Amount::new(dec!(-10), "BAM")).with_cost(
                            CostSpec::default()
                                .with_number(rustledger_core::CostNumber::PerUnit {
                                    value: dec!(0.5113),
                                })
                                .with_currency("EUR"),
                        ),
                    )
                    .with_synthesized_posting(Posting::new(
                        "Assets:Cash",
                        Amount::new(dec!(5.113), "EUR"),
                    )),
            ),
            Directive::Transaction(
                Transaction::new(date(2017, 12, 15), "Sale 2")
                    .with_synthesized_posting(
                        Posting::new("Assets:Stock", Amount::new(dec!(-20), "BAM")).with_cost(
                            CostSpec::default()
                                .with_number(rustledger_core::CostNumber::PerUnit {
                                    value: dec!(0.5113),
                                })
                                .with_currency("EUR"),
                        ),
                    )
                    .with_synthesized_posting(Posting::new(
                        "Assets:Cash",
                        Amount::new(dec!(10.226), "EUR"),
                    )),
            ),
        ];
        let db = PriceDatabase::from_directives(&directives);

        // Two entries — both from pass 1 (the plugin), zero from
        // pass 2 (gated). Pre-#1015 fix this would have been four
        // (2 plugin + 2 BQL re-extraction). Mirrors the bean-query
        // behavior reported in the issue.
        assert_eq!(
            db.len(),
            2,
            "plugin emits one Price per priced posting; pass 2 must skip both transactions"
        );
        assert_eq!(
            db.get_price("BAM", "EUR", date(2017, 12, 15)),
            Some(dec!(0.5113))
        );
    }

    // ============================================================================
    // Issue #1759 regressions — direction-blind date recency
    // ============================================================================
    //
    // Beancount's `build_price_map` materializes both directions of
    // every pair, so a lookup picks the most recent rate regardless
    // of which direction it was declared in. Pre-fix, rustledger
    // returned any direct entry before consulting the inverse
    // direction, so an OLDER direct rate shadowed a NEWER inverse
    // one.

    fn price(date_: NaiveDate, base: &str, number: Decimal, quote: &str) -> PriceDirective {
        PriceDirective {
            date: date_,
            currency: base.into(),
            amount: Amount::new(number, quote),
            meta: Default::default(),
        }
    }

    /// The core #1759 shape: USD→GBP declared on the 12th, GBP→USD
    /// declared on the 13th. The newer inverse must win for USD→GBP.
    #[test]
    fn test_newer_inverse_beats_older_direct() {
        let mut db = PriceDatabase::new();
        db.add_price(&price(date(2026, 7, 12), "USD", dec!(0.7472), "GBP"));
        db.add_price(&price(date(2026, 7, 13), "GBP", dec!(1.2655), "USD"));
        db.sort_prices();

        // Latest USD→GBP is the 13th's inverted GBP→USD rate.
        assert_eq!(
            db.get_latest_price("USD", "GBP"),
            Some(Decimal::ONE / dec!(1.2655))
        );
        assert_eq!(
            db.get_price("USD", "GBP", date(2026, 7, 13)),
            Some(Decimal::ONE / dec!(1.2655))
        );
        // On the 12th the direct rate is still the most recent.
        assert_eq!(
            db.get_price("USD", "GBP", date(2026, 7, 12)),
            Some(dec!(0.7472))
        );
        // And the other direction mirrors it.
        assert_eq!(db.get_latest_price("GBP", "USD"), Some(dec!(1.2655)));
        assert_eq!(
            db.get_price("GBP", "USD", date(2026, 7, 12)),
            Some(Decimal::ONE / dec!(0.7472))
        );
    }

    /// Symmetric sanity: when the DIRECT rate is newer it still wins.
    #[test]
    fn test_newer_direct_beats_older_inverse() {
        let mut db = PriceDatabase::new();
        db.add_price(&price(date(2026, 7, 12), "GBP", dec!(1.2655), "USD"));
        db.add_price(&price(date(2026, 7, 13), "USD", dec!(0.7472), "GBP"));
        db.sort_prices();

        assert_eq!(db.get_latest_price("USD", "GBP"), Some(dec!(0.7472)));
    }

    /// The swallow rule: the direction with fewer rates is inverted
    /// into the one with more, and date recency is decided on the
    /// merged list.
    #[test]
    fn test_swallow_smaller_direction_into_larger() {
        let mut db = PriceDatabase::new();
        db.add_price(&price(date(2026, 7, 10), "USD", dec!(0.75), "GBP"));
        db.add_price(&price(date(2026, 7, 12), "USD", dec!(0.7472), "GBP"));
        db.add_price(&price(date(2026, 7, 13), "GBP", dec!(1.2655), "USD"));
        db.sort_prices();

        // Merged USD→GBP list: 10th direct, 12th direct, 13th inverted.
        assert_eq!(
            db.get_price("USD", "GBP", date(2026, 7, 11)),
            Some(dec!(0.75))
        );
        assert_eq!(
            db.get_price("USD", "GBP", date(2026, 7, 12)),
            Some(dec!(0.7472))
        );
        assert_eq!(
            db.get_latest_price("USD", "GBP"),
            Some(Decimal::ONE / dec!(1.2655))
        );
    }

    /// Same-date tie between a direct and an inverse rate: Python's
    /// `sorted_uniquify(..., last=True)` keeps ONE rate per date, and
    /// with equal counts the first-seen direction survives the
    /// swallow, so its list is [direct, appended-inverted] and the
    /// inverted rate wins the stable sort's last position.
    #[test]
    fn test_same_date_direct_and_inverse_last_wins() {
        let mut db = PriceDatabase::new();
        db.add_price(&price(date(2026, 7, 12), "USD", dec!(0.75), "GBP"));
        db.add_price(&price(date(2026, 7, 12), "GBP", dec!(1.25), "USD"));
        db.sort_prices();

        // 1/1.25 = 0.8 — the inverted entry replaces the direct one.
        assert_eq!(
            db.get_price("USD", "GBP", date(2026, 7, 12)),
            Some(dec!(0.8))
        );
        assert_eq!(db.get_latest_price("GBP", "USD"), Some(dec!(1.25)));
    }

    /// Zero rates (zero-cost postings, e.g. gifted options) stay in
    /// their declared direction but are never inverted — no division
    /// by zero, and the reverse direction simply has no rate.
    #[test]
    fn test_zero_rate_not_inverted() {
        let mut db = PriceDatabase::new();
        db.add_price(&price(date(2026, 7, 12), "OPT", Decimal::ZERO, "USD"));
        db.sort_prices();

        assert_eq!(
            db.get_price("OPT", "USD", date(2026, 7, 12)),
            Some(Decimal::ZERO)
        );
        assert_eq!(db.get_price("USD", "OPT", date(2026, 7, 12)), None);
    }

    /// End-to-end #1759 shape via `from_directives`: implicit prices
    /// from transaction postings in BOTH directions, newest declared
    /// as the inverse (`-18.68 GBP @ 1.2655 USD`), exactly like the
    /// issue's Format C / Format D pair.
    #[test]
    fn test_implicit_inverse_price_wins_by_date() {
        use rustledger_core::{Posting, PriceAnnotation, Transaction};

        let directives = vec![
            // Format C: 12.70 USD @@ 9.49 GBP → USD→GBP on the 12th.
            Directive::Transaction(
                Transaction::new(date(2026, 7, 12), "Format C")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Checking",
                        Amount::new(dec!(-9.49), "GBP"),
                    ))
                    .with_synthesized_posting(
                        Posting::new("Expenses:Test", Amount::new(dec!(12.70), "USD"))
                            .with_price(PriceAnnotation::total(Amount::new(dec!(9.49), "GBP"))),
                    ),
            ),
            // Format D: -18.68 GBP @ 1.2655 USD → GBP→USD on the 13th.
            Directive::Transaction(
                Transaction::new(date(2026, 7, 13), "Format D")
                    .with_synthesized_posting(
                        Posting::new("Assets:Checking", Amount::new(dec!(-18.68), "GBP"))
                            .with_price(PriceAnnotation::unit(Amount::new(dec!(1.2655), "USD"))),
                    )
                    .with_synthesized_posting(Posting::new(
                        "Expenses:Test",
                        Amount::new(dec!(23.64), "USD"),
                    )),
            ),
        ];
        let db = PriceDatabase::from_directives(&directives);

        // Beancount converts 100 USD to 79.02 GBP using the 13th's
        // inverted rate, not 74.72 GBP from the 12th's direct one.
        let converted = db
            .convert_latest(&Amount::new(dec!(100.00), "USD"), "GBP")
            .expect("USD→GBP rate available");
        assert_eq!(converted.number.round_dp(2), dec!(79.02));

        // The raw provenance store is untouched by the index build:
        // both extracted entries remain, in their declared directions.
        assert_eq!(db.len(), 2);
    }

    /// Chained lookups go through the bidirectional index too: an
    /// inverse-declared leg participates in an A→B→C path with the
    /// same date-recency rule per leg.
    #[test]
    fn test_chained_lookup_uses_newest_rate_per_leg() {
        let mut db = PriceDatabase::new();
        // AAPL→USD.
        db.add_price(&price(date(2026, 7, 10), "AAPL", dec!(150.00), "USD"));
        // USD→EUR twice: old direct, newer inverse.
        db.add_price(&price(date(2026, 7, 11), "USD", dec!(0.92), "EUR"));
        db.add_price(&price(date(2026, 7, 12), "EUR", dec!(1.10), "USD"));
        db.sort_prices();

        // AAPL→EUR = 150 × (1/1.10), not 150 × 0.92.
        assert_eq!(
            db.get_latest_price("AAPL", "EUR"),
            Some(dec!(150.00) * (Decimal::ONE / dec!(1.10)))
        );
    }
}
