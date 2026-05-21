//! Price database for currency conversions.
//!
//! This module provides a price database that stores historical prices
//! and allows looking up prices for currency conversions.

use rust_decimal::Decimal;
use rustledger_core::{Amount, Directive, NaiveDate, Price as PriceDirective, Transaction};
use std::collections::HashMap;

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
/// Stores prices as a map from base currency to a list of (date, price, quote currency).
/// Prices are kept sorted by date for efficient lookup.
#[derive(Debug, Default)]
pub struct PriceDatabase {
    /// Prices indexed by base currency.
    /// Each base currency maps to a list of price entries sorted by date.
    prices: HashMap<rustledger_core::Currency, Vec<PriceEntry>>,
}

impl PriceDatabase {
    /// Create a new empty price database.
    pub fn new() -> Self {
        Self {
            prices: HashMap::new(),
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

    /// Sort all price entries by date.
    ///
    /// Call this after adding prices to ensure lookups work correctly.
    pub fn sort_prices(&mut self) {
        for entries in self.prices.values_mut() {
            entries.sort_by_key(|e| e.date);
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
            let annotation = posting.price.as_ref().and_then(|annotation| {
                let amount = annotation.amount()?;
                Some((
                    !annotation.is_unit(),
                    amount.number,
                    amount.currency.clone(),
                ))
            });
            let cost = posting.cost.as_ref().and_then(|c| {
                let currency = c.currency.clone()?;
                if c.number_per.is_none() && c.number_total.is_none() {
                    return None;
                }
                Some((c.number_per, c.number_total, currency))
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

        self.prices
            .entry(base_currency.clone())
            .or_default()
            .push(entry);
    }

    /// Get the price of a currency on or before a given date.
    ///
    /// Returns the most recent price for the base currency in terms of the quote currency.
    /// Tries direct lookup, inverse lookup, and chained lookup (A→B→C).
    pub fn get_price(&self, base: &str, quote: &str, date: NaiveDate) -> Option<Decimal> {
        // Same currency = price of 1
        if base == quote {
            return Some(Decimal::ONE);
        }

        // Try direct price lookup
        if let Some(price) = self.get_direct_price(base, quote, date) {
            return Some(price);
        }

        // Try inverse price lookup
        if let Some(price) = self.get_direct_price(quote, base, date)
            && price != Decimal::ZERO
        {
            return Some(Decimal::ONE / price);
        }

        // Try chained lookup (A→B→C where B is an intermediate currency)
        self.get_chained_price(base, quote, date)
    }

    /// Get direct price (base currency priced in quote currency).
    fn get_direct_price(&self, base: &str, quote: &str, date: NaiveDate) -> Option<Decimal> {
        if let Some(entries) = self.prices.get(base) {
            for entry in entries.iter().rev() {
                if entry.date <= date && entry.currency == quote {
                    return Some(entry.price);
                }
            }
        }
        None
    }

    /// Try to find a price through an intermediate currency.
    /// For A→C, try to find A→B and B→C for some intermediate B.
    fn get_chained_price(&self, base: &str, quote: &str, date: NaiveDate) -> Option<Decimal> {
        // Collect all currencies that have prices from 'base'
        let intermediates: Vec<rustledger_core::Currency> =
            if let Some(entries) = self.prices.get(base) {
                entries
                    .iter()
                    .filter(|e| e.date <= date)
                    .map(|e| e.currency.clone())
                    .collect()
            } else {
                Vec::new()
            };

        // Try each intermediate currency
        for intermediate in intermediates {
            if intermediate == quote {
                continue; // Already tried direct
            }

            // Get price base→intermediate
            if let Some(price1) = self.get_direct_price(base, &intermediate, date) {
                // Get price intermediate→quote (try direct, inverse, but not chained to avoid loops)
                if let Some(price2) = self.get_direct_price(&intermediate, quote, date) {
                    return Some(price1 * price2);
                }
                // Try inverse for second leg
                if let Some(price2) = self.get_direct_price(quote, &intermediate, date)
                    && price2 != Decimal::ZERO
                {
                    return Some(price1 / price2);
                }
            }
        }

        // Also try currencies that price TO base (inverse first leg)
        for (currency, entries) in &self.prices {
            for entry in entries.iter().rev() {
                if entry.date <= date && entry.currency == base && entry.price != Decimal::ZERO {
                    // We have currency→base, so base→currency = 1/price
                    let price1 = Decimal::ONE / entry.price;

                    // Now try currency→quote
                    if let Some(price2) = self.get_direct_price(currency, quote, date) {
                        return Some(price1 * price2);
                    }
                    if let Some(price2) = self.get_direct_price(quote, currency, date)
                        && price2 != Decimal::ZERO
                    {
                        return Some(price1 / price2);
                    }
                }
            }
        }

        None
    }

    /// Get the latest price of a currency (most recent date).
    ///
    /// Supports direct lookup, inverse lookup, and chained lookup (A→B→C).
    pub fn get_latest_price(&self, base: &str, quote: &str) -> Option<Decimal> {
        // Same currency = price of 1
        if base == quote {
            return Some(Decimal::ONE);
        }

        // Try direct price lookup
        if let Some(price) = self.get_direct_latest_price(base, quote) {
            return Some(price);
        }

        // Try inverse price lookup
        if let Some(price) = self.get_direct_latest_price(quote, base)
            && price != Decimal::ZERO
        {
            return Some(Decimal::ONE / price);
        }

        // Try chained lookup (A→B→C where B is an intermediate currency)
        self.get_chained_latest_price(base, quote)
    }

    /// Get direct latest price (base currency priced in quote currency).
    fn get_direct_latest_price(&self, base: &str, quote: &str) -> Option<Decimal> {
        if let Some(entries) = self.prices.get(base) {
            // Find the most recent price in the target currency
            for entry in entries.iter().rev() {
                if entry.currency == quote {
                    return Some(entry.price);
                }
            }
        }
        None
    }

    /// Try to find the latest price through an intermediate currency.
    /// For A→C, try to find A→B and B→C for some intermediate B.
    fn get_chained_latest_price(&self, base: &str, quote: &str) -> Option<Decimal> {
        // Collect all currencies that have prices from 'base'
        let intermediates: Vec<rustledger_core::Currency> =
            if let Some(entries) = self.prices.get(base) {
                entries.iter().map(|e| e.currency.clone()).collect()
            } else {
                Vec::new()
            };

        // Try each intermediate currency
        for intermediate in intermediates {
            if intermediate == quote {
                continue; // Already tried direct
            }

            // Get price base→intermediate
            if let Some(price1) = self.get_direct_latest_price(base, &intermediate) {
                // Get price intermediate→quote (try direct, inverse, but not chained to avoid loops)
                if let Some(price2) = self.get_direct_latest_price(&intermediate, quote) {
                    return Some(price1 * price2);
                }
                // Try inverse for second leg
                if let Some(price2) = self.get_direct_latest_price(quote, &intermediate)
                    && price2 != Decimal::ZERO
                {
                    return Some(price1 / price2);
                }
            }
        }

        // Also try currencies that price TO base (inverse first leg)
        for (currency, entries) in &self.prices {
            for entry in entries.iter().rev() {
                if entry.currency == base && entry.price != Decimal::ZERO {
                    // We have currency→base, so base→currency = 1/price
                    let price1 = Decimal::ONE / entry.price;

                    // Now try currency→quote
                    if let Some(price2) = self.get_direct_latest_price(currency, quote) {
                        return Some(price1 * price2);
                    }
                    if let Some(price2) = self.get_direct_latest_price(quote, currency)
                        && price2 != Decimal::ZERO
                    {
                        return Some(price1 / price2);
                    }
                }
            }
        }

        None
    }

    /// Convert an amount to a target currency.
    ///
    /// Returns the converted amount, or None if no price is available.
    pub fn convert(&self, amount: &Amount, to_currency: &str, date: NaiveDate) -> Option<Amount> {
        if amount.currency == to_currency {
            return Some(amount.clone());
        }

        self.get_price(&amount.currency, to_currency, date)
            .map(|price| Amount::new(amount.number * price, to_currency))
    }

    /// Convert an amount using the latest available price.
    pub fn convert_latest(&self, amount: &Amount, to_currency: &str) -> Option<Amount> {
        if amount.currency == to_currency {
            return Some(amount.clone());
        }

        self.get_latest_price(&amount.currency, to_currency)
            .map(|price| Amount::new(amount.number * price, to_currency))
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
        for entries in db.prices.values_mut() {
            entries.sort_by_key(|e| e.date);
        }

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
        for entries in db.prices.values_mut() {
            entries.sort_by_key(|e| e.date);
        }

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

        for entries in db.prices.values_mut() {
            entries.sort_by_key(|e| e.date);
        }

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
        for entries in db.prices.values_mut() {
            entries.sort_by_key(|e| e.date);
        }

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
        for entries in db.prices.values_mut() {
            entries.sort_by_key(|e| e.date);
        }

        // BTC -> EUR should work via BTC -> USD -> EUR
        // BTC -> USD = 40000
        // USD -> EUR = 1/1.10 ≈ 0.909
        // BTC -> EUR = 40000 / 1.10 ≈ 36363.63
        let chained = db.get_price("BTC", "EUR", date(2024, 1, 1)).unwrap();
        // 40000 / 1.10 = 36363.636363...
        assert!(chained > dec!(36363) && chained < dec!(36364));
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
        for entries in db.prices.values_mut() {
            entries.sort_by_key(|e| e.date);
        }

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
                            .with_number_per(dec!(1.25))
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
                        .with_number_per(dec!(50.00))
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
                            .with_number_per(dec!(1.25))
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
                        .with_number_per(dec!(50))
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
                            .with_number_per(dec!(1.25))
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
                                    .with_number_per(dec!(1.25))
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
                                .with_number_per(dec!(0.5113))
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
                                .with_number_per(dec!(0.5113))
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
                                .with_number_per(dec!(0.5113))
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
                                .with_number_per(dec!(0.5113))
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
}
