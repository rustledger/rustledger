//! Price database for currency conversions.
//!
//! This module provides a price database that stores historical prices
//! and allows looking up prices for currency conversions.

use rust_decimal::Decimal;
use rustledger_core::{
    Amount, Directive, InternedStr, NaiveDate, Price as PriceDirective, Transaction,
};
use std::collections::HashMap;

/// A price entry.
#[derive(Debug, Clone)]
pub struct PriceEntry {
    /// Date of the price.
    pub date: NaiveDate,
    /// Price amount.
    pub price: Decimal,
    /// Quote currency.
    pub currency: InternedStr,
}

/// Database of currency prices.
///
/// Stores prices as a map from base currency to a list of (date, price, quote currency).
/// Prices are kept sorted by date for efficient lookup.
#[derive(Debug, Default)]
pub struct PriceDatabase {
    /// Prices indexed by base currency.
    /// Each base currency maps to a list of price entries sorted by date.
    prices: HashMap<InternedStr, Vec<PriceEntry>>,
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
    /// Extracts prices from:
    /// - Explicit `price` directives
    /// - Implicit prices from transaction postings (@ price annotations and cost specs)
    ///
    /// This matches Python beancount's behavior when using the `implicit_prices` plugin.
    pub fn from_directives(directives: &[Directive]) -> Self {
        let mut db = Self::new();

        for directive in directives {
            match directive {
                Directive::Price(price) => {
                    db.add_price(price);
                }
                Directive::Transaction(txn) => {
                    db.add_implicit_prices_from_transaction(txn);
                }
                _ => {}
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
    pub fn add_price(&mut self, price: &PriceDirective) {
        let entry = PriceEntry {
            date: price.date,
            price: price.amount.number,
            currency: price.amount.currency.clone(),
        };

        self.prices
            .entry(price.currency.clone())
            .or_default()
            .push(entry);
    }

    /// Add implicit prices from transaction postings.
    ///
    /// Delegates per-posting price math to
    /// [`rustledger_core::extract_per_unit_price`], which is also used
    /// by the native `implicit_prices` plugin
    /// (`rustledger_plugin::native::plugins::implicit_prices`). Pre-fix
    /// (issue #992) the two paths were independently implemented and
    /// diverged on `@@` handling — the plugin emitted total amounts as
    /// per-unit prices. The shared helper eliminates that drift by
    /// construction.
    ///
    /// Resolution priority (matches Python beancount's
    /// `implicit_prices` plugin):
    /// 1. Price annotation (`@` or `@@`) when an amount is present
    /// 2. Cost spec (`{...}`) as fallback
    /// 3. Otherwise no price emitted
    pub fn add_implicit_prices_from_transaction(&mut self, txn: &Transaction) {
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

            self.add_implicit_price(txn.date, &units.currency, per_unit, &quote);
        }
    }

    /// Add an implicit price entry.
    fn add_implicit_price(
        &mut self,
        date: NaiveDate,
        base_currency: &InternedStr,
        price: Decimal,
        quote_currency: &InternedStr,
    ) {
        let entry = PriceEntry {
            date,
            price,
            currency: quote_currency.clone(),
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
        let intermediates: Vec<InternedStr> = if let Some(entries) = self.prices.get(base) {
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
        let intermediates: Vec<InternedStr> = if let Some(entries) = self.prices.get(base) {
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
        self.prices.keys().map(InternedStr::as_str)
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

    /// Iterate over all price entries with their base currency.
    ///
    /// Returns tuples of (`base_currency`, `date`, `price`, `quote_currency`).
    pub fn iter_entries(&self) -> impl Iterator<Item = (&str, NaiveDate, Decimal, &str)> {
        self.prices.iter().flat_map(|(base, entries)| {
            entries
                .iter()
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
    // Implicit Price Extraction Tests
    // ============================================================================

    #[test]
    fn test_implicit_price_from_annotation() {
        use rustledger_core::{CostSpec, Posting, PriceAnnotation, Transaction};

        // Transaction with @ price annotation
        let txn = Transaction::new(date(2024, 1, 15), "Sell stock")
            .with_posting(
                Posting::new("Assets:Stocks", Amount::new(dec!(-5), "ABC"))
                    .with_cost(
                        CostSpec::default()
                            .with_number_per(dec!(1.25))
                            .with_currency("EUR"),
                    )
                    .with_price(PriceAnnotation::Unit(Amount::new(dec!(1.40), "EUR"))),
            )
            .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(7.00), "EUR")));

        let directives = vec![Directive::Transaction(txn)];
        let db = PriceDatabase::from_directives(&directives);

        // Should have implicit price ABC = 1.40 EUR (from @ annotation, not cost)
        let price = db.get_price("ABC", "EUR", date(2024, 1, 15));
        assert_eq!(price, Some(dec!(1.40)));
    }

    #[test]
    fn test_implicit_price_from_cost_only() {
        use rustledger_core::{CostSpec, Posting, Transaction};

        // Transaction with cost but no price annotation
        let txn = Transaction::new(date(2024, 1, 10), "Buy stock")
            .with_posting(
                Posting::new("Assets:Stocks", Amount::new(dec!(10), "XYZ")).with_cost(
                    CostSpec::default()
                        .with_number_per(dec!(50.00))
                        .with_currency("USD"),
                ),
            )
            .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-500), "USD")));

        let directives = vec![Directive::Transaction(txn)];
        let db = PriceDatabase::from_directives(&directives);

        // Should have implicit price XYZ = 50.00 USD (from cost)
        let price = db.get_price("XYZ", "USD", date(2024, 1, 10));
        assert_eq!(price, Some(dec!(50.00)));
    }

    #[test]
    fn test_implicit_price_from_total_annotation() {
        use rustledger_core::{Posting, PriceAnnotation, Transaction};

        // Transaction with @@ total price annotation
        let txn = Transaction::new(date(2024, 1, 15), "Sell")
            .with_posting(
                Posting::new("Assets:Stocks", Amount::new(dec!(-10), "ABC"))
                    .with_price(PriceAnnotation::Total(Amount::new(dec!(1500), "USD"))),
            )
            .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(1500), "USD")));

        let directives = vec![Directive::Transaction(txn)];
        let db = PriceDatabase::from_directives(&directives);

        // Per-unit price should be 1500 / 10 = 150 USD
        let price = db.get_price("ABC", "USD", date(2024, 1, 15));
        assert_eq!(price, Some(dec!(150)));
    }

    #[test]
    fn test_implicit_price_annotation_takes_priority_over_cost() {
        use rustledger_core::{CostSpec, Posting, PriceAnnotation, Transaction};

        // Transaction with both cost and @ price annotation
        // The @ price (1.40) should be used, not the cost (1.25)
        let txn = Transaction::new(date(2024, 1, 15), "Sell")
            .with_posting(
                Posting::new("Assets:Stocks", Amount::new(dec!(-5), "ABC"))
                    .with_cost(
                        CostSpec::default()
                            .with_number_per(dec!(1.25))
                            .with_currency("EUR"),
                    )
                    .with_price(PriceAnnotation::Unit(Amount::new(dec!(1.40), "EUR"))),
            )
            .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(7.00), "EUR")));

        let directives = vec![Directive::Transaction(txn)];
        let db = PriceDatabase::from_directives(&directives);

        // Should use @ price, not cost
        let price = db.get_price("ABC", "EUR", date(2024, 1, 15));
        assert_eq!(price, Some(dec!(1.40)));
    }

    #[test]
    fn test_implicit_price_combined_with_explicit() {
        use rustledger_core::{CostSpec, Posting, PriceAnnotation, Transaction};

        // Both explicit price directive and implicit price from transaction
        let explicit_price = PriceDirective {
            date: date(2024, 1, 10),
            currency: "ABC".into(),
            amount: Amount::new(dec!(1.30), "EUR"),
            meta: Default::default(),
        };

        let txn = Transaction::new(date(2024, 1, 15), "Sell")
            .with_posting(
                Posting::new("Assets:Stocks", Amount::new(dec!(-5), "ABC"))
                    .with_cost(
                        CostSpec::default()
                            .with_number_per(dec!(1.25))
                            .with_currency("EUR"),
                    )
                    .with_price(PriceAnnotation::Unit(Amount::new(dec!(1.40), "EUR"))),
            )
            .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(7.00), "EUR")));

        let directives = vec![
            Directive::Price(explicit_price),
            Directive::Transaction(txn),
        ];
        let db = PriceDatabase::from_directives(&directives);

        // At 2024-01-10, should use explicit price 1.30
        assert_eq!(
            db.get_price("ABC", "EUR", date(2024, 1, 10)),
            Some(dec!(1.30))
        );

        // At 2024-01-15 or later, should use implicit price 1.40 (latest)
        assert_eq!(db.get_latest_price("ABC", "EUR"), Some(dec!(1.40)));
    }

    /// Currency-pairing regression for the query path. Mirrors the
    /// plugin-side `test_implicit_prices_zero_unit_total_falls_through_to_cost_currency`
    /// (Copilot review on PR #997). With zero units, the `@@` total
    /// annotation is unusable, so the per-unit value falls through to
    /// the cost spec — and the quote currency MUST come from the cost,
    /// not the dropped annotation. Pre-fix, both paths emitted
    /// `(50, EUR)` instead of `(50, USD)`. The shared helper now binds
    /// each value to its source currency, making this bug structurally
    /// impossible. This test pins the query path's behavior so a
    /// future caller-side refactor cannot silently regress it.
    #[test]
    fn test_implicit_price_zero_units_total_annotation_uses_cost_currency() {
        use rustledger_core::{CostSpec, Posting, PriceAnnotation, Transaction};

        let txn = Transaction::new(date(2024, 1, 15), "Close position").with_posting(
            Posting::new("Assets:Stocks", Amount::new(dec!(0), "ABC"))
                .with_cost(
                    CostSpec::default()
                        .with_number_per(dec!(50))
                        .with_currency("USD"),
                )
                .with_price(PriceAnnotation::Total(Amount::new(dec!(100), "EUR"))),
        );

        let db = PriceDatabase::from_directives(&[Directive::Transaction(txn)]);

        // Per-unit value (50) was paired with USD (cost currency),
        // not EUR (dropped annotation currency).
        assert_eq!(
            db.get_price("ABC", "USD", date(2024, 1, 15)),
            Some(dec!(50))
        );
        // ABC→EUR has no path: no direct entry, no inverse EUR→ABC,
        // no chain through any other currency. Pre-fix this would
        // have been Some(50) because the bogus (50, EUR) entry was
        // recorded.
        assert_eq!(db.get_price("ABC", "EUR", date(2024, 1, 15)), None);
    }
}
