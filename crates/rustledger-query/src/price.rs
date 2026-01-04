//! Price database for currency conversions.
//!
//! This module provides a price database that stores historical prices
//! and allows looking up prices for currency conversions.

use rust_decimal::Decimal;
use rustledger_core::{Amount, Directive, NaiveDate, Price as PriceDirective};
use std::collections::HashMap;

/// A price entry.
#[derive(Debug, Clone)]
pub struct PriceEntry {
    /// Date of the price.
    pub date: NaiveDate,
    /// Price amount.
    pub price: Decimal,
    /// Quote currency.
    pub currency: String,
}

/// Database of currency prices.
///
/// Stores prices as a map from base currency to a list of (date, price, quote currency).
/// Prices are kept sorted by date for efficient lookup.
#[derive(Debug, Default)]
pub struct PriceDatabase {
    /// Prices indexed by base currency.
    /// Each base currency maps to a list of price entries sorted by date.
    prices: HashMap<String, Vec<PriceEntry>>,
}

impl PriceDatabase {
    /// Create a new empty price database.
    pub fn new() -> Self {
        Self {
            prices: HashMap::new(),
        }
    }

    /// Build a price database from directives.
    pub fn from_directives(directives: &[Directive]) -> Self {
        let mut db = Self::new();

        for directive in directives {
            if let Directive::Price(price) = directive {
                db.add_price(price);
            }
        }

        // Sort all price lists by date
        for entries in db.prices.values_mut() {
            entries.sort_by_key(|e| e.date);
        }

        db
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
        if let Some(price) = self.get_direct_price(quote, base, date) {
            if price != Decimal::ZERO {
                return Some(Decimal::ONE / price);
            }
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
        let intermediates: Vec<String> = if let Some(entries) = self.prices.get(base) {
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
                if let Some(price2) = self.get_direct_price(quote, &intermediate, date) {
                    if price2 != Decimal::ZERO {
                        return Some(price1 / price2);
                    }
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
                    if let Some(price2) = self.get_direct_price(quote, currency, date) {
                        if price2 != Decimal::ZERO {
                            return Some(price1 / price2);
                        }
                    }
                }
            }
        }

        None
    }

    /// Get the latest price of a currency (most recent date).
    pub fn get_latest_price(&self, base: &str, quote: &str) -> Option<Decimal> {
        if let Some(entries) = self.prices.get(base) {
            // Find the most recent price in the target currency
            for entry in entries.iter().rev() {
                if entry.currency == quote {
                    return Some(entry.price);
                }
            }
        }

        // Check inverse
        if let Some(entries) = self.prices.get(quote) {
            for entry in entries.iter().rev() {
                if entry.currency == base && entry.price != Decimal::ZERO {
                    return Some(Decimal::ONE / entry.price);
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
        self.prices.keys().map(String::as_str)
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;

    fn date(y: i32, m: u32, d: u32) -> NaiveDate {
        NaiveDate::from_ymd_opt(y, m, d).unwrap()
    }

    #[test]
    fn test_price_lookup() {
        let mut db = PriceDatabase::new();

        // Add some prices
        db.add_price(&PriceDirective {
            date: date(2024, 1, 1),
            currency: "AAPL".to_string(),
            amount: Amount::new(dec!(150.00), "USD"),
            meta: Default::default(),
        });

        db.add_price(&PriceDirective {
            date: date(2024, 6, 1),
            currency: "AAPL".to_string(),
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
            currency: "USD".to_string(),
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
            currency: "AAPL".to_string(),
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
                currency: "AAPL".to_string(),
                amount: Amount::new(dec!(150.00), "USD"),
                meta: Default::default(),
            }),
            Directive::Price(PriceDirective {
                date: date(2024, 1, 1),
                currency: "EUR".to_string(),
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
            currency: "AAPL".to_string(),
            amount: Amount::new(dec!(150.00), "USD"),
            meta: Default::default(),
        });

        // Add USD -> EUR price
        db.add_price(&PriceDirective {
            date: date(2024, 1, 1),
            currency: "USD".to_string(),
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
            currency: "BTC".to_string(),
            amount: Amount::new(dec!(40000.00), "USD"),
            meta: Default::default(),
        });

        // Add EUR -> USD price (inverse of what we need for USD -> EUR)
        db.add_price(&PriceDirective {
            date: date(2024, 1, 1),
            currency: "EUR".to_string(),
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
            currency: "AAPL".to_string(),
            amount: Amount::new(dec!(150.00), "USD"),
            meta: Default::default(),
        });

        // Add GBP -> EUR price (disconnected from USD)
        db.add_price(&PriceDirective {
            date: date(2024, 1, 1),
            currency: "GBP".to_string(),
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
}
