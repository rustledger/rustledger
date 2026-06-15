//! Built-in merchant dictionary for transaction categorization.
//!
//! Contains ~75 common merchant patterns covering groceries, dining,
//! transport, shopping, subscriptions, utilities, health, and more.
//! These are compiled into the binary and serve as a low-priority
//! fallback when user rules don't match.
//!
//! Users can override any merchant pattern by adding a higher-priority
//! rule in their `importers.toml`.

/// A single merchant dictionary entry.
#[derive(Debug)]
pub struct MerchantEntry {
    /// Regex pattern to match against payee/narration (case-insensitive).
    pub pattern: &'static str,
    /// The account to assign when this pattern matches.
    pub account: &'static str,
    /// Human-readable category name.
    pub category: &'static str,
}

/// Built-in merchant patterns for common transaction categorization.
///
/// See `data/merchants.csv` for the reference data these patterns are based on.
pub static MERCHANT_PATTERNS: &[MerchantEntry] = &[
    // ===== Groceries =====
    MerchantEntry {
        pattern: r"WHOLE\s*FOODS",
        account: "Expenses:Groceries",
        category: "Groceries",
    },
    MerchantEntry {
        pattern: r"TRADER\s*JOE",
        account: "Expenses:Groceries",
        category: "Groceries",
    },
    MerchantEntry {
        pattern: "KROGER",
        account: "Expenses:Groceries",
        category: "Groceries",
    },
    MerchantEntry {
        pattern: "SAFEWAY",
        account: "Expenses:Groceries",
        category: "Groceries",
    },
    MerchantEntry {
        pattern: "PUBLIX",
        account: "Expenses:Groceries",
        category: "Groceries",
    },
    MerchantEntry {
        pattern: "ALDI",
        account: "Expenses:Groceries",
        category: "Groceries",
    },
    MerchantEntry {
        pattern: "LIDL",
        account: "Expenses:Groceries",
        category: "Groceries",
    },
    MerchantEntry {
        pattern: "COSTCO",
        account: "Expenses:Groceries",
        category: "Groceries",
    },
    MerchantEntry {
        pattern: r"SAM'?S\s*CLUB",
        account: "Expenses:Groceries",
        category: "Groceries",
    },
    MerchantEntry {
        pattern: "WEGMANS",
        account: "Expenses:Groceries",
        category: "Groceries",
    },
    MerchantEntry {
        pattern: r"H[\s-]?E[\s-]?B\b",
        account: "Expenses:Groceries",
        category: "Groceries",
    },
    MerchantEntry {
        pattern: "MEIJER",
        account: "Expenses:Groceries",
        category: "Groceries",
    },
    MerchantEntry {
        pattern: r"FOOD\s*LION",
        account: "Expenses:Groceries",
        category: "Groceries",
    },
    MerchantEntry {
        pattern: "SPROUTS",
        account: "Expenses:Groceries",
        category: "Groceries",
    },
    MerchantEntry {
        pattern: "INSTACART",
        account: "Expenses:Groceries",
        category: "Groceries",
    },
    // ===== Dining =====
    MerchantEntry {
        pattern: "STARBUCKS",
        account: "Expenses:Dining:Coffee",
        category: "Dining",
    },
    MerchantEntry {
        pattern: "DUNKIN",
        account: "Expenses:Dining:Coffee",
        category: "Dining",
    },
    MerchantEntry {
        pattern: r"PEET'?S\s*COFFEE",
        account: "Expenses:Dining:Coffee",
        category: "Dining",
    },
    MerchantEntry {
        pattern: "MCDONALD",
        account: "Expenses:Dining:FastFood",
        category: "Dining",
    },
    MerchantEntry {
        pattern: r"BURGER\s*KING",
        account: "Expenses:Dining:FastFood",
        category: "Dining",
    },
    MerchantEntry {
        pattern: r"TACO\s*BELL",
        account: "Expenses:Dining:FastFood",
        category: "Dining",
    },
    MerchantEntry {
        pattern: r"CHICK[\s-]?FIL[\s-]?A",
        account: "Expenses:Dining:FastFood",
        category: "Dining",
    },
    MerchantEntry {
        pattern: "SUBWAY",
        account: "Expenses:Dining:FastFood",
        category: "Dining",
    },
    MerchantEntry {
        pattern: "CHIPOTLE",
        account: "Expenses:Dining:FastFood",
        category: "Dining",
    },
    MerchantEntry {
        pattern: "PANERA",
        account: "Expenses:Dining:FastFood",
        category: "Dining",
    },
    MerchantEntry {
        pattern: "DOORDASH",
        account: "Expenses:Dining:Delivery",
        category: "Dining",
    },
    MerchantEntry {
        pattern: "GRUBHUB",
        account: "Expenses:Dining:Delivery",
        category: "Dining",
    },
    MerchantEntry {
        pattern: r"UBER\s*EATS",
        account: "Expenses:Dining:Delivery",
        category: "Dining",
    },
    // ===== Transport =====
    MerchantEntry {
        pattern: r"UBER\s*(TRIP|RIDE|BV)",
        account: "Expenses:Transport:Rideshare",
        category: "Transport",
    },
    MerchantEntry {
        pattern: "LYFT",
        account: "Expenses:Transport:Rideshare",
        category: "Transport",
    },
    MerchantEntry {
        pattern: r"SHELL\b",
        account: "Expenses:Transport:Fuel",
        category: "Transport",
    },
    MerchantEntry {
        pattern: "CHEVRON",
        account: "Expenses:Transport:Fuel",
        category: "Transport",
    },
    MerchantEntry {
        pattern: "EXXON",
        account: "Expenses:Transport:Fuel",
        category: "Transport",
    },
    MerchantEntry {
        pattern: r"BP\b",
        account: "Expenses:Transport:Fuel",
        category: "Transport",
    },
    MerchantEntry {
        pattern: "SPEEDWAY",
        account: "Expenses:Transport:Fuel",
        category: "Transport",
    },
    MerchantEntry {
        pattern: "PARKING",
        account: "Expenses:Transport:Parking",
        category: "Transport",
    },
    MerchantEntry {
        pattern: r"E[\s-]?Z\s*PASS",
        account: "Expenses:Transport:Tolls",
        category: "Transport",
    },
    // ===== Shopping =====
    MerchantEntry {
        pattern: "AMAZON|AMZN",
        account: "Expenses:Shopping:Amazon",
        category: "Shopping",
    },
    MerchantEntry {
        pattern: r"WALMART|WM\s*SUPERCENTER",
        account: "Expenses:Shopping",
        category: "Shopping",
    },
    MerchantEntry {
        pattern: r"TARGET\b",
        account: "Expenses:Shopping",
        category: "Shopping",
    },
    MerchantEntry {
        pattern: r"BEST\s*BUY",
        account: "Expenses:Shopping:Electronics",
        category: "Shopping",
    },
    MerchantEntry {
        pattern: r"APPLE\.COM|APPLE\s*STORE",
        account: "Expenses:Shopping:Electronics",
        category: "Shopping",
    },
    MerchantEntry {
        pattern: r"HOME\s*DEPOT",
        account: "Expenses:Shopping:Home",
        category: "Shopping",
    },
    MerchantEntry {
        pattern: r"LOWE'?S",
        account: "Expenses:Shopping:Home",
        category: "Shopping",
    },
    MerchantEntry {
        pattern: "IKEA",
        account: "Expenses:Shopping:Home",
        category: "Shopping",
    },
    // ===== Subscriptions =====
    MerchantEntry {
        pattern: "NETFLIX",
        account: "Expenses:Subscriptions:Streaming",
        category: "Subscriptions",
    },
    MerchantEntry {
        pattern: "SPOTIFY",
        account: "Expenses:Subscriptions:Streaming",
        category: "Subscriptions",
    },
    MerchantEntry {
        pattern: "HULU",
        account: "Expenses:Subscriptions:Streaming",
        category: "Subscriptions",
    },
    MerchantEntry {
        pattern: r"DISNEY\s*\+|DISNEYPLUS",
        account: "Expenses:Subscriptions:Streaming",
        category: "Subscriptions",
    },
    MerchantEntry {
        pattern: r"HBO\s*MAX|MAX\.COM",
        account: "Expenses:Subscriptions:Streaming",
        category: "Subscriptions",
    },
    MerchantEntry {
        pattern: r"APPLE\s*(TV|MUSIC|ONE|ICLOUD)",
        account: "Expenses:Subscriptions:Apple",
        category: "Subscriptions",
    },
    MerchantEntry {
        pattern: r"AMAZON\s*PRIME",
        account: "Expenses:Subscriptions:Amazon",
        category: "Subscriptions",
    },
    MerchantEntry {
        pattern: "ADOBE",
        account: "Expenses:Subscriptions:Software",
        category: "Subscriptions",
    },
    MerchantEntry {
        pattern: r"MICROSOFT\s*(365|OFFICE)",
        account: "Expenses:Subscriptions:Software",
        category: "Subscriptions",
    },
    MerchantEntry {
        pattern: "GITHUB",
        account: "Expenses:Subscriptions:Software",
        category: "Subscriptions",
    },
    MerchantEntry {
        pattern: "OPENAI|CHATGPT",
        account: "Expenses:Subscriptions:Software",
        category: "Subscriptions",
    },
    // ===== Utilities =====
    MerchantEntry {
        pattern: r"AT\s*&?\s*T\b",
        account: "Expenses:Utilities:Phone",
        category: "Utilities",
    },
    MerchantEntry {
        pattern: "VERIZON",
        account: "Expenses:Utilities:Phone",
        category: "Utilities",
    },
    MerchantEntry {
        pattern: r"T[\s-]?MOBILE",
        account: "Expenses:Utilities:Phone",
        category: "Utilities",
    },
    MerchantEntry {
        pattern: "COMCAST|XFINITY",
        account: "Expenses:Utilities:Internet",
        category: "Utilities",
    },
    MerchantEntry {
        pattern: "SPECTRUM",
        account: "Expenses:Utilities:Internet",
        category: "Utilities",
    },
    // ===== Health =====
    MerchantEntry {
        pattern: "CVS",
        account: "Expenses:Health:Pharmacy",
        category: "Health",
    },
    MerchantEntry {
        pattern: "WALGREENS",
        account: "Expenses:Health:Pharmacy",
        category: "Health",
    },
    MerchantEntry {
        pattern: r"PLANET\s*FITNESS",
        account: "Expenses:Health:Fitness",
        category: "Health",
    },
    MerchantEntry {
        pattern: "PELOTON",
        account: "Expenses:Health:Fitness",
        category: "Health",
    },
    // ===== Travel =====
    MerchantEntry {
        pattern: "AIRBNB",
        account: "Expenses:Travel:Lodging",
        category: "Travel",
    },
    MerchantEntry {
        pattern: r"BOOKING\.COM",
        account: "Expenses:Travel:Lodging",
        category: "Travel",
    },
    MerchantEntry {
        pattern: "MARRIOTT",
        account: "Expenses:Travel:Lodging",
        category: "Travel",
    },
    MerchantEntry {
        pattern: "HILTON",
        account: "Expenses:Travel:Lodging",
        category: "Travel",
    },
    MerchantEntry {
        pattern: "EXPEDIA",
        account: "Expenses:Travel",
        category: "Travel",
    },
    // ===== Financial =====
    MerchantEntry {
        pattern: "VENMO",
        account: "Expenses:Transfers:Venmo",
        category: "Financial",
    },
    MerchantEntry {
        pattern: "PAYPAL",
        account: "Expenses:Transfers:PayPal",
        category: "Financial",
    },
    MerchantEntry {
        pattern: "ZELLE",
        account: "Expenses:Transfers:Zelle",
        category: "Financial",
    },
    // ===== Entertainment =====
    MerchantEntry {
        pattern: "TICKETMASTER",
        account: "Expenses:Entertainment",
        category: "Entertainment",
    },
    MerchantEntry {
        pattern: r"STEAM\s*(GAMES|PURCHASE)",
        account: "Expenses:Entertainment:Games",
        category: "Entertainment",
    },
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn merchant_patterns_not_empty() {
        assert!(!MERCHANT_PATTERNS.is_empty());
        assert!(
            MERCHANT_PATTERNS.len() > 50,
            "Expected at least 50 merchant patterns"
        );
    }

    #[test]
    fn all_patterns_compile() {
        for entry in MERCHANT_PATTERNS {
            let result = regex::RegexBuilder::new(entry.pattern)
                .case_insensitive(true)
                .build();
            assert!(
                result.is_ok(),
                "Pattern '{}' for {} failed to compile: {:?}",
                entry.pattern,
                entry.account,
                result.err()
            );
        }
    }

    #[test]
    fn patterns_have_valid_accounts() {
        for entry in MERCHANT_PATTERNS {
            assert!(
                entry.account.starts_with("Expenses:") || entry.account.starts_with("Income:"),
                "Pattern '{}' has invalid account '{}' — must start with Expenses: or Income:",
                entry.pattern,
                entry.account,
            );
        }
    }

    #[test]
    fn patterns_have_categories() {
        for entry in MERCHANT_PATTERNS {
            assert!(
                !entry.category.is_empty(),
                "Pattern '{}' is missing a category",
                entry.pattern,
            );
        }
    }
}
