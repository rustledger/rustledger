//! Rules-based transaction categorization.
//!
//! The [`RulesEngine`] matches transaction payee/narration against a set of
//! rules to determine the contra-account. Rules can use substring matching,
//! regex patterns, or exact matching. They are evaluated in priority order
//! (highest first), with first match winning.
//!
//! The engine can also load the built-in merchant dictionary from
//! [`crate::merchants`] as low-priority fallback rules.

use crate::enrichment::CategorizationMethod;
use regex::Regex;
use std::sync::LazyLock;

/// Built-in merchant-dictionary regexes, compiled once on first use. Patterns
/// that fail to compile are skipped. Each entry pairs a case-insensitive,
/// unanchored regex with its `&'static` category and account; the `Regex` is
/// cheaply `Arc`-cloned into per-engine rules by [`RulesEngine::load_merchant_dict`].
static MERCHANT_REGEXES: LazyLock<Vec<(Regex, &'static str, &'static str)>> = LazyLock::new(|| {
    crate::merchants::MERCHANT_PATTERNS
        .iter()
        .filter_map(|entry| {
            regex::RegexBuilder::new(entry.pattern)
                .case_insensitive(true)
                .build()
                .ok()
                .map(|re| (re, entry.category, entry.account))
        })
        .collect()
});

/// A categorization rule.
#[derive(Debug)]
pub struct Rule {
    /// Optional name for this rule (for debugging/display).
    pub name: Option<String>,
    /// The pattern to match against payee/narration.
    pub pattern: RulePattern,
    /// The account to assign when this rule matches.
    pub account: String,
    /// Priority for ordering (higher = checked first). Default: 0.
    /// User rules should use positive priorities, merchant dict uses -1000.
    pub priority: i32,
}

/// Pattern types for matching.
#[derive(Debug)]
pub enum RulePattern {
    /// Case-insensitive substring match (fast, no regex overhead).
    ///
    /// The stored value **must be lowercase** because [`RulesEngine::categorize`]
    /// lowercases input text before comparison using a case-sensitive `contains()`.
    Substring(String),
    /// Compiled regex pattern.
    Regex(Regex),
    /// Exact case-insensitive match.
    Exact(String),
}

impl RulePattern {
    /// Test if this pattern matches the given text.
    fn matches(&self, text: &str) -> bool {
        match self {
            Self::Substring(s) => text.contains(s.as_str()),
            Self::Regex(r) => r.is_match(text),
            Self::Exact(s) => text.eq_ignore_ascii_case(s.as_str()),
        }
    }
}

/// Result of a successful categorization match.
#[derive(Debug, Clone)]
pub struct RuleMatch {
    /// The matched account.
    pub account: String,
    /// Name of the rule that matched (if any).
    pub rule_name: Option<String>,
    /// How this match was determined.
    pub method: CategorizationMethod,
    /// Confidence score (1.0 for rules, lower for weaker matches).
    pub confidence: f64,
}

/// Rules engine for transaction categorization.
///
/// Evaluates rules in priority order (highest first). First match wins.
/// Supports loading rules from user config, merchant dictionary, or both.
#[derive(Debug)]
pub struct RulesEngine {
    rules: Vec<Rule>,
}

impl RulesEngine {
    /// Create an empty rules engine.
    #[must_use]
    pub const fn new() -> Self {
        Self { rules: Vec::new() }
    }

    /// Add a single rule.
    ///
    /// Rules are kept sorted by priority (descending) after each insertion.
    pub fn add_rule(&mut self, rule: Rule) {
        self.rules.push(rule);
        self.rules.sort_by_key(|r| std::cmp::Reverse(r.priority));
    }

    /// Load rules from substring-based mappings (existing `importers.toml` format).
    ///
    /// All patterns are lowercased. Priority is set to 0 (user rules).
    pub fn load_from_mappings(&mut self, mappings: &[(String, String)]) {
        for (pattern, account) in mappings {
            self.rules.push(Rule {
                name: None,
                pattern: RulePattern::Substring(pattern.to_lowercase()),
                account: account.clone(),
                priority: 0,
            });
        }
        self.rules.sort_by_key(|r| std::cmp::Reverse(r.priority));
    }

    /// Load rules from regex-based mappings.
    ///
    /// Patterns that fail to compile are silently skipped.
    /// Priority is set to 0 (user rules).
    pub fn load_from_regex_mappings(&mut self, mappings: &[(String, String)]) {
        for (pattern, account) in mappings {
            if let Ok(regex) = regex::RegexBuilder::new(pattern)
                .case_insensitive(true)
                .build()
            {
                self.rules.push(Rule {
                    name: Some(pattern.clone()),
                    pattern: RulePattern::Regex(regex),
                    account: account.clone(),
                    priority: 0,
                });
            }
        }
        self.rules.sort_by_key(|r| std::cmp::Reverse(r.priority));
    }

    /// Load the built-in merchant dictionary as low-priority rules.
    pub fn load_merchant_dict(&mut self) {
        // Merchant regexes are compiled once process-wide (see `MERCHANT_REGEXES`)
        // and cheaply `Arc`-cloned per engine. Recompiling them on every
        // `build_rules_engine` call — one per imported file — was a real cost;
        // this restores the cache the plain CSV path had before unification,
        // now shared by both the plain and enriched paths.
        for (regex, category, account) in MERCHANT_REGEXES.iter() {
            self.rules.push(Rule {
                name: Some((*category).to_string()),
                pattern: RulePattern::Regex(regex.clone()),
                account: (*account).to_string(),
                priority: -1000, // Below all user rules
            });
        }
        self.rules.sort_by_key(|r| std::cmp::Reverse(r.priority));
    }

    /// Categorize a transaction by matching payee and narration against rules.
    ///
    /// Returns the first matching rule's account and metadata, or `None` if
    /// no rule matches.
    pub fn categorize(&self, payee: Option<&str>, narration: &str) -> Option<RuleMatch> {
        let payee_lower = payee.map(str::to_lowercase);
        let narration_lower = narration.to_lowercase();

        for rule in &self.rules {
            // Try payee first (more specific)
            if let Some(ref p) = payee_lower
                && rule.pattern.matches(p)
            {
                return Some(RuleMatch {
                    account: rule.account.clone(),
                    rule_name: rule.name.clone(),
                    method: if rule.priority <= -1000 {
                        CategorizationMethod::MerchantDict
                    } else {
                        CategorizationMethod::Rule
                    },
                    confidence: 1.0,
                });
            }
            // Then narration
            if rule.pattern.matches(&narration_lower) {
                return Some(RuleMatch {
                    account: rule.account.clone(),
                    rule_name: rule.name.clone(),
                    method: if rule.priority <= -1000 {
                        CategorizationMethod::MerchantDict
                    } else {
                        CategorizationMethod::Rule
                    },
                    confidence: 1.0,
                });
            }
        }

        None
    }

    /// Number of loaded rules.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.rules.len()
    }

    /// Whether the engine has no rules.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.rules.is_empty()
    }
}

impl Default for RulesEngine {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn substring_match() {
        let mut engine = RulesEngine::new();
        engine.load_from_mappings(&[("amazon".to_string(), "Expenses:Shopping".to_string())]);

        let result = engine.categorize(Some("AMAZON MARKETPLACE"), "Order #123");
        assert!(result.is_some());
        assert_eq!(result.unwrap().account, "Expenses:Shopping");
    }

    #[test]
    fn substring_match_narration() {
        let mut engine = RulesEngine::new();
        engine.load_from_mappings(&[("coffee".to_string(), "Expenses:Dining:Coffee".to_string())]);

        let result = engine.categorize(None, "Morning coffee at the cafe");
        assert!(result.is_some());
        assert_eq!(result.unwrap().account, "Expenses:Dining:Coffee");
    }

    #[test]
    fn regex_match() {
        let mut engine = RulesEngine::new();
        engine.load_from_regex_mappings(&[(
            r"UBER(EATS)?".to_string(),
            "Expenses:Transport".to_string(),
        )]);

        let result = engine.categorize(Some("UBEREATS"), "food delivery");
        assert!(result.is_some());
        assert_eq!(result.unwrap().account, "Expenses:Transport");

        let result = engine.categorize(Some("UBER TRIP"), "ride");
        assert!(result.is_some());
    }

    #[test]
    fn no_match_returns_none() {
        let mut engine = RulesEngine::new();
        engine.load_from_mappings(&[("amazon".to_string(), "Expenses:Shopping".to_string())]);

        let result = engine.categorize(Some("STARBUCKS"), "Latte");
        assert!(result.is_none());
    }

    #[test]
    fn priority_ordering() {
        let mut engine = RulesEngine::new();
        // Low priority rule
        engine.add_rule(Rule {
            name: Some("general".to_string()),
            pattern: RulePattern::Substring("food".to_string()),
            account: "Expenses:Food".to_string(),
            priority: -100,
        });
        // High priority rule
        engine.add_rule(Rule {
            name: Some("specific".to_string()),
            pattern: RulePattern::Substring("food".to_string()),
            account: "Expenses:Groceries".to_string(),
            priority: 100,
        });

        let result = engine.categorize(None, "whole food market");
        assert!(result.is_some());
        assert_eq!(result.unwrap().account, "Expenses:Groceries");
    }

    #[test]
    fn user_rules_beat_merchant_dict() {
        let mut engine = RulesEngine::new();
        // User rule (priority 0)
        engine.load_from_mappings(&[("starbucks".to_string(), "Expenses:Coffee".to_string())]);
        // Merchant dict (priority -1000)
        engine.load_merchant_dict();

        let result = engine.categorize(Some("STARBUCKS"), "");
        assert!(result.is_some());
        let m = result.unwrap();
        assert_eq!(m.account, "Expenses:Coffee");
        assert_eq!(m.method, CategorizationMethod::Rule);
    }

    #[test]
    fn merchant_dict_as_fallback() {
        let mut engine = RulesEngine::new();
        engine.load_merchant_dict();

        // Netflix should be in the dictionary
        let result = engine.categorize(Some("NETFLIX.COM"), "");
        assert!(result.is_some());
        let m = result.unwrap();
        assert_eq!(m.method, CategorizationMethod::MerchantDict);
    }

    #[test]
    fn exact_match() {
        let mut engine = RulesEngine::new();
        engine.add_rule(Rule {
            name: None,
            pattern: RulePattern::Exact("rent".to_string()),
            account: "Expenses:Rent".to_string(),
            priority: 0,
        });

        // Exact match works
        let result = engine.categorize(None, "rent");
        assert!(result.is_some());

        // Substring doesn't match exact
        let result = engine.categorize(None, "rent payment");
        assert!(result.is_none());
    }

    #[test]
    fn payee_takes_priority_over_narration() {
        let mut engine = RulesEngine::new();
        engine.load_from_mappings(&[("whole foods".to_string(), "Expenses:Groceries".to_string())]);
        engine.load_from_mappings(&[("whole foods".to_string(), "Expenses:Organic".to_string())]);

        // First rule wins (same priority, same pattern — first added wins)
        let result = engine.categorize(Some("Whole Foods Market"), "weekly shopping");
        assert_eq!(result.unwrap().account, "Expenses:Groceries");
    }

    #[test]
    fn empty_engine() {
        let engine = RulesEngine::new();
        assert!(engine.is_empty());
        assert_eq!(engine.len(), 0);
        assert!(engine.categorize(Some("anything"), "anything").is_none());
    }
}
