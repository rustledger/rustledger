//! Beancount options parsing and storage.

use rust_decimal::Decimal;
use std::collections::{HashMap, HashSet};
use std::str::FromStr;

/// Known beancount option names.
const KNOWN_OPTIONS: &[&str] = &[
    "title",
    "filename",
    "operating_currency",
    "name_assets",
    "name_liabilities",
    "name_equity",
    "name_income",
    "name_expenses",
    "account_rounding",
    "account_previous_balances",
    "account_previous_earnings",
    "account_previous_conversions",
    "account_current_earnings",
    "account_current_conversions",
    "account_unrealized_gains",
    "conversion_currency",
    "inferred_tolerance_default",
    "inferred_tolerance_multiplier",
    "infer_tolerance_from_cost",
    "use_legacy_fixed_tolerances",
    "experiment_explicit_tolerances",
    "booking_method",
    "render_commas",
    "allow_pipe_separator",
    "long_string_maxlines",
    "documents",
    "insert_pythonpath",
    "plugin_processing_mode",
];

/// Options that can be specified multiple times.
const REPEATABLE_OPTIONS: &[&str] = &["operating_currency", "insert_pythonpath", "documents"];

/// Option validation warning.
#[derive(Debug, Clone)]
pub struct OptionWarning {
    /// Warning code (E7001, E7002, E7003).
    pub code: &'static str,
    /// Warning message.
    pub message: String,
    /// Option name.
    pub option: String,
    /// Option value.
    pub value: String,
}

/// Beancount file options.
///
/// These correspond to the `option` directives in beancount files.
#[derive(Debug, Clone, Default)]
pub struct Options {
    /// Title for the ledger.
    pub title: Option<String>,

    /// Source filename (auto-set).
    pub filename: Option<String>,

    /// Operating currencies (for reporting).
    pub operating_currency: Vec<String>,

    /// Name prefix for Assets accounts.
    pub name_assets: String,

    /// Name prefix for Liabilities accounts.
    pub name_liabilities: String,

    /// Name prefix for Equity accounts.
    pub name_equity: String,

    /// Name prefix for Income accounts.
    pub name_income: String,

    /// Name prefix for Expenses accounts.
    pub name_expenses: String,

    /// Account for rounding errors.
    pub account_rounding: Option<String>,

    /// Account for previous balances (opening balances).
    pub account_previous_balances: String,

    /// Account for previous earnings.
    pub account_previous_earnings: String,

    /// Account for previous conversions.
    pub account_previous_conversions: String,

    /// Account for current earnings.
    pub account_current_earnings: String,

    /// Account for current conversion differences.
    pub account_current_conversions: Option<String>,

    /// Account for unrealized gains.
    pub account_unrealized_gains: Option<String>,

    /// Currency for conversion (if specified).
    pub conversion_currency: Option<String>,

    /// Default tolerances per currency (e.g., "USD:0.005" or "*:0.001").
    pub inferred_tolerance_default: HashMap<String, Decimal>,

    /// Tolerance multiplier for balance assertions.
    pub inferred_tolerance_multiplier: Decimal,

    /// Whether to infer tolerance from cost.
    pub infer_tolerance_from_cost: bool,

    /// Whether to use legacy fixed tolerances.
    pub use_legacy_fixed_tolerances: bool,

    /// Enable experimental explicit tolerances in balance assertions.
    pub experiment_explicit_tolerances: bool,

    /// Default booking method.
    pub booking_method: String,

    /// Whether to render commas in numbers.
    pub render_commas: bool,

    /// Whether to allow pipe separator in numbers.
    pub allow_pipe_separator: bool,

    /// Maximum lines in multi-line strings.
    pub long_string_maxlines: u32,

    /// Directories to scan for document files.
    pub documents: Vec<String>,

    /// Any other custom options.
    pub custom: HashMap<String, String>,

    /// Options that have been set (for duplicate detection).
    #[doc(hidden)]
    pub set_options: HashSet<String>,

    /// Validation warnings collected during parsing.
    pub warnings: Vec<OptionWarning>,
}

impl Options {
    /// Create new options with defaults.
    #[must_use]
    pub fn new() -> Self {
        Self {
            title: None,
            filename: None,
            operating_currency: Vec::new(),
            name_assets: "Assets".to_string(),
            name_liabilities: "Liabilities".to_string(),
            name_equity: "Equity".to_string(),
            name_income: "Income".to_string(),
            name_expenses: "Expenses".to_string(),
            account_rounding: None,
            account_previous_balances: "Equity:Opening-Balances".to_string(),
            account_previous_earnings: "Equity:Earnings:Previous".to_string(),
            account_previous_conversions: "Equity:Conversions:Previous".to_string(),
            account_current_earnings: "Equity:Earnings:Current".to_string(),
            account_current_conversions: None,
            account_unrealized_gains: None,
            conversion_currency: None,
            inferred_tolerance_default: HashMap::new(),
            inferred_tolerance_multiplier: Decimal::new(5, 1), // 0.5
            infer_tolerance_from_cost: true,
            use_legacy_fixed_tolerances: false,
            experiment_explicit_tolerances: false,
            booking_method: "STRICT".to_string(),
            render_commas: true,
            allow_pipe_separator: false,
            long_string_maxlines: 64,
            documents: Vec::new(),
            custom: HashMap::new(),
            set_options: HashSet::new(),
            warnings: Vec::new(),
        }
    }

    /// Set an option by name.
    ///
    /// Validates the option and collects any warnings in `self.warnings`.
    pub fn set(&mut self, key: &str, value: &str) {
        // Check for unknown options (E7001)
        let is_known = KNOWN_OPTIONS.contains(&key);
        if !is_known {
            self.warnings.push(OptionWarning {
                code: "E7001",
                message: format!("Unknown option \"{key}\""),
                option: key.to_string(),
                value: value.to_string(),
            });
        }

        // Check for duplicate non-repeatable options (E7003)
        let is_repeatable = REPEATABLE_OPTIONS.contains(&key);
        if is_known && !is_repeatable && self.set_options.contains(key) {
            self.warnings.push(OptionWarning {
                code: "E7003",
                message: format!("Option \"{key}\" can only be specified once"),
                option: key.to_string(),
                value: value.to_string(),
            });
        }

        // Track that this option was set
        self.set_options.insert(key.to_string());

        // Apply the option value
        match key {
            "title" => self.title = Some(value.to_string()),
            "operating_currency" => self.operating_currency.push(value.to_string()),
            "name_assets" => self.name_assets = value.to_string(),
            "name_liabilities" => self.name_liabilities = value.to_string(),
            "name_equity" => self.name_equity = value.to_string(),
            "name_income" => self.name_income = value.to_string(),
            "name_expenses" => self.name_expenses = value.to_string(),
            "account_rounding" => self.account_rounding = Some(value.to_string()),
            "account_current_conversions" => {
                self.account_current_conversions = Some(value.to_string());
            }
            "account_unrealized_gains" => {
                self.account_unrealized_gains = Some(value.to_string());
            }
            "inferred_tolerance_multiplier" => {
                if let Ok(d) = Decimal::from_str(value) {
                    self.inferred_tolerance_multiplier = d;
                } else {
                    // E7002: Invalid option value
                    self.warnings.push(OptionWarning {
                        code: "E7002",
                        message: format!(
                            "Invalid value \"{value}\" for option \"{key}\": expected decimal number"
                        ),
                        option: key.to_string(),
                        value: value.to_string(),
                    });
                }
            }
            "infer_tolerance_from_cost" => {
                if !value.eq_ignore_ascii_case("true") && !value.eq_ignore_ascii_case("false") {
                    self.warnings.push(OptionWarning {
                        code: "E7002",
                        message: format!(
                            "Invalid value \"{value}\" for option \"{key}\": expected TRUE or FALSE"
                        ),
                        option: key.to_string(),
                        value: value.to_string(),
                    });
                }
                self.infer_tolerance_from_cost = value.eq_ignore_ascii_case("true");
            }
            "booking_method" => {
                let valid_methods = [
                    "STRICT",
                    "STRICT_WITH_SIZE",
                    "FIFO",
                    "LIFO",
                    "HIFO",
                    "AVERAGE",
                    "NONE",
                ];
                if !valid_methods.contains(&value.to_uppercase().as_str()) {
                    self.warnings.push(OptionWarning {
                        code: "E7002",
                        message: format!(
                            "Invalid value \"{}\" for option \"{}\": expected one of {}",
                            value,
                            key,
                            valid_methods.join(", ")
                        ),
                        option: key.to_string(),
                        value: value.to_string(),
                    });
                }
                self.booking_method = value.to_string();
            }
            "render_commas" => {
                if !value.eq_ignore_ascii_case("true") && !value.eq_ignore_ascii_case("false") {
                    self.warnings.push(OptionWarning {
                        code: "E7002",
                        message: format!(
                            "Invalid value \"{value}\" for option \"{key}\": expected TRUE or FALSE"
                        ),
                        option: key.to_string(),
                        value: value.to_string(),
                    });
                }
                self.render_commas = value.eq_ignore_ascii_case("true");
            }
            "filename" => self.filename = Some(value.to_string()),
            "account_previous_balances" => self.account_previous_balances = value.to_string(),
            "account_previous_earnings" => self.account_previous_earnings = value.to_string(),
            "account_previous_conversions" => self.account_previous_conversions = value.to_string(),
            "account_current_earnings" => self.account_current_earnings = value.to_string(),
            "conversion_currency" => self.conversion_currency = Some(value.to_string()),
            "inferred_tolerance_default" => {
                // Parse "CURRENCY:TOLERANCE" or "*:TOLERANCE"
                if let Some((curr, tol)) = value.split_once(':') {
                    if let Ok(d) = Decimal::from_str(tol) {
                        self.inferred_tolerance_default.insert(curr.to_string(), d);
                    } else {
                        self.warnings.push(OptionWarning {
                            code: "E7002",
                            message: format!(
                                "Invalid tolerance value \"{tol}\" in option \"{key}\""
                            ),
                            option: key.to_string(),
                            value: value.to_string(),
                        });
                    }
                } else {
                    self.warnings.push(OptionWarning {
                        code: "E7002",
                        message: format!(
                            "Invalid format for option \"{key}\": expected CURRENCY:TOLERANCE"
                        ),
                        option: key.to_string(),
                        value: value.to_string(),
                    });
                }
            }
            "use_legacy_fixed_tolerances" => {
                self.use_legacy_fixed_tolerances = value.eq_ignore_ascii_case("true");
            }
            "experiment_explicit_tolerances" => {
                self.experiment_explicit_tolerances = value.eq_ignore_ascii_case("true");
            }
            "allow_pipe_separator" => {
                self.allow_pipe_separator = value.eq_ignore_ascii_case("true");
            }
            "long_string_maxlines" => {
                if let Ok(n) = value.parse::<u32>() {
                    self.long_string_maxlines = n;
                } else {
                    self.warnings.push(OptionWarning {
                        code: "E7002",
                        message: format!(
                            "Invalid value \"{value}\" for option \"{key}\": expected integer"
                        ),
                        option: key.to_string(),
                        value: value.to_string(),
                    });
                }
            }
            "documents" => self.documents.push(value.to_string()),
            _ => {
                // Unknown options go to custom map
                self.custom.insert(key.to_string(), value.to_string());
            }
        }
    }

    /// Get a custom option value.
    #[must_use]
    pub fn get(&self, key: &str) -> Option<&str> {
        self.custom.get(key).map(String::as_str)
    }

    /// Get all account type prefixes.
    #[must_use]
    pub fn account_types(&self) -> [&str; 5] {
        [
            &self.name_assets,
            &self.name_liabilities,
            &self.name_equity,
            &self.name_income,
            &self.name_expenses,
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_options() {
        let opts = Options::new();
        assert_eq!(opts.name_assets, "Assets");
        assert_eq!(opts.booking_method, "STRICT");
        assert!(opts.infer_tolerance_from_cost);
    }

    #[test]
    fn test_set_options() {
        let mut opts = Options::new();
        opts.set("title", "My Ledger");
        opts.set("operating_currency", "USD");
        opts.set("operating_currency", "EUR");
        opts.set("booking_method", "FIFO");

        assert_eq!(opts.title, Some("My Ledger".to_string()));
        assert_eq!(opts.operating_currency, vec!["USD", "EUR"]);
        assert_eq!(opts.booking_method, "FIFO");
    }

    #[test]
    fn test_custom_options() {
        let mut opts = Options::new();
        opts.set("my_custom_option", "my_value");

        assert_eq!(opts.get("my_custom_option"), Some("my_value"));
        assert_eq!(opts.get("nonexistent"), None);
    }

    #[test]
    fn test_unknown_option_warning() {
        let mut opts = Options::new();
        opts.set("unknown_option", "value");

        assert_eq!(opts.warnings.len(), 1);
        assert_eq!(opts.warnings[0].code, "E7001");
        assert!(opts.warnings[0].message.contains("Unknown option"));
    }

    #[test]
    fn test_duplicate_option_warning() {
        let mut opts = Options::new();
        opts.set("title", "First Title");
        opts.set("title", "Second Title");

        assert_eq!(opts.warnings.len(), 1);
        assert_eq!(opts.warnings[0].code, "E7003");
        assert!(opts.warnings[0].message.contains("only be specified once"));
    }

    #[test]
    fn test_repeatable_option_no_warning() {
        let mut opts = Options::new();
        opts.set("operating_currency", "USD");
        opts.set("operating_currency", "EUR");

        // No warnings for repeatable options
        assert!(
            opts.warnings.is_empty(),
            "Should not warn for repeatable options: {:?}",
            opts.warnings
        );
        assert_eq!(opts.operating_currency, vec!["USD", "EUR"]);
    }

    #[test]
    fn test_invalid_tolerance_value() {
        let mut opts = Options::new();
        opts.set("inferred_tolerance_multiplier", "not_a_number");

        assert_eq!(opts.warnings.len(), 1);
        assert_eq!(opts.warnings[0].code, "E7002");
        assert!(opts.warnings[0].message.contains("expected decimal"));
    }

    #[test]
    fn test_invalid_boolean_value() {
        let mut opts = Options::new();
        opts.set("infer_tolerance_from_cost", "maybe");

        assert_eq!(opts.warnings.len(), 1);
        assert_eq!(opts.warnings[0].code, "E7002");
        assert!(opts.warnings[0].message.contains("TRUE or FALSE"));
    }

    #[test]
    fn test_invalid_booking_method() {
        let mut opts = Options::new();
        opts.set("booking_method", "RANDOM");

        assert_eq!(opts.warnings.len(), 1);
        assert_eq!(opts.warnings[0].code, "E7002");
        assert!(opts.warnings[0].message.contains("STRICT"));
    }

    #[test]
    fn test_valid_booking_methods() {
        for method in &["STRICT", "FIFO", "LIFO", "AVERAGE", "NONE"] {
            let mut opts = Options::new();
            opts.set("booking_method", method);
            assert!(
                opts.warnings.is_empty(),
                "Should accept {method} as valid booking method"
            );
        }
    }
}
