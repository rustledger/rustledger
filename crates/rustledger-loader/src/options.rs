//! Beancount options parsing and storage.

use rust_decimal::Decimal;
use rustc_hash::{FxHashMap, FxHashSet};
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
    "display_precision",
    "allow_pipe_separator",
    "long_string_maxlines",
    "documents",
    "insert_pythonpath",
    "plugin_processing_mode",
    "plugin",               // Deprecated, but still known
    "tolerance_multiplier", // Renamed from inferred_tolerance_multiplier
];

/// Options that can be specified multiple times.
const REPEATABLE_OPTIONS: &[&str] = &[
    "operating_currency",
    "insert_pythonpath",
    "documents",
    "inferred_tolerance_default",
    "display_precision",
];

/// Options that are read-only and cannot be set by users.
const READONLY_OPTIONS: &[&str] = &["filename"];

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
#[derive(Debug, Clone)]
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
    pub inferred_tolerance_default: FxHashMap<String, Decimal>,

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

    /// Display precision per currency (e.g., "USD:2" means format USD with 2 decimal places).
    /// Format: CURRENCY:PRECISION where PRECISION is the number of decimal places.
    pub display_precision: FxHashMap<String, u32>,

    /// Whether to allow pipe separator in numbers.
    pub allow_pipe_separator: bool,

    /// Maximum lines in multi-line strings.
    pub long_string_maxlines: u32,

    /// Directories to scan for document files.
    pub documents: Vec<String>,

    /// Plugin processing mode: "default" or "raw".
    pub plugin_processing_mode: String,

    /// Any other custom options.
    pub custom: FxHashMap<String, String>,

    /// Options that have been set (for duplicate detection).
    #[doc(hidden)]
    pub set_options: FxHashSet<String>,

    /// Validation warnings collected during parsing.
    pub warnings: Vec<OptionWarning>,
}

impl Default for Options {
    fn default() -> Self {
        Self::new()
    }
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
            inferred_tolerance_default: FxHashMap::default(),
            inferred_tolerance_multiplier: Decimal::new(5, 1), // 0.5
            infer_tolerance_from_cost: false,
            use_legacy_fixed_tolerances: false,
            experiment_explicit_tolerances: false,
            booking_method: "STRICT".to_string(),
            render_commas: false, // Python beancount default is FALSE
            display_precision: FxHashMap::default(),
            allow_pipe_separator: false,
            long_string_maxlines: 64,
            documents: Vec::new(),
            plugin_processing_mode: "default".to_string(),
            custom: FxHashMap::default(),
            set_options: FxHashSet::default(),
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
                message: format!("Invalid option \"{key}\""),
                option: key.to_string(),
                value: value.to_string(),
            });
        }

        // Check for read-only options (E7005)
        if READONLY_OPTIONS.contains(&key) {
            self.warnings.push(OptionWarning {
                code: "E7005",
                message: format!("Option '{key}' may not be set"),
                option: key.to_string(),
                value: value.to_string(),
            });
            return; // Don't apply the value
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
            "account_rounding" => {
                if !Self::is_valid_account(value) {
                    self.warnings.push(OptionWarning {
                        code: "E7002",
                        message: format!("Invalid leaf account name: '{value}'"),
                        option: key.to_string(),
                        value: value.to_string(),
                    });
                }
                self.account_rounding = Some(value.to_string());
            }
            "account_current_conversions" => {
                if !Self::is_valid_account(value) {
                    self.warnings.push(OptionWarning {
                        code: "E7002",
                        message: format!("Invalid leaf account name: '{value}'"),
                        option: key.to_string(),
                        value: value.to_string(),
                    });
                }
                self.account_current_conversions = Some(value.to_string());
            }
            "account_unrealized_gains" => {
                if !Self::is_valid_account(value) {
                    self.warnings.push(OptionWarning {
                        code: "E7002",
                        message: format!("Invalid leaf account name: '{value}'"),
                        option: key.to_string(),
                        value: value.to_string(),
                    });
                }
                self.account_unrealized_gains = Some(value.to_string());
            }
            "inferred_tolerance_multiplier" => {
                // Deprecated: renamed to tolerance_multiplier in Python beancount
                self.warnings.push(OptionWarning {
                    code: "E7004",
                    message: "Renamed to 'tolerance_multiplier'.".to_string(),
                    option: key.to_string(),
                    value: value.to_string(),
                });
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
            "tolerance_multiplier" => {
                if let Ok(d) = Decimal::from_str(value) {
                    self.inferred_tolerance_multiplier = d;
                } else {
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
                // Accept TRUE/FALSE, true/false, 1/0 (Python beancount compatibility)
                let is_true = value.eq_ignore_ascii_case("true") || value == "1";
                let is_false = value.eq_ignore_ascii_case("false") || value == "0";
                if !is_true && !is_false {
                    self.warnings.push(OptionWarning {
                        code: "E7002",
                        message: format!(
                            "Invalid value \"{value}\" for option \"{key}\": expected TRUE or FALSE"
                        ),
                        option: key.to_string(),
                        value: value.to_string(),
                    });
                }
                self.render_commas = is_true;
            }
            "display_precision" => {
                // Parse "CURRENCY:EXAMPLE" where EXAMPLE's decimal places define the precision.
                // E.g., "CHF:0.01" means 2 decimal places for CHF.
                // E.g., "USD:0.001" means 3 decimal places for USD.
                if let Some((curr, example)) = value.split_once(':') {
                    if let Ok(d) = Decimal::from_str(example) {
                        // Get the precision from the example number's decimal places
                        let precision = d.scale();
                        self.display_precision.insert(curr.to_string(), precision);
                    } else {
                        self.warnings.push(OptionWarning {
                            code: "E7002",
                            message: format!(
                                "Invalid precision value \"{example}\" in option \"{key}\""
                            ),
                            option: key.to_string(),
                            value: value.to_string(),
                        });
                    }
                } else {
                    self.warnings.push(OptionWarning {
                        code: "E7002",
                        message: format!(
                            "Invalid format for option \"{key}\": expected CURRENCY:EXAMPLE (e.g., CHF:0.01)"
                        ),
                        option: key.to_string(),
                        value: value.to_string(),
                    });
                }
            }
            "filename" => self.filename = Some(value.to_string()),
            "account_previous_balances" => {
                if !Self::is_valid_account(value) {
                    self.warnings.push(OptionWarning {
                        code: "E7002",
                        message: format!("Invalid leaf account name: '{value}'"),
                        option: key.to_string(),
                        value: value.to_string(),
                    });
                }
                self.account_previous_balances = value.to_string();
            }
            "account_previous_earnings" => {
                if !Self::is_valid_account(value) {
                    self.warnings.push(OptionWarning {
                        code: "E7002",
                        message: format!("Invalid leaf account name: '{value}'"),
                        option: key.to_string(),
                        value: value.to_string(),
                    });
                }
                self.account_previous_earnings = value.to_string();
            }
            "account_previous_conversions" => {
                if !Self::is_valid_account(value) {
                    self.warnings.push(OptionWarning {
                        code: "E7002",
                        message: format!("Invalid leaf account name: '{value}'"),
                        option: key.to_string(),
                        value: value.to_string(),
                    });
                }
                self.account_previous_conversions = value.to_string();
            }
            "account_current_earnings" => {
                if !Self::is_valid_account(value) {
                    self.warnings.push(OptionWarning {
                        code: "E7002",
                        message: format!("Invalid leaf account name: '{value}'"),
                        option: key.to_string(),
                        value: value.to_string(),
                    });
                }
                self.account_current_earnings = value.to_string();
            }
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
                // This option is deprecated in Python beancount
                self.warnings.push(OptionWarning {
                    code: "E7004",
                    message: "Option 'allow_pipe_separator' is deprecated".to_string(),
                    option: key.to_string(),
                    value: value.to_string(),
                });
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
            "documents" => {
                // Validate that document root exists
                if !std::path::Path::new(value).exists() {
                    self.warnings.push(OptionWarning {
                        code: "E7006",
                        message: format!("Document root '{value}' does not exist"),
                        option: key.to_string(),
                        value: value.to_string(),
                    });
                }
                self.documents.push(value.to_string());
            }
            "plugin_processing_mode" => {
                // Valid values are "default" and "raw" (case-sensitive, like Python)
                if value != "default" && value != "raw" {
                    self.warnings.push(OptionWarning {
                        code: "E7002",
                        message: format!("Invalid value '{value}'"),
                        option: key.to_string(),
                        value: value.to_string(),
                    });
                }
                self.plugin_processing_mode = value.to_string();
            }
            "plugin" => {
                // Deprecated: should use `plugin` directive instead of `option "plugin"`
                self.warnings.push(OptionWarning {
                    code: "E7004",
                    message: "Option 'plugin' is deprecated; use the 'plugin' directive instead"
                        .to_string(),
                    option: key.to_string(),
                    value: value.to_string(),
                });
            }
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

    /// Check if a value looks like a valid account name.
    ///
    /// Valid accounts have format "Type:Subaccount:..." where each component
    /// starts with an uppercase letter (any script) or a non-ASCII letter
    /// without case (CJK, etc.), and components are colon-separated.
    fn is_valid_account(value: &str) -> bool {
        // Must contain at least one colon
        if !value.contains(':') {
            return false;
        }

        // Check each component
        for part in value.split(':') {
            if let Some(first) = part.chars().next() {
                // Accept: uppercase (any script), non-ASCII alphabetic (CJK, etc.)
                let valid = first.is_uppercase() || (!first.is_ascii() && first.is_alphabetic());
                if !valid {
                    return false;
                }
            } else {
                // Empty component
                return false;
            }
        }

        true
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
        assert!(!opts.infer_tolerance_from_cost);
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
        assert!(opts.warnings[0].message.contains("Invalid option"));
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

        // E7004 (deprecated name) + E7002 (invalid value)
        assert_eq!(opts.warnings.len(), 2);
        assert_eq!(opts.warnings[0].code, "E7004");
        assert!(opts.warnings[0].message.contains("Renamed"));
        assert_eq!(opts.warnings[1].code, "E7002");
        assert!(opts.warnings[1].message.contains("expected decimal"));
    }

    #[test]
    fn test_tolerance_multiplier_new_name() {
        let mut opts = Options::new();
        opts.set("tolerance_multiplier", "1.5");

        assert!(opts.warnings.is_empty());
        assert_eq!(opts.inferred_tolerance_multiplier, Decimal::new(15, 1));
    }

    #[test]
    fn test_inferred_tolerance_multiplier_deprecated() {
        let mut opts = Options::new();
        opts.set("inferred_tolerance_multiplier", "1.01");

        assert_eq!(opts.warnings.len(), 1);
        assert_eq!(opts.warnings[0].code, "E7004");
        assert!(
            opts.warnings[0]
                .message
                .contains("Renamed to 'tolerance_multiplier'")
        );
        assert_eq!(
            opts.inferred_tolerance_multiplier,
            Decimal::from_str("1.01").unwrap()
        );
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

    #[test]
    fn test_readonly_option_warning() {
        let mut opts = Options::new();
        opts.set("filename", "/some/path.beancount");

        assert_eq!(opts.warnings.len(), 1);
        assert_eq!(opts.warnings[0].code, "E7005");
        assert!(opts.warnings[0].message.contains("may not be set"));
    }

    #[test]
    fn test_invalid_account_name_validation() {
        // Test account_rounding with invalid value
        let mut opts = Options::new();
        opts.set("account_rounding", "invalid");

        assert_eq!(opts.warnings.len(), 1);
        assert_eq!(opts.warnings[0].code, "E7002");
        assert!(opts.warnings[0].message.contains("Invalid leaf account"));
    }

    #[test]
    fn test_valid_account_name() {
        let mut opts = Options::new();
        opts.set("account_rounding", "Equity:Rounding");

        assert!(
            opts.warnings.is_empty(),
            "Valid account name should not produce warnings: {:?}",
            opts.warnings
        );
        assert_eq!(opts.account_rounding, Some("Equity:Rounding".to_string()));
    }

    #[test]
    fn test_render_commas_with_numeric_values() {
        let mut opts = Options::new();
        opts.set("render_commas", "1");
        assert!(opts.render_commas);
        assert!(opts.warnings.is_empty());

        let mut opts2 = Options::new();
        opts2.set("render_commas", "0");
        assert!(!opts2.render_commas);
        assert!(opts2.warnings.is_empty());
    }

    #[test]
    fn test_plugin_processing_mode_validation() {
        // Valid values
        let mut opts = Options::new();
        opts.set("plugin_processing_mode", "default");
        assert!(opts.warnings.is_empty());
        assert_eq!(opts.plugin_processing_mode, "default");

        let mut opts2 = Options::new();
        opts2.set("plugin_processing_mode", "raw");
        assert!(opts2.warnings.is_empty());
        assert_eq!(opts2.plugin_processing_mode, "raw");

        // Invalid value
        let mut opts3 = Options::new();
        opts3.set("plugin_processing_mode", "invalid");
        assert_eq!(opts3.warnings.len(), 1);
        assert_eq!(opts3.warnings[0].code, "E7002");
    }

    #[test]
    fn test_deprecated_plugin_option() {
        let mut opts = Options::new();
        opts.set("plugin", "some.plugin");

        assert_eq!(opts.warnings.len(), 1);
        assert_eq!(opts.warnings[0].code, "E7004");
        assert!(opts.warnings[0].message.contains("deprecated"));
    }

    #[test]
    fn test_deprecated_allow_pipe_separator() {
        let mut opts = Options::new();
        opts.set("allow_pipe_separator", "true");

        assert_eq!(opts.warnings.len(), 1);
        assert_eq!(opts.warnings[0].code, "E7004");
        assert!(opts.warnings[0].message.contains("deprecated"));
    }

    #[test]
    fn test_is_valid_account() {
        // Valid accounts — ASCII
        assert!(Options::is_valid_account("Assets:Bank"));
        assert!(Options::is_valid_account("Equity:Rounding:Precision"));

        // Valid accounts — Unicode
        assert!(Options::is_valid_account("Капитал:Retained"));
        assert!(Options::is_valid_account("资产:银行:支票"));

        // Invalid accounts
        assert!(!Options::is_valid_account("invalid")); // No colon
        assert!(!Options::is_valid_account("assets:bank")); // Lowercase ASCII
        assert!(!Options::is_valid_account("Assets:")); // Empty component
        assert!(!Options::is_valid_account(":Bank")); // Empty first component
    }

    #[test]
    fn test_account_validation_options() {
        // Test all account options that require validation
        let account_options = [
            "account_rounding",
            "account_current_conversions",
            "account_unrealized_gains",
            "account_previous_balances",
            "account_previous_earnings",
            "account_previous_conversions",
            "account_current_earnings",
        ];

        for opt in account_options {
            let mut opts = Options::new();
            opts.set(opt, "lowercase:invalid");

            assert!(
                !opts.warnings.is_empty(),
                "Option '{opt}' should warn on invalid account name"
            );
            assert_eq!(opts.warnings[0].code, "E7002");
        }
    }

    #[test]
    fn test_inferred_tolerance_default() {
        let mut opts = Options::new();
        opts.set("inferred_tolerance_default", "USD:0.005");

        assert!(opts.warnings.is_empty());
        assert_eq!(
            opts.inferred_tolerance_default.get("USD"),
            Some(&rust_decimal_macros::dec!(0.005))
        );

        // Test wildcard
        let mut opts2 = Options::new();
        opts2.set("inferred_tolerance_default", "*:0.01");
        assert!(opts2.warnings.is_empty());
        assert_eq!(
            opts2.inferred_tolerance_default.get("*"),
            Some(&rust_decimal_macros::dec!(0.01))
        );

        // Test invalid format
        let mut opts3 = Options::new();
        opts3.set("inferred_tolerance_default", "INVALID");
        assert_eq!(opts3.warnings.len(), 1);
        assert_eq!(opts3.warnings[0].code, "E7002");
    }

    #[test]
    fn test_display_precision_basic() {
        let mut opts = Options::new();
        opts.set("display_precision", "USD:0.01");
        assert!(opts.warnings.is_empty(), "warnings: {:?}", opts.warnings);
        assert_eq!(opts.display_precision.get("USD"), Some(&2));
    }

    #[test]
    fn test_display_precision_high_precision() {
        let mut opts = Options::new();
        opts.set("display_precision", "BTC:0.00000001");
        assert!(opts.warnings.is_empty());
        assert_eq!(opts.display_precision.get("BTC"), Some(&8));
    }

    #[test]
    fn test_display_precision_zero_decimals() {
        // "JPY:1" → no fractional digits → precision 0.
        let mut opts = Options::new();
        opts.set("display_precision", "JPY:1");
        assert!(opts.warnings.is_empty());
        assert_eq!(opts.display_precision.get("JPY"), Some(&0));
    }

    #[test]
    fn test_display_precision_repeatable_per_currency() {
        let mut opts = Options::new();
        opts.set("display_precision", "USD:0.01");
        opts.set("display_precision", "EUR:0.001");
        assert!(opts.warnings.is_empty(), "warnings: {:?}", opts.warnings);
        assert_eq!(opts.display_precision.get("USD"), Some(&2));
        assert_eq!(opts.display_precision.get("EUR"), Some(&3));
    }

    #[test]
    fn test_display_precision_missing_colon_warns() {
        let mut opts = Options::new();
        opts.set("display_precision", "USD0.01");
        assert_eq!(opts.warnings.len(), 1);
        assert_eq!(opts.warnings[0].code, "E7002");
        assert!(opts.warnings[0].message.contains("CURRENCY:EXAMPLE"));
        assert!(opts.display_precision.is_empty());
    }

    #[test]
    fn test_display_precision_invalid_example_warns() {
        let mut opts = Options::new();
        opts.set("display_precision", "USD:abc");
        assert_eq!(opts.warnings.len(), 1);
        assert_eq!(opts.warnings[0].code, "E7002");
        assert!(opts.warnings[0].message.contains("Invalid precision"));
        assert!(opts.display_precision.is_empty());
    }
}
