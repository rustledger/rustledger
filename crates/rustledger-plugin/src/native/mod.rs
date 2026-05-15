//! Native (non-WASM) plugin support.
//!
//! These plugins run as native Rust code for maximum performance.
//! They implement the same interface as WASM plugins.

mod plugins;

pub use plugins::*;

use crate::types::PluginInput;
use crate::types::PluginOutput;

/// Trait for native plugins.
pub trait NativePlugin: Send + Sync {
    /// Plugin name.
    fn name(&self) -> &'static str;

    /// Plugin description.
    fn description(&self) -> &'static str;

    /// Process directives and return modified directives + errors.
    fn process(&self, input: PluginInput) -> PluginOutput;

    /// Whether this plugin synthesizes directives the loader's
    /// `Phase::Early` validation depends on (e.g. injecting `Open`
    /// directives so account-presence checks see them).
    ///
    /// Plugins returning `true` run in the loader's pre-booking pass;
    /// plugins returning `false` (the default — transformations on
    /// already-parsed directives) run post-booking so they see
    /// filled-in `cost.number_per` values from the booker.
    ///
    /// This is the trait-level analogue of the loader's `PluginPass`
    /// enum; the loader consults this method to classify each plugin
    /// at scheduling time, avoiding a hardcoded list of synthesizer
    /// names.
    fn is_synth(&self) -> bool {
        false
    }
}

/// Registry of built-in native plugins.
pub struct NativePluginRegistry {
    plugins: Vec<Box<dyn NativePlugin>>,
}

/// Extract the short plugin name from a potentially qualified module path.
///
/// Examples:
/// - `"zerosum"` → `"zerosum"`
/// - `"beancount.plugins.implicit_prices"` → `"implicit_prices"`
/// - `"beancount_reds_plugins.zerosum.zerosum"` → `"zerosum"`
#[inline]
fn plugin_short_name(name: &str) -> &str {
    name.rsplit('.').next().unwrap_or(name)
}

impl NativePluginRegistry {
    /// Create a new registry with all built-in plugins.
    pub fn new() -> Self {
        Self {
            plugins: vec![
                Box::new(ImplicitPricesPlugin),
                Box::new(CheckCommodityPlugin),
                Box::new(AutoTagPlugin::new()),
                Box::new(AutoAccountsPlugin),
                Box::new(LeafOnlyPlugin),
                Box::new(NoDuplicatesPlugin),
                Box::new(OneCommodityPlugin),
                Box::new(UniquePricesPlugin),
                Box::new(CheckClosingPlugin),
                Box::new(CloseTreePlugin),
                Box::new(CoherentCostPlugin),
                Box::new(ForecastPlugin),
                Box::new(SellGainsPlugin),
                Box::new(PedanticPlugin),
                Box::new(RxTxnPlugin),
                Box::new(SplitExpensesPlugin),
                Box::new(UnrealizedPlugin::new()),
                Box::new(NoUnusedPlugin),
                Box::new(CheckDrainedPlugin),
                Box::new(CommodityAttrPlugin::new()),
                Box::new(CheckAverageCostPlugin::new()),
                Box::new(CurrencyAccountsPlugin::new()),
                Box::new(ZerosumPlugin),
                Box::new(EffectiveDatePlugin),
                Box::new(GenerateBaseCcyPricesPlugin),
                Box::new(RenameAccountsPlugin),
                Box::new(ValuationPlugin),
                Box::new(CapitalGainsLongShortPlugin),
                Box::new(CapitalGainsGainLossPlugin),
                Box::new(BoxAccrualPlugin),
            ],
        }
    }

    /// Find a plugin by name.
    ///
    /// Accepts both short names (`"implicit_prices"`) and fully qualified
    /// module paths (`"beancount.plugins.implicit_prices"`).
    pub fn find(&self, name: &str) -> Option<&dyn NativePlugin> {
        let short_name = plugin_short_name(name);
        self.plugins
            .iter()
            .find(|p| p.name() == short_name)
            .map(std::convert::AsRef::as_ref)
    }

    /// List all available plugins.
    pub fn list(&self) -> Vec<&dyn NativePlugin> {
        self.plugins.iter().map(AsRef::as_ref).collect()
    }

    /// Check if a name refers to a built-in plugin.
    ///
    /// Accepts both short names and fully qualified module paths.
    pub fn is_builtin(name: &str) -> bool {
        let short_name = plugin_short_name(name);
        // Check against registered plugin names
        let registry = Self::new();
        registry.plugins.iter().any(|p| p.name() == short_name)
    }
}

impl Default for NativePluginRegistry {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_plugin_short_name_bare() {
        assert_eq!(plugin_short_name("zerosum"), "zerosum");
        assert_eq!(plugin_short_name("implicit_prices"), "implicit_prices");
    }

    #[test]
    fn test_plugin_short_name_beancount_plugins() {
        assert_eq!(
            plugin_short_name("beancount.plugins.implicit_prices"),
            "implicit_prices"
        );
        assert_eq!(
            plugin_short_name("beancount.plugins.check_commodity"),
            "check_commodity"
        );
    }

    #[test]
    fn test_plugin_short_name_beanahead() {
        assert_eq!(
            plugin_short_name("beanahead.plugins.rx_txn_plugin"),
            "rx_txn_plugin"
        );
    }

    #[test]
    fn test_plugin_short_name_reds_plugins() {
        assert_eq!(
            plugin_short_name("beancount_reds_plugins.zerosum.zerosum"),
            "zerosum"
        );
        assert_eq!(
            plugin_short_name("beancount_reds_plugins.capital_gains_classifier.gain_loss"),
            "gain_loss"
        );
        assert_eq!(
            plugin_short_name("beancount_reds_plugins.effective_date.effective_date"),
            "effective_date"
        );
    }

    #[test]
    fn test_plugin_short_name_tarioch() {
        assert_eq!(
            plugin_short_name("tariochbctools.plugins.generate_base_ccy_prices"),
            "generate_base_ccy_prices"
        );
    }

    #[test]
    fn test_plugin_short_name_empty() {
        assert_eq!(plugin_short_name(""), "");
    }

    #[test]
    fn test_registry_find_short_name() {
        let registry = NativePluginRegistry::new();
        assert!(registry.find("implicit_prices").is_some());
        assert!(registry.find("zerosum").is_some());
        assert!(registry.find("nonexistent").is_none());
    }

    #[test]
    fn test_registry_find_qualified_name() {
        let registry = NativePluginRegistry::new();
        assert!(registry.find("beancount.plugins.implicit_prices").is_some());
        assert!(registry.find("beanahead.plugins.rx_txn_plugin").is_some());
        assert!(
            registry
                .find("beancount_reds_plugins.zerosum.zerosum")
                .is_some()
        );
        assert!(
            registry
                .find("beancount_reds_plugins.capital_gains_classifier.gain_loss")
                .is_some()
        );
    }

    #[test]
    fn test_is_builtin_short_name() {
        assert!(NativePluginRegistry::is_builtin("implicit_prices"));
        assert!(NativePluginRegistry::is_builtin("zerosum"));
        assert!(!NativePluginRegistry::is_builtin("nonexistent"));
    }

    #[test]
    fn test_is_builtin_qualified_name() {
        assert!(NativePluginRegistry::is_builtin(
            "beancount.plugins.implicit_prices"
        ));
        assert!(NativePluginRegistry::is_builtin(
            "beanahead.plugins.rx_txn_plugin"
        ));
        assert!(NativePluginRegistry::is_builtin(
            "beancount_reds_plugins.zerosum.zerosum"
        ));
        assert!(!NativePluginRegistry::is_builtin("some.random.nonexistent"));
    }
}
