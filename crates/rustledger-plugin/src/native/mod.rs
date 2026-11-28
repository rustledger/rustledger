//! Native (non-WASM) plugin support.
//!
//! These plugins run as native Rust code for maximum performance.
//! They implement the same interface as WASM plugins.
//!
//! ## Pass discrimination (issue #1166)
//!
//! Plugins run in one of two passes — see the loader's `PluginPass`
//! enum:
//!
//! - **Pre-booking synth pass**: `document_discovery`, which beancount
//!   runs first of all (`PLUGINS_PRE`) and whose `Document` directives
//!   carry no amounts, so running it ahead of booking is invisible.
//!   `auto_accounts` was here too; it is a regular plugin now, run where
//!   it is declared as beancount runs it, and Early validation reads its
//!   opens from a provisional view instead (the loader's
//!   `early_validation_view`).
//! - **Post-booking regular pass**: transformations on already-
//!   booked directives — most plugins, including the cost-spec-
//!   reading ones (`implicit_prices`, `unrealized`, etc.) that need
//!   to see filled-in per-unit values from the booker.
//!
//! Each native plugin declares which pass it runs in by implementing
//! either [`SynthPlugin`] or [`RegularPlugin`] (both extend the base
//! [`NativePlugin`] trait). The registry holds two separately-typed
//! Vecs (`Vec<Box<dyn SynthPlugin>>` and `Vec<Box<dyn RegularPlugin>>`),
//! and the loader's runner consults the typed registry for the
//! appropriate pass via [`NativePluginRegistry::find_synth`] /
//! [`NativePluginRegistry::find_regular`]. The returned trait
//! reference's type matches the pass: `find_synth` can never return
//! a `RegularPlugin` and vice versa, so the dispatch site can't
//! accidentally invoke a wrong-pass plugin even on a name collision.
//!
//! ## Where the discipline is enforced
//!
//! The marker traits are intentionally **not mutually exclusive** at
//! the type level — `SynthPlugin` and `RegularPlugin` are empty
//! sub-traits of `NativePlugin`, and nothing in the type system
//! prevents a single type from implementing both. Exclusivity is
//! enforced by:
//!
//! 1. **Registry construction convention**: each plugin is pushed
//!    into exactly one of the two Vecs in `build_global_registry`.
//! 2. **A pinned test** (`test_registry_synth_and_regular_are_disjoint`):
//!    iterates `registry.iter()` and asserts every plugin lives in
//!    exactly one Vec — CI catches a wrong-pass registration or a
//!    type that implements both markers and ends up in both Vecs.
//!
//! The marker pair is therefore lighter than full type-level
//! exclusivity (which would need negative trait bounds or a sealed
//! pass-marker pattern that breaks object safety in our registry) —
//! the cost is one assertion in CI instead of a compile error.
//!
//! ## Why a marker-trait pair rather than a single trait with a const
//!
//! `const PASS: PluginPass` on the base trait would be cleaner if
//! consts were object-safe — but they aren't, and the registry uses
//! trait objects (`Box<dyn SynthPlugin>` / `Box<dyn RegularPlugin>`)
//! for heterogeneous storage. The marker-pair approach gives the
//! dispatch-site type guarantee (described above) at the cost of one
//! extra empty `impl` line per plugin.
//!
//! ## WASM and Python plugins
//!
//! Non-native plugins don't implement `NativePlugin` and therefore
//! aren't held in this registry. They're dispatched by the loader
//! through path-based name resolution, run only in the post-booking
//! regular pass, and never carry a synth/regular marker at the type
//! level. Synth-pass semantics are a native-only concern.

mod plugins;

pub use plugins::*;

use std::sync::LazyLock;

use crate::types::PluginInput;
use crate::types::PluginOutput;

/// Base capability for native plugins. Both [`SynthPlugin`] and
/// [`RegularPlugin`] extend this — every native plugin has these
/// three methods regardless of pass.
///
/// The bounds (`Send + Sync`) are the minimum to satisfy the
/// global singleton registry; the registry's `Box<dyn ...>` storage
/// implicitly requires `'static`, but the trait itself doesn't add
/// that bound so external implementors can write borrowing impls
/// for non-registry use (testing helpers, ad-hoc adapters).
pub trait NativePlugin: Send + Sync {
    /// Plugin name (short form — `"implicit_prices"`, not the
    /// fully-qualified module path).
    fn name(&self) -> &'static str;

    /// Plugin description for `--help` and similar UI surfaces.
    fn description(&self) -> &'static str;

    /// Process directives and return modified directives + errors.
    fn process(&self, input: PluginInput) -> PluginOutput;
}

/// Marker trait: a plugin that runs in the **pre-booking synth pass**.
///
/// Synth plugins inject directives before booking and before
/// validation. Only `document_discovery` is one: its output carries no
/// amounts and beancount runs it before every other plugin, so the order
/// is not observable. A plugin whose place among the others IS observable
/// (`auto_accounts`: a `close_tree` declared before it must not see its
/// opens) is a regular plugin.
///
/// Implement this trait (in addition to [`NativePlugin`]) for any
/// plugin that synthesizes directives. The registry's
/// [`NativePluginRegistry::find_synth`] lookup only returns plugins
/// implementing this marker; a regular plugin can't accidentally
/// be invoked in the synth pass.
pub trait SynthPlugin: NativePlugin {}

/// Marker trait: a plugin that runs in the **post-booking regular pass**.
///
/// Regular plugins transform already-booked directives. The
/// cost-spec-reading ones (`implicit_prices`,
/// `capital_gains_classifier`, `check_average_cost`, `sell_gains`,
/// `unrealized`, `valuation`) specifically need to see filled-in
/// per-unit values on `CostNumber::PerUnitFromTotal` — which is
/// what booking produces. Running them pre-booking would see the
/// raw `Total` shape and produce wrong results.
///
/// Implement this trait (in addition to [`NativePlugin`]) for any
/// plugin that transforms post-booking directives. Most plugins go
/// here.
pub trait RegularPlugin: NativePlugin {}

/// Registry of built-in native plugins, split by pass.
///
/// Holding synth and regular plugins in separately-typed `Vec`s lets
/// the loader's pass-dispatch site ask for the right kind directly:
/// the returned trait reference's type matches the pass, so a
/// regular-pass plugin can't be returned from `find_synth` even on a
/// name collision.
///
/// The loader still gates two **implicit** invocations on `LoadOptions` /
/// `Options` flags (`options.auto_accounts`, in the regular pass after the
/// file's plugins, and the `option "documents"` directive that drives
/// `document_discovery`, in the synth pass),
/// but those flow through the same unified dispatch loop as
/// file-declared and CLI plugins — there's no per-plugin special
/// case at the dispatch site.
pub struct NativePluginRegistry {
    synth: Vec<Box<dyn SynthPlugin>>,
    regular: Vec<Box<dyn RegularPlugin>>,
}

/// The third-party plugin modules native plugins stand in for, by exact path.
///
/// Each maps a module path to the native plugin's name. Documented in
/// `docs/reference/plugins.md` ("Supported Python Plugins") and
/// `docs/reference/compatibility.md` #2.
pub const THIRD_PARTY_MODULES: &[(&str, &str)] = &[
    ("beancount_reds_plugins.zerosum.zerosum", "zerosum"),
    (
        "beancount_reds_plugins.effective_date.effective_date",
        "effective_date",
    ),
    (
        "beancount_reds_plugins.rename_accounts.rename_accounts",
        "rename_accounts",
    ),
    (
        "beancount_reds_plugins.box_accrual.box_accrual",
        "box_accrual",
    ),
    (
        "beancount_reds_plugins.capital_gains_classifier.long_short",
        "long_short",
    ),
    (
        "beancount_reds_plugins.capital_gains_classifier.gain_loss",
        "gain_loss",
    ),
    ("beancount_ln_plugins.ln.long_short", "long_short"),
    ("beanahead.plugins.rx_txn_plugin", "rx_txn_plugin"),
    (
        "tariochbctools.plugins.generate_base_ccy_prices",
        "generate_base_ccy_prices",
    ),
    (
        "beancount_lazy_plugins.generate_base_ccy_prices",
        "generate_base_ccy_prices",
    ),
    ("beancount_lazy_plugins.valuation", "valuation"),
    (
        "beancount_options.check_option_expiry",
        "check_option_expiry",
    ),
    (
        "beancount_options.check_option_assignment",
        "check_option_assignment",
    ),
];

/// The native plugin name a `plugin` reference names, or `None` when it
/// names no native plugin.
///
/// A reference names a native plugin by exactly one of:
///
/// - its bare name (`"zerosum"`, `"implicit_prices"`);
/// - beancount's module path for it, `beancount.plugins.<name>`
///   (`"beancount.plugins.implicit_prices"`);
/// - the exact module path of the third-party plugin it stands in for
///   ([`THIRD_PARTY_MODULES`]: `"beancount_reds_plugins.zerosum.zerosum"`).
///
/// Anything else is not native, and resolves as any other module reference
/// (a plugin that is not found). It used to match by the last dotted
/// segment alone, so a misspelled `beancount.plugin.unrealized` (or
/// `anything.zerosum`) silently ran the native plugin, where beancount
/// fails to import it.
#[must_use]
pub fn native_plugin_name(name: &str) -> Option<&str> {
    if !name.contains('.') {
        return Some(name);
    }
    if let Some(rest) = name.strip_prefix("beancount.plugins.")
        && !rest.contains('.')
    {
        return Some(rest);
    }
    THIRD_PARTY_MODULES
        .iter()
        .find(|(module, _)| *module == name)
        .map(|(_, native)| *native)
}

/// Build the singleton registry. Called once per process via the
/// `LazyLock` below; broken out as a named function so the call stack
/// reflects what's happening at first access.
fn build_global_registry() -> NativePluginRegistry {
    let synth: Vec<Box<dyn SynthPlugin>> = vec![Box::new(DocumentDiscoveryPlugin)];
    let regular: Vec<Box<dyn RegularPlugin>> = vec![
        Box::new(AutoAccountsPlugin),
        Box::new(ImplicitPricesPlugin),
        Box::new(CheckCommodityPlugin),
        Box::new(AutoTagPlugin::new()),
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
        Box::new(CheckOptionExpiryPlugin),
        Box::new(CheckOptionAssignmentPlugin),
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
    ];
    NativePluginRegistry { synth, regular }
}

/// Process-wide singleton registry — the registry holds no per-load
/// state, so allocating one per call is pure waste. Use
/// [`NativePluginRegistry::global`] to access it.
static GLOBAL_REGISTRY: LazyLock<NativePluginRegistry> = LazyLock::new(build_global_registry);

impl NativePluginRegistry {
    /// Access the process-wide registry singleton.
    ///
    /// The registry is immutable and stateless; reuse this reference
    /// instead of constructing a fresh registry per call. The
    /// underlying `LazyLock` initializes on first access.
    #[must_use]
    pub fn global() -> &'static Self {
        &GLOBAL_REGISTRY
    }

    /// Find a **synth-pass** plugin by name.
    ///
    /// Returns `None` if the plugin doesn't exist OR if it exists
    /// but is a regular-pass plugin — the type system guarantees the
    /// returned reference is `dyn SynthPlugin`.
    ///
    /// Accepts both short names (`"auto_accounts"`) and fully
    /// qualified module paths (`"beancount.plugins.auto_accounts"`).
    pub fn find_synth(&self, name: &str) -> Option<&dyn SynthPlugin> {
        let short_name = native_plugin_name(name)?;
        self.synth
            .iter()
            .find(|p| p.name() == short_name)
            .map(std::convert::AsRef::as_ref)
    }

    /// Find a **regular-pass** plugin by name.
    ///
    /// Returns `None` if the plugin doesn't exist OR if it exists
    /// but is a synth-pass plugin — the type system guarantees the
    /// returned reference is `dyn RegularPlugin`.
    ///
    /// Accepts both short names (`"implicit_prices"`) and fully
    /// qualified module paths (`"beancount.plugins.implicit_prices"`).
    pub fn find_regular(&self, name: &str) -> Option<&dyn RegularPlugin> {
        let short_name = native_plugin_name(name)?;
        self.regular
            .iter()
            .find(|p| p.name() == short_name)
            .map(std::convert::AsRef::as_ref)
    }

    /// Iterate every plugin in the registry, synth then regular.
    /// Returns trait references upcast to the base [`NativePlugin`] —
    /// callers that need pass information should use
    /// [`Self::find_synth`] / [`Self::find_regular`] instead.
    pub fn iter(&self) -> impl Iterator<Item = &dyn NativePlugin> {
        self.synth
            .iter()
            .map(|p| p.as_ref() as &dyn NativePlugin)
            .chain(self.regular.iter().map(|p| p.as_ref() as &dyn NativePlugin))
    }

    /// Check if a name refers to any plugin in this registry, in
    /// either pass. Use this for existence queries; for invocation
    /// use [`Self::find_synth`] / [`Self::find_regular`] so the
    /// returned reference's type carries the pass.
    #[must_use]
    pub fn has(&self, name: &str) -> bool {
        let Some(short_name) = native_plugin_name(name) else {
            return false;
        };
        self.synth.iter().any(|p| p.name() == short_name)
            || self.regular.iter().any(|p| p.name() == short_name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_native_plugin_name_bare_and_beancount_path() {
        assert_eq!(native_plugin_name("zerosum"), Some("zerosum"));
        assert_eq!(
            native_plugin_name("beancount.plugins.implicit_prices"),
            Some("implicit_prices")
        );
        assert_eq!(native_plugin_name(""), Some(""));
    }

    #[test]
    fn test_native_plugin_name_third_party_exact_paths() {
        assert_eq!(
            native_plugin_name("beancount_reds_plugins.zerosum.zerosum"),
            Some("zerosum")
        );
        assert_eq!(
            native_plugin_name("beancount_reds_plugins.capital_gains_classifier.gain_loss"),
            Some("gain_loss")
        );
        assert_eq!(
            native_plugin_name("beanahead.plugins.rx_txn_plugin"),
            Some("rx_txn_plugin")
        );
        assert_eq!(
            native_plugin_name("tariochbctools.plugins.generate_base_ccy_prices"),
            Some("generate_base_ccy_prices")
        );
    }

    /// A path that only ENDS in a native plugin's name is not that plugin:
    /// beancount fails to import `beancount.plugin.unrealized` (the
    /// singular `plugin`), and so does rledger now, where it ran the native
    /// `unrealized`.
    #[test]
    fn test_native_plugin_name_rejects_other_paths() {
        for name in [
            "beancount.plugin.unrealized",
            "my.zerosum",
            "beancount.plugins.sub.leafonly",
            "beancount_reds_plugins.zerosum",
        ] {
            assert_eq!(native_plugin_name(name), None, "{name}");
            assert!(!NativePluginRegistry::global().has(name), "{name}");
        }
    }

    #[test]
    fn test_registry_find_regular_short_name() {
        let registry = NativePluginRegistry::global();
        assert!(registry.find_regular("implicit_prices").is_some());
        assert!(registry.find_regular("zerosum").is_some());
        assert!(registry.find_regular("nonexistent").is_none());
    }

    #[test]
    fn test_registry_find_regular_qualified_name() {
        let registry = NativePluginRegistry::global();
        assert!(
            registry
                .find_regular("beancount.plugins.implicit_prices")
                .is_some()
        );
        assert!(
            registry
                .find_regular("beanahead.plugins.rx_txn_plugin")
                .is_some()
        );
        assert!(
            registry
                .find_regular("beancount_reds_plugins.zerosum.zerosum")
                .is_some()
        );
        assert!(
            registry
                .find_regular("beancount_reds_plugins.capital_gains_classifier.gain_loss")
                .is_some()
        );
    }

    /// Pin the trait-split contract (issue #1166): EVERY plugin in the
    /// registry lives in exactly one pass-typed Vec. This is what
    /// catches "regular plugin invoked in synth pass" at the type
    /// level — the lookup in the wrong Vec wouldn't find it.
    ///
    /// Exhaustive over `list()` so adding a new plugin without
    /// declaring a pass marker can't slip past CI as a Vec-membership
    /// mistake. Also covers `has` and prefix-stripping coverage that
    /// the old separate `is_builtin_*` tests used to duplicate.
    #[test]
    fn test_registry_synth_and_regular_are_disjoint() {
        let registry = NativePluginRegistry::global();

        for plugin in registry.iter() {
            let name = plugin.name();
            let in_synth = registry.find_synth(name).is_some();
            let in_regular = registry.find_regular(name).is_some();
            assert!(
                in_synth ^ in_regular,
                "plugin {name:?} must live in exactly one pass Vec (synth={in_synth}, regular={in_regular})",
            );
            assert!(
                registry.has(name),
                "list() yielded {name:?} but has() disagrees"
            );
        }

        // Non-existent names return false from every lookup.
        assert!(!registry.has("nonexistent"));
        assert!(registry.find_synth("nonexistent").is_none());
        assert!(registry.find_regular("nonexistent").is_none());

        // Prefix-stripping works for fully-qualified module paths.
        assert!(registry.has("beancount.plugins.implicit_prices"));
        assert!(registry.has("beanahead.plugins.rx_txn_plugin"));
        assert!(registry.has("beancount_reds_plugins.zerosum.zerosum"));
        assert!(!registry.has("some.random.nonexistent"));
    }
}
