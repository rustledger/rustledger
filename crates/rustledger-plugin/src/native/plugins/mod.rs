//! Native plugin implementations, one per file.

pub mod utils;

mod auto_accounts;
mod auto_tag;
mod box_accrual;
mod capital_gains_classifier;
mod check_average_cost;
mod check_closing;
mod check_commodity;
mod check_drained;
mod close_tree;
mod coherent_cost;
mod commodity_attr;
mod currency_accounts;
mod document_discovery;
mod effective_date;
mod forecast;
mod generate_base_ccy_prices;
mod implicit_prices;
mod leaf_only;
mod no_duplicates;
mod no_unused;
mod one_commodity;
mod pedantic;
mod rename_accounts;
mod rx_txn;
mod sell_gains;
mod split_expenses;
mod unique_prices;
mod unrealized;
mod valuation;
mod zerosum;

pub use auto_accounts::{AUTO_ACCOUNTS_NAME, AutoAccountsPlugin};
pub use auto_tag::AutoTagPlugin;
pub use box_accrual::BoxAccrualPlugin;
pub use capital_gains_classifier::{CapitalGainsGainLossPlugin, CapitalGainsLongShortPlugin};
pub use check_average_cost::CheckAverageCostPlugin;
pub use check_closing::CheckClosingPlugin;
pub use check_commodity::CheckCommodityPlugin;
pub use check_drained::CheckDrainedPlugin;
pub use close_tree::CloseTreePlugin;
pub use coherent_cost::CoherentCostPlugin;
pub use commodity_attr::CommodityAttrPlugin;
pub use currency_accounts::CurrencyAccountsPlugin;
pub use document_discovery::{
    DOCUMENT_DISCOVERY_NAME, DocumentDiscoveryPlugin, document_discovery_config,
};
pub use effective_date::EffectiveDatePlugin;
pub use forecast::ForecastPlugin;
pub use generate_base_ccy_prices::GenerateBaseCcyPricesPlugin;
pub use implicit_prices::ImplicitPricesPlugin;
pub use leaf_only::LeafOnlyPlugin;
pub use no_duplicates::NoDuplicatesPlugin;
pub use no_unused::NoUnusedPlugin;
pub use one_commodity::OneCommodityPlugin;
pub use pedantic::PedanticPlugin;
pub use rename_accounts::RenameAccountsPlugin;
pub use rx_txn::RxTxnPlugin;
pub use sell_gains::SellGainsPlugin;
pub use split_expenses::SplitExpensesPlugin;
pub use unique_prices::UniquePricesPlugin;
pub use unrealized::UnrealizedPlugin;
pub use valuation::ValuationPlugin;
pub use zerosum::ZerosumPlugin;
