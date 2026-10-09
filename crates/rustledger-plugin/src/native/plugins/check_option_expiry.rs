//! Error on option contracts still open after their expiry date.
//!
//! Option contracts are recognized by their OCC symbol with spaces removed:
//! a root of 1–6 characters, the expiry as `YYMMDD`, `C` or `P`, and the
//! strike × 1000 as 8 digits — e.g. `AAPL261016P00230000` is the AAPL
//! 2026-10-16 230 put. Every other commodity is ignored.
//!
//! "Today" is the date of the last directive in the ledger, not the system
//! clock, so the result is the same on every run. A contract is reported when
//! its net units in an account are non-zero and the ledger contains an entry
//! dated after its expiry. A close dated on the expiry day itself is fine.
//!
//! The plugin only reports: every directive is kept unchanged and nothing is
//! inserted, so a ledger stays complete without it.

use std::collections::BTreeMap;
use std::str::FromStr;

use rust_decimal::Decimal;

use crate::types::{DirectiveData, PluginError, PluginInput, PluginOp, PluginOutput};

use super::super::{NativePlugin, RegularPlugin};
use super::option_symbol::parse_occ;

/// Net position of one contract in one account.
struct Position {
    expiry: String,
    net: Decimal,
    /// Index of the directive that last opened the position from flat.
    opened_at: usize,
}

/// Plugin that reports option contracts left open past expiry.
pub struct CheckOptionExpiryPlugin;

impl NativePlugin for CheckOptionExpiryPlugin {
    fn name(&self) -> &'static str {
        "check_option_expiry"
    }

    fn description(&self) -> &'static str {
        "Error on option contracts still open after their expiry date"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        // Walk directives in date order without assuming the input is sorted.
        // `sort_by` is stable, so same-day directives keep their file order.
        let mut order: Vec<usize> = (0..input.directives.len()).collect();
        order.sort_by(|&a, &b| input.directives[a].date.cmp(&input.directives[b].date));

        let mut positions: BTreeMap<(String, String), Position> = BTreeMap::new();
        for &i in &order {
            let DirectiveData::Transaction(txn) = &input.directives[i].data else {
                continue;
            };
            for posting in &txn.postings {
                let Some(units) = &posting.units else {
                    continue;
                };
                let Some(occ) = parse_occ(&units.currency) else {
                    continue;
                };
                let Ok(number) = Decimal::from_str(&units.number) else {
                    continue;
                };
                let pos = positions
                    .entry((posting.account.clone(), units.currency.clone()))
                    .or_insert(Position {
                        expiry: occ.expiry,
                        net: Decimal::ZERO,
                        opened_at: i,
                    });
                if pos.net.is_zero() {
                    pos.opened_at = i;
                }
                pos.net += number;
            }
        }

        // ISO dates compare correctly as strings.
        let last_date = input.directives.iter().map(|d| d.date.as_str()).max();

        let mut errors = Vec::new();
        if let Some(last_date) = last_date {
            for ((account, symbol), pos) in &positions {
                if pos.net.is_zero() || pos.expiry.as_str() >= last_date {
                    continue;
                }
                let mut error = PluginError::error(format!(
                    "{symbol} expired {} but {} contract(s) remain open in {account}",
                    pos.expiry,
                    pos.net.normalize()
                ));
                let opened = &input.directives[pos.opened_at];
                if let (Some(file), Some(line)) = (&opened.filename, opened.lineno) {
                    error = error.at(file.clone(), line);
                }
                errors.push(error);
            }
        }

        PluginOutput {
            ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
            errors,
        }
    }
}

impl RegularPlugin for CheckOptionExpiryPlugin {}
